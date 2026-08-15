//! I2P SAM v3.1 transport support.

use std::{collections::HashMap, fs, path::PathBuf, sync::Arc, time::Duration};

use anyhow::{Context, Result, bail};
use base64::Engine;
use rand::random;
use sha2::{Digest, Sha256};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use tokio::sync::Mutex;

use crate::address::NetworkEndpoint;

/// SAM v3.1 does not carry a Bitcoin service port. Core represents those
/// endpoints with port zero; older local address entries in this node use the
/// SAM control port, so both forms are accepted when connecting.
pub(crate) const I2P_SAM_PORT: u16 = 7656;
const MAX_SAM_MESSAGE_BYTES: usize = 65_536;
const SAM_REPLY_TIMEOUT: Duration = Duration::from_secs(3 * 60);

#[derive(Clone)]
pub(crate) struct I2pSam {
    control_address: std::net::SocketAddr,
    datadir: PathBuf,
    connect_timeout: Duration,
    persistent: bool,
    state: Arc<Mutex<SamState>>,
}

#[derive(Default)]
struct SamState {
    session: Option<SamSession>,
}

struct SamSession {
    session_id: String,
    destination: Vec<u8>,
    control: TcpStream,
}

#[derive(Clone)]
struct SamSessionInfo {
    session_id: String,
    destination: Vec<u8>,
}

struct SamReply {
    full: String,
    fields: HashMap<String, String>,
}

impl I2pSam {
    pub(crate) fn new(
        control_address: std::net::SocketAddr,
        datadir: PathBuf,
        connect_timeout: Duration,
        persistent: bool,
    ) -> Self {
        Self {
            control_address,
            datadir,
            connect_timeout,
            persistent,
            state: Arc::new(Mutex::new(SamState::default())),
        }
    }

    pub(crate) async fn local_endpoint(&self) -> Result<NetworkEndpoint> {
        if !self.persistent {
            bail!("I2P inbound listening requires a persistent SAM session")
        }
        let session = self.ensure_persistent_session().await?;
        Ok(NetworkEndpoint::I2p {
            address: destination_address(&session.destination),
            port: I2P_SAM_PORT,
        })
    }

    pub(crate) async fn connect(&self, endpoint: &NetworkEndpoint) -> Result<TcpStream> {
        let result = self.connect_inner(endpoint).await;
        if result.is_err() && self.persistent {
            self.reset().await;
        }
        result
    }

    async fn connect_inner(&self, endpoint: &NetworkEndpoint) -> Result<TcpStream> {
        let NetworkEndpoint::I2p { port, .. } = endpoint else {
            bail!("I2P SAM can only connect to I2P endpoints")
        };
        if *port != 0 && *port != I2P_SAM_PORT {
            bail!("I2P SAM v3.1 only supports port 0 or {I2P_SAM_PORT}, not {port}")
        }

        if self.persistent {
            let session = self.ensure_persistent_session().await?;
            let mut stream = self.open_control().await?;
            self.hello(&mut stream).await?;
            self.stream_connect(&mut stream, &session, endpoint).await?;
            Ok(stream)
        } else {
            // A transient session is intentionally scoped to one outbound
            // connection. Keeping its control socket open is required by SAM
            // for the lifetime of the returned stream.
            let mut session = self.create_session(false).await?;
            let info = session.info();
            self.stream_connect(&mut session.control, &info, endpoint)
                .await?;
            Ok(session.control)
        }
    }

    pub(crate) async fn accept(&self) -> Result<(TcpStream, NetworkEndpoint)> {
        if !self.persistent {
            bail!("I2P inbound listening requires a persistent SAM session")
        }
        let session = self.ensure_persistent_session().await?;
        let mut stream = self.open_control().await?;
        self.hello(&mut stream).await?;
        let reply = self
            .request(
                &mut stream,
                &format!("STREAM ACCEPT ID={} SILENT=false", session.session_id),
                false,
            )
            .await?;
        if reply.fields.get("RESULT").map(String::as_str) != Some("OK") {
            bail!("I2P SAM rejected STREAM ACCEPT: {}", reply.full)
        }

        // SAM sends the connecting peer's destination as the first line on
        // the accepted stream before handing over the Bitcoin byte stream.
        let peer_destination = read_line(&mut stream).await?;
        let peer_destination = decode_i2p_base64(peer_destination.trim())
            .with_context(|| "decoding I2P peer destination from SAM")?;
        Ok((
            stream,
            NetworkEndpoint::I2p {
                address: destination_address(&peer_destination),
                port: I2P_SAM_PORT,
            },
        ))
    }

    pub(crate) async fn reset(&self) {
        self.state.lock().await.session = None;
    }

    async fn ensure_persistent_session(&self) -> Result<SamSessionInfo> {
        let mut state = self.state.lock().await;
        if let Some(session) = state.session.as_ref() {
            return Ok(session.info());
        }
        let session = self.create_session(true).await?;
        let info = session.info();
        state.session = Some(session);
        Ok(info)
    }

    async fn create_session(&self, persistent: bool) -> Result<SamSession> {
        let mut control = self.open_control().await?;
        self.hello(&mut control).await?;
        let session_id = format!("bitcoin-rs-{}", hex::encode(random::<[u8; 8]>()));

        let private_key = if persistent {
            let path = self.datadir.join("i2p_private_key");
            match fs::read(&path) {
                Ok(key) if !key.is_empty() => key,
                Ok(_) => bail!("I2P private key file {} is empty", path.display()),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    let reply = self
                        .request(&mut control, "DEST GENERATE SIGNATURE_TYPE=7", true)
                        .await?;
                    let key = decode_i2p_base64(reply.required("PRIV")?)
                        .with_context(|| "decoding generated I2P private key")?;
                    fs::write(&path, &key).with_context(|| {
                        format!("writing generated I2P private key to {}", path.display())
                    })?;
                    set_private_key_permissions(&path)?;
                    key
                }
                Err(error) => {
                    return Err(error)
                        .with_context(|| format!("reading I2P private key {}", path.display()));
                }
            }
        } else {
            Vec::new()
        };

        let destination = if persistent {
            destination_from_private_key(&private_key)?
        } else {
            let reply = self
                .request(
                    &mut control,
                    &format!(
                        concat!(
                            "SESSION CREATE STYLE=STREAM ID={} DESTINATION=TRANSIENT ",
                            "SIGNATURE_TYPE=7 i2cp.leaseSetEncType=4,0 inbound.quantity=1 ",
                            "outbound.quantity=1"
                        ),
                        session_id
                    ),
                    true,
                )
                .await?;
            let key = decode_i2p_base64(reply.required("DESTINATION")?)
                .with_context(|| "decoding transient I2P private key")?;
            destination_from_private_key(&key)?
        };

        if persistent {
            let private_key = encode_i2p_base64(&private_key);
            self.request(
                &mut control,
                &format!(
                    concat!(
                        "SESSION CREATE STYLE=STREAM ID={} DESTINATION={} ",
                        "i2cp.leaseSetEncType=4,0 inbound.quantity=3 outbound.quantity=3"
                    ),
                    session_id, private_key
                ),
                true,
            )
            .await?;
        }

        Ok(SamSession {
            session_id,
            destination,
            control,
        })
    }

    async fn stream_connect(
        &self,
        stream: &mut TcpStream,
        session: &SamSessionInfo,
        endpoint: &NetworkEndpoint,
    ) -> Result<()> {
        let lookup = self
            .request(
                stream,
                &format!("NAMING LOOKUP NAME={}", endpoint.host_string()),
                true,
            )
            .await?;
        let destination = lookup.required("VALUE")?;
        self.request(
            stream,
            &format!(
                "STREAM CONNECT ID={} DESTINATION={} SILENT=false",
                session.session_id, destination
            ),
            true,
        )
        .await?;
        Ok(())
    }

    async fn open_control(&self) -> Result<TcpStream> {
        tokio::time::timeout(
            self.connect_timeout,
            TcpStream::connect(self.control_address),
        )
        .await
        .with_context(|| {
            format!(
                "connecting to I2P SAM control service {}",
                self.control_address
            )
        })?
        .with_context(|| {
            format!(
                "connecting to I2P SAM control service {}",
                self.control_address
            )
        })
    }

    async fn hello(&self, stream: &mut TcpStream) -> Result<()> {
        self.request(stream, "HELLO VERSION MIN=3.1 MAX=3.1", true)
            .await?;
        Ok(())
    }

    async fn request(
        &self,
        stream: &mut TcpStream,
        request: &str,
        check_result_ok: bool,
    ) -> Result<SamReply> {
        write_line(stream, request).await?;
        let full = read_line(stream).await?;
        let fields = full
            .split_whitespace()
            .filter_map(|field| field.split_once('='))
            .map(|(key, value)| (key.to_owned(), value.trim_matches('"').to_owned()))
            .collect::<HashMap<_, _>>();
        let reply = SamReply { full, fields };
        if check_result_ok && reply.fields.get("RESULT").map(String::as_str) != Some("OK") {
            bail!("I2P SAM rejected `{request}`: {}", reply.full)
        }
        Ok(reply)
    }
}

impl SamSession {
    fn info(&self) -> SamSessionInfo {
        SamSessionInfo {
            session_id: self.session_id.clone(),
            destination: self.destination.clone(),
        }
    }
}

impl SamReply {
    fn required(&self, key: &str) -> Result<&str> {
        self.fields
            .get(key)
            .map(String::as_str)
            .with_context(|| format!("I2P SAM reply is missing {key}="))
    }
}

async fn write_line(stream: &mut TcpStream, line: &str) -> Result<()> {
    tokio::time::timeout(SAM_REPLY_TIMEOUT, stream.write_all(line.as_bytes()))
        .await
        .context("timed out writing to I2P SAM")??;
    tokio::time::timeout(SAM_REPLY_TIMEOUT, stream.write_all(b"\n"))
        .await
        .context("timed out writing to I2P SAM")??;
    Ok(())
}

async fn read_line(stream: &mut TcpStream) -> Result<String> {
    let mut bytes = Vec::new();
    loop {
        let mut byte = [0u8; 1];
        tokio::time::timeout(SAM_REPLY_TIMEOUT, stream.read_exact(&mut byte))
            .await
            .context("timed out reading from I2P SAM")??;
        if byte[0] == b'\n' {
            break;
        }
        if bytes.len() >= MAX_SAM_MESSAGE_BYTES {
            bail!("I2P SAM reply exceeds {MAX_SAM_MESSAGE_BYTES} bytes")
        }
        bytes.push(byte[0]);
    }
    if bytes.last() == Some(&b'\r') {
        bytes.pop();
    }
    String::from_utf8(bytes).context("I2P SAM reply is not UTF-8")
}

fn destination_from_private_key(private_key: &[u8]) -> Result<Vec<u8>> {
    const DESTINATION_BASE_LENGTH: usize = 387;
    const CERTIFICATE_LENGTH_OFFSET: usize = 385;
    if private_key.len() < DESTINATION_BASE_LENGTH {
        bail!("I2P private key is too short: {} bytes", private_key.len())
    }
    let certificate_length = usize::from(u16::from_be_bytes(
        private_key[CERTIFICATE_LENGTH_OFFSET..CERTIFICATE_LENGTH_OFFSET + 2]
            .try_into()
            .expect("slice length checked"),
    ));
    let destination_length = DESTINATION_BASE_LENGTH + certificate_length;
    if destination_length > private_key.len() {
        bail!(
            "I2P private key certificate length requires {destination_length} bytes, found {}",
            private_key.len()
        )
    }
    Ok(private_key[..destination_length].to_vec())
}

fn destination_address(destination: &[u8]) -> [u8; 32] {
    Sha256::digest(destination).into()
}

fn decode_i2p_base64(value: &str) -> Result<Vec<u8>> {
    let mut standard = value.trim().replace('-', "+").replace('~', "/");
    while standard.len() % 4 != 0 {
        standard.push('=');
    }
    base64::engine::general_purpose::STANDARD
        .decode(standard)
        .context("invalid I2P base64")
}

fn encode_i2p_base64(value: &[u8]) -> String {
    base64::engine::general_purpose::STANDARD
        .encode(value)
        .trim_end_matches('=')
        .replace('+', "-")
        .replace('/', "~")
}

fn set_private_key_permissions(path: &std::path::Path) -> Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(path, fs::Permissions::from_mode(0o600))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::io::AsyncBufReadExt;
    use tokio::net::TcpListener;

    #[test]
    fn i2p_base64_round_trip_uses_url_safe_alphabet() {
        let bytes = [0xfb, 0xff, 0x00, 0x01];
        let encoded = encode_i2p_base64(&bytes);
        assert_eq!(encoded, "-~8AAQ");
        assert_eq!(decode_i2p_base64(&encoded).unwrap(), bytes);
    }

    #[test]
    fn private_key_destination_uses_certificate_length() {
        let mut key = vec![0; 387 + 3];
        key[385..387].copy_from_slice(&3u16.to_be_bytes());
        assert_eq!(destination_from_private_key(&key).unwrap().len(), 390);
    }

    #[tokio::test]
    async fn transient_session_connects_and_keeps_stream_open() -> Result<()> {
        let listener = TcpListener::bind("127.0.0.1:0").await?;
        let address = listener.local_addr()?;
        let mut private_key = vec![0; 387];
        private_key[0] = 7;
        let destination = encode_i2p_base64(&private_key);
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            let mut reader = tokio::io::BufReader::new(stream);
            let mut line = String::new();
            reader.read_line(&mut line).await.unwrap();
            assert_eq!(line.trim_end(), "HELLO VERSION MIN=3.1 MAX=3.1");
            reader
                .get_mut()
                .write_all(b"HELLO REPLY RESULT=OK VERSION=3.1\n")
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert!(line.starts_with("SESSION CREATE STYLE=STREAM"));
            reader
                .get_mut()
                .write_all(
                    format!("SESSION STATUS RESULT=OK DESTINATION={destination}\n").as_bytes(),
                )
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert!(line.starts_with("NAMING LOOKUP NAME="));
            reader
                .get_mut()
                .write_all(format!("NAMING REPLY RESULT=OK VALUE={destination}\n").as_bytes())
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert!(line.starts_with("STREAM CONNECT ID="));
            reader
                .get_mut()
                .write_all(b"STREAM STATUS RESULT=OK\npeer-data")
                .await
                .unwrap();
        });

        let sam = I2pSam::new(
            address,
            tempfile::tempdir()?.keep(),
            Duration::from_secs(1),
            false,
        );
        let endpoint = NetworkEndpoint::I2p {
            address: [1; 32],
            // Core's generated fixed seeds use the SAM 3.1 port-zero form.
            port: 0,
        };
        let mut stream = sam.connect(&endpoint).await?;
        let mut data = [0; 9];
        stream.read_exact(&mut data).await?;
        assert_eq!(&data, b"peer-data");
        server.await.unwrap();
        Ok(())
    }

    #[tokio::test]
    async fn persistent_session_advertises_and_accepts_i2p_peers() -> Result<()> {
        let listener = TcpListener::bind("127.0.0.1:0").await?;
        let address = listener.local_addr()?;
        let mut private_key = vec![0; 387];
        private_key[0] = 9;
        let private_key_b64 = encode_i2p_base64(&private_key);
        let mut peer_destination = vec![0; 387];
        peer_destination[0] = 11;
        let peer_destination_b64 = encode_i2p_base64(&peer_destination);
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            let mut reader = tokio::io::BufReader::new(stream);
            let mut line = String::new();
            reader.read_line(&mut line).await.unwrap();
            assert_eq!(line.trim_end(), "HELLO VERSION MIN=3.1 MAX=3.1");
            reader
                .get_mut()
                .write_all(b"HELLO REPLY RESULT=OK VERSION=3.1\n")
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert_eq!(line.trim_end(), "DEST GENERATE SIGNATURE_TYPE=7");
            reader
                .get_mut()
                .write_all(format!("DEST REPLY RESULT=OK PRIV={private_key_b64}\n").as_bytes())
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert!(line.starts_with("SESSION CREATE STYLE=STREAM"));
            reader
                .get_mut()
                .write_all(b"SESSION STATUS RESULT=OK\n")
                .await
                .unwrap();

            let (stream, _) = listener.accept().await.unwrap();
            let mut reader = tokio::io::BufReader::new(stream);
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert_eq!(line.trim_end(), "HELLO VERSION MIN=3.1 MAX=3.1");
            reader
                .get_mut()
                .write_all(b"HELLO REPLY RESULT=OK VERSION=3.1\n")
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert!(line.starts_with("STREAM ACCEPT ID="));
            reader
                .get_mut()
                .write_all(format!("STREAM STATUS RESULT=OK\n{peer_destination_b64}\n").as_bytes())
                .await
                .unwrap();

            let (stream, _) = listener.accept().await.unwrap();
            let mut reader = tokio::io::BufReader::new(stream);
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert_eq!(line.trim_end(), "HELLO VERSION MIN=3.1 MAX=3.1");
            reader
                .get_mut()
                .write_all(b"HELLO REPLY RESULT=OK VERSION=3.1\n")
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert!(line.contains(&format!("DESTINATION={private_key_b64}")));
            reader
                .get_mut()
                .write_all(b"SESSION STATUS RESULT=OK\n")
                .await
                .unwrap();
        });

        let datadir = tempfile::tempdir()?;
        let sam = I2pSam::new(
            address,
            datadir.path().to_owned(),
            Duration::from_secs(1),
            true,
        );
        let local = sam.local_endpoint().await?;
        assert_eq!(local.port(), I2P_SAM_PORT);
        assert!(datadir.path().join("i2p_private_key").exists());
        let (mut stream, peer) = sam.accept().await?;
        assert_eq!(peer.port(), I2P_SAM_PORT);
        assert_eq!(peer.network_name(), "i2p");
        stream.shutdown().await?;
        drop(sam);
        let restarted = I2pSam::new(
            address,
            datadir.path().to_owned(),
            Duration::from_secs(1),
            true,
        );
        assert_eq!(restarted.local_endpoint().await?, local);
        server.await.unwrap();
        Ok(())
    }
}
