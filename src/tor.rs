//! Tor control-port support for automatic onion services.

use std::{
    collections::HashMap,
    fs,
    net::SocketAddr,
    path::{Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

use anyhow::{Context, Result, bail};
use parking_lot::RwLock;
use rand::random;
use sha2::{Digest, Sha256};
use tokio::{
    io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader},
    net::TcpStream,
};

use crate::address::NetworkEndpoint;

pub(crate) const DEFAULT_TOR_CONTROL_PORT: u16 = 9051;
pub(crate) const DEFAULT_TOR_SOCKS_PORT: u16 = 9050;

const MAX_TOR_LINE_LENGTH: usize = 100_000;
const TOR_REPLY_TIMEOUT: Duration = Duration::from_secs(3 * 60);
const TOR_COOKIE_SIZE: usize = 32;
const TOR_NONCE_SIZE: usize = 32;
const SAFE_SERVER_KEY: &[u8] = b"Tor safe cookie authentication server-to-controller hash";
const SAFE_CLIENT_KEY: &[u8] = b"Tor safe cookie authentication controller-to-server hash";

#[derive(Clone)]
pub(crate) struct TorController {
    control_address: SocketAddr,
    password: Option<String>,
    datadir: PathBuf,
    connect_timeout: Duration,
    socks_proxy: Arc<RwLock<Option<SocketAddr>>>,
    reachable: Arc<AtomicBool>,
}

#[derive(Debug)]
struct TorReply {
    code: u16,
    lines: Vec<String>,
}

impl TorController {
    pub(crate) fn new(
        control_address: SocketAddr,
        password: Option<String>,
        datadir: PathBuf,
        connect_timeout: Duration,
    ) -> Self {
        Self {
            control_address,
            password,
            datadir,
            connect_timeout,
            socks_proxy: Arc::new(RwLock::new(None)),
            reachable: Arc::new(AtomicBool::new(false)),
        }
    }

    pub(crate) fn is_reachable(&self) -> bool {
        self.reachable.load(Ordering::Relaxed)
    }

    pub(crate) fn socks_proxy(&self) -> Option<SocketAddr> {
        *self.socks_proxy.read()
    }

    pub(crate) fn clear(&self) {
        self.reachable.store(false, Ordering::Relaxed);
        *self.socks_proxy.write() = None;
    }

    /// Connect to Tor, authenticate, publish an onion service, and return the
    /// still-open control connection. Tor removes ephemeral services as soon
    /// as this connection closes, so the caller must retain it for the life
    /// of the service.
    pub(crate) async fn publish(
        &self,
        target: SocketAddr,
        virtual_port: u16,
    ) -> Result<(NetworkEndpoint, BufReader<TcpStream>)> {
        let stream = tokio::time::timeout(
            self.connect_timeout,
            TcpStream::connect(self.control_address),
        )
        .await
        .with_context(|| format!("connecting to Tor control service {}", self.control_address))?
        .with_context(|| format!("connecting to Tor control service {}", self.control_address))?;
        let mut reader = BufReader::new(stream);

        let protocol = self.command(&mut reader, "PROTOCOLINFO 1").await?;
        if protocol.code != 250 {
            bail!("Tor PROTOCOLINFO failed with status {}", protocol.code);
        }
        self.authenticate(&mut reader, &protocol.lines).await?;

        let socks_proxy = self
            .discover_socks_proxy(&mut reader)
            .await
            .unwrap_or_else(|_| SocketAddr::from(([127, 0, 0, 1], DEFAULT_TOR_SOCKS_PORT)));
        *self.socks_proxy.write() = Some(socks_proxy);

        let private_key_path = self.datadir.join("onion_v3_private_key");
        let private_key = match fs::read_to_string(&private_key_path) {
            Ok(key) if !key.trim().is_empty() => key.trim().to_owned(),
            Ok(_) => bail!(
                "Tor onion private key file {} is empty",
                private_key_path.display()
            ),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                "NEW:ED25519-V3".to_owned()
            }
            Err(error) => {
                return Err(error).with_context(|| {
                    format!(
                        "reading Tor onion private key {}",
                        private_key_path.display()
                    )
                });
            }
        };
        let reply = self
            .command(
                &mut reader,
                &format!("ADD_ONION {private_key} Port={virtual_port},{target}"),
            )
            .await?;
        if reply.code != 250 {
            bail!("Tor ADD_ONION failed with status {}", reply.code);
        }

        let mut service_id = None;
        let mut returned_private_key = None;
        for line in &reply.lines {
            if line == "OK" {
                continue;
            }
            let mapping = parse_mapping(line)?;
            if let Some(value) = mapping.get("ServiceID") {
                service_id = Some(value.clone());
            }
            if let Some(value) = mapping.get("PrivateKey") {
                returned_private_key = Some(value.clone());
            }
        }
        let service_id = service_id.context("Tor ADD_ONION reply omitted ServiceID")?;
        let endpoint = NetworkEndpoint::parse(
            Some("onion"),
            &format!("{service_id}.onion"),
            Some(virtual_port),
        )?;
        if let Some(private_key) = returned_private_key {
            fs::write(&private_key_path, private_key.as_bytes()).with_context(|| {
                format!(
                    "writing Tor onion private key {}",
                    private_key_path.display()
                )
            })?;
            set_private_key_permissions(&private_key_path)?;
        }

        self.reachable.store(true, Ordering::Relaxed);
        Ok((endpoint, reader))
    }

    pub(crate) async fn wait_for_disconnect(
        &self,
        reader: &mut BufReader<TcpStream>,
    ) -> Result<()> {
        let mut buffer = [0u8; 4096];
        loop {
            let count = reader.read(&mut buffer).await?;
            if count == 0 {
                bail!("Tor control connection closed");
            }
        }
    }

    async fn authenticate(
        &self,
        reader: &mut BufReader<TcpStream>,
        lines: &[String],
    ) -> Result<()> {
        let mut methods = Vec::new();
        let mut cookie_file = None;
        for line in lines {
            let Some(arguments) = line.strip_prefix("AUTH ") else {
                continue;
            };
            let mapping = parse_mapping(arguments)?;
            if let Some(value) = mapping.get("METHODS") {
                methods.extend(value.split(',').map(ToOwned::to_owned));
            }
            if let Some(value) = mapping.get("COOKIEFILE") {
                cookie_file = Some(value.clone());
            }
        }

        let reply = if let Some(password) = self.password.as_deref() {
            if !methods.iter().any(|method| method == "HASHEDPASSWORD") {
                bail!("Tor does not advertise HASHEDPASSWORD authentication")
            }
            self.command(
                reader,
                &format!("AUTHENTICATE {}", quote_tor_string(password)),
            )
            .await?
        } else if methods.iter().any(|method| method == "NULL") {
            self.command(reader, "AUTHENTICATE").await?
        } else if methods.iter().any(|method| method == "SAFECOOKIE") {
            let path = cookie_file.context("Tor SAFECOOKIE reply omitted COOKIEFILE")?;
            let cookie =
                fs::read(&path).with_context(|| format!("reading Tor control cookie {path}"))?;
            if cookie.len() != TOR_COOKIE_SIZE {
                bail!(
                    "Tor control cookie must be {TOR_COOKIE_SIZE} bytes, found {}",
                    cookie.len()
                );
            }
            let client_nonce = random::<[u8; TOR_NONCE_SIZE]>();
            let challenge = self
                .command(
                    reader,
                    &format!("AUTHCHALLENGE SAFECOOKIE {}", hex::encode(client_nonce)),
                )
                .await?;
            if challenge.code != 250 {
                bail!("Tor AUTHCHALLENGE failed with status {}", challenge.code);
            }
            let challenge_line = challenge
                .lines
                .iter()
                .find_map(|line| line.strip_prefix("AUTHCHALLENGE "))
                .context("Tor AUTHCHALLENGE reply omitted challenge data")?;
            let mapping = parse_mapping(challenge_line)?;
            let server_nonce = decode_hex_field(&mapping, "SERVERNONCE")?;
            let server_hash = decode_hex_field(&mapping, "SERVERHASH")?;
            if server_nonce.len() != TOR_NONCE_SIZE || server_hash.len() != 32 {
                bail!("Tor AUTHCHALLENGE returned invalid nonce or hash length");
            }
            let expected_server_hash =
                safe_cookie_hmac(SAFE_SERVER_KEY, &cookie, &client_nonce, &server_nonce);
            if server_hash != expected_server_hash {
                bail!("Tor SAFECOOKIE server hash did not match");
            }
            let client_hash =
                safe_cookie_hmac(SAFE_CLIENT_KEY, &cookie, &client_nonce, &server_nonce);
            self.command(
                reader,
                &format!("AUTHENTICATE {}", hex::encode(client_hash)),
            )
            .await?
        } else if methods.iter().any(|method| method == "COOKIE") {
            let path = cookie_file.context("Tor COOKIE reply omitted COOKIEFILE")?;
            let cookie =
                fs::read(&path).with_context(|| format!("reading Tor control cookie {path}"))?;
            if cookie.len() != TOR_COOKIE_SIZE {
                bail!(
                    "Tor control cookie must be {TOR_COOKIE_SIZE} bytes, found {}",
                    cookie.len()
                );
            }
            self.command(reader, &format!("AUTHENTICATE {}", hex::encode(cookie)))
                .await?
        } else {
            bail!("Tor advertised no supported authentication method")
        };
        if reply.code != 250 {
            bail!("Tor AUTHENTICATE failed with status {}", reply.code);
        }
        Ok(())
    }

    async fn discover_socks_proxy(&self, reader: &mut BufReader<TcpStream>) -> Result<SocketAddr> {
        let reply = self.command(reader, "GETINFO net/listeners/socks").await?;
        if reply.code != 250 {
            bail!(
                "Tor GETINFO net/listeners/socks failed with status {}",
                reply.code
            );
        }
        for line in reply.lines {
            let Some(value) = line.strip_prefix("net/listeners/socks=") else {
                continue;
            };
            let value = unquote_tor_value(value);
            for candidate in value.split_whitespace() {
                if let Ok(address) = candidate.parse::<SocketAddr>() {
                    if address.ip().is_loopback() {
                        return Ok(address);
                    }
                }
            }
        }
        Ok(SocketAddr::from(([127, 0, 0, 1], DEFAULT_TOR_SOCKS_PORT)))
    }

    async fn command(&self, reader: &mut BufReader<TcpStream>, command: &str) -> Result<TorReply> {
        tokio::time::timeout(
            self.connect_timeout,
            reader
                .get_mut()
                .write_all(format!("{command}\r\n").as_bytes()),
        )
        .await
        .context("timed out writing to Tor control port")??;

        let mut lines = Vec::new();
        let mut code = None;
        loop {
            let line = tokio::time::timeout(TOR_REPLY_TIMEOUT, read_line(reader))
                .await
                .context("timed out reading from Tor control port")??;
            if line.len() < 4 {
                bail!("invalid short Tor control reply line")
            }
            let line_code = line[..3]
                .parse::<u16>()
                .with_context(|| format!("invalid Tor reply status in {line:?}"))?;
            if code.is_none() {
                code = Some(line_code);
            } else if code != Some(line_code) {
                bail!("Tor reply changed status code within one response")
            }
            match line.as_bytes()[3] {
                b'-' => lines.push(line[4..].to_owned()),
                b' ' => {
                    lines.push(line[4..].to_owned());
                    return Ok(TorReply {
                        code: line_code,
                        lines,
                    });
                }
                b'+' => {
                    lines.push(line[4..].to_owned());
                    loop {
                        let data = tokio::time::timeout(TOR_REPLY_TIMEOUT, read_line(reader))
                            .await
                            .context("timed out reading Tor control data")??;
                        if data == "." {
                            break;
                        }
                        lines.push(data);
                    }
                }
                _ => bail!("invalid Tor control reply separator"),
            }
        }
    }
}

async fn read_line(reader: &mut BufReader<TcpStream>) -> Result<String> {
    let mut line = String::new();
    let count = reader.read_line(&mut line).await?;
    if count == 0 {
        bail!("Tor control connection closed")
    }
    if line.len() > MAX_TOR_LINE_LENGTH {
        bail!("Tor control reply line exceeds {MAX_TOR_LINE_LENGTH} bytes")
    }
    Ok(line.trim_end_matches(['\r', '\n']).to_owned())
}

fn parse_mapping(value: &str) -> Result<HashMap<String, String>> {
    let mut mapping = HashMap::new();
    let bytes = value.as_bytes();
    let mut cursor = 0;
    while cursor < bytes.len() {
        while bytes.get(cursor) == Some(&b' ') {
            cursor += 1;
        }
        if cursor == bytes.len() {
            break;
        }
        let key_start = cursor;
        while cursor < bytes.len() && bytes[cursor] != b'=' && bytes[cursor] != b' ' {
            cursor += 1;
        }
        if cursor == key_start || bytes.get(cursor) != Some(&b'=') {
            bail!("invalid Tor key/value mapping: {value}")
        }
        let key = &value[key_start..cursor];
        cursor += 1;
        let parsed = if bytes.get(cursor) == Some(&b'"') {
            cursor += 1;
            let mut output = String::new();
            let mut escaped = false;
            while cursor < bytes.len() {
                let byte = bytes[cursor];
                cursor += 1;
                if escaped {
                    output.push(match byte {
                        b'n' => '\n',
                        b'r' => '\r',
                        b't' => '\t',
                        other => char::from(other),
                    });
                    escaped = false;
                } else if byte == b'\\' {
                    escaped = true;
                } else if byte == b'"' {
                    break;
                } else {
                    output.push(char::from(byte));
                }
            }
            if escaped || bytes.get(cursor.saturating_sub(1)) != Some(&b'"') {
                bail!("unterminated quoted Tor mapping value: {value}")
            }
            output
        } else {
            let value_start = cursor;
            while cursor < bytes.len() && bytes[cursor] != b' ' {
                cursor += 1;
            }
            value[value_start..cursor].to_owned()
        };
        mapping.insert(key.to_owned(), parsed);
    }
    Ok(mapping)
}

fn unquote_tor_value(value: &str) -> String {
    value
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
        .unwrap_or(value)
        .to_owned()
}

fn quote_tor_string(value: &str) -> String {
    let mut quoted = String::with_capacity(value.len() + 2);
    quoted.push('"');
    for character in value.chars() {
        match character {
            '\\' => quoted.push_str("\\\\"),
            '"' => quoted.push_str("\\\""),
            '\n' => quoted.push_str("\\n"),
            '\r' => quoted.push_str("\\r"),
            '\t' => quoted.push_str("\\t"),
            character => quoted.push(character),
        }
    }
    quoted.push('"');
    quoted
}

fn decode_hex_field(mapping: &HashMap<String, String>, field: &str) -> Result<Vec<u8>> {
    let value = mapping
        .get(field)
        .with_context(|| format!("Tor reply omitted {field}"))?;
    hex::decode(value).with_context(|| format!("invalid Tor {field} hex"))
}

fn safe_cookie_hmac(
    key: &[u8],
    cookie: &[u8],
    client_nonce: &[u8],
    server_nonce: &[u8],
) -> [u8; 32] {
    hmac_sha256(key, &[cookie, client_nonce, server_nonce])
}

fn hmac_sha256(key: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut key_block = [0u8; 64];
    if key.len() > key_block.len() {
        key_block[..32].copy_from_slice(&Sha256::digest(key));
    } else {
        key_block[..key.len()].copy_from_slice(key);
    }
    let mut inner_pad = [0x36u8; 64];
    let mut outer_pad = [0x5cu8; 64];
    for index in 0..64 {
        inner_pad[index] ^= key_block[index];
        outer_pad[index] ^= key_block[index];
    }

    let mut inner = Sha256::new();
    inner.update(inner_pad);
    for part in parts {
        inner.update(part);
    }
    let inner_digest = inner.finalize();
    let mut outer = Sha256::new();
    outer.update(outer_pad);
    outer.update(inner_digest);
    outer.finalize().into()
}

fn set_private_key_permissions(path: &Path) -> Result<()> {
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

    #[tokio::test]
    async fn publishes_onion_service_with_null_auth_and_discovers_socks() -> Result<()> {
        let listener = TcpListener::bind("127.0.0.1:0").await?;
        let control_address = listener.local_addr()?;
        let service_id = NetworkEndpoint::OnionV3 {
            address: [7; 32],
            port: 8333,
        }
        .host_string()
        .strip_suffix(".onion")
        .expect("onion suffix")
        .to_owned();
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            let mut reader = tokio::io::BufReader::new(stream);
            let mut line = String::new();
            reader.read_line(&mut line).await.unwrap();
            assert_eq!(line.trim_end(), "PROTOCOLINFO 1");
            reader
                .get_mut()
                .write_all(b"250-PROTOCOLINFO 1\r\n250-AUTH METHODS=NULL\r\n250 OK\r\n")
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert_eq!(line.trim_end(), "AUTHENTICATE");
            reader.get_mut().write_all(b"250 OK\r\n").await.unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert_eq!(line.trim_end(), "GETINFO net/listeners/socks");
            reader
                .get_mut()
                .write_all(b"250-net/listeners/socks=127.0.0.1:19050\r\n250 OK\r\n")
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert!(line.starts_with("ADD_ONION NEW:ED25519-V3 Port=8333,127.0.0.1:8333"));
            reader
                .get_mut()
                .write_all(
                    format!(
                        "250-ServiceID={service_id}\r\n250-PrivateKey=ED25519-V3:test-key\r\n250 OK\r\n"
                    )
                    .as_bytes(),
                )
                .await
                .unwrap();
            let mut byte = [0; 1];
            let _ = reader.read(&mut byte).await;
        });

        let datadir = tempfile::tempdir()?;
        let controller = TorController::new(
            control_address,
            None,
            datadir.path().to_owned(),
            Duration::from_secs(1),
        );
        let (endpoint, mut control) = controller.publish("127.0.0.1:8333".parse()?, 8333).await?;
        assert_eq!(endpoint.network_name(), "onion");
        assert_eq!(controller.socks_proxy(), Some("127.0.0.1:19050".parse()?));
        assert!(controller.is_reachable());
        assert_eq!(
            fs::read_to_string(datadir.path().join("onion_v3_private_key"))?,
            "ED25519-V3:test-key"
        );
        control.get_mut().shutdown().await?;
        server.await.unwrap();
        Ok(())
    }

    #[tokio::test]
    async fn authenticates_with_safe_cookie() -> Result<()> {
        let listener = TcpListener::bind("127.0.0.1:0").await?;
        let control_address = listener.local_addr()?;
        let datadir = tempfile::tempdir()?;
        let cookie_path = datadir.path().join("control_auth_cookie");
        let cookie = [3u8; TOR_COOKIE_SIZE];
        fs::write(&cookie_path, cookie)?;
        let service_id = NetworkEndpoint::OnionV3 {
            address: [8; 32],
            port: 8333,
        }
        .host_string()
        .strip_suffix(".onion")
        .expect("onion suffix")
        .to_owned();
        let cookie_path_text = cookie_path.to_str().unwrap().to_owned();
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            let mut reader = tokio::io::BufReader::new(stream);
            let mut line = String::new();
            reader.read_line(&mut line).await.unwrap();
            assert_eq!(line.trim_end(), "PROTOCOLINFO 1");
            reader
                .get_mut()
                .write_all(
                    format!(
                        "250-PROTOCOLINFO 1\r\n250-AUTH METHODS=SAFECOOKIE COOKIEFILE=\"{cookie_path_text}\"\r\n250 OK\r\n"
                    )
                    .as_bytes(),
                )
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            let client_nonce = hex::decode(line.split_whitespace().last().unwrap()).unwrap();
            let server_nonce = [4u8; TOR_NONCE_SIZE];
            let server_hash =
                safe_cookie_hmac(SAFE_SERVER_KEY, &cookie, &client_nonce, &server_nonce);
            reader
                .get_mut()
                .write_all(
                    format!(
                        "250-AUTHCHALLENGE SERVERHASH={} SERVERNONCE={}\r\n250 OK\r\n",
                        hex::encode(server_hash),
                        hex::encode(server_nonce),
                    )
                    .as_bytes(),
                )
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            let client_hash = hex::decode(line.split_whitespace().last().unwrap()).unwrap();
            assert_eq!(
                client_hash,
                safe_cookie_hmac(SAFE_CLIENT_KEY, &cookie, &client_nonce, &server_nonce)
            );
            reader.get_mut().write_all(b"250 OK\r\n").await.unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert_eq!(line.trim_end(), "GETINFO net/listeners/socks");
            reader
                .get_mut()
                .write_all(b"250-net/listeners/socks=127.0.0.1:19050\r\n250 OK\r\n")
                .await
                .unwrap();
            line.clear();
            reader.read_line(&mut line).await.unwrap();
            assert!(line.starts_with("ADD_ONION NEW:ED25519-V3"));
            reader
                .get_mut()
                .write_all(format!("250-ServiceID={service_id}\r\n250 OK\r\n").as_bytes())
                .await
                .unwrap();
        });

        let controller = TorController::new(
            control_address,
            None,
            datadir.path().to_owned(),
            Duration::from_secs(1),
        );
        let (endpoint, mut control) = controller.publish("127.0.0.1:8333".parse()?, 8333).await?;
        assert_eq!(endpoint.network_name(), "onion");
        control.get_mut().shutdown().await?;
        server.await.unwrap();
        Ok(())
    }

    #[test]
    fn parses_quoted_mappings_and_escapes_passwords() {
        let mapping = parse_mapping(r#"METHODS=SAFECOOKIE COOKIEFILE="/tmp/a b""#).unwrap();
        assert_eq!(mapping["METHODS"], "SAFECOOKIE");
        assert_eq!(mapping["COOKIEFILE"], "/tmp/a b");
        assert_eq!(quote_tor_string("a\\b\"c"), r#""a\\b\"c""#);
    }
}
