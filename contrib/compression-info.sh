#!/usr/bin/env bash

set -euo pipefail

usage() {
    cat >&2 <<'EOF'
Usage: contrib/compression-info.sh <storage-file> [xor-key-file]

Reports the exact Zstandard compression ratio of a native append-only storage
file such as blocks.dat or undo.dat. When the XOR key is omitted, an xor.dat
next to the storage file is detected automatically.

Set BITCOIN_UTIL to use a particular bitcoin-util binary.
EOF
}

if [[ $# -eq 1 && ( $1 == "-h" || $1 == "--help" ) ]]; then
    usage
    exit 0
fi
if [[ $# -lt 1 || $# -gt 2 ]]; then
    usage
    exit 2
fi

script_directory="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
repository_root="$(cd -- "$script_directory/.." && pwd -P)"
bitcoin_util="${BITCOIN_UTIL:-$repository_root/target/release/bitcoin-util}"

if [[ ! -x "$bitcoin_util" ]]; then
    cargo_command="${CARGO:-cargo}"
    "$cargo_command" build --release --bin bitcoin-util \
        --manifest-path "$repository_root/Cargo.toml"
fi

exec "$bitcoin_util" compressioninfo "$@"
