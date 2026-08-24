use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let schemas = [
        "schema/mp/proxy.capnp",
        "schema/ipc/common.capnp",
        "schema/ipc/echo.capnp",
        "schema/ipc/init.capnp",
        "schema/ipc/mining.capnp",
    ];

    for schema in schemas {
        println!("cargo:rerun-if-changed={schema}");
    }
    println!("cargo:rerun-if-changed=src/data/ip_asn.dat");

    let mut command = capnpc::codegen::CodeGenerationCommand::new();
    command.output_directory(std::env::var("OUT_DIR").expect("OUT_DIR is set"));

    let request = capnpc_embedded::CompileCommand::new()
        .src_prefix("schema")
        .import_path("schema")
        .file("schema/mp/proxy.capnp")
        .file("schema/ipc/common.capnp")
        .file("schema/ipc/echo.capnp")
        .file("schema/ipc/init.capnp")
        .file("schema/ipc/mining.capnp")
        .compile()
        .expect("failed to compile Cap'n Proto IPC schemas");

    command
        .run(&request[..])
        .expect("failed to generate Rust IPC bindings");

    compile_script_batch_verifier();
}

/// Compile the small C++ bridge that exposes the same shared transaction
/// precomputation Core uses before it queues script checks. The public
/// libbitcoinconsensus ABI verifies one input per call and therefore reparses
/// and rebuilds `PrecomputedTransactionData` for every input. The bridge is
/// linked against the exact Core sources bundled by the bitcoinconsensus
/// dependency, so consensus execution remains on the same implementation.
fn compile_script_batch_verifier() {
    let source_dir = find_bitcoinconsensus_source_dir();
    println!("cargo:rerun-if-changed=native/script_batch.cpp");

    cc::Build::new()
        .cpp(true)
        .std("c++17")
        .include(&source_dir)
        .include(source_dir.join("secp256k1/include"))
        .file("native/script_batch.cpp")
        .compile("bitcoind_rs_script_batch");
}

fn find_bitcoinconsensus_source_dir() -> PathBuf {
    let cargo_home = env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo")))
        .expect("CARGO_HOME or HOME must be set to locate bitcoinconsensus");
    let registry_src = cargo_home.join("registry/src");
    let mut candidates = Vec::new();
    let indexes = fs::read_dir(&registry_src)
        .unwrap_or_else(|error| panic!("reading {}: {error}", registry_src.display()));
    for index in indexes.flatten() {
        let Ok(packages) = fs::read_dir(index.path()) else {
            continue;
        };
        for package in packages.flatten() {
            let path = package.path();
            if package
                .file_name()
                .to_string_lossy()
                .starts_with("bitcoinconsensus-")
                && path
                    .join("depend/bitcoin/src/script/interpreter.h")
                    .is_file()
            {
                candidates.push(path);
            }
        }
    }
    candidates.sort();
    let preferred = candidates.iter().position(|path| {
        path.file_name()
            .is_some_and(|name| name == "bitcoinconsensus-0.106.0+26.0")
    });
    preferred
        .map(|index| candidates.remove(index))
        .or_else(|| candidates.into_iter().next())
        .map(|path| path.join("depend/bitcoin/src"))
        .expect("bitcoinconsensus Core source was not found in the Cargo registry")
}
