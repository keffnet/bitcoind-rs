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
}
