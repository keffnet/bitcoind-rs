//! Core-compatible multiprocess node entry point.

// The multiprocess and monolithic binaries intentionally share the same node
// engine. Keep the entry-point implementation single-sourced while exposing
// Core's distinct executable name to the `bitcoin` launcher and supervisors.
include!("main.rs");
