# Lean protocol definitions and proofs

Run `make build` to compile the public roots declared in `lakefile.toml`.
`Proofs.lean` imports the Safety and conditional progress results through
`ProtocolExecution` and `ProtocolLiveness`. The compiler version is recorded
in `lean-toolchain`.
