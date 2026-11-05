# Bend protocol definitions and proofs

`model/kernel.bend` defines the protocol model. `proofs/` contains quorum,
Safety, execution and conditional progress proofs.

Install the compiler revision and Bun version recorded in `TOOLCHAIN.toml`.
Set `BEND_COMPILER` to that checkout's compiler entrypoint and run `make build`.
Set `BUN` when the pinned Bun executable is outside `PATH`.
The build checks every source and runs kernel verdicts for the network
execution and conditional progress proofs.
