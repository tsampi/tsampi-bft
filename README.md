# Tsampi BFT

Tsampi BFT is a leaderless, asynchronous Byzantine fault tolerant state replication protocol.

This directory contains the protocol definitions and proofs in Lean, Rocq and
Bend, the executable Python model with basic simulations, and the paper's TeX
and PDF.
The protocol sources build with publicly available toolchains.

Votes form a VoteChain through PrevVote. Blocks carry Votes for their parent,
and repeated quorum queries determine finalization.

## Read

| Topic | Entry point |
| --- | --- |
| Protocol | [Paper](tsampi-bft.pdf) |
| Objects | [`Vote`, `Block`](python/primitives.py), [`Validator`](python/consensus.py) |
| Quorums | [`scan_quorum`](python/quorum.py), [`quorums`](python/consensus.py) |
| Ranking | [`fork_order`, `proposal_improves`](python/consensus.py) |
| Safety | [Lean: `ProtocolExecution.finalizedSafety`](lean/ProtocolExecution.lean), [Rocq: `protocol_projected_execution_finalized_agreement`](rocq/ProtocolSafety.v), [Bend: `NetworkExecution.finalized_safety`](bend/proofs/network_execution.bend) |
| Conditional progress | [Lean: `ProtocolExecution.rankedConditionalLiveness`](lean/ProtocolLiveness.lean), [Rocq: `ranked_protocol_conditional_finality_liveness`](rocq/ProtocolLiveness.v), [Bend: `NetworkExecution.ranked_conditional_liveness`](bend/proofs/conditional_liveness.bend) |

Each theorem states its assumptions. Lean's frontier contract is in
[`Frontiers.lean`](lean/Frontiers.lean).

`Validator` stores immutable local state. `EventDelivery` schedules actions for
a `Network`. To run the event queue from this directory:

```sh
PYTHONPATH=python python3 - <<'PYTHON'
from event_delivery import EventDelivery
delivery = EventDelivery()
delivery.until_finalized(1)
print([v.block(v.finalized).height for v in delivery.network.receivers.values()])
PYTHON
```

This prints `[1, 1, 1]`, the finalized height at each honest Validator.

## Build

Build the image from this repository, then list its targets:

```sh
docker build -t tsampi-bft .
docker run --rm tsampi-bft
```

The Debian 13 slim image installs the recorded Lean and Bend toolchains, Rocq,
Python and TeX Live, then runs `make verify`. CI builds this Dockerfile on each change.
Bend is configured inside the image, so all targets use the same interface.
For example, `docker run --rm tsampi-bft make bend` checks the Bend proofs.

`make help` prints:

```text
lean    Check the Lean definitions and proofs.
bend    Check the Bend definitions and kernel verdicts.
rocq    Compile and kernel-check the Rocq proofs.
python  Run the Python simulation tests.
paper   Build tsampi-bft.pdf.
verify  Run all checks and build the paper (default).
clean   Remove generated build files.
help    Show these targets.
```

For native builds, the shared Lean version is recorded in `lean/lean-toolchain` and
`bend/lean-toolchain`; the Bend compiler and Bun versions are in
`bend/TOOLCHAIN.toml`. Rocq uses `coqc` and `coqchk`. Python requires version
3.11 or later. The paper uses `pdflatex` and `bibtex` from TeX Live.

The 14 basic simulations cover Block generation, Vote admission, ranking,
finalization and delayed delivery. The manuscript in `paper/tsampi-bft.tex`
includes its bibliography, style and template license; the compiled paper is
`tsampi-bft.pdf` at the repository root.

## Sources

- `lean/` contains protocol definitions and Safety and conditional progress proofs.
- `rocq/` contains its protocol definitions and proofs.
- `bend/model/` and `bend/proofs/` contain the Bend model and proofs.
- `python/` contains the executable reference model.
- `python/test_*.py` contains the basic simulation tests.
- `paper/` contains the self-contained manuscript TeX; `tsampi-bft.pdf` is the compiled paper.
