# semioverse

Lean 4 theory of software artifacts. The operational repos stay operational.

| File | What |
|---|---|
| `semioverse.lean` §§1–5 | State, deltas, traces, lenses, patches, the dependency hypergraph. Open proofs are in `residuals.csv`. |
| `semioverse.lean` §6 | Custody. `here` / `replica` / `offbox`, and when a policy is a boundary. |
| `semioverse.lean` §7 | Firewall, from [test-gov](https://github.com/Syntra-Labs/test-gov). One named deficiency, and no realization unless the gate holds and the invariant holds. |
| `Gap.lean` §8 | Phase table from [router](https://github.com/Syntra-Labs/router), and the patch judgment from [taskflow](https://github.com/Syntra-Archive/taskflow). |
| `Alignment.lean` | Residual ledger, stages 0–7. |

`lake build` builds `Gap`, which imports `semioverse`.

Not brought across: similarity cutoffs, hypervectors, the Myers diff, Neovim, protobuf, the C++ runtime, or the CI workflow. Those are witnesses.
