# semioverse

Lean 4 theory of software artifacts.

| File | What |
|---|---|
| `semioverse.lean` §§1–5 | State, deltas, traces, lenses, patches, the dependency hypergraph. Open proofs are in `residuals.csv`. |
| `semioverse.lean` §6 | Custody. `here` / `replica` / `offbox`, and when a policy is a boundary. |
| `semioverse.lean` §7 | Firewall, from [test-gov](https://github.com/Syntra-Labs/test-gov). One named deficiency, and no realization unless the gate holds and the invariant holds. |
| `Alignment.lean` | Residual ledger, stages 0–7. |

Brought across from test-gov: the adequacy rule (exactly one deficiency) and the evaluation firewall (no realization without the invariant).

Not brought across: `schema.proto`, `CMakeLists.txt`, `workflows/firewall.yml`, and the tier diagrams. The C++ runtime, protobuf contract, and PromQL stream are witnesses of `applyDelta`, the schema, and `O_Observe`. The labels there (`Delta`, `O`, `Pi_UI`, the build DAG, patch commutation, the dependency hypergraph) are already the primitives in §§1–5.
