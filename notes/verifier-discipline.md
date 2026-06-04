# The verifier discipline (set 2026-06-03, by John)

Spec FIRST, construction SECOND. The verifier is fixed so the implementer cannot overclaim.

## The two parts (`FormalRV/Verifier/`)

### 1. Enforcement gate — `ProofGate.lean`
- `#verify_clean foo` — build-time ERROR unless `foo` depends only on
  `{propext, Classical.choice, Quot.sound}`. Any `sorryAx` or custom `axiom` → REJECTED, build
  fails. This is the "Lean rejects an incomplete submission" mechanism.
- `#verify_rejects foo` — dual regression check: succeeds iff `foo` would be rejected.
- Self-tests: `#verify_clean clean_example` accepts; `#verify_rejects unproven_fixture` confirms
  rejection of an axiom-asserted claim.

### 2. The obligation — `ShorSpec.lean`
The USER fixes the inputs and the implementer must inhabit
`VerifiedShorOnCode (N Δ k : Nat) (code : CSSCode) (L : LogicalBasis code k) : Prop`, whose fields
are ALL real (no vacuous `:= True`):

| field | obligation |
|---|---|
| `code_valid` | `code.valid = true` (decidable — valid CSS code) |
| `code_qldpc` | `code.is_qldpc_code Δ = true` (decidable — qLDPC) |
| `logical_valid` | `L.valid = true` (decidable — `lz`/`lx` are genuine logical Paulis) |
| `N_target` | `1 < N ∧ Odd N ∧ ¬ N.Prime` (legitimate Shor target) |
| `succeeds_on_code` | ∃ Shor instance + oracle `u`: `LogicalShorSucceeds` (the REAL `probability_of_success ≥ κ/(log₂N)⁴` with `ModMulImpl u`) AND `OracleRealizedOnCode code L u` |

- `LogicalShorSucceeds` uses the genuine measurement-success metric, not a gate-count proxy.
- `OracleRealizedOnCode` is a MATRIX equation `uc_eval(physical)·enc = enc·uc_eval(u i)` (physical
  `Gate` realizes the logical oracle through an encoding isometry `enc` into the code) — false
  unless the physical construction genuinely implements the logical computation. **Not** `True`.
- `verified_guarantees` extracts the real guarantees (code valid + N composite + success) from any
  submission, and `#verify_clean verified_guarantees` accepts it — proving the spec is non-vacuous.

## Acceptance protocol for the construction (next phase)

The implementer (a later iteration) provides, for a concrete user `code`/`L`:
```
theorem submission : VerifiedShorOnCode N Δ k code L := { code_valid := …, …, succeeds_on_code := … }
#verify_clean submission
```
If `submission` compiles AND `#verify_clean` accepts, the whole thing is genuinely proved. Any
`sorry` anywhere → the gate rejects → not accepted. No hand-waving survives.

## Honest gaps the construction must still close (do not fake these)
- `OracleRealizedOnCode` currently demands realization of the ORACLE family on the code. The full
  obligation should also tie the QPE/post-processing layers and the per-logical-qubit encoding to
  `code`/`L`; strengthen the spec as those layers get real (never weaken it to pass).
- The physical realization `enc`/`physical` must be CONSTRUCTED (PPM / lattice surgery on the LP
  code), not assumed. This is the L4↔L3↔L2 build, gated by `#verify_clean`.
