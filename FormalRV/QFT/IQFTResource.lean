/-
  FormalRV.QFT.IQFTResource
  ─────────────────────────
  THE "resource" theorem for the inverse QFT.

  Unlike a reversible arithmetic gadget (whose resource is an exact T-count),
  the IQFT's controlled phases are continuous rotations, so its hardware cost is
  governed by COMPILATION to a finite gate set.  The resource story is therefore
  the approximate ("banded") QFT compiler:

    • `iqft_banded_isCliffordT` — the cutoff-`c` compiled ladder is EXACTLY
      Clifford+T for `c ≤ 2` (every kept rotation is depth 0/1 = `S†`/`controlled-S†`,
      every dropped one is `SKIP`).
    • `iqft_banded_error_budget` — the TOTAL approximation error of the cutoff is
      the derived geometric tail `≤ 2π/2^c` (no axiom; chord-≤-arc per drop).
    • `iqft_banded_error_to_zero` — that budget is antitone in the cutoff, so it
      drives below any target as `c` grows.
    • `iqft_banded_semantics` — the compiled ladder's actual action on basis
      states is the product of its kept controlled-phase scalars.

  EXACT GATE/QUBIT COUNTS (the `Resource/` counters walking THE circuit's
  syntax tree — see `IQFTCount.lean`, imported below):
    • `Resource.cnotCountU_IQFT`  — CNOTs = `3·⌊n/2⌋ + n·(n−1)`  (TIME)
    • `Resource.oneQCountU_IQFT`  — 1q gates = `3·(n(n−1)/2) + n + 2`  (TIME)
    • `Resource.widthU_IQFT`      — qubits = `n`, no hidden ancilla  (SPACE)
    • `Resource.iqft_verified_with_resources` — semantics + time + space,
      all about the SAME syntactic object.

  Imports the counts (`IQFTCount`), the compiler (`AQFTCompile`), its semantics
  (`AQFTCompileSemantics`), and the elementary error bound (`Core.ApproxQFT`).
  These are re-surfaced headlines; proofs live in those files.
-/
import FormalRV.QFT.IQFTCount
import FormalRV.QFT.AQFTCompile
import FormalRV.QFT.AQFTCompileSemantics
import FormalRV.Core.ApproxQFT

namespace FormalRV.Framework.AQFTCompile

open FormalRV.Framework
open FormalRV.Framework.ApproxQFT
open FormalRV.Framework.CliffordTRotations

/-- **Banded IQFT is exactly Clifford+T (THE gate-set resource).**  For cutoff
`c ≤ 2`, the compiled phase ladder emits only Clifford+T gates. -/
theorem iqft_banded_isCliffordT {dim : Nat} (c : Nat) (hc : c ≤ 2)
    (rs : List PhaseRot) :
    IsCliffordT (compileLadder c rs : BaseUCom dim) :=
  compileLadder_isCliffordT c hc rs

/-- **Banded IQFT error budget (THE approximation resource).**  The total cost
of the cutoff-`c` compilation, summed over every dropped depth `c ≤ m < n`, is
at most `2π/2^c` — a closed-form geometric tail, derived (not assumed). -/
theorem iqft_banded_error_budget (c n : ℕ) (hcn : c ≤ n) :
    ∑ m ∈ Finset.Ico c n, (Real.pi / 2 ^ m) ≤ 2 * Real.pi / 2 ^ c :=
  compileLadder_error_budget c n hcn

/-- **The budget → 0 with cutoff.**  Increasing the cutoff `c` cannot increase
the error bound `2π/2^c`, so it can be driven below any target. -/
theorem iqft_banded_error_to_zero {c c' : ℕ} (h : c ≤ c') :
    (2 * Real.pi / 2 ^ c' : ℝ) ≤ 2 * Real.pi / 2 ^ c :=
  aqft_error_budget_antitone h

/-- **Banded IQFT semantics.**  On any computational-basis state, the compiled
cutoff-`c` ladder acts as the product of its kept controlled-phase scalars
(dropped rotations contribute `1`) — its action is the banded inverse-QFT, not
just its gate count. -/
theorem iqft_banded_semantics {dim : Nat} (c : Nat) (rs : List PhaseRot)
    (f : Nat → Bool) (hpos : 0 < dim) (hwf : ∀ r ∈ rs, RotWF dim r) :
    uc_eval (compileLadder c rs : BaseUCom dim) * f_to_vec dim f
      = ladderScalar c rs f • f_to_vec dim f :=
  compileLadder_acts_on_basis c rs f hpos hwf

end FormalRV.Framework.AQFTCompile
