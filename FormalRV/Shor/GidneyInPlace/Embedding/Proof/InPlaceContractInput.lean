/-
  FormalRV.Shor.GidneyInPlace.InPlaceContractInput — G5 PROBE anchor.
  ════════════════════════════════════════════════════════════════════════════

  The §2 `prepB` feasibility probe (see `INPLACE_DISCHARGE_PLAN.md`) asked the one
  question that decides the whole G5 route: how does the FROZEN contract's input
  `cosetState (2^(n+anc)) N cm z` (`InPlaceCosetSpec.lean:71`) relate to the PROVEN
  two-register input `cosetInputVec z 0`?

  This file makes the load-bearing structural fact a CHECKED theorem rather than prose:
  the contract's single-register coset input lives ENTIRELY in the a-block (the low `n`
  bits) — every support index is `< 2^n`, so the b-block / scratch / ctrl bits are all
  `0`.  (Support indices are `z + j·N < N + 2^cm·N ≤ 2^n` under the standard fit.)

  CONSEQUENCE (the probe verdict, locked by this lemma):
    * The contract input is `cosetState z` on the a-block ⊗ **|0⟩** on the b-block — it is
      NOT the two-register `cosetInputVec z 0`, whose b-block is `cosetState 0` (a runway
      SUPERPOSITION).  The two states have different support cardinalities
      (`2^cm` vs `(2^cm)²`), so NO permutation / register-iso (a G4-style relabel) can
      bridge them.  G5 genuinely requires a state-CHANGING step (prepare the b-runway,
      Route A) or a marginal trace-out of the b-ancilla (Route B) — never a relabel.
    * Combined with `CosetEphys.cosetEmbedMat_eq_cosetState` (the downstream embedding is
      PINNED to this single-register `cosetState`, b=|0⟩) and `CosetEmbeddedInit` (coset
      preparation is modelled as the abstract isometry `E_phys`, never a circuit), this is
      why Route C (re-point the embedding to the two-register input) is rejected as
      invasive, and the marginal Route B is recommended.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Primitives.Def.ApproxOp

namespace FormalRV.Shor.GidneyInPlace.InPlaceContractInput

open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow)

/-- **Contract input lives in the a-block (G5 probe anchor).**  Every support index of the
    frozen contract's coset input `cosetState dim N cm z` is `< 2^n`, given the standard
    a-block fit `z + (2^cm − 1)·N < 2^n` (with `z < N`).  At `dim := 2^(n+anc)` this says the
    state is `cosetState z` on the low-`n` a-block ⊗ |0⟩ on the b-block/scratch/ctrl — so it
    is DISTINCT from the two-register `cosetInputVec z 0` (b-block = `cosetState 0`), and no
    register relabel can bridge the two. -/
theorem cosetState_support_lt_aBlock (dim N cm n z : Nat) (hN : 0 < N)
    (hfit : z + (2 ^ cm - 1) * N < 2 ^ n) (i : Fin dim)
    (h : cosetState dim N cm z i 0 ≠ 0) : (i : Nat) < 2 ^ n := by
  by_cases hmem : i ∈ cosetWindow dim N cm z
  · obtain ⟨j, hj, hival⟩ := (mem_cosetWindow dim N cm z hN i).mp hmem
    have hjle : j ≤ 2 ^ cm - 1 := by
      have : 0 < 2 ^ cm := Nat.two_pow_pos cm
      omega
    have hmono : j * N ≤ (2 ^ cm - 1) * N := Nat.mul_le_mul_right N hjle
    omega
  · exact absurd (by rw [cosetState, if_neg hmem] : cosetState dim N cm z i 0 = 0) h

end FormalRV.Shor.GidneyInPlace.InPlaceContractInput
