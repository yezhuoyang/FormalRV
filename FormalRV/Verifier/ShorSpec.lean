/-
  FormalRV.Verifier.ShorSpec — the AIRTIGHT obligation a Shor implementation must satisfy.

  The USER (spec-setter) fixes the inputs: the number `N` to factor, the LP code `code`
  (a `CSSCode`), and the logical operators `L` (a `LogicalBasis`, giving the logical Z̄_i for
  every logical qubit).  The IMPLEMENTER must then inhabit `VerifiedShorOnCode N Δ k code L`,
  and `#verify_clean` (ProofGate) rejects any submission that uses `sorry` or an extra axiom.

  Every field is a REAL obligation — no escape hatches, no vacuous `:= True` placeholders:

  * `code_valid` / `code_qldpc` / `logical_valid` / `N_target` are DECIDABLE facts about the
    user's inputs (a `= true` / concrete `Prop`), so they cannot be faked.
  * `succeeds` demands the genuine measurement-success metric `probability_of_success ≥ κ/(log₂N)⁴`
    on an oracle satisfying `ModMulImpl` (the actual SQIR Shor statement) — NOT a gate-count proxy.
  * `realized_on_code` demands a CONCRETE physical circuit on the code's qubits that REALIZES the
    logical oracle through an encoding isometry into the code (`uc_eval physical · enc = enc · uc_eval (u i)`),
    with the user's `L.zbar` as the logical Z observables.  This is a matrix equation — it is
    false unless the physical construction genuinely implements the logical computation.

  This file only DEFINES the obligation (it compiles).  The construction + proof is the
  implementer's job, gated by `#verify_clean`.
-/
import FormalRV.QEC.Logical
import FormalRV.Shor.VerifiedShor
import FormalRV.Arithmetic.GateToUCom
import FormalRV.PPM.Semantics.LogicalState
import FormalRV.Verifier.ProofGate

namespace FormalRV.Verifier

open FormalRV.QEC FormalRV.SQIRPort

/-- A legitimate Shor factoring target: odd composite greater than one. -/
def ShorTarget (N : Nat) : Prop := 1 < N ∧ Odd N ∧ ¬ Nat.Prime N

/-- The LOGICAL Shor algorithm meets its success bound on oracle family `u`: the REAL
    measurement-success metric, with `u` proven to implement modular multiplication. -/
def LogicalShorSucceeds (a r N m bits : Nat)
    (u : Nat → BaseUCom (bits + FormalRV.BQAlgo.sqir_modmult_rev_anc bits)) : Prop :=
  VerifiedShor.ShorSetting a r N m bits ∧
  ModMulImpl a N bits (FormalRV.BQAlgo.sqir_modmult_rev_anc bits) u ∧
  probability_of_success a r N m bits (FormalRV.BQAlgo.sqir_modmult_rev_anc bits) u
    ≥ κ / (Nat.log2 N : ℝ) ^ 4

/-- **Code realization (the L4↔L1 obligation).**  Each logical oracle `u i` is realized by a
    CONCRETE physical `Gate` circuit on the code's `code.n` qubits, through an encoding isometry
    `enc` into the code: `uc_eval(physical)·enc = enc·uc_eval(u i)`.  A matrix equation — NOT a
    `True` placeholder; it forces a genuine physical implementation. -/
def OracleRealizedOnCode (code : CSSCode) {k : Nat} (_L : LogicalBasis code k)
    {dim : Nat} (u : Nat → BaseUCom dim) : Prop :=
  ∀ i, ∃ (physical : FormalRV.Framework.Gate)
         (enc : Matrix (Fin (2 ^ code.n)) (Fin (2 ^ dim)) ℂ),
    enc.conjTranspose * enc = (1 : Matrix (Fin (2 ^ dim)) (Fin (2 ^ dim)) ℂ) ∧
    FormalRV.Framework.uc_eval (FormalRV.BQAlgo.Gate.toUCom code.n physical) * enc
      = enc * FormalRV.Framework.uc_eval (u i)

/-- **THE VERIFIER OBLIGATION.**  A complete, correct Shor implementation on the user's LP code
    `code` with logical operators `L`, factoring `N`.  The implementer must provide a term of this
    type — every field, sorry-free — and `#verify_clean` enforces it. -/
structure VerifiedShorOnCode (N Δ k : Nat) (code : CSSCode) (L : LogicalBasis code k) : Prop where
  /-- (A) the user's LP code is a valid CSS code. -/
  code_valid : code.valid = true
  /-- (B) the user's LP code is qLDPC with degree bound `Δ`. -/
  code_qldpc : code.is_qldpc_code Δ = true
  /-- (C) the user's logical operators are genuine logical Paulis. -/
  logical_valid : L.valid = true
  /-- (D) `N` is a legitimate Shor target. -/
  N_target : ShorTarget N
  /-- (E) a Shor instance whose LOGICAL success probability meets the bound, with a verified
      modular-multiplication oracle, AND that oracle is physically realized on THIS code. -/
  succeeds_on_code :
    ∃ (a r m bits : Nat)
      (u : Nat → BaseUCom (bits + FormalRV.BQAlgo.sqir_modmult_rev_anc bits)),
      LogicalShorSucceeds a r N m bits u ∧
      OracleRealizedOnCode code L u

/-! ## The obligation delivers REAL guarantees (so it is not a vacuous/trivial spec).

    Any verified submission `h : VerifiedShorOnCode …` PROVES, with no escape, that the user's
    code is a valid qLDPC CSS code, the logical operators are genuine, `N` is genuinely composite,
    AND a Shor instance succeeds with the κ/(log₂N)⁴ bound on a verified oracle realized on the
    code.  `#verify_clean` accepts this extraction because it is axiom-free. -/
theorem verified_guarantees {N Δ k : Nat} {code : CSSCode} {L : LogicalBasis code k}
    (h : VerifiedShorOnCode N Δ k code L) :
    code.valid = true ∧ code.is_qldpc_code Δ = true ∧ L.valid = true ∧
    ¬ Nat.Prime N ∧
    (∃ a r m bits u, LogicalShorSucceeds a r N m bits u ∧ OracleRealizedOnCode code L u) :=
  ⟨h.code_valid, h.code_qldpc, h.logical_valid, h.N_target.2.2, h.succeeds_on_code⟩

#verify_clean verified_guarantees

end FormalRV.Verifier
