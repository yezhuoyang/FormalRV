/-
  FormalRV.PauliRotation.Compiler.ToPPM.GadgetLowering
  ───────────────────────────────────────────
  **THE GADGET-TO-PPM CAPSTONE**: gluing the preservation theorem
  (`lowerFlat_denote`) to the dictionary capstone
  (`gateRots_denote_applyNat`):

      every compiled Gate-IR gadget's LOWERED PPM PROGRAM implements the
      gadget's own Boolean semantics, up to `gphase` and the explicit
      branch scalar, tensored with the ancilla collapses — on EVERY
      measurement branch.

  `gateRots_kinds` discharges the Z/X side condition once and for all
  (every dictionary axis is Z/X by construction).
-/
import FormalRV.PauliRotation.Compiler.ToPPM.Induction
import FormalRV.PauliRotation.Correctness.Assembly
import FormalRV.PauliRotation.Correctness.ShorEndToEnd

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open FormalRV.Resource
open Matrix

/-! ## §1. Every compiled axis is Z/X. -/

theorem kinds_hGate (q : Nat) :
    ∀ r ∈ (hGate q).flatten, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x := by
  intro r hr f hf
  simp [hGate, rot1] at hr
  rcases hr with hr | hr | hr <;> subst hr <;> simp at hf <;> subst hf <;>
    first
      | exact Or.inl rfl
      | exact Or.inr rfl

theorem kinds_mk2 (c t : Nat) (kc kt : PKind)
    (hc : kc = PKind.z ∨ kc = PKind.x) (ht : kt = PKind.z ∨ kt = PKind.x) :
    ∀ f ∈ mk2 c kc t kt, f.kind = PKind.z ∨ f.kind = PKind.x := by
  intro f hf
  unfold mk2 at hf
  by_cases h : c < t <;> simp [h] at hf <;>
    rcases hf with hf | hf <;> subst hf <;> assumption

theorem kinds_cnot (c t : Nat) :
    ∀ r ∈ (cnotGate c t).flatten, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x := by
  intro r hr f hf
  simp [cnotGate] at hr
  rcases hr with hr | hr | hr <;> subst hr
  · exact kinds_mk2 c t .z .x (Or.inl rfl) (Or.inr rfl) f hf
  · simp at hf
    subst hf
    exact Or.inl rfl
  · simp at hf
    subst hf
    exact Or.inr rfl

theorem kinds_ccz (a b c : Nat) :
    ∀ r ∈ (cczGate a b c).flatten, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x := by
  intro r hr f hf
  simp [cczGate] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr <;> subst hr <;>
    simp at hf <;>
    first
      | (subst hf; exact Or.inl rfl)
      | (rcases hf with hf | hf <;> subst hf <;> exact Or.inl rfl)
      | (rcases hf with hf | hf | hf <;> subst hf <;> exact Or.inl rfl)

/-- **Every compiled gadget axis uses only Z and X factors** — the kinds
side condition of the preservation theorem, once and for all. -/
theorem gateRots_kinds (g : FormalRV.Framework.Gate) :
    ∀ r ∈ gateRots g, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x := by
  induction g with
  | I => intro r hr; cases hr
  | X q =>
      intro r hr f hf
      simp [gateRots] at hr
      subst hr
      simp at hf
      subst hf
      exact Or.inr rfl
  | CX c t => exact kinds_cnot c t
  | CCX a b t =>
      intro r hr f hf
      rcases List.mem_append.mp hr with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact kinds_hGate t r h' f hf
        · exact kinds_ccz _ _ _ r h' f hf
      · exact kinds_hGate t r h f hf
  | seq g h ihg ihh =>
      intro r hr f hf
      rcases List.mem_append.mp hr with h' | h'
      · exact ihg r h' f hf
      · exact ihh r h' f hf

/-! ## §2. THE GADGET-LOWERING CAPSTONE. -/

/-- **EVERY GATE-IR GADGET LOWERS TO PPM SEMANTICS-PRESERVINGLY**: on every
measurement branch, the lowered PPM program of the compiled gadget, applied
to `ψ ⊗ (magic/stabilizer ancillas)`, equals the explicit branch scalar
times `gphase g` times the gadget's OWN Boolean semantics `applyMat m g`
applied to the data, tensored with the collapsed ancillas. -/
theorem lowerGate_denote (m : Nat) (g : FormalRV.Framework.Gate)
    (hops : opsOK g = true) (hw : width g ≤ m)
    (ω : Nat → Bool) (outs : List Bool) (ψ : Fin (2 ^ m) → ℂ) :
    (progDenote (ampsWidth m (ancAmps (gateRots g))) ω outs
        (lowerFlat m outs.length (gateRots g))).mulVec
      (stateOver (ancAmps (gateRots g)) (ancAmps (gateRots g)) m ψ)
    = (branchScalar ω (gateRots g) outs.length * gphase g)
        • stateOver (ancAmps (gateRots g))
            (ancOutAmps ω (gateRots g) outs.length) m
            ((applyMat m g).mulVec ψ) := by
  rw [lowerFlat_denote (gateRots g) m ψ ω outs
        (fun r hr => (gateRots_bounded g hops r hr).1)
        (fun r hr => Nat.le_trans (gateRots_bounded g hops r hr).2 hw)
        (gateRots_kinds g),
      gateRots_denote_applyNat m g hops hw,
      smul_mulVec, stateOver_smul, smul_smul]

/-! ## §3. QFT/QPE axes are Z/X too. -/

theorem kinds_csDag (t : Nat) :
    ∀ r ∈ csDagRots t, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x := by
  intro r hr f hf
  simp [csDagRots] at hr
  rcases hr with hr | hr | hr <;> subst hr <;> simp at hf <;>
    first
      | (subst hf; exact Or.inl rfl)
      | (rcases hf with hf | hf <;> subst hf <;> exact Or.inl rfl)

theorem kinds_swap (i j : Nat) :
    ∀ r ∈ swapRots i j, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x := by
  intro r hr f hf
  rcases List.mem_append.mp hr with h | h
  · rcases List.mem_append.mp h with h' | h'
    · exact kinds_cnot i j r h' f hf
    · exact kinds_cnot j i r h' f hf
  · exact kinds_cnot i j r h f hf

theorem kinds_bitRev (k : Nat) :
    ∀ r ∈ bitRevRots k, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x := by
  intro r hr
  obtain ⟨i, _, hri⟩ := List.mem_flatMap.mp hr
  exact kinds_swap i (k - 1 - i) r hri

theorem kinds_ladderLow :
    ∀ (t : Nat), ∀ r ∈ aqftLadderLow t, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x
  | 0, r, hr => by cases hr
  | t + 1, r, hr => by
      rcases List.mem_append.mp hr with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact kinds_csDag t r h'
        · exact kinds_hGate t r h'
      · exact kinds_ladderLow t r h

theorem kinds_hLayer (k : Nat) :
    ∀ r ∈ hLayerRots k, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x := by
  intro r hr
  obtain ⟨q, _, hrq⟩ := List.mem_flatMap.mp hr
  exact kinds_hGate q r hrq

theorem kinds_aqft2 :
    ∀ (k : Nat), ∀ r ∈ aqft2Rots k, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x
  | 0, r, hr => by cases hr
  | k + 1, r, hr => by
      rcases List.mem_append.mp hr with h | h
      · exact kinds_bitRev (k + 1) r h
      · rcases List.mem_append.mp h with h' | h'
        · exact kinds_hGate k r h'
        · exact kinds_ladderLow k r h'

theorem kinds_qpe (k : Nat) (oracle : List Rot)
    (horacle : ∀ r ∈ oracle, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x) :
    ∀ r ∈ qpeRots k oracle, ∀ f ∈ r.axis,
      f.kind = PKind.z ∨ f.kind = PKind.x := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact kinds_hLayer k r h
  · rcases List.mem_append.mp h with h' | h'
    · exact horacle r h'
    · exact kinds_aqft2 k r h'

/-! ## §4. THE FULL SHOR LOWERING. -/

/-- **THE FULL SHOR/QPE CIRCUIT LOWERS TO PPM SEMANTICS-PRESERVINGLY**: on
every measurement branch, the lowered PPM program of the complete compiled
algorithm — H-layer, modexp oracle, banded inverse QFT — applied to
`ψ ⊗ ancillas`, equals the branch scalar times the composed closed form
(IQFT block · oracle's `applyMat` · H-layer block) on the data, tensored
with the ancilla collapses. -/
theorem lowerShorQPE_denote (n k : Nat) (oracleG : FormalRV.Framework.Gate)
    (hops : opsOK oracleG = true) (hw : width oracleG ≤ n)
    (hk : k + 1 ≤ n)
    (hb : ∀ r ∈ qpeRots (k + 1) (gateRots oracleG),
        sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ n)
    (ω : Nat → Bool) (outs : List Bool) (ψ : Fin (2 ^ n) → ℂ) :
    (progDenote
        (ampsWidth n (ancAmps (qpeRots (k + 1) (gateRots oracleG)))) ω outs
        (lowerFlat n outs.length (qpeRots (k + 1) (gateRots oracleG)))).mulVec
      (stateOver (ancAmps (qpeRots (k + 1) (gateRots oracleG)))
        (ancAmps (qpeRots (k + 1) (gateRots oracleG))) n ψ)
    = (branchScalar ω (qpeRots (k + 1) (gateRots oracleG)) outs.length
        * (iqftPhase k * gphase oracleG
            * ((-Complex.I) * (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ)) ^ (k + 1)))
        • stateOver (ancAmps (qpeRots (k + 1) (gateRots oracleG)))
            (ancOutAmps ω (qpeRots (k + 1) (gateRots oracleG)) outs.length) n
            ((iqftMat n k * applyMat n oracleG
                * hLayerMat n (k + 1)).mulVec ψ) := by
  rw [lowerFlat_denote (qpeRots (k + 1) (gateRots oracleG)) n ψ ω outs
        (fun r hr => (hb r hr).1) (fun r hr => (hb r hr).2)
        (kinds_qpe (k + 1) (gateRots oracleG) (gateRots_kinds oracleG)),
      shorQPE_rots_denote n k oracleG hops hw hk,
      smul_mulVec, stateOver_smul, smul_smul]

end FormalRV.PauliRotation
