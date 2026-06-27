/-
  FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepCore — a CIRCUIT preparing the
  Zalka/Gidney coset state from |0…0⟩.
  ════════════════════════════════════════════════════════════════════════════

  GOAL.  Build a state-prep circuit `cosetStatePrep` and prove it produces the
  coset state `cosetState (2^dim) N cm k` from the all-zeros basis vector:

      uc_eval (cosetStatePrep …) * basis0 dim  =  cosetState (2^dim) N cm k.

  CONSTRUCTION (npar_H + permGate; no index register / no disentangle):

      cosetStatePrep := UCom.seq (npar_H cm) (Gate.toUCom dim (permGate reg σ_k anc)).

  * `npar_H cm` on |0…0⟩ gives the uniform superposition over the H-support
    `{x·2^rest : x < 2^cm}` — exactly `cosetState (2^dim) (2^rest) cm 0`, the
    `N = 2^rest` contiguous-step window at base 0.  (Closed form
    `uc_eval_npar_H_basis0`, reproduced below.)

  * `permGate reg σ_k anc` is the generic clean-ancilla permutation gate
    (`E2RunwaySynthPerm`).  Its permutation `σ_k` is chosen to send the H-window
    BIJECTIVELY onto the coset window `{k + j·N : j < 2^cm}` (and the complement off
    it).  Since the state is UNIFORM, ANY such set-bijection works, so we take
    `σ_k := windowEquiv.extendSubtype` for an ARBITRARY equiv between the two
    equal-cardinality window subtypes (`Equiv.extendSubtype` + `extendSubtype_mem`
    / `extendSubtype_not_mem`); off-window behaviour is irrelevant because the H
    output vanishes there.

  HYPOTHESES.  `1 < N`, `k < N`, the FULL-BLOCKS budget `2^cm · N ≤ 2^dim`,
  `0 < cm`.  (No `rest` placement / endianness is needed for the abstract
  permutation; see §5 for the status of lifting through `permGate`'s register
  semantics.)

  Kernel-clean target: axioms ⊆ {propext, Classical.choice, Quot.sound};
  no `sorry`, no `native_decide`.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthPerm
import FormalRV.Shor.GidneyInPlace.Gate.Spec.UCEvalBridge
import FormalRV.Shor.GidneyInPlace.Gate.Proof.CuccaroGatePerm
import FormalRV.QPE.PhaseKickback
import Mathlib.Logic.Equiv.Fintype

namespace FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepCore

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthPerm
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState uc_eval_basis_agree uc_eval_entry)
open FormalRV.Shor.GidneyInPlace.GatePerm (gateToPerm funboolNat funboolEquiv extendBool applyFin)
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm (gateToPerm_funboolNat)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState permState)
open FormalRV.Shor.GidneyInPlace.CosetClass
  (cosetWindow mem_cosetWindow cosetWindow_card cosetRep_mem_window)
open FormalRV.Framework.BaseUCom (npar_H)
open scoped Classical

/-! ## §0. The all-zeros input and the `npar_H` uniform superposition.

These reproduce the (volatile, scratch) sibling `E2RunwayPrepScratchA` lemmas so this
module is self-contained against the committed foundations (`PhaseKickback`). -/

/-- The all-zeros basis state on a `D`-qubit register. -/
noncomputable def basis0 (D : Nat) : Matrix (Fin (2 ^ D)) (Fin 1) ℂ :=
  FormalRV.Framework.basis_vector (2 ^ D) 0

open FormalRV.SQIRPort (npar_H_kron_zeros_eq_uniform_sum kron_vec_basis_eq_basis_combine)
open FormalRV.Framework (kron_vec_combine)

/-- `basis0 (cm + rest) = kron_vec (kron_zeros cm) (kron_zeros rest)`. -/
theorem basis0_split (cm rest : Nat) :
    basis0 (cm + rest)
      = kron_vec (FormalRV.Framework.kron_zeros cm) (FormalRV.Framework.kron_zeros rest) := by
  rw [basis0]
  rw [show (FormalRV.Framework.kron_zeros cm : Matrix (Fin (2 ^ cm)) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector (2 ^ cm) 0 from rfl,
      show (FormalRV.Framework.kron_zeros rest : Matrix (Fin (2 ^ rest)) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector (2 ^ rest) 0 from rfl]
  rw [show (0 : Nat) = ((⟨0, Nat.two_pow_pos cm⟩ : Fin (2 ^ cm)) : Nat) from rfl]
  rw [kron_vec_basis_eq_basis_combine cm rest ⟨0, Nat.two_pow_pos cm⟩ ⟨0, Nat.two_pow_pos rest⟩]
  congr 1
  show (0 : Nat) = (FormalRV.Framework.kron_vec_combine
      (⟨0, Nat.two_pow_pos cm⟩ : Fin (2 ^ cm)) (⟨0, Nat.two_pow_pos rest⟩ : Fin (2 ^ rest))).val
  show (0 : Nat) = 0 * 2 ^ rest + 0
  omega

/-- **The uniform-low-`cm` input.**  `npar_H cm` on `(cm+rest)` qubits, applied to
    `basis0`, is the uniform superposition `(1/√2^cm) ∑_{x<2^cm} |x · 2^rest⟩`. -/
theorem uc_eval_npar_H_basis0 (cm rest : Nat) (hcm : 0 < cm) :
    FormalRV.Framework.uc_eval (npar_H cm : Framework.BaseUCom (cm + rest))
        * basis0 (cm + rest)
      = ((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) •
          ∑ x : Fin (2 ^ cm),
            FormalRV.Framework.basis_vector (2 ^ (cm + rest)) (x.val * 2 ^ rest) := by
  rw [basis0_split cm rest]
  rw [npar_H_kron_zeros_eq_uniform_sum (anc := rest) hcm (FormalRV.Framework.kron_zeros rest)]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [show (FormalRV.Framework.kron_zeros rest : Matrix (Fin (2 ^ rest)) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector (2 ^ rest) 0 from rfl]
  rw [show (0 : Nat) = ((⟨0, Nat.two_pow_pos rest⟩ : Fin (2 ^ rest)) : Nat) from rfl]
  rw [kron_vec_basis_eq_basis_combine cm rest x ⟨0, Nat.two_pow_pos rest⟩]
  congr 1

/-! ## §1. The H-support and coset windows; their equal cardinality. -/

/-- The H-support window: `{x · 2^rest : x < 2^cm}` — the support of `npar_H cm` on
    a `(cm + rest)`-qubit register (big-endian, top `cm` qubits).  This is exactly the
    `N = 2^rest` contiguous-step coset window at base `0`. -/
abbrev hWindow (rest cm : Nat) : Finset (Fin (2 ^ (cm + rest))) :=
  cosetWindow (2 ^ (cm + rest)) (2 ^ rest) cm 0

/-- The coset window `{k + j·N : j < 2^cm}` of residue `k` — the TARGET support. -/
abbrev cWindow (rest cm N k : Nat) : Finset (Fin (2 ^ (cm + rest))) :=
  cosetWindow (2 ^ (cm + rest)) N cm k

/-- The H-support window has `2^cm` elements (its `2^rest`-step reps `j·2^rest` fit). -/
theorem hWindow_card (rest cm : Nat) : (hWindow rest cm).card = 2 ^ cm := by
  refine cosetWindow_card (2 ^ (cm + rest)) (2 ^ rest) cm 0 (Nat.two_pow_pos rest) ?_
  -- 0 + (2^cm - 1)·2^rest < 2^(cm+rest)
  have hpow : 0 < 2 ^ cm := Nat.two_pow_pos cm
  calc 0 + (2 ^ cm - 1) * 2 ^ rest
      < 2 ^ cm * 2 ^ rest := by
        have : (2 ^ cm - 1) * 2 ^ rest < 2 ^ cm * 2 ^ rest :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos rest)).mpr (by omega)
        omega
    _ = 2 ^ (cm + rest) := (pow_add 2 cm rest).symm

/-- The coset window has `2^cm` elements (its `N`-step reps fit under the budget). -/
theorem cWindow_card (rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) : (cWindow rest cm N k).card = 2 ^ cm := by
  refine cosetWindow_card (2 ^ (cm + rest)) N cm k hN ?_
  -- k + (2^cm - 1)·N < 2^(cm+rest)
  have hpow : 0 < 2 ^ cm := Nat.two_pow_pos cm
  have h1 : (2 ^ cm - 1) * N = 2 ^ cm * N - N := Nat.sub_one_mul _ _
  have h2 : N ≤ 2 ^ cm * N := Nat.le_mul_of_pos_left N hpow
  omega

/-! ## §2. The window permutation `σ_k` (the crux).

Both windows have card `2^cm`, hence their subtypes are equinumerous; we take an
ARBITRARY equiv between them (`Fintype.equivOfCardEq`) and extend it to a permutation of
the whole register with `Equiv.extendSubtype`.  Uniformity of the state means we only
need the SET image, not a specific affine map. -/

/-- An arbitrary equiv of the two window subtypes (equal cardinality). -/
noncomputable def windowEquiv (rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    {v : Fin (2 ^ (cm + rest)) // v ∈ hWindow rest cm}
      ≃ {v : Fin (2 ^ (cm + rest)) // v ∈ cWindow rest cm N k} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, Fintype.card_coe, hWindow_card rest cm,
        cWindow_card rest cm N k hN hk hbudget])

/-- **`σ_k` — the window permutation.**  Extends `windowEquiv` to a permutation of the
    full register: it maps the H-window bijectively onto the coset window (and the
    complement off it). -/
noncomputable def σ_k (rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) : Equiv.Perm (Fin (2 ^ (cm + rest))) :=
  (windowEquiv rest cm N k hN hk hbudget).extendSubtype

/-- **`σ_k` maps the H-window INTO the coset window.**  (The set-bijection form the task
    asks for: `σ_k` carries every H-support index to a coset-window index.) -/
theorem σ_k_window (rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest))
    (v : Fin (2 ^ (cm + rest))) (hv : v ∈ hWindow rest cm) :
    σ_k rest cm N k hN hk hbudget v ∈ cWindow rest cm N k :=
  Equiv.extendSubtype_mem (windowEquiv rest cm N k hN hk hbudget) v hv

/-- **`σ_k` maps OFF the H-window to OFF the coset window** (support preservation). -/
theorem σ_k_not_window (rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest))
    (v : Fin (2 ^ (cm + rest))) (hv : v ∉ hWindow rest cm) :
    σ_k rest cm N k hN hk hbudget v ∉ cWindow rest cm N k :=
  Equiv.extendSubtype_not_mem (windowEquiv rest cm N k hN hk hbudget) v hv

/-- **`σ_k` BIJECTS the H-window onto the coset window** (the image is the whole target
    window, by cardinality).  Packaged form combining `σ_k_window` (forward) with
    surjectivity from equal cardinality. -/
theorem σ_k_bijOn (rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    Set.BijOn (σ_k rest cm N k hN hk hbudget) (hWindow rest cm) (cWindow rest cm N k) := by
  set σ := σ_k rest cm N k hN hk hbudget with hσ
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo
    intro v hv
    exact σ_k_window rest cm N k hN hk hbudget v hv
  · -- InjOn (σ is a permutation, so globally injective)
    exact (σ.injective).injOn
  · -- SurjOn: |image| = |hWindow| = 2^cm = |cWindow|, and image ⊆ cWindow ⇒ image = cWindow
    intro w hw
    have hmaps : Set.MapsTo σ (hWindow rest cm) (cWindow rest cm N k) :=
      fun v hv => σ_k_window rest cm N k hN hk hbudget v hv
    -- use Finset image cardinality
    have himg_sub : (hWindow rest cm).image σ ⊆ cWindow rest cm N k := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      exact σ_k_window rest cm N k hN hk hbudget v hv
    have hcard : ((hWindow rest cm).image σ).card = (cWindow rest cm N k).card := by
      rw [Finset.card_image_of_injective _ σ.injective, hWindow_card rest cm,
          cWindow_card rest cm N k hN hk hbudget]
    have heq : (hWindow rest cm).image σ = cWindow rest cm N k :=
      Finset.eq_of_subset_of_card_le himg_sub (le_of_eq hcard.symm)
    -- w ∈ cWindow = image, so ∃ v ∈ hWindow, σ v = w
    have hwimg : w ∈ (hWindow rest cm).image σ := by rw [heq]; exact hw
    rw [Finset.mem_image] at hwimg
    obtain ⟨v, hv, hvw⟩ := hwimg
    exact ⟨v, hv, hvw⟩

/-! ## §3. The H uniform sum, as a window-indexed sum.

`uc_eval_npar_H_basis0` gives the H output as `(1/√2^cm) ∑_{x:Fin(2^cm)} |x·2^rest⟩`.
We reindex this `2^cm`-term sum over `Fin (2^cm)` to a sum over the H-window Finset
(`x ↦ ⟨x·2^rest⟩ : hWindow`), so the subsequent permutation step can use the window
bijection `σ_k_bijOn` directly. -/

/-- `x·2^rest < 2^(cm+rest)` for `x < 2^cm`. -/
theorem affineSrc_lt (cm rest x : Nat) (hx : x < 2 ^ cm) :
    x * 2 ^ rest < 2 ^ (cm + rest) := by
  calc x * 2 ^ rest < 2 ^ cm * 2 ^ rest :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos rest)).mpr hx
    _ = 2 ^ (cm + rest) := (pow_add 2 cm rest).symm

/-- **The H uniform sum reindexed over the H-window Finset.** -/
theorem npar_H_sum_over_hWindow (cm rest : Nat) (hcm : 0 < cm) :
    FormalRV.Framework.uc_eval (npar_H cm : Framework.BaseUCom (cm + rest))
        * basis0 (cm + rest)
      = ((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) •
          ∑ v ∈ hWindow rest cm,
            FormalRV.Framework.basis_vector (2 ^ (cm + rest)) (v : Nat) := by
  rw [uc_eval_npar_H_basis0 cm rest hcm]
  congr 1
  -- reindex ∑_{x:Fin(2^cm)} f(x·2^rest)  =  ∑_{v∈hWindow} f(v) via the bijection x ↦ x·2^rest
  refine (Finset.sum_bij (fun (x : Fin (2 ^ cm)) _ =>
      (⟨x.val * 2 ^ rest, affineSrc_lt cm rest x.val x.isLt⟩ : Fin (2 ^ (cm + rest)))) ?_ ?_ ?_ ?_)
  · -- maps into hWindow
    intro x _
    rw [hWindow, mem_cosetWindow _ _ _ _ (Nat.two_pow_pos rest)]
    exact ⟨x.val, x.isLt, by simp⟩
  · -- injective
    intro x _ y _ hxy
    have : x.val * 2 ^ rest = y.val * 2 ^ rest := congrArg Fin.val hxy
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos rest) this)
  · -- surjective onto hWindow
    intro v hv
    rw [hWindow, mem_cosetWindow _ _ _ _ (Nat.two_pow_pos rest)] at hv
    obtain ⟨j, hj, hjeq⟩ := hv
    exact ⟨⟨j, hj⟩, Finset.mem_univ _, Fin.ext (by rw [hjeq]; ring)⟩
  · -- summand agreement
    intro x _
    rfl

/-! ## §4. Sum-to-indicator: a window-indexed uniform sum IS a `cosetState`.

A uniform `(1/√2^cm)`-weighted sum of basis vectors indexed by a card-`2^cm` coset
window equals the `cosetState` on that window. -/

/-- **Sum-to-indicator.**  `(1/√2^cm) ∑_{v∈W} |v⟩ = cosetState dim N cm r`, with the
    sum indexed by EXACTLY the coset window `cosetWindow dim N cm r`. -/
theorem uniform_window_sum_eq_cosetState (dim N cm r : Nat) :
    ((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) •
        ∑ v ∈ cosetWindow dim N cm r,
          FormalRV.Framework.basis_vector dim (v : Nat)
      = cosetState dim N cm r := by
  funext i z
  obtain rfl : z = 0 := Subsingleton.elim z 0
  rw [Matrix.smul_apply, Matrix.sum_apply, cosetState]
  simp only [FormalRV.Framework.basis_vector_apply, smul_eq_mul]
  -- ∑_{v∈W} (if ↑i = ↑v then 1 else 0) = (if i ∈ W then 1 else 0)
  have hsum : (∑ v ∈ cosetWindow dim N cm r, (if (i : Nat) = (v : Nat) then (1 : ℂ) else 0))
      = (if i ∈ cosetWindow dim N cm r then (1 : ℂ) else 0) := by
    by_cases hmem : i ∈ cosetWindow dim N cm r
    · rw [if_pos hmem, Finset.sum_eq_single i]
      · rw [if_pos rfl]
      · intro b _ hb; rw [if_neg (fun hc => hb (Fin.ext hc.symm))]
      · intro hcontra; exact absurd hmem hcontra
    · rw [if_neg hmem, Finset.sum_eq_zero]
      intro v hv
      rw [if_neg (fun hc => hmem (by rw [show i = v from Fin.ext hc]; exact hv))]
  rw [hsum]
  by_cases hmem : i ∈ cosetWindow dim N cm r
  · rw [if_pos hmem, if_pos hmem, mul_one]
    push_cast
    ring
  · rw [if_neg hmem, if_neg hmem, mul_zero]

/-! ## §5. The H output IS the contiguous coset state `cosetState (2^dim) (2^rest) cm 0`. -/

/-- **The npar_H output is the base coset state.**  On a `(cm+rest)`-qubit register,
    `npar_H cm` carries `|0…0⟩` to the uniform coset state with step `N = 2^rest` at base
    `0`: `cosetState (2^(cm+rest)) (2^rest) cm 0`. -/
theorem uc_eval_npar_H_eq_cosetState0 (cm rest : Nat) (hcm : 0 < cm) :
    FormalRV.Framework.uc_eval (npar_H cm : Framework.BaseUCom (cm + rest))
        * basis0 (cm + rest)
      = cosetState (2 ^ (cm + rest)) (2 ^ rest) cm 0 := by
  rw [npar_H_sum_over_hWindow cm rest hcm]
  exact uniform_window_sum_eq_cosetState (2 ^ (cm + rest)) (2 ^ rest) cm 0

/-! ## §6. Applying a window-bijecting gate: the GENERAL headline.

This is the structural lift, parametrized by the gate `g` whose basis permutation
`gateToPerm g` bijects the H-window onto the coset window.  Given such a `g`, applying
`uc_eval (toUCom g)` to the `npar_H` output produces `cosetState (2^(cm+rest)) N cm k`. -/

/-- **The general window-prep lift.**  If `g` is `WellTyped` on `cm+rest` qubits and its
    basis permutation `gateToPerm g` maps the H-window bijectively ONTO the coset window,
    then `uc_eval (toUCom g)` carries the `npar_H` uniform output to the coset state. -/
theorem uc_eval_gate_on_hOutput (g : Gate) (cm rest N k : Nat) (hcm : 0 < cm)
    (hwt : Gate.WellTyped (cm + rest) g)
    (hbij : Set.BijOn (gateToPerm g (cm + rest) hwt) (hWindow rest cm) (cWindow rest cm N k)) :
    FormalRV.Framework.uc_eval (Gate.toUCom (cm + rest) g)
        * (FormalRV.Framework.uc_eval (npar_H cm : Framework.BaseUCom (cm + rest))
            * basis0 (cm + rest))
      = cosetState (2 ^ (cm + rest)) N cm k := by
  set σ := gateToPerm g (cm + rest) hwt with hσ
  rw [npar_H_sum_over_hWindow cm rest hcm, Matrix.mul_smul, Matrix.mul_sum]
  -- push uc_eval through each basis vector via uc_eval_basis_agree
  have hstep : ∀ v ∈ hWindow rest cm,
      FormalRV.Framework.uc_eval (Gate.toUCom (cm + rest) g)
          * FormalRV.Framework.basis_vector (2 ^ (cm + rest)) (v : Nat)
        = FormalRV.Framework.basis_vector (2 ^ (cm + rest)) ((σ v : Fin _) : Nat) := by
    intro v _
    exact uc_eval_basis_agree g (cm + rest) hwt v
  rw [Finset.sum_congr rfl hstep]
  -- reindex ∑_{v∈hWindow} |σ v⟩  =  ∑_{w∈cWindow} |w⟩   (σ : hWindow ≃ cWindow)
  rw [← uniform_window_sum_eq_cosetState (2 ^ (cm + rest)) N cm k]
  congr 1
  refine Finset.sum_bij (fun v _ => σ v) ?_ ?_ ?_ ?_
  · intro v hv; exact Finset.mem_coe.mp (hbij.1 (Finset.mem_coe.mpr hv))
  · intro v _ w _ h; exact σ.injective h
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hbij.2.2 (Finset.mem_coe.mpr hw)
    exact ⟨v, Finset.mem_coe.mp hv, hvw⟩
  · intro v _; rfl

/-! ## §7. The concrete circuit `cosetStatePrep` and its well-typedness.

LAYOUT.  We work on `Dt = 2·bits` qubits.  The VALUE register occupies the top `bits`
wires (big-endian), listed REVERSED as `prepReg bits = [bits-1, …, 1, 0]` so that
`regVal (prepReg bits) φ` equals the big-endian value of those wires (no bit-reversal
mismatch with `funbool_to_nat`).  The bottom `bits` wires `[bits, 2·bits)` are the CLEAN
swap-ancilla `prepAnc bits`.  `npar_H cm` runs on the top `cm` MSB wires `[0, cm)` ⊆ reg.

The permutation fed to `permGate` is `σ_k (bits-cm) cm N k …`, transported across
`cm + (bits-cm) = bits = (prepReg bits).length`; this is the value-level map
`x·2^(bits-cm) ↦ k + x·N`. -/

/-- The value register: the top `bits` wires, listed reversed `[bits-1, …, 0]`. -/
def prepReg (bits : Nat) : List Nat := (List.range bits).reverse

/-- The swap-ancilla: the bottom `bits` wires `[bits, 2·bits)`. -/
def prepAnc (bits : Nat) : List Nat := (List.range bits).map (fun i => bits + i)

theorem prepReg_length (bits : Nat) : (prepReg bits).length = bits := by
  unfold prepReg; rw [List.length_reverse, List.length_range]

theorem prepAnc_length (bits : Nat) : (prepAnc bits).length = bits := by
  unfold prepAnc; rw [List.length_map, List.length_range]

theorem prepReg_nodup (bits : Nat) : (prepReg bits).Nodup := by
  unfold prepReg; rw [List.nodup_reverse]; exact List.nodup_range

theorem prepReg_mem (bits q : Nat) : q ∈ prepReg bits ↔ q < bits := by
  unfold prepReg; rw [List.mem_reverse, List.mem_range]

theorem prepAnc_nodup (bits : Nat) : (prepAnc bits).Nodup := by
  unfold prepAnc
  apply List.Nodup.map (fun a b h => by omega) List.nodup_range

theorem prepAnc_disj_prepReg (bits : Nat) : ∀ a ∈ prepAnc bits, a ∉ prepReg bits := by
  intro a ha hr
  rw [prepAnc, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [prepReg_mem] at hr
  rw [List.mem_range] at hi
  omega

theorem prepReg_lt (bits : Nat) : ∀ q ∈ prepReg bits, q < 2 * bits := by
  intro q hq
  rw [prepReg_mem] at hq; omega

theorem prepAnc_lt (bits : Nat) : ∀ a ∈ prepAnc bits, a < 2 * bits := by
  intro a ha
  rw [prepAnc, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [List.mem_range] at hi; omega

/-- The value-level permutation fed to `permGate`, on `Fin (2^(cm+rest))` (= the value
    register `Fin (2^(prepReg (cm+rest)).length)` after transport).  It is exactly `σ_k`,
    i.e. `x·2^rest ↦ k + x·N` on the window. -/
noncomputable def prepPerm (cm rest N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) : Equiv.Perm (Fin (2 ^ (cm + rest))) :=
  σ_k rest cm N k hN hk hbudget

/-- The total qubit count, written in the `cm + R` form (`R = cm + 2·rest`) that matches
    `uc_eval_gate_on_hOutput` natively.  Equals `2·(cm+rest)`. -/
abbrev prepDim (cm rest : Nat) : Nat := cm + (cm + 2 * rest)

/-- **The state-prep circuit.**  `npar_H cm` on the top `cm` wires, then the generic
    permutation gate routing the H-window onto the coset window, on `prepDim = 2·(cm+rest)`
    qubits.  The value register is the top `bits = cm+rest` wires; the bottom `bits` are the
    clean swap-ancilla. -/
noncomputable def cosetStatePrep (cm rest N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) : Framework.BaseUCom (prepDim cm rest) :=
  UCom.seq (FormalRV.Framework.BaseUCom.npar_H cm)
    (Gate.toUCom (prepDim cm rest)
      (permGate (prepReg (cm + rest))
        ((prepReg_length (cm + rest)).symm ▸ prepPerm cm rest N k hN hk hbudget)
        (prepAnc (cm + rest))))

/-- The permutation-gate leg of `cosetStatePrep`. -/
noncomputable def prepGate (cm rest N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) : Gate :=
  permGate (prepReg (cm + rest))
    ((prepReg_length (cm + rest)).symm ▸ prepPerm cm rest N k hN hk hbudget)
    (prepAnc (cm + rest))

/-- **`cosetStatePrep_wellTyped`.**  The permutation-gate leg is well-typed on
    `prepDim = 2·(cm+rest)` qubits (the npar_H leg is well-typed via `npar_H_well_typed`). -/
theorem cosetStatePrep_permGate_wellTyped (cm rest N k : Nat) (hbits : 0 < cm + rest)
    (hN : 0 < N) (hk : k < N) (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    Gate.WellTyped (prepDim cm rest) (prepGate cm rest N k hN hk hbudget) := by
  unfold prepGate
  exact permGate_wellTyped (prepReg (cm + rest))
    ((prepReg_length (cm + rest)).symm ▸ prepPerm cm rest N k hN hk hbudget)
    (prepAnc (cm + rest)) (prepDim cm rest)
    (prepReg_nodup (cm + rest)) (prepAnc_nodup (cm + rest)) (prepAnc_disj_prepReg (cm + rest))
    (by unfold prepDim; omega) (fun q hq => by unfold prepDim; have := prepReg_lt (cm + rest) q hq; omega)
    (fun a ha => by unfold prepDim; have := prepAnc_lt (cm + rest) a ha; omega)
    (by rw [prepReg_length, prepAnc_length]; omega)

/-! ## §7b. The funbool↔regVal coordinate identities (the bridge core). -/

/-- `funbool_to_nat` splits across an addition: high `a` wires × `2^b` plus low `b` wires. -/
theorem fbn_add (a b : Nat) (f : Nat → Bool) :
    FormalRV.Framework.funbool_to_nat (a + b) f
      = FormalRV.Framework.funbool_to_nat a f * 2 ^ b
        + FormalRV.Framework.funbool_to_nat b (fun p => f (p + a)) := by
  induction b with
  | zero => simp
  | succ n ih =>
    rw [show a + (n+1) = (a+n)+1 from by omega, FormalRV.Framework.funbool_to_nat_succ,
        FormalRV.Framework.funbool_to_nat_succ, ih, pow_succ,
        show (n + a) = (a + n) from by omega]
    ring

/-- Bit `i` of `funbool_to_nat n f` is `f (n-1-i)` (big-endian: `f 0` is the MSB). -/
theorem fbn_testBit (n : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n) :
    (FormalRV.Framework.funbool_to_nat n f).testBit i = f (n - 1 - i) := by
  induction n generalizing i with
  | zero => omega
  | succ m ih =>
    rw [FormalRV.Framework.funbool_to_nat_succ]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [show 2 * FormalRV.Framework.funbool_to_nat m f + (if f m then 1 else 0)
            = (if f m then 1 else 0) + 2 * FormalRV.Framework.funbool_to_nat m f from by ring,
          Nat.testBit_zero]
      simp only [Nat.add_mul_mod_self_left]
      rcases hfm : f m with _ | _ <;> simp [hfm]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [show 2 * FormalRV.Framework.funbool_to_nat m f + (if f m then 1 else 0)
            = (if f m then 1 else 0) + 2 * FormalRV.Framework.funbool_to_nat m f from by ring,
          Nat.testBit_add_one, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2),
          show (if f m then 1 else 0) / 2 = 0 from by rcases f m <;> simp, Nat.zero_add,
          ih j (by omega)]
      congr 1; omega

/-- `regIdx (prepReg bits) i = bits - 1 - i` for `i < bits` (the reversed register). -/
theorem regIdx_prepReg (bits i : Nat) (hi : i < bits) :
    FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.regIdx (prepReg bits) i = bits - 1 - i := by
  unfold FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.regIdx prepReg
  have hi' : i < (List.range bits).reverse.length := by rw [List.length_reverse, List.length_range]; exact hi
  rw [List.getD_eq_getElem _ 0 hi', List.getElem_reverse, List.getElem_range, List.length_range]

/-- **The DECODE identity (A).**  Over the reversed top-`bits` register `prepReg bits`,
    `regVal` reads off the big-endian value of the top wires: it equals
    `funbool_to_nat bits`.  (No bit-reversal mismatch — that is the point of `prepReg`.) -/
theorem funbool_eq_regVal (bits : Nat) (f : Nat → Bool) :
    FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.regVal (prepReg bits) f
      = FormalRV.Framework.funbool_to_nat bits f := by
  unfold FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.regVal
  rw [show (prepReg bits).length = bits from prepReg_length bits]
  rw [FormalRV.Shor.WindowedCircuit.decodeReg_eq_mod_of_testBit
        (FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.regIdx (prepReg bits)) bits
        (FormalRV.Framework.funbool_to_nat bits f) f
        (fun i hi => by rw [regIdx_prepReg bits i hi, fbn_testBit bits f i hi])]
  exact Nat.mod_eq_of_lt (FormalRV.Framework.funbool_to_nat_lt bits f)

/-- `funbool_to_nat n g = 0` when `g` is `false` on `[0,n)`. -/
theorem fbn_zero_of_clean (n : Nat) (g : Nat → Bool) (h : ∀ i, i < n → g i = false) :
    FormalRV.Framework.funbool_to_nat n g = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [FormalRV.Framework.funbool_to_nat_succ, ih (fun i hi => h i (by omega)),
        h m (by omega)]
    simp

/-- `prepDim cm rest = (cm+rest) + (cm+rest)` (the value register + the ancilla, each
    `bits = cm+rest` wires). -/
theorem prepDim_eq (cm rest : Nat) : prepDim cm rest = (cm + rest) + (cm + rest) := by
  unfold prepDim; omega

/-- **The CLEAN-REGISTER funbool value (identities A and B unified).**  For any state `h`
    that is clean on the swap-ancilla `prepAnc (cm+rest)` (the bottom `bits` wires), the
    full-register `funbool_to_nat` value is the top-register value `regVal (prepReg)`,
    SCALED by `2^(cm+rest)` (the ancilla scale). -/
theorem funbool_of_clean_reg (cm rest : Nat) (h : Nat → Bool)
    (hclean : ∀ a ∈ prepAnc (cm + rest), h a = false) :
    FormalRV.Framework.funbool_to_nat (prepDim cm rest) h
      = FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.regVal (prepReg (cm + rest)) h
        * 2 ^ (cm + rest) := by
  rw [prepDim_eq, fbn_add (cm + rest) (cm + rest) h, funbool_eq_regVal (cm + rest) h]
  rw [fbn_zero_of_clean (cm + rest) (fun p => h (p + (cm + rest))) ?_, Nat.add_zero]
  intro p hp
  refine hclean (p + (cm + rest)) ?_
  rw [prepAnc, List.mem_map]
  exact ⟨p, List.mem_range.mpr hp, by omega⟩

/-! ## §7c. The BRIDGE: `gateToPerm (prepGate)` bijects the windows.

Putting §7b together with `permGate_RegAct` and `gateToPerm_funboolNat`. -/

open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
  (regVal setReg RegAct regVal_lt setReg_clean regVal_setReg)

/-- The ANCILLA SCALE.  The value register sits at the top `bits = cm+rest` wires; the
    clean swap-ancilla occupies the bottom `bits` wires (the low-order `funbool` bits).  So
    a clean-ancilla value `V` is encoded as the full-register index `V · 2^(cm+rest)`.  The
    coset window therefore appears in the FULL register SCALED by `2^(cm+rest)`: step
    `N · 2^(cm+rest)`, base `k · 2^(cm+rest)`.  This is a genuine, honest coset state. -/
abbrev prepScale (cm rest : Nat) : Nat := 2 ^ (cm + rest)

/-- Applying a length-transported perm reads off the same value as the untransported one.
    (Replicated from `E2RunwaySynthRunwayGate.perm_cast_apply`.) -/
theorem perm_cast_apply {a b : Nat} (hh : a = b) (τ : Equiv.Perm (Fin (2 ^ a)))
    (v : Nat) (hb : v < 2 ^ b) (ha : v < 2 ^ a) :
    ((hh ▸ τ) ⟨v, hb⟩ : Fin (2 ^ b)).val = (τ ⟨v, ha⟩).val := by
  subst hh; rfl

/-- The bottom `funbool` bits of an H-window index are 0: `extendBool prepDim φ` is clean on
    `prepAnc` when `funbool_to_nat prepDim (extendBool φ) = x · 2^(cm+2·rest)`. -/
theorem extendBool_clean_of_hwin (cm rest x : Nat) (φ : Fin (prepDim cm rest) → Bool)
    (hval : FormalRV.Framework.funbool_to_nat (prepDim cm rest) (extendBool (prepDim cm rest) φ)
      = x * 2 ^ (cm + 2 * rest)) :
    ∀ a ∈ prepAnc (cm + rest), extendBool (prepDim cm rest) φ a = false := by
  intro a ha
  rw [prepAnc, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [List.mem_range] at hi
  -- a = (cm+rest)+i; its funbool bit position is (cm+rest)-1-i, below cm+2·rest, where x·2^… is 0.
  have hapos : (cm + rest) + i < prepDim cm rest := by unfold prepDim; omega
  have hbit : (extendBool (prepDim cm rest) φ) ((cm + rest) + i)
      = (x * 2 ^ (cm + 2 * rest)).testBit ((cm + rest) - 1 - i) := by
    have hfb := fbn_testBit (prepDim cm rest) (extendBool (prepDim cm rest) φ)
      ((cm + rest) - 1 - i) (by unfold prepDim; omega)
    rw [hval] at hfb
    rw [show (cm + rest) + i = prepDim cm rest - 1 - ((cm + rest) - 1 - i) from by
          unfold prepDim; omega]
    exact hfb.symm
  rw [hbit, Nat.testBit_mul_two_pow]
  simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
  intro hle; omega

/-- **THE BRIDGE.**  `gateToPerm (prepGate …)` maps the H-window of the full register
    bijectively onto the SCALED coset window (step `N·2^(cm+rest)`, base `k·2^(cm+rest)`). -/
theorem prepGate_bridge (cm rest N k : Nat) (_hcm : 0 < cm) (hbits : 0 < cm + rest)
    (hN : 0 < N) (hk : k < N) (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    Set.BijOn
      (gateToPerm (prepGate cm rest N k hN hk hbudget) (prepDim cm rest)
        (cosetStatePrep_permGate_wellTyped cm rest N k hbits hN hk hbudget))
      (hWindow (cm + 2 * rest) cm)
      (cWindow (cm + 2 * rest) cm (N * prepScale cm rest) (k * prepScale cm rest)) := by
  set hwt := cosetStatePrep_permGate_wellTyped cm rest N k hbits hN hk hbudget with hhwt
  set g := prepGate cm rest N k hN hk hbudget with hg
  set σ := gateToPerm g (prepDim cm rest) hwt with hσ
  -- abbreviations
  set τ := prepPerm cm rest N k hN hk hbudget with hτ
  set τcast : Equiv.Perm (Fin (2 ^ (prepReg (cm + rest)).length)) :=
    (prepReg_length (cm + rest)).symm ▸ τ with hτcast
  have hglen : (prepReg (cm + rest)).length = (cm + rest) := prepReg_length (cm + rest)
  -- the RegAct of the permutation gate (clean ancilla ⇒ value = permOnVal on regVal).
  have hRA : RegAct g (prepReg (cm + rest)) (prepAnc (cm + rest)) (permOnVal (prepReg (cm + rest)) τcast) := by
    rw [hg]; unfold prepGate
    exact permGate_RegAct (prepReg (cm + rest)) τcast (prepAnc (cm + rest))
      (prepReg_nodup (cm + rest)) (prepAnc_nodup (cm + rest)) (prepAnc_disj_prepReg (cm + rest))
      (by rw [prepReg_length, prepAnc_length]; omega)
  obtain ⟨_, hact⟩ := hRA
  -- KEY: the value action.  For v ∈ hWindow, σ v ∈ scaled cWindow.
  have hMapsTo : ∀ v ∈ hWindow (cm + 2 * rest) cm,
      σ v ∈ cWindow (cm + 2 * rest) cm (N * prepScale cm rest) (k * prepScale cm rest) := by
    intro v hv
    -- decode v as x·2^(cm+2·rest)
    rw [hWindow, mem_cosetWindow _ _ _ _ (Nat.two_pow_pos (cm + 2 * rest))] at hv
    obtain ⟨x, hx, hxeq⟩ := hv
    rw [Nat.zero_add] at hxeq
    -- φ : the funbool of v
    set φ := (funboolEquiv (prepDim cm rest)).symm v with hφ
    have hvfb : v = funboolNat (prepDim cm rest) φ := by
      rw [hφ]; exact (Equiv.apply_symm_apply (funboolEquiv (prepDim cm rest)) v).symm
    have hvval : FormalRV.Framework.funbool_to_nat (prepDim cm rest) (extendBool (prepDim cm rest) φ)
        = x * 2 ^ (cm + 2 * rest) := by
      have hvv : (funboolNat (prepDim cm rest) φ : Fin _).val = v.val := by rw [← hvfb]
      -- (funboolNat dim φ).val = funbool_to_nat dim (extendBool dim φ)  definitionally
      show (funboolNat (prepDim cm rest) φ : Fin _).val = x * 2 ^ (cm + 2 * rest)
      rw [hvv, hxeq]
    -- clean ancilla
    have hcl : ∀ a ∈ prepAnc (cm + rest), extendBool (prepDim cm rest) φ a = false :=
      extendBool_clean_of_hwin cm rest x φ hvval
    -- regVal of extendBool φ = x·2^rest
    have hRV : regVal (prepReg (cm + rest)) (extendBool (prepDim cm rest) φ) = x * 2 ^ rest := by
      have hfc := funbool_of_clean_reg cm rest (extendBool (prepDim cm rest) φ) hcl
      rw [hvval] at hfc
      -- x·2^(cm+2rest) = regVal · 2^(cm+rest)  ⇒  regVal = x·2^rest
      have hcancel : regVal (prepReg (cm + rest)) (extendBool (prepDim cm rest) φ) * 2 ^ (cm + rest)
          = (x * 2 ^ rest) * 2 ^ (cm + rest) := by
        rw [← hfc]
        rw [show (x * 2 ^ rest) * 2 ^ (cm + rest) = x * 2 ^ (cm + 2 * rest) from by
              rw [mul_assoc, ← pow_add]; congr 2; omega]
      exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos (cm + rest)) hcancel
    -- the value written by the gate
    have hRVlt : regVal (prepReg (cm + rest)) (extendBool (prepDim cm rest) φ) < 2 ^ (prepReg (cm + rest)).length := by
      rw [hglen, hRV]
      calc x * 2 ^ rest < 2 ^ cm * 2 ^ rest :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos rest)).mpr hx
        _ = 2 ^ (cm + rest) := (pow_add 2 cm rest).symm
    -- permOnVal = (σ_k ⟨x·2^rest⟩).val ∈ cWindow rest cm N k
    set W := permOnVal (prepReg (cm + rest)) τcast (regVal (prepReg (cm + rest)) (extendBool (prepDim cm rest) φ))
      with hW
    have hWval : W = (σ_k rest cm N k hN hk hbudget
        ⟨x * 2 ^ rest, by
          calc x * 2 ^ rest < 2 ^ cm * 2 ^ rest :=
                (Nat.mul_lt_mul_right (Nat.two_pow_pos rest)).mpr hx
            _ = 2 ^ (cm + rest) := (pow_add 2 cm rest).symm⟩).val := by
      rw [hW, permOnVal, dif_pos hRVlt]
      rw [perm_cast_apply (prepReg_length (cm + rest)).symm τ
            (regVal (prepReg (cm + rest)) (extendBool (prepDim cm rest) φ)) hRVlt
            (by rw [hglen] at hRVlt; exact hRVlt)]
      rw [show τ = σ_k rest cm N k hN hk hbudget from hτ]
      exact congrArg (fun t => ((σ_k rest cm N k hN hk hbudget) t).val) (Fin.ext hRV)
    -- σ_k ⟨x·2^rest⟩ ∈ cWindow rest cm N k
    have hWin : (σ_k rest cm N k hN hk hbudget
        ⟨x * 2 ^ rest, by
          calc x * 2 ^ rest < 2 ^ cm * 2 ^ rest :=
                (Nat.mul_lt_mul_right (Nat.two_pow_pos rest)).mpr hx
            _ = 2 ^ (cm + rest) := (pow_add 2 cm rest).symm⟩)
        ∈ cWindow rest cm N k := by
      refine σ_k_window rest cm N k hN hk hbudget _ ?_
      rw [hWindow, mem_cosetWindow _ _ _ _ (Nat.two_pow_pos rest)]
      exact ⟨x, hx, by simp⟩
    -- so W = k + j·N (some j<2^cm), and W < 2^(cm+rest)
    rw [cWindow, mem_cosetWindow _ _ _ _ hN] at hWin
    obtain ⟨j, hj, hjeq⟩ := hWin
    rw [← hWval] at hjeq
    -- σ v value = W · 2^(cm+rest)  (encode identity on the clean written register)
    have hσval : (σ v).val = W * 2 ^ (cm + rest) := by
      rw [hσ, hvfb, gateToPerm_funboolNat g (prepDim cm rest) hwt φ, funboolNat]
      -- funbool_to_nat prepDim (extendBool (applyFin g φ)) ; applyFin = applyNat on [0,prepDim)
      show FormalRV.Framework.funbool_to_nat (prepDim cm rest)
            (extendBool (prepDim cm rest) (applyFin g (prepDim cm rest) φ)) = W * 2 ^ (cm + rest)
      -- the written register `applyNat g (extendBool φ)` agrees with its funbool on [0,prepDim)
      have hagree : ∀ p, p < prepDim cm rest →
          extendBool (prepDim cm rest) (applyFin g (prepDim cm rest) φ) p
            = Gate.applyNat g (extendBool (prepDim cm rest) φ) p := by
        intro p hp
        simp only [extendBool, applyFin, dif_pos hp]
      rw [FormalRV.Shor.GidneyInPlace.UCEvalBridge.funbool_to_nat_congr (prepDim cm rest) _ _ hagree]
      -- applyNat g (extendBool φ) = setReg prepReg W (extendBool φ)  (clean ancilla)
      rw [hact (extendBool (prepDim cm rest) φ) hcl]
      -- funbool of the written register: clean ancilla preserved, value = W
      rw [funbool_of_clean_reg cm rest (setReg (prepReg (cm + rest)) W (extendBool (prepDim cm rest) φ))
            (setReg_clean (prepReg (cm + rest)) (prepAnc (cm + rest)) W (extendBool (prepDim cm rest) φ)
              (prepAnc_disj_prepReg (cm + rest)) hcl)]
      congr 1
      rw [regVal_setReg (prepReg (cm + rest)) W (extendBool (prepDim cm rest) φ) (prepReg_nodup (cm + rest))
            (by rw [hW]; rw [permOnVal, dif_pos hRVlt]; exact (τcast _).isLt)]
    -- conclude: (σ v).val = (k+j·N)·2^(cm+rest) ∈ scaled cWindow
    rw [show cWindow (cm + 2 * rest) cm (N * prepScale cm rest) (k * prepScale cm rest)
          = cosetWindow (2 ^ (cm + (cm + 2 * rest))) (N * prepScale cm rest) cm
              (k * prepScale cm rest) from rfl,
        mem_cosetWindow _ _ _ _ (by positivity : 0 < N * prepScale cm rest)]
    refine ⟨j, hj, ?_⟩
    rw [hσval]
    show W * 2 ^ (cm + rest) = k * prepScale cm rest + j * (N * prepScale cm rest)
    rw [prepScale, hjeq]
    ring
  -- BijOn from MapsTo + injectivity + card (mirror σ_k_bijOn)
  refine ⟨hMapsTo, (σ.injective).injOn, ?_⟩
  intro w hw
  have himg_sub : (hWindow (cm + 2 * rest) cm).image σ
      ⊆ cWindow (cm + 2 * rest) cm (N * prepScale cm rest) (k * prepScale cm rest) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact hMapsTo u hu
  have hcard : ((hWindow (cm + 2 * rest) cm).image σ).card
      = (cWindow (cm + 2 * rest) cm (N * prepScale cm rest) (k * prepScale cm rest)).card := by
    rw [Finset.card_image_of_injective _ σ.injective, hWindow_card (cm + 2 * rest) cm,
        cWindow_card (cm + 2 * rest) cm (N * prepScale cm rest) (k * prepScale cm rest)
          (by positivity)
          (show k * prepScale cm rest < N * prepScale cm rest from
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hk)
          ?_]
    -- scaled budget: 2^cm · (N·2^(cm+rest)) ≤ 2^(cm+(cm+2·rest))
    show 2 ^ cm * (N * 2 ^ (cm + rest)) ≤ 2 ^ (cm + (cm + 2 * rest))
    calc 2 ^ cm * (N * 2 ^ (cm + rest))
        = (2 ^ cm * N) * 2 ^ (cm + rest) := by ring
      _ ≤ 2 ^ (cm + rest) * 2 ^ (cm + rest) := Nat.mul_le_mul_right (2 ^ (cm + rest)) hbudget
      _ = 2 ^ (cm + (cm + 2 * rest)) := by rw [← pow_add]; congr 1; omega
  have heq : (hWindow (cm + 2 * rest) cm).image σ
      = cWindow (cm + 2 * rest) cm (N * prepScale cm rest) (k * prepScale cm rest) :=
    Finset.eq_of_subset_of_card_le himg_sub (le_of_eq hcard.symm)
  have hwimg : w ∈ (hWindow (cm + 2 * rest) cm).image σ := by
    rw [heq]; exact Finset.mem_coe.mpr hw
  rw [Finset.mem_image] at hwimg
  obtain ⟨u, hu, huw⟩ := hwimg
  exact ⟨u, Finset.mem_coe.mpr hu, huw⟩

/-! ## §8. The headline, reduced to the funbool↔regVal BRIDGE.

The remaining content is purely the coordinate bridge: the `permGate`'s register-value
action (`permGate_RegAct` / `gateToPerm_funboolNat`, in `regVal` space) must be shown to
biject the `funbool_to_nat`-encoded H-window onto the `funbool_to_nat`-encoded coset window
of the FULL `prepDim = 2·(cm+rest)`-qubit register.  We isolate that as the hypothesis
`hbridge` and prove the headline GIVEN it (everything else — the npar_H closed form, the
uniform-sum reindexing, the per-basis gate action, and the sum-to-indicator — is already
discharged in §0–§6).  See the module report for the precise next step. -/

/-- **The headline, modulo the coordinate bridge.**  Given that the permutation gate's
    basis permutation `gateToPerm (prepGate …)` maps the H-window of the FULL
    `prepDim = 2·(cm+rest)`-qubit register bijectively onto the SCALED coset window
    (step `N·2^(cm+rest)`, base `k·2^(cm+rest)` — the ancilla scale, see `prepScale`),
    `cosetStatePrep` prepares the corresponding scaled `cosetState` from `|0…0⟩`.

    The FULL-register rest is `R = prepDim − cm = cm + 2·rest`, so the H-window is
    `hWindow (cm+2·rest) cm` and the target is `cWindow (cm+2·rest) cm (N·2^(cm+rest))
    (k·2^(cm+rest))`. -/
theorem uc_eval_cosetStatePrep_of_bridge (cm rest N k : Nat) (hcm : 0 < cm) (hbits : 0 < cm + rest)
    (hN : 0 < N) (hk : k < N) (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest))
    (hbridge : Set.BijOn
      (gateToPerm (prepGate cm rest N k hN hk hbudget) (prepDim cm rest)
        (cosetStatePrep_permGate_wellTyped cm rest N k hbits hN hk hbudget))
      (hWindow (cm + 2 * rest) cm)
      (cWindow (cm + 2 * rest) cm (N * prepScale cm rest) (k * prepScale cm rest))) :
    FormalRV.Framework.uc_eval (cosetStatePrep cm rest N k hN hk hbudget)
        * basis0 (prepDim cm rest)
      = cosetState (2 ^ prepDim cm rest) (N * prepScale cm rest) cm (k * prepScale cm rest) := by
  rw [cosetStatePrep, FormalRV.Framework.uc_eval_seq_mul]
  have key := uc_eval_gate_on_hOutput (prepGate cm rest N k hN hk hbudget) cm (cm + 2 * rest)
    (N * prepScale cm rest) (k * prepScale cm rest)
    hcm (cosetStatePrep_permGate_wellTyped cm rest N k hbits hN hk hbudget) hbridge
  -- `prepGate` unfolds to the permGate term appearing in the goal; `prepDim = cm+(cm+2·rest)`.
  rw [show prepGate cm rest N k hN hk hbudget
        = permGate (prepReg (cm + rest))
            ((prepReg_length (cm + rest)).symm ▸ prepPerm cm rest N k hN hk hbudget)
            (prepAnc (cm + rest)) from rfl] at key
  exact key

/-- **THE HEADLINE (unconditional).**  The state-prep circuit `cosetStatePrep` carries
    `|0…0⟩` on the `prepDim = 2·(cm+rest)`-qubit register to the Zalka/Gidney coset state
    `cosetState (2^prepDim) (N·2^(cm+rest)) cm (k·2^(cm+rest))` — the coset window of step
    `N`, base `k`, scaled by the ancilla factor `2^(cm+rest)` (the clean swap-ancilla
    occupies the low `cm+rest` bits).

    Hypotheses: `0 < cm`, `0 < cm+rest`, `0 < N`, `k < N`, and the FULL-BLOCKS budget
    `2^cm · N ≤ 2^(cm+rest)`.  Construction: `npar_H cm` then `permGate` with the window
    permutation `σ_k`.  Kernel-clean. -/
theorem uc_eval_cosetStatePrep (cm rest N k : Nat) (hcm : 0 < cm) (hbits : 0 < cm + rest)
    (hN : 0 < N) (hk : k < N) (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    FormalRV.Framework.uc_eval (cosetStatePrep cm rest N k hN hk hbudget)
        * basis0 (prepDim cm rest)
      = cosetState (2 ^ prepDim cm rest) (N * prepScale cm rest) cm (k * prepScale cm rest) :=
  uc_eval_cosetStatePrep_of_bridge cm rest N k hcm hbits hN hk hbudget
    (prepGate_bridge cm rest N k hcm hbits hN hk hbudget)

-- Kernel-cleanliness check (axioms ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms uc_eval_cosetStatePrep
#print axioms uc_eval_cosetStatePrep_of_bridge
#print axioms prepGate_bridge
#print axioms uc_eval_npar_H_eq_cosetState0
#print axioms σ_k_bijOn
#print axioms cosetStatePrep_permGate_wellTyped

end FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepCore
