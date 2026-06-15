/-
  FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Correctness
  ──────────────────────────────────────────────────────────────
  VALUE correctness of the faithful Gidney-2025 subtract-fixup modular adder:
  the low `bits` target register decodes to `(x + c) % p` for `x < p`, `c < p`,
  with the extra top qubit `Q` released to `0`.

  See `Def.lean` for the construction. The two additions are the MEASURED Gidney
  adder, REUSED verbatim (`gidneyAdderMeasured_target_val`,
  `gidneyAdderMeasured_correct`); the only NEW arithmetic is the two's-complement
  underflow case-split (`fixup_value`).
-/
import FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Def

namespace FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Arithmetic.MeasuredAdder

/-! ## §0. A TIGHT boundedness for the measured adder.

`MeasuredAdder` exports `gidneyAdderMeasured_boundedBy : boundedBy (adder_n_qubits
(n+2)) = boundedBy (3·(n+2)+2)`. We need the slightly TIGHTER `boundedBy
(3·(n+2))`: the adder's highest index is the top carry `carry_idx (n+1) = 3n+5 =
3·(n+2) − 1`, so it touches NOTHING at `3·(n+2)` or above — in particular it leaves
the two free slots `read_idx (n+2) = 3·(n+2)` and `target_idx (n+1) = 3·(n+2)−1`…
We reprove the cascade bounds at the tight bound from the public step definitions. -/

private theorem forward_first_bnd : Gate.boundedBy 5 gidney_adder_bit_step_faithful_first := by
  simp only [gidney_adder_bit_step_faithful_first, Gate.boundedBy, read_idx, target_idx, carry_idx]; omega

private theorem forward_interior_bnd (i : Nat) :
    Gate.boundedBy (3 * i + 5) (gidney_adder_bit_step_faithful_interior i) := by
  simp only [gidney_adder_bit_step_faithful_interior, Gate.boundedBy, read_idx, target_idx, carry_idx]; omega

private theorem forward_last_bnd (i : Nat) :
    Gate.boundedBy (3 * i + 3) (gidney_adder_bit_step_faithful_last i) := by
  simp only [gidney_adder_bit_step_faithful_last, Gate.boundedBy, read_idx, target_idx, carry_idx]; omega

private theorem forward_prop_bnd :
    ∀ k, Gate.boundedBy (3 * k + 2) (gidney_adder_forward_with_propagation k)
  | 0 => trivial
  | 1 => Gate.boundedBy_mono (by omega) _ forward_first_bnd
  | n + 2 => ⟨Gate.boundedBy_mono (by omega) _ (forward_prop_bnd (n + 1)),
             Gate.boundedBy_mono (by omega) _ (forward_interior_bnd (n + 1))⟩

/-- The faithful forward sweep at width `n+2` is bounded by `3·(n+2)` (tight). -/
theorem forward_full_bnd_tight (n : Nat) :
    Gate.boundedBy (3 * (n + 2)) (gidney_adder_forward_faithful_full (n + 2)) := by
  show Gate.boundedBy (3 * (n + 2))
    (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
              (gidney_adder_bit_step_faithful_last (n + 1)))
  exact ⟨Gate.boundedBy_mono (by omega) _ (forward_prop_bnd (n + 1)),
         Gate.boundedBy_mono (by omega) _ (forward_last_bnd (n + 1))⟩

/-- The final-CX cascade of length `k` is bounded by `3·k` (tight). -/
theorem final_cx_bnd_tight : ∀ k, Gate.boundedBy (3 * k) (gidney_final_cx_cascade k)
  | 0 => trivial
  | k + 1 => by
      show Gate.boundedBy (3 * (k + 1))
        (Gate.seq (gidney_final_cx_cascade k) (Gate.CX (read_idx k) (target_idx k)))
      exact ⟨Gate.boundedBy_mono (by omega) _ (final_cx_bnd_tight k),
             by simp only [Gate.boundedBy, read_idx, target_idx]; omega⟩

private theorem measFirst_bnd : EGate.boundedBy 5 gidneyMeasFirstReverse := by
  simp only [gidneyMeasFirstReverse, EGate.boundedBy, Gate.boundedBy, read_idx, target_idx, carry_idx]; omega

private theorem measInterior_bnd (i : Nat) :
    EGate.boundedBy (3 * i + 5) (gidneyMeasInteriorReverse i) := by
  simp only [gidneyMeasInteriorReverse, EGate.boundedBy, Gate.boundedBy, read_idx, target_idx, carry_idx]; omega

private theorem measLast_bnd (i : Nat) :
    EGate.boundedBy (3 * i + 3) (gidneyMeasLastReverse i) := by
  simp only [gidneyMeasLastReverse, EGate.boundedBy, Gate.boundedBy, carry_idx]; omega

private theorem measProp_bnd :
    ∀ K, EGate.boundedBy (3 * K + 2) (gidneyMeasPropReverse K)
  | 0 => by simp [gidneyMeasPropReverse, EGate.boundedBy, Gate.boundedBy]
  | 1 => EGate.boundedBy_mono (by omega) _ measFirst_bnd
  | n + 2 => by
      show EGate.boundedBy (3 * (n + 2) + 2)
        (EGate.seq (gidneyMeasInteriorReverse (n + 1)) (gidneyMeasPropReverse (n + 1)))
      exact ⟨EGate.boundedBy_mono (by omega) _ (measInterior_bnd (n + 1)),
             EGate.boundedBy_mono (by omega) _ (measProp_bnd (n + 1))⟩

/-- The measured full-reverse cascade at width `n+2` is bounded by `3·(n+2)` (tight). -/
theorem measFullReverse_bnd_tight (n : Nat) :
    EGate.boundedBy (3 * (n + 2)) (gidneyMeasFullReverse (n + 2)) := by
  show EGate.boundedBy (3 * (n + 2))
    (EGate.seq (gidneyMeasLastReverse (n + 1)) (gidneyMeasPropReverse (n + 1)))
  exact ⟨EGate.boundedBy_mono (by omega) _ (measLast_bnd (n + 1)),
         EGate.boundedBy_mono (by omega) _ (measProp_bnd (n + 1))⟩

/-- **TIGHT boundedness of the measured adder:** `gidneyAdderMeasured (n+2) q_start`
references only indices `< 3·(n+2)`, so it is the identity at every index
`≥ 3·(n+2)` — in particular the two free slots `read_idx (n+2)` and
`target_idx (n+1)` above the `(n+2)`-bit register. -/
theorem gidneyAdderMeasured_boundedBy_tight (n q_start : Nat) :
    EGate.boundedBy (3 * (n + 2)) (gidneyAdderMeasured (n + 2) q_start) := by
  show EGate.boundedBy (3 * (n + 2))
    (EGate.seq
      (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                            (gidney_final_cx_cascade (n + 2))))
      (gidneyMeasFullReverse (n + 2)))
  exact ⟨⟨forward_full_bnd_tight n, Gate.boundedBy_mono (by omega) _ (final_cx_bnd_tight (n + 2))⟩,
         measFullReverse_bnd_tight n⟩

/-! ## §1. Loading a constant turns the clean input into the two-operand input. -/

/-- `loadConst W d` is the identity outside the read window `read_idx [0, W)`. -/
theorem loadConst_preserves_outside
    (W d : Nat) (f : Nat → Bool) (q : Nat) (h : ∀ i, i < W → q ≠ read_idx i) :
    Gate.applyNat (loadConst W d) f q = f q := by
  induction W with
  | zero => rfl
  | succ k ih =>
      have ih' : Gate.applyNat (loadConst k d) f q = f q := ih (fun i hi => h i (by omega))
      show Gate.applyNat (if d.testBit k then Gate.X (read_idx k) else Gate.I)
            (Gate.applyNat (loadConst k d) f) q = f q
      split
      · simp only [Gate.applyNat_X]; rw [update_neq _ _ _ _ (h k (by omega)), ih']
      · simp only [Gate.applyNat]; exact ih'

/-- At `read_idx j` (for `j < W`), `loadConst W d` XORs in `d.testBit j`. -/
theorem loadConst_at_read_idx
    (W d : Nat) (f : Nat → Bool) (j : Nat) (hj : j < W) :
    Gate.applyNat (loadConst W d) f (read_idx j) = xor (f (read_idx j)) (d.testBit j) := by
  induction W with
  | zero => omega
  | succ k ih =>
      show Gate.applyNat (if d.testBit k then Gate.X (read_idx k) else Gate.I)
            (Gate.applyNat (loadConst k d) f) (read_idx j) = _
      by_cases hjk : j < k
      · have hne : read_idx j ≠ read_idx k := by unfold read_idx; omega
        have hframe := ih hjk
        split
        · simp only [Gate.applyNat_X]; rw [update_neq _ _ _ _ hne, hframe]
        · simp only [Gate.applyNat]; exact hframe
      · have hjeq : j = k := by omega
        subst hjeq
        have hframe : Gate.applyNat (loadConst j d) f (read_idx j) = f (read_idx j) :=
          loadConst_preserves_outside j d f (read_idx j) (fun i hi => by unfold read_idx; omega)
        split
        next ht => simp only [Gate.applyNat_X]; rw [update_eq, hframe, ht, Bool.xor_true]
        next hf =>
          simp only [Gate.applyNat]
          rw [hframe, (by simpa using hf : d.testBit j = false), Bool.xor_false]

/-- **Loading turns the clean input into the two-operand input.** On the clean
input `adder_input_F W 0 x` (read register `0`, target = `x`, carries `0`),
`loadConst W d` produces exactly `adder_input_F W d x`. -/
theorem loadConst_clean_eq_input (W d x : Nat) :
    Gate.applyNat (loadConst W d) (adder_input_F W 0 x) = adder_input_F W d x := by
  funext q
  obtain ⟨j, hj⟩ : ∃ j, j = q / 3 := ⟨_, rfl⟩
  have h3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h3 with hmod | hmod | hmod
  · -- read index q = read_idx j
    have hqread : q = read_idx j := by unfold read_idx; omega
    subst hqread
    by_cases hjW : j < W
    · rw [loadConst_at_read_idx W d _ j hjW]
      have hin0 : adder_input_F W 0 x (read_idx j) = false := by
        unfold adder_input_F read_idx
        rw [show (3 * j) % 3 = 0 by omega]; simp
      rw [hin0, Bool.false_xor]
      unfold adder_input_F read_idx
      rw [show (3 * j) % 3 = 0 by omega, show (3 * j) / 3 = j by omega, decide_eq_true hjW,
          Bool.true_and]
    · rw [loadConst_preserves_outside W d _ (read_idx j)
            (fun i hi => by unfold read_idx; omega)]
      unfold adder_input_F read_idx
      rw [show (3 * j) % 3 = 0 by omega, show (3 * j) / 3 = j by omega,
          show decide (j < W) = false by simp [hjW]]
      simp
  · -- target index
    have hqtarget : q = target_idx j := by unfold target_idx; omega
    subst hqtarget
    rw [loadConst_preserves_outside W d _ (target_idx j)
          (fun i hi => by unfold target_idx read_idx; omega)]
    unfold adder_input_F target_idx
    rw [show (3 * j + 1) % 3 = 1 by omega]
  · -- carry index
    have hqcarry : q = carry_idx j := by unfold carry_idx; omega
    subst hqcarry
    rw [loadConst_preserves_outside W d _ (carry_idx j)
          (fun i hi => by unfold carry_idx read_idx; omega)]
    unfold adder_input_F carry_idx
    rw [show (3 * j + 2) % 3 = 2 by omega]

/-! ## §2. The measured adder preserves the read register.

The measured reverse cascade agrees with the reversible reverse on every non-carry
index (`gidneyMeasFullReverse_rt`); read indices are non-carry, so the measured
adder's read register equals the reversible adder's = the augend `a`. -/

/-- **The measured Gidney adder preserves the read register** (`= a`). -/
theorem gidneyAdderMeasured_read
    (n a b q_start : Nat) (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    ∀ i, i < n + 2 →
      EGate.applyNat (gidneyAdderMeasured (n + 2) q_start)
          (adder_input_F (n + 2) a b) (read_idx i) = a.testBit i := by
  intro i hi
  rw [gidneyAdderMeasured_applyNat,
      gidneyMeasFullReverse_rt n _ (read_idx i) (by intro m; unfold read_idx carry_idx; omega),
      ← gidney_adder_full_faithful_no_measurement_applyNat n (adder_input_F (n + 2) a b)]
  exact gidney_adder_full_faithful_no_measurement_read_correct (n + 2) a b (by omega) ha hb i hi

/-! ## §3. `addConstMeasured` value bundle: `target += d` on a clean input. -/

/-- `loadConst W d` is the identity at every target/carry index (it only touches
read indices). -/
theorem loadConst_target (W d : Nat) (f : Nat → Bool) (i : Nat) :
    Gate.applyNat (loadConst W d) f (target_idx i) = f (target_idx i) :=
  loadConst_preserves_outside W d f (target_idx i) (fun j _ => by unfold target_idx read_idx; omega)

theorem loadConst_carry (W d : Nat) (f : Nat → Bool) (i : Nat) :
    Gate.applyNat (loadConst W d) f (carry_idx i) = f (carry_idx i) :=
  loadConst_preserves_outside W d f (carry_idx i) (fun j _ => by unfold carry_idx read_idx; omega)

/-- **`addConstMeasured` per-index bundle.** On the clean input `adder_input_F (n+2)
0 x`, the gate `addConstMeasured (n+2) d` (load `d`, measured-add, unload) gives,
for every `i < n+2`:
  • `target[i] = (x + d).testBit i`,
  • `read[i]   = false`  (read register restored to `0`),
  • `carry[i]  = false`  (carries released). -/
theorem addConstMeasured_bundle (n d x : Nat) (hd : d < 2 ^ (n + 2)) (hx : x < 2 ^ (n + 2)) :
    ∀ i, i < n + 2 →
      (EGate.applyNat (addConstMeasured (n + 2) d) (adder_input_F (n + 2) 0 x) (target_idx i)
        = (x + d).testBit i)
      ∧ (EGate.applyNat (addConstMeasured (n + 2) d) (adder_input_F (n + 2) 0 x) (read_idx i)
        = false)
      ∧ (EGate.applyNat (addConstMeasured (n + 2) d) (adder_input_F (n + 2) 0 x) (carry_idx i)
        = false) := by
  intro i hi
  -- unfold the EGate seq structure to a final `loadConst` applied to the measured-adder output
  have hstep : ∀ q,
      EGate.applyNat (addConstMeasured (n + 2) d) (adder_input_F (n + 2) 0 x) q
        = Gate.applyNat (loadConst (n + 2) d)
            (EGate.applyNat (gidneyAdderMeasured (n + 2) 0) (adder_input_F (n + 2) d x)) q := by
    intro q
    show Gate.applyNat (loadConst (n + 2) d)
          (EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
            (Gate.applyNat (loadConst (n + 2) d) (adder_input_F (n + 2) 0 x))) q = _
    rw [loadConst_clean_eq_input]
  obtain ⟨htgt, hcar⟩ := gidneyAdderMeasured_correct n d x 0 hd hx i hi
  have hread := gidneyAdderMeasured_read n d x 0 hd hx i hi
  refine ⟨?_, ?_, ?_⟩
  · -- target: loadConst preserves target; measured adder target = (d+x).testBit
    rw [hstep, loadConst_target, htgt, adder_sum_bit_classical, Nat.add_comm d x]
  · -- read: loadConst unloads read; after adder read = d, XOR d.testBit → false
    rw [hstep, loadConst_at_read_idx (n + 2) d _ i hi, hread, Bool.xor_self]
  · -- carry: loadConst preserves carry; measured adder carry = false
    rw [hstep, loadConst_carry, hcar]

/-- **`addConstMeasured` decoded value.** On the clean input, the low `n+2` target
register decodes to `(x + d) % 2^(n+2)`. -/
theorem addConstMeasured_target_val (n d x : Nat) (hd : d < 2 ^ (n + 2)) (hx : x < 2 ^ (n + 2)) :
    gidney_target_val (n + 2)
        (EGate.applyNat (addConstMeasured (n + 2) d) (adder_input_F (n + 2) 0 x))
      = (x + d) % 2 ^ (n + 2) := by
  apply gidney_target_val_eq_sum_when_bits_match (n + 2) (x + d)
  intro i hi
  exact (addConstMeasured_bundle n d x hd hx i hi).1

/-- `loadConst W d` references only read indices `read_idx j = 3j` for `j < W`,
hence is bounded by `3·W` (its highest target is `read_idx (W-1) = 3W-3 < 3W`). -/
theorem loadConst_boundedBy (W d : Nat) :
    Gate.boundedBy (3 * W) (loadConst W d) := by
  induction W with
  | zero => trivial
  | succ k ih =>
      show Gate.boundedBy (3 * (k + 1))
        (Gate.seq (loadConst k d) (if d.testBit k then Gate.X (read_idx k) else Gate.I))
      refine ⟨Gate.boundedBy_mono (by omega) _ ih, ?_⟩
      split
      · show read_idx k < 3 * (k + 1); unfold read_idx; omega
      · trivial

/-- **`addConstMeasured W d` is bounded by `adder_n_qubits W`.** -/
theorem addConstMeasured_boundedBy (n d : Nat) :
    EGate.boundedBy (adder_n_qubits (n + 2)) (addConstMeasured (n + 2) d) := by
  show EGate.boundedBy (adder_n_qubits (n + 2))
    (EGate.seq (EGate.seq (EGate.base (loadConst (n + 2) d)) (gidneyAdderMeasured (n + 2) 0))
      (EGate.base (loadConst (n + 2) d)))
  have hl : Gate.boundedBy (adder_n_qubits (n + 2)) (loadConst (n + 2) d) :=
    Gate.boundedBy_mono (by unfold adder_n_qubits; omega) _ (loadConst_boundedBy (n + 2) d)
  exact ⟨⟨hl, gidneyAdderMeasured_boundedBy n 0⟩, hl⟩

/-- **TIGHT boundedness of `addConstMeasured`:** bounded by `3·(n+2)`, so it is the
identity at every index `≥ 3·(n+2)` (the two free slots above the register). -/
theorem addConstMeasured_boundedBy_tight (n d : Nat) :
    EGate.boundedBy (3 * (n + 2)) (addConstMeasured (n + 2) d) :=
  ⟨⟨loadConst_boundedBy (n + 2) d, gidneyAdderMeasured_boundedBy_tight n 0⟩,
   loadConst_boundedBy (n + 2) d⟩

/-! ## §4. The masked conditional add: `prepareMaskedP` semantics.

`prepareMaskedP flagIdx W p` is a CX cascade from `flagIdx` into the read register;
its action mirrors `loadConst` but XORs in `(g flagIdx) ∧ p.testBit k` rather than
`p.testBit k`. With the control `flagIdx` out-of-band (`flagIdx ≥ adder_n_qubits W`)
it never targets a read index, so the cascade preserves it. -/

/-- `prepareMaskedP flagIdx W p` is the identity outside the read window, PROVIDED
the control `flagIdx` is itself outside the read window (so the CXs do not modify
it). -/
theorem prepareMaskedP_preserves_outside
    (flagIdx W p : Nat) (f : Nat → Bool) (q : Nat)
    (hflag : ∀ i, i < W → flagIdx ≠ read_idx i)
    (h : ∀ i, i < W → q ≠ read_idx i) :
    Gate.applyNat (prepareMaskedP flagIdx W p) f q = f q := by
  induction W with
  | zero => rfl
  | succ k ih =>
      have ih' : Gate.applyNat (prepareMaskedP flagIdx k p) f q = f q :=
        ih (fun i hi => hflag i (by omega)) (fun i hi => h i (by omega))
      show Gate.applyNat (if p.testBit k then Gate.CX flagIdx (read_idx k) else Gate.I)
            (Gate.applyNat (prepareMaskedP flagIdx k p) f) q = f q
      split
      · simp only [Gate.applyNat_CX]; rw [update_neq _ _ _ _ (h k (by omega)), ih']
      · simp only [Gate.applyNat]; exact ih'

/-- At `read_idx j` (for `j < W`), `prepareMaskedP flagIdx W p` XORs in
`(f flagIdx) ∧ p.testBit j`, provided `flagIdx` is outside the read window. -/
theorem prepareMaskedP_at_read_idx
    (flagIdx W p : Nat) (f : Nat → Bool) (j : Nat) (hj : j < W)
    (hflag : ∀ i, i < W → flagIdx ≠ read_idx i) :
    Gate.applyNat (prepareMaskedP flagIdx W p) f (read_idx j)
      = xor (f (read_idx j)) (f flagIdx && p.testBit j) := by
  induction W with
  | zero => omega
  | succ k ih =>
      show Gate.applyNat (if p.testBit k then Gate.CX flagIdx (read_idx k) else Gate.I)
            (Gate.applyNat (prepareMaskedP flagIdx k p) f) (read_idx j) = _
      by_cases hjk : j < k
      · have hframe := ih hjk (fun i hi => hflag i (by omega))
        have hne : read_idx j ≠ read_idx k := by unfold read_idx; omega
        split
        · simp only [Gate.applyNat_CX]; rw [update_neq _ _ _ _ hne, hframe]
        · simp only [Gate.applyNat]; exact hframe
      · have hjeq : j = k := by omega
        subst hjeq
        have hpres : ∀ q, (∀ i, i < j → q ≠ read_idx i) →
            Gate.applyNat (prepareMaskedP flagIdx j p) f q = f q := fun q hq =>
          prepareMaskedP_preserves_outside flagIdx j p f q (fun i hi => hflag i (by omega)) hq
        have hframe_read : Gate.applyNat (prepareMaskedP flagIdx j p) f (read_idx j) = f (read_idx j) :=
          hpres (read_idx j) (fun i hi => by unfold read_idx; omega)
        have hframe_flag : Gate.applyNat (prepareMaskedP flagIdx j p) f flagIdx = f flagIdx :=
          hpres flagIdx (fun i hi => hflag i (by omega))
        split
        next ht => simp only [Gate.applyNat_CX]; rw [update_eq, hframe_read, hframe_flag, ht,
                               Bool.and_true]
        next hf =>
          simp only [Gate.applyNat]
          rw [hframe_read, (by simpa using hf : p.testBit j = false), Bool.and_false, Bool.xor_false]

/-- A constant's bit-`j` masked by a boolean flag: `(flag ∧ p.testBit j) =
(if flag then p else 0).testBit j`. -/
private theorem mask_testBit (flag : Bool) (p j : Nat) :
    (flag && p.testBit j) = (if flag then p else 0).testBit j := by
  cases flag with
  | false => simp
  | true  => simp

/-- **The masked prepare turns a block-clean state into the gated-addend input.** If
`g` equals `adder_input_F W 0 v` on every adder-block index (read `0`, target = bits
of `v`, carries `0`) and the flag control sits out-of-band
(`adder_n_qubits W ≤ flagIdx`), then `prepareMaskedP flagIdx W p` produces, on every
block index `q < adder_n_qubits W`, exactly `adder_input_F W (if g flagIdx then p
else 0) v` — the read register loaded with the GATED constant, target and carries
unchanged. -/
theorem prepareMaskedP_eq_adder_input
    (W p v flagIdx : Nat) (g : Nat → Bool)
    (hflag : adder_n_qubits W ≤ flagIdx)
    (hblock : ∀ q, q < adder_n_qubits W → g q = adder_input_F W 0 v q)
    (q : Nat) (hq : q < adder_n_qubits W) :
    Gate.applyNat (prepareMaskedP flagIdx W p) g q
      = adder_input_F W (if g flagIdx then p else 0) v q := by
  have hflag_read : ∀ i, i < W → flagIdx ≠ read_idx i := by
    intro i hi
    have : read_idx i < adder_n_qubits W := by unfold read_idx adder_n_qubits; omega
    omega
  obtain ⟨j, hj⟩ : ∃ j, j = q / 3 := ⟨_, rfl⟩
  have h3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h3 with hmod | hmod | hmod
  · -- read index
    have hqread : q = read_idx j := by unfold read_idx; omega
    have hjle : j ≤ W := by unfold read_idx adder_n_qubits at *; omega
    subst hqread
    by_cases hjW : j < W
    · rw [prepareMaskedP_at_read_idx flagIdx W p g j hjW hflag_read]
      have hg_read : g (read_idx j) = false := by
        rw [hblock _ (by unfold read_idx adder_n_qubits; omega)]
        unfold adder_input_F read_idx; rw [show (3 * j) % 3 = 0 by omega]; simp
      rw [hg_read, Bool.false_xor, mask_testBit]
      unfold adder_input_F read_idx
      rw [show (3 * j) % 3 = 0 by omega, show (3 * j) / 3 = j by omega, decide_eq_true hjW,
          Bool.true_and]
    · -- j = W: the free read slot above the register; prepare preserves, both sides false
      rw [prepareMaskedP_preserves_outside flagIdx W p g (read_idx j) hflag_read
            (fun i hi => by unfold read_idx; omega),
          hblock _ (by unfold read_idx adder_n_qubits; omega)]
      unfold adder_input_F read_idx
      rw [show (3 * j) % 3 = 0 by omega, show (3 * j) / 3 = j by omega,
          show decide (j < W) = false by simp [hjW]]
      simp
  · -- target index: prepare preserves; both sides read v's bits
    have hqtarget : q = target_idx j := by unfold target_idx; omega
    subst hqtarget
    rw [prepareMaskedP_preserves_outside flagIdx W p g (target_idx j) hflag_read
          (fun i _ => by unfold target_idx read_idx; omega),
        hblock _ hq]
    unfold adder_input_F target_idx
    rw [show (3 * j + 1) % 3 = 1 by omega]
  · -- carry index: prepare preserves; both false
    have hqcarry : q = carry_idx j := by unfold carry_idx; omega
    subst hqcarry
    rw [prepareMaskedP_preserves_outside flagIdx W p g (carry_idx j) hflag_read
          (fun i _ => by unfold carry_idx read_idx; omega),
        hblock _ hq]
    unfold adder_input_F carry_idx
    rw [show (3 * j + 2) % 3 = 2 by omega]

/-! ## §5. A bounded circuit preserves out-of-band qubits. -/

/-- A `Gate` bounded by `B` preserves every index `≥ B`. -/
theorem Gate_boundedBy_preserves_ge (B : Nat) :
    ∀ (gate : Gate), Gate.boundedBy B gate →
      ∀ (f : Nat → Bool) (q : Nat), B ≤ q → Gate.applyNat gate f q = f q := by
  intro gate
  induction gate with
  | I => intro _ f q _; rfl
  | X p => intro hb f q hq; have : p < B := hb; simp only [Gate.applyNat_X]; exact update_neq _ _ _ _ (by omega)
  | CX c t => intro hb f q hq; have : t < B := hb.2; simp only [Gate.applyNat_CX]; exact update_neq _ _ _ _ (by omega)
  | CCX a b c => intro hb f q hq; have : c < B := hb.2.2; simp only [Gate.applyNat_CCX]; exact update_neq _ _ _ _ (by omega)
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hb f q hq
      show Gate.applyNat g₂ (Gate.applyNat g₁ f) q = f q
      rw [ih₂ hb.2 _ q hq, ih₁ hb.1 f q hq]

/-- An `EGate` bounded by `B` preserves every index `≥ B`. -/
theorem EGate_boundedBy_preserves_ge (B : Nat) :
    ∀ (eg : EGate), EGate.boundedBy B eg →
      ∀ (f : Nat → Bool) (q : Nat), B ≤ q → EGate.applyNat eg f q = f q := by
  intro eg
  induction eg with
  | base gate => intro hb f q hq; exact Gate_boundedBy_preserves_ge B gate hb f q hq
  | mz p =>
      intro hb f q hq
      have hpB : p < B := hb
      show Function.update f p false q = f q
      rw [funupd_eq_update]; exact update_neq _ _ _ _ (by omega)
  | seq a b iha ihb =>
      intro hb f q hq
      show EGate.applyNat b (EGate.applyNat a f) q = f q
      rw [ihb hb.2 _ q hq, iha hb.1 f q hq]

/-! ## §6. `conditionalAddP` value bundle: conditional `+p` on a block-clean state. -/

/-- **`conditionalAddP` per-index bundle.** Let `g` be block-clean — equal to
`adder_input_F (n+2) 0 v` on every adder-block index (read `0`, target = bits of
`v`, carries `0`) — with the flag control out-of-band (`adder_n_qubits (n+2) ≤
flagIdx`) and `v < 2^(n+2)`, `p < 2^(n+2)`. Then `conditionalAddP (n+2) flagIdx p`
gives, for every `i < n+2`:
  • `target[i] = (v + (if g flagIdx then p else 0)).testBit i`,
  • `read[i]   = false`,
  • `carry[i]  = false`,
and the flag bit is preserved (`out (flagIdx) = g flagIdx`). -/
theorem conditionalAddP_bundle
    (n p v flagIdx : Nat) (g : Nat → Bool)
    (hflag : adder_n_qubits (n + 2) ≤ flagIdx)
    (hblock : ∀ q, q < adder_n_qubits (n + 2) → g q = adder_input_F (n + 2) 0 v q)
    (hp : p < 2 ^ (n + 2)) (hv : v < 2 ^ (n + 2)) :
    (∀ i, i < n + 2 →
      (EGate.applyNat (conditionalAddP (n + 2) flagIdx p) g (target_idx i)
        = (v + (if g flagIdx then p else 0)).testBit i)
      ∧ (EGate.applyNat (conditionalAddP (n + 2) flagIdx p) g (read_idx i) = false)
      ∧ (EGate.applyNat (conditionalAddP (n + 2) flagIdx p) g (carry_idx i) = false))
    ∧ EGate.applyNat (conditionalAddP (n + 2) flagIdx p) g flagIdx = g flagIdx := by
  set d' := if g flagIdx then p else 0 with hd'
  have hd'lt : d' < 2 ^ (n + 2) := by rw [hd']; split <;> [exact hp; exact Nat.two_pow_pos _]
  -- the state after prepare, abbreviated; we never need it explicitly off-block except at flagIdx
  have hflag_read : ∀ i, i < n + 2 → flagIdx ≠ read_idx i := by
    intro i hi
    have : read_idx i < adder_n_qubits (n + 2) := by unfold read_idx adder_n_qubits; omega
    omega
  -- unfold to: prepare ; measured-adder ; prepare
  have hstep : ∀ q,
      EGate.applyNat (conditionalAddP (n + 2) flagIdx p) g q
        = Gate.applyNat (prepareMaskedP flagIdx (n + 2) p)
            (EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
              (Gate.applyNat (prepareMaskedP flagIdx (n + 2) p) g)) q := fun q => rfl
  -- middle = measured adder on the literal `adder_input_F (n+2) d' v`, on the block
  have hmid_block : ∀ q, q < adder_n_qubits (n + 2) →
      EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
        (Gate.applyNat (prepareMaskedP flagIdx (n + 2) p) g) q
      = EGate.applyNat (gidneyAdderMeasured (n + 2) 0) (adder_input_F (n + 2) d' v) q := by
    intro q hq
    exact EGate.applyNat_congr_lt (adder_n_qubits (n + 2)) (gidneyAdderMeasured (n + 2) 0)
      (gidneyAdderMeasured_boundedBy n 0) _ _
      (fun r hr => prepareMaskedP_eq_adder_input (n + 2) p v flagIdx g hflag hblock r hr) q hq
  -- the prepared state preserves flagIdx (out-of-band), so flag stays `g flagIdx`
  have hprep_flag : Gate.applyNat (prepareMaskedP flagIdx (n + 2) p) g flagIdx = g flagIdx :=
    prepareMaskedP_preserves_outside flagIdx (n + 2) p g flagIdx hflag_read hflag_read
  -- the measured adder preserves flagIdx (out-of-band, since it is bounded by the block)
  have hadder_flag : ∀ h : Nat → Bool,
      EGate.applyNat (gidneyAdderMeasured (n + 2) 0) h flagIdx = h flagIdx := fun h =>
    EGate_boundedBy_preserves_ge (adder_n_qubits (n + 2))
      (gidneyAdderMeasured (n + 2) 0) (gidneyAdderMeasured_boundedBy n 0) h flagIdx hflag
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨htgt, hcar⟩ := gidneyAdderMeasured_correct n d' v 0 hd'lt hv i hi
    have hread := gidneyAdderMeasured_read n d' v 0 hd'lt hv i hi
    -- the flag value seen by the un-prepare equals `g flagIdx`
    have hmidflag : EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
        (Gate.applyNat (prepareMaskedP flagIdx (n + 2) p) g) flagIdx = g flagIdx := by
      rw [hadder_flag, hprep_flag]
    refine ⟨?_, ?_, ?_⟩
    · -- target: un-prepare preserves target; middle target = (v+d').testBit
      rw [hstep, prepareMaskedP_preserves_outside flagIdx (n + 2) p _ (target_idx i) hflag_read
            (fun j _ => by unfold target_idx read_idx; omega),
          hmid_block _ (by unfold target_idx adder_n_qubits; omega), htgt,
          adder_sum_bit_classical, Nat.add_comm d' v]
    · -- read: un-prepare XORs `flag ∧ p.testBit i`; middle read = d'.testBit; cancels
      rw [hstep, prepareMaskedP_at_read_idx flagIdx (n + 2) p _ i hi hflag_read,
          hmid_block _ (by unfold read_idx adder_n_qubits; omega), hread, hmidflag, mask_testBit,
          ← hd', Bool.xor_self]
    · -- carry: un-prepare preserves carry; middle carry = false
      rw [hstep, prepareMaskedP_preserves_outside flagIdx (n + 2) p _ (carry_idx i) hflag_read
            (fun j _ => by unfold carry_idx read_idx; omega),
          hmid_block _ (by unfold carry_idx adder_n_qubits; omega), hcar]
  · -- flag preserved: un-prepare preserves flagIdx, adder preserves flagIdx, prepare preserves flagIdx
    rw [hstep, prepareMaskedP_preserves_outside flagIdx (n + 2) p _ flagIdx hflag_read hflag_read,
        hadder_flag, hprep_flag]

/-! ## §7. The two's-complement underflow arithmetic (the only NEW arithmetic).

The whole pipeline is captured by a pure-`Nat` lemma. Writing `W = bits + 1`,
`H = 2^bits` (so `2^W = 2·H`), `T2 = p − c`, and `v1 = (x + (2^W − T2)) % 2^W` for
the subtraction result:

  • the underflow flag `Q = decide(v1 ≥ H)` equals `decide(x + c < p)`;
  • the fixup `v2 = (v1 + (if Q then p else 0)) % 2^W` equals `(x + c) % p`;
  • `v2 < H` (the top bit `Q` is cleared after the fixup). -/

/-- **Subtraction result range + underflow flag.** For `x < p`, `c < p`,
`0 < p ≤ H` (`H = 2^bits`), the subtraction `v1 = (x + (2·H − (p−c))) % (2·H)`
satisfies: if `x + c ≥ p` then `v1 = x + c − p < H`; if `x + c < p` then
`v1 = x + c − p + 2·H` with `H ≤ v1 < 2·H`. -/
theorem subtract_underflow (H p c x : Nat)
    (hp : 0 < p) (hpH : p ≤ H) (hx : x < p) (hc : c < p) :
    (x + c < p → (x + (2 * H - (p - c))) % (2 * H) = x + c + 2 * H - p
                  ∧ H ≤ x + c + 2 * H - p)
    ∧ (p ≤ x + c → (x + (2 * H - (p - c))) % (2 * H) = x + c - p
                    ∧ x + c - p < H) := by
  constructor
  · intro hlt
    have h1 : x + (2 * H - (p - c)) = x + c + 2 * H - p := by omega
    have h2 : x + c + 2 * H - p < 2 * H := by omega
    have h3 : H ≤ x + c + 2 * H - p := by omega
    rw [h1, Nat.mod_eq_of_lt h2]; exact ⟨rfl, h3⟩
  · intro hge
    have h1 : x + (2 * H - (p - c)) = (x + c - p) + 2 * H := by omega
    have h2 : x + c - p < H := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; exact ⟨rfl, h2⟩

/-- **The full fixup value = `(x+c) % p`.** Combining the two branches of
`subtract_underflow` with the conditional add-back of `p`. -/
theorem fixup_value (H p c x : Nat)
    (hp : 0 < p) (hpH : p ≤ H) (hx : x < p) (hc : c < p) :
    ((x + (2 * H - (p - c))) % (2 * H)
      + (if (x + (2 * H - (p - c))) % (2 * H) ≥ H then p else 0)) % (2 * H)
      = (x + c) % p
    ∧ ((x + (2 * H - (p - c))) % (2 * H)
        + (if (x + (2 * H - (p - c))) % (2 * H) ≥ H then p else 0)) % (2 * H) < H := by
  obtain ⟨hlt_branch, hge_branch⟩ := subtract_underflow H p c x hp hpH hx hc
  by_cases hsum : x + c < p
  · obtain ⟨hv1, hv1ge⟩ := hlt_branch hsum
    rw [hv1, if_pos hv1ge]
    have hxcp : x + c < p := hsum
    have hmod : (x + c) % p = x + c := Nat.mod_eq_of_lt hsum
    -- v1 + p = x + c + 2*H, mod 2*H = x + c
    have he : x + c + 2 * H - p + p = (x + c) + 2 * H := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), hmod]
    exact ⟨rfl, by omega⟩
  · have hsum : p ≤ x + c := Nat.not_lt.mp hsum
    obtain ⟨hv1, hv1lt⟩ := hge_branch hsum
    rw [hv1, if_neg (by omega), Nat.mod_eq_of_lt (by omega)]
    -- v2 = x + c - p = (x + c) % p since p ≤ x + c < 2p
    have hxc2p : x + c < 2 * p := by omega
    have : (x + c) % p = x + c - p := by
      rw [Nat.mod_eq_sub_mod hsum, Nat.mod_eq_of_lt (by omega)]
    rw [this]; exact ⟨rfl, hv1lt⟩

/-- **Top bit = high-half threshold.** For `v < 2^(bits+1)`, the bit at position
`bits` of `v` equals `decide(2^bits ≤ v)`. -/
theorem testBit_top_eq_threshold (bits v : Nat) (hv : v < 2 ^ (bits + 1)) :
    v.testBit bits = decide (2 ^ bits ≤ v) := by
  by_cases hge : 2 ^ bits ≤ v
  · rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hge hv, decide_eq_true hge]
  · rw [Nat.testBit_lt_two_pow (by omega), decide_eq_false (by omega)]

/-! ## §8. THE headline value theorem. -/

/-- The `bits`-bit target register decoder restricted to the low `bits` of a
`(bits+1)`-bit value: if `v < 2^bits`, then `gidney_target_val bits` reads `v`
back, while `gidney_target_val (bits+1)` reads `v` too (the top bit being `0`). We
only need the former. The decoder reads `target_idx i` for `i < bits`, so it is
determined by those bits alone. -/
theorem gidney_target_val_low (bits S : Nat) (f : Nat → Bool)
    (h : ∀ i, i < bits → f (target_idx i) = S.testBit i) :
    gidney_target_val bits f = S % 2 ^ bits :=
  gidney_target_val_eq_sum_when_bits_match bits S f h

/-- **★ HEADLINE — the faithful Gidney-2025 subtract-fixup modular adder is correct.**
For `1 ≤ bits`, `0 < p ≤ 2^bits`, `x < p`, `c < p`, the gate `gidneyModAddFixup
bits p c` applied to the clean input `adder_input_F (bits+1) 0 x` (target = `x`, read
`0`, carries `0`, flag `0`):
  1. decodes the low `bits` target register to `(x + c) % p`;
  2. releases the extra top qubit `Q = target_idx bits` to `0`;
  3. releases the fixup flag ancilla (`adder_n_qubits (bits+1)`) to `0`. -/
theorem gidneyModAddFixup_correct
    (bits p c x : Nat) (hbits : 1 ≤ bits)
    (hp : 0 < p) (hpH : p ≤ 2 ^ bits) (hx : x < p) (hc : c < p) :
    gidney_target_val bits
        (EGate.applyNat (gidneyModAddFixup bits p c) (adder_input_F (bits + 1) 0 x))
      = (x + c) % p
    ∧ EGate.applyNat (gidneyModAddFixup bits p c) (adder_input_F (bits + 1) 0 x)
        (target_idx bits) = false
    ∧ EGate.applyNat (gidneyModAddFixup bits p c) (adder_input_F (bits + 1) 0 x)
        (adder_n_qubits (bits + 1)) = false := by
  obtain ⟨n, rfl⟩ : ∃ n, bits = n + 1 := ⟨bits - 1, by omega⟩
  set W := n + 2 with hW
  set H := 2 ^ (n + 1) with hH
  set d1 := 2 ^ W - (p - c) with hd1
  set flagIdx := adder_n_qubits W with hflagIdx
  -- bounds
  have hxlt : x < 2 ^ W := by rw [hW]; calc x < p := hx
                                        _ ≤ 2 ^ (n + 1) := hpH
                                        _ ≤ 2 ^ (n + 2) := by exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd1lt : d1 < 2 ^ W := by
    rw [hd1]; have : 0 < p - c := by omega
    have h2 : 0 < 2 ^ W := Nat.two_pow_pos _
    omega
  have hplt : p < 2 ^ W := by rw [hW]; calc p ≤ 2 ^ (n + 1) := hpH
                                       _ < 2 ^ (n + 2) := by exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpow : (2 : Nat) ^ W = 2 * H := by rw [hW, hH, pow_succ]; ring
  -- ===== stage 1 : subtract =====
  set s1 := EGate.applyNat (addConstMeasured W d1) (adder_input_F W 0 x) with hs1
  have hb1 := addConstMeasured_bundle n d1 x hd1lt hxlt
  -- value v1 of the target after stage 1
  set v1 := (x + d1) % 2 ^ W with hv1def
  have hv1lt : v1 < 2 ^ W := Nat.mod_lt _ (Nat.two_pow_pos _)
  -- stage-1 target bits decode to v1 ; read = carry = 0
  have hs1_tgt : ∀ i, i < W → s1 (target_idx i) = v1.testBit i := by
    intro i hi; rw [hs1, (hb1 i hi).1, hv1def, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  have hs1_read : ∀ i, i < W → s1 (read_idx i) = false := fun i hi => by rw [hs1]; exact (hb1 i hi).2.1
  have hs1_carry : ∀ i, i < W → s1 (carry_idx i) = false := fun i hi => by rw [hs1]; exact (hb1 i hi).2.2
  -- stage 1 preserves the out-of-band flag (= false on the clean input)
  have hflag_ge : adder_n_qubits W ≤ flagIdx := le_of_eq hflagIdx.symm
  have hs1_flag : s1 flagIdx = false := by
    rw [hs1, EGate_boundedBy_preserves_ge (adder_n_qubits W) (addConstMeasured W d1)
          (addConstMeasured_boundedBy n d1) (adder_input_F W 0 x) flagIdx hflag_ge]
    unfold adder_input_F flagIdx adder_n_qubits
    rw [show (3 * W + 2) % 3 = 2 by omega]
  -- ===== stage 2 : copy Q (top target bit) into the flag =====
  set s2 := Gate.applyNat (Gate.CX (target_idx (n + 1)) flagIdx) s1 with hs2
  -- s2 agrees with s1 everywhere except flagIdx; in particular it stays block-clean
  have htgt_ne_flag : target_idx (n + 1) ≠ flagIdx := by
    rw [hflagIdx]; unfold target_idx adder_n_qubits; omega
  have hs2_off : ∀ q, q ≠ flagIdx → s2 q = s1 q := by
    intro q hq; rw [hs2, Gate.applyNat_CX, update_neq _ _ _ _ hq]
  have hs2_flag : s2 flagIdx = decide (H ≤ v1) := by
    rw [hs2, Gate.applyNat_CX, update_eq, hs1_flag, Bool.false_xor,
        hs1_tgt (n + 1) (by omega)]
    exact testBit_top_eq_threshold (n + 1) v1 (by rw [← hW]; exact hv1lt)
  -- s2 is block-clean: equals `adder_input_F W 0 v1` on every block index
  have hs2_block : ∀ q, q < adder_n_qubits W → s2 q = adder_input_F W 0 v1 q := by
    intro q hq
    rw [hs2_off q (by rw [hflagIdx]; omega)]
    obtain ⟨j, hj⟩ : ∃ j, j = q / 3 := ⟨_, rfl⟩
    have h3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    have hjle : j ≤ W := by unfold adder_n_qubits at hq; omega
    rcases h3 with hmod | hmod | hmod
    · -- read index
      have hqr : q = read_idx j := by unfold read_idx; omega
      subst hqr
      by_cases hjW : j < W
      · rw [hs1_read j hjW]
        unfold adder_input_F read_idx
        rw [show (3 * j) % 3 = 0 by omega]; simp
      · -- free read slot j = W = n+2 (index 3·(n+2), above the adder's reach)
        have hjeq : j = W := by unfold read_idx adder_n_qubits at hq; omega
        have hpres : s1 (read_idx j) = adder_input_F W 0 x (read_idx j) := by
          rw [hs1, EGate_boundedBy_preserves_ge (3 * (n + 2)) (addConstMeasured (n + 2) d1)
                (addConstMeasured_boundedBy_tight n d1) (adder_input_F (n + 2) 0 x) (read_idx j)
                (by rw [hjeq, hW]; unfold read_idx; omega)]
        rw [hpres]
        unfold adder_input_F read_idx
        simp only [show (3 * j) % 3 = 0 by omega, show (3 * j) / 3 = j by omega,
            show decide (j < W) = false by simp [hjW], Bool.false_and]
    · -- target index
      have hqt : q = target_idx j := by unfold target_idx; omega
      subst hqt
      have hjle' : j ≤ W := by unfold target_idx adder_n_qubits at hq; omega
      by_cases hjW : j < W
      · rw [hs1_tgt j hjW]
        unfold adder_input_F target_idx
        simp only [show (3 * j + 1) % 3 = 1 by omega, show (3 * j + 1) / 3 = j by omega,
            show decide (j < W) = true by simp [hjW], Bool.true_and]
      · -- free target slot j = W (index 3·(n+2)+1, above the adder's reach)
        have hjeq : j = W := by omega
        have hpres : s1 (target_idx j) = adder_input_F W 0 x (target_idx j) := by
          rw [hs1, EGate_boundedBy_preserves_ge (3 * (n + 2)) (addConstMeasured (n + 2) d1)
                (addConstMeasured_boundedBy_tight n d1) (adder_input_F (n + 2) 0 x) (target_idx j)
                (by rw [hjeq, hW]; unfold target_idx; omega)]
        rw [hpres]
        unfold adder_input_F target_idx
        simp only [show (3 * j + 1) % 3 = 1 by omega, show (3 * j + 1) / 3 = j by omega,
            show decide (j < W) = false by simp [hjW], Bool.false_and]
    · -- carry index (carry_idx j < adder_n_qubits W forces j < W)
      have hqc : q = carry_idx j := by unfold carry_idx; omega
      subst hqc
      have hjW : j < W := by unfold carry_idx adder_n_qubits at hq; omega
      rw [hs1_carry j hjW]; unfold adder_input_F carry_idx; rw [show (3 * j + 2) % 3 = 2 by omega]
  -- ===== stage 3 : conditional +p, controlled by the flag =====
  obtain ⟨hb3, hb3flag⟩ := conditionalAddP_bundle n p v1 flagIdx s2 hflag_ge hs2_block hplt hv1lt
  -- abbreviate the fixup constant; `s2 flagIdx = decide (H ≤ v1)`
  set s3 := EGate.applyNat (conditionalAddP W flagIdx p) s2 with hs3
  -- the conditional-add constant in Nat form
  have hcond : (if s2 flagIdx then p else 0) = (if H ≤ v1 then p else 0) := by
    rw [hs2_flag]; by_cases h : H ≤ v1 <;> simp [h]
  -- final value of the target after stage 3
  set v2 := (v1 + (if H ≤ v1 then p else 0)) % 2 ^ W with hv2def
  -- v1 in the fixup lemma's form ; and `≥ H` ↔ `H ≤`
  have hv1eq : v1 = (x + (2 * H - (p - c))) % (2 * H) := by
    rw [hv1def, hd1, ← hpow, hW]
  obtain ⟨hfix_val, hfix_lt⟩ := fixup_value H p c x hp hpH hx hc
  -- rewrite v2 into the fixup lemma's exact expression
  have hv2_alt : v2 = ((x + (2 * H - (p - c))) % (2 * H)
      + (if (x + (2 * H - (p - c))) % (2 * H) ≥ H then p else 0)) % (2 * H) := by
    rw [hv2def, hpow, hv1eq]
  have hv2_eq : v2 = (x + c) % p := by rw [hv2_alt]; exact hfix_val
  have hv2_lt : v2 < H := by rw [hv2_alt]; exact hfix_lt
  -- ===== stage 4 : measure-clear the flag =====
  -- the whole gate = mz flagIdx applied to s3
  have hgate : EGate.applyNat (gidneyModAddFixup (n + 1) p c) (adder_input_F W 0 x)
        = Function.update s3 flagIdx false := by
    show Function.update
          (EGate.applyNat (conditionalAddP W flagIdx p)
            (Gate.applyNat (Gate.CX (target_idx (n + 1)) flagIdx)
              (EGate.applyNat (addConstMeasured W (2 ^ W - (p - c))) (adder_input_F W 0 x))))
          flagIdx false = _
    rw [hs3, hs2, hs1]
  -- the flag index is never a target index, so `mz flagIdx` does not affect the
  -- decoded target register
  have hflag_ne_tgt : ∀ i, i < n + 1 → flagIdx ≠ target_idx i := by
    intro i hi; rw [hflagIdx]; unfold target_idx adder_n_qubits; omega
  refine ⟨?_, ?_, ?_⟩
  · -- (1) low `bits` register decodes to (x+c) % p
    rw [hgate]
    have hdecode : gidney_target_val (n + 1) (Function.update s3 flagIdx false)
        = (x + c) % p % 2 ^ (n + 1) := by
      apply gidney_target_val_low (n + 1) ((x + c) % p)
      intro i hi
      rw [Function.update_of_ne (hflag_ne_tgt i hi).symm]
      have := (hb3 i (by omega)).1
      rw [this, hcond]
      have hbit : ((x + c) % p).testBit i = v2.testBit i := by rw [hv2_eq]
      rw [hbit, hv2def, Nat.testBit_mod_two_pow, decide_eq_true (show i < W by omega), Bool.true_and]
    rw [hdecode, Nat.mod_eq_of_lt (by calc (x + c) % p < p := Nat.mod_lt _ hp
                                      _ ≤ 2 ^ (n + 1) := hpH)]
  · -- (2) Q = target_idx (n+1) released to 0
    rw [hgate, Function.update_of_ne (by exact htgt_ne_flag)]
    -- target bit (n+1) of stage 3 = v2.testBit (n+1) ; v2 < H = 2^(n+1) ⇒ false
    have h := (hb3 (n + 1) (by omega)).1
    rw [h, hcond]
    -- bit (n+1) of the (unreduced) sum equals bit (n+1) of v2 (reduction mod 2^W is invisible at n+1 < W)
    have hbit : (v1 + (if H ≤ v1 then p else 0)).testBit (n + 1) = v2.testBit (n + 1) := by
      rw [hv2def, Nat.testBit_mod_two_pow, decide_eq_true (show n + 1 < W by omega), Bool.true_and]
    rw [hbit]
    exact Nat.testBit_lt_two_pow (by rw [hH] at hv2_lt; exact hv2_lt)
  · -- (3) flag released to 0 by the measurement
    rw [hgate, Function.update_self]

end FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup
