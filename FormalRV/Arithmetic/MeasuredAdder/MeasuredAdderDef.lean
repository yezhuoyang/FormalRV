/-
  FormalRV.Arithmetic.MeasuredAdder.MeasuredAdderDef
  ──────────────────────────────────────────────────
  SHARED BASE for the **measured** Gidney ripple-carry adder family (uncontrolled
  + controlled).  Holds ALL the `def`s and the internal frame/congruence lemmas
  that the Correctness (value) and Resource (count) files depend on.  The split is
  purely structural — every declaration here is byte-for-byte the one that used to
  live in `GidneyMeasured.lean` / `GidneyMeasuredControlled.lean`, just relocated.

  ## The construction (composition, not from scratch)

  Our reversible faithful Gidney adder
  `gidney_adder_full_faithful_no_measurement = forward ; final_cx ; reverse`
  costs `2·(n+2)` Toffolis:
    • the FORWARD sweep `gidney_adder_forward_faithful_full` computes the carry
      chain into the carry ancillas (`carry_idx i = 3i+2`) — `n+2` Toffolis (CCX);
    • `gidney_final_cx_cascade` stamps `read ⊕ target` (T-free CNOTs);
    • the REVERSE sweep `gidney_adder_forward_faithful_full_reverse` simultaneously
      (a) undoes the forward propagation CXs so that `target` is RESTORED to the
      true sum bits, and (b) **uncomputes** the carry ancillas with a SECOND `n+2`
      Toffolis (the per-step `CCX(read i, target i, carry i)` AND-uncomputes).

  NOTE on a tempting-but-WRONG shortcut: `forward ; final_cx ; mz(carries)` does
  NOT compute `a + b` — after `forward ; final_cx` the target still holds the
  carry-sweep value, not the sum (machine-checked: at `n=2, a=b=1` it gives
  `target₁ = false` where the sum needs `true`).  The reverse sweep's CXs are
  genuinely load-bearing for the sum, so they are KEPT.

  ## Gidney's measurement trick, faithfully

  Gidney's temporary-AND replaces ONLY the reverse sweep's AND-**uncompute** (each
  `CCX(read i, target i, carry i)`) by an X-basis MEASUREMENT of `carry i` plus a
  classically-controlled phase fixup (PROVEN to be the perfect uncompute on the
  computed family at the density layer in
  `FormalRV.Shor.MeasuredANDUncompute.measANDUncompute_perfect`).  In the Boolean
  `EGate` model (`FormalRV.Shor.MeasUncompute.EGate`) the net effect of that
  channel is `EGate.mz (carry i)` — reset `carry i` to `|0⟩` — which is
  **Toffoli-free**.  The reverse sweep's CX gates are kept verbatim.

  Concretely we build `gidneyMeasuredReverse` = the reverse cascade with each
  per-step uncompute `CCX(read i, target i, carry i)` swapped for `mz (carry i)`,
  KEEPING every CX.  Its Toffoli count is `0`, so the measured adder
  `forward ; final_cx ; gidneyMeasuredReverse` costs exactly the forward sweep's
  `n+2` — HALF the reversible adder (`gidneyAdderMeasured_halves`).

  The `q_start` parameter is carried for API parity with the windowed-adder
  convention; THIS adder is hardwired to the interleaved layout
  `read/target/carry = 3i/3i+1/3i+2` (base 0), so `q_start` does not shift indices.

  Refs: Gidney arXiv:1709.06648 §"temporary AND"; Cain–Xu 2026 (n Toffoli/add).
-/
import FormalRV.Shor.MeasUncompute
import FormalRV.Arithmetic.RippleCarryAdder.PropagationReverse.ApplyNatBridge
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderCorrectness

namespace FormalRV.Arithmetic.MeasuredAdder

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute

/-! ## §0. A small bridge: `EGate.mz` reset matches the project `update`. -/

/-- `EGate.mz` resets via `Function.update`; relate it to the project's `update`. -/
theorem funupd_eq_update (f : Nat → Bool) (c : Nat) (v : Bool) :
    Function.update f c v = update f c v := by
  funext i; by_cases h : i = c <;> simp [Function.update, update, h]

/-! ## §1. The measured reverse steps (CCX-uncompute → measurement). -/

/-- Measured first-bit reverse: the first-bit reverse with its uncompute
`CCX(read 0, target 0, carry 0)` replaced by `mz (carry 0)` (CXs kept). -/
def gidneyMeasFirstReverse : EGate :=
  EGate.seq (EGate.seq
    (EGate.base (Gate.CX (carry_idx 0) (target_idx 1)))
    (EGate.base (Gate.CX (carry_idx 0) (read_idx 1))))
    (EGate.mz (carry_idx 0))

/-- Measured interior-bit reverse `i`: the interior reverse with its uncompute
`CCX(read i, target i, carry i)` replaced by `mz (carry i)` (CXs kept). -/
def gidneyMeasInteriorReverse (i : Nat) : EGate :=
  EGate.seq (EGate.seq (EGate.seq
    (EGate.base (Gate.CX (carry_idx i) (target_idx (i + 1))))
    (EGate.base (Gate.CX (carry_idx i) (read_idx (i + 1)))))
    (EGate.base (Gate.CX (carry_idx (i - 1)) (carry_idx i))))
    (EGate.mz (carry_idx i))

/-- Measured last-bit reverse `i`: the last reverse with its uncompute
`CCX(read i, target i, carry i)` replaced by `mz (carry i)` (chain CX kept). -/
def gidneyMeasLastReverse (i : Nat) : EGate :=
  EGate.seq (EGate.base (Gate.CX (carry_idx (i - 1)) (carry_idx i)))
            (EGate.mz (carry_idx i))

/-- **Measured first-step = unitary first-step then clear `carry 0`.** -/
theorem gidneyMeasFirstReverse_eq (f : Nat → Bool) :
    EGate.applyNat gidneyMeasFirstReverse f
      = update (gidney_first_bit_reverse_post_state f) (carry_idx 0) false := by
  simp only [gidneyMeasFirstReverse, EGate.applyNat, Gate.applyNat_CX]
  rw [funupd_eq_update]; funext p
  by_cases hp : p = carry_idx 0
  · subst hp; simp only [update_eq]
  · rw [update_neq _ _ _ _ hp]
    unfold gidney_first_bit_reverse_post_state; simp only [update_neq _ _ _ _ hp]

/-- **Measured interior-step `i` = unitary interior-step then clear `carry i`.** -/
theorem gidneyMeasInteriorReverse_eq (i : Nat) (f : Nat → Bool) :
    EGate.applyNat (gidneyMeasInteriorReverse i) f
      = update (gidney_interior_bit_reverse_post_state i f) (carry_idx i) false := by
  simp only [gidneyMeasInteriorReverse, EGate.applyNat, Gate.applyNat_CX]
  rw [funupd_eq_update]; funext p
  by_cases hp : p = carry_idx i
  · subst hp; simp only [update_eq]
  · rw [update_neq _ _ _ _ hp]
    unfold gidney_interior_bit_reverse_post_state; simp only [update_neq _ _ _ _ hp]

/-- **Measured last-step `i` = unitary last-step then clear `carry i`.** -/
theorem gidneyMeasLastReverse_eq (i : Nat) (f : Nat → Bool) :
    EGate.applyNat (gidneyMeasLastReverse i) f
      = update (gidney_last_bit_reverse_post_state i f) (carry_idx i) false := by
  simp only [gidneyMeasLastReverse, EGate.applyNat, Gate.applyNat_CX]
  rw [funupd_eq_update]; funext p
  by_cases hp : p = carry_idx i
  · subst hp; simp only [update_eq]
  · rw [update_neq _ _ _ _ hp]
    unfold gidney_last_bit_reverse_post_state; simp only [update_neq _ _ _ _ hp]

/-! ## §2. The measured reverse cascade. -/

/-- The measured propagation-reverse cascade (mirrors
`gidney_adder_forward_with_propagation_reverse`). -/
def gidneyMeasPropReverse : Nat → EGate
  | 0     => EGate.base Gate.I
  | 1     => gidneyMeasFirstReverse
  | n + 2 => EGate.seq (gidneyMeasInteriorReverse (n + 1)) (gidneyMeasPropReverse (n + 1))

/-- The measured full reverse cascade (mirrors
`gidney_adder_forward_faithful_full_reverse`). -/
def gidneyMeasFullReverse : Nat → EGate
  | 0     => EGate.base Gate.I
  | 1     => EGate.base Gate.I
  | n + 2 => EGate.seq (gidneyMeasLastReverse (n + 1)) (gidneyMeasPropReverse (n + 1))

/-- The measured propagation reverse is Toffoli-free (only CX + measurement). -/
theorem tcount_gidneyMeasPropReverse : ∀ n, EGate.tcount (gidneyMeasPropReverse n) = 0
  | 0     => rfl
  | 1     => by simp [gidneyMeasPropReverse, gidneyMeasFirstReverse, EGate.tcount, Gate.tcount]
  | n + 2 => by
      simp [gidneyMeasPropReverse, EGate.tcount, gidneyMeasInteriorReverse, Gate.tcount,
            tcount_gidneyMeasPropReverse (n + 1)]

/-- The measured full reverse is Toffoli-free (only CX + measurement). -/
theorem tcount_gidneyMeasFullReverse : ∀ n, EGate.tcount (gidneyMeasFullReverse n) = 0
  | 0     => rfl
  | 1     => rfl
  | n + 2 => by
      simp [gidneyMeasFullReverse, EGate.tcount, gidneyMeasLastReverse, Gate.tcount,
            tcount_gidneyMeasPropReverse (n + 1)]

/-! ## §3. Frame lemmas: the unitary cascade is insensitive to clearing a high carry. -/

/-- **First-reverse insensitivity.**  For `m ≥ 1` and `q ≠ carry m`, clearing
`carry m` before the first-reverse leaves every other output unchanged
(the first-reverse only reads `carry 0`, never `carry m`). -/
theorem first_reverse_clear_carry_insensitive
    (m : Nat) (hm : 0 < m) (v : Bool) (f : Nat → Bool) (q : Nat) (hq : q ≠ carry_idx m) :
    gidney_first_bit_reverse_post_state (update f (carry_idx m) v) q
      = gidney_first_bit_reverse_post_state f q := by
  set g := update f (carry_idx m) v with hg
  have agree : ∀ p, p < 5 → g p = f p := by
    intro p hp; rw [hg, update_neq]; unfold carry_idx; omega
  by_cases hlow : q < 5
  · rw [gidney_first_bit_reverse_low_dependence g f q hlow agree]
  · have h1 : q ≠ target_idx 1 := by unfold target_idx; omega
    have h2 : q ≠ read_idx 1 := by unfold read_idx; omega
    have h3 : q ≠ carry_idx 0 := by unfold carry_idx; omega
    have hpres : ∀ r : Nat → Bool, gidney_first_bit_reverse_post_state r q = r q := by
      intro r; unfold gidney_first_bit_reverse_post_state
      rw [update_neq _ _ _ _ h3, update_neq _ _ _ _ h2, update_neq _ _ _ _ h1]
    rw [hpres g, hpres f, hg, update_neq _ _ _ _ hq]

/-- **Interior-reverse insensitivity.**  For `i ≥ 1`, `m > i` and `q ≠ carry m`,
clearing `carry m` before the interior-reverse `i` leaves every other output
unchanged (the step reads only `carry i`, `carry (i-1)`, both `< m`). -/
theorem interior_reverse_clear_carry_insensitive
    (i m : Nat) (hi : 0 < i) (him : i < m) (v : Bool) (f : Nat → Bool) (q : Nat)
    (hq : q ≠ carry_idx m) :
    gidney_interior_bit_reverse_post_state i (update f (carry_idx m) v) q
      = gidney_interior_bit_reverse_post_state i f q := by
  set g := update f (carry_idx m) v with hg
  have a_ci : g (carry_idx i) = f (carry_idx i) := by rw [hg, update_neq]; unfold carry_idx; omega
  have a_cim1 : g (carry_idx (i - 1)) = f (carry_idx (i - 1)) := by
    rw [hg, update_neq]; unfold carry_idx; omega
  have a_ri : g (read_idx i) = f (read_idx i) := by rw [hg, update_neq]; unfold read_idx carry_idx; omega
  have a_ti : g (target_idx i) = f (target_idx i) := by rw [hg, update_neq]; unfold target_idx carry_idx; omega
  have a_ri1 : g (read_idx (i + 1)) = f (read_idx (i + 1)) := by
    rw [hg, update_neq]; unfold read_idx carry_idx; omega
  have a_ti1 : g (target_idx (i + 1)) = f (target_idx (i + 1)) := by
    rw [hg, update_neq]; unfold target_idx carry_idx; omega
  by_cases hci : q = carry_idx i
  · subst hci
    rw [(gidney_interior_bit_reverse_post_state_in_bits i hi g).1,
        (gidney_interior_bit_reverse_post_state_in_bits i hi f).1, a_ci, a_cim1, a_ri, a_ti]
  by_cases hri1 : q = read_idx (i + 1)
  · subst hri1
    rw [(gidney_interior_bit_reverse_post_state_in_bits i hi g).2.1,
        (gidney_interior_bit_reverse_post_state_in_bits i hi f).2.1, a_ri1, a_ci]
  by_cases hti1 : q = target_idx (i + 1)
  · subst hti1
    rw [(gidney_interior_bit_reverse_post_state_in_bits i hi g).2.2,
        (gidney_interior_bit_reverse_post_state_in_bits i hi f).2.2, a_ti1, a_ci]
  rw [gidney_interior_bit_reverse_post_state_preserves_outside i g q hci hri1 hti1,
      gidney_interior_bit_reverse_post_state_preserves_outside i f q hci hri1 hti1,
      hg, update_neq _ _ _ _ hq]

/-- **Propagation-reverse cascade insensitivity.**  For `K ≤ m` and `q ≠ carry m`,
clearing `carry m` before the propagation-reverse cascade of length `K` is
invisible at `q`.  `propagation_reverse K` reads only carries `0 .. K-1`, all `< m`. -/
theorem propagation_reverse_clear_carry_insensitive (m : Nat) :
    ∀ (K : Nat) (v : Bool) (f : Nat → Bool) (q : Nat), K ≤ m → q ≠ carry_idx m →
      gidney_propagation_reverse_post_state K (update f (carry_idx m) v) q
        = gidney_propagation_reverse_post_state K f q := by
  intro K
  induction K with
  | zero => intro v f q _ hq; show update f (carry_idx m) v q = f q; rw [update_neq _ _ _ _ hq]
  | succ k ih =>
      match k with
      | 0 => intro v f q _ hq; exact first_reverse_clear_carry_insensitive m (by omega) v f q hq
      | p + 1 =>
          intro v f q hKm hq
          show gidney_propagation_reverse_post_state (p + 1)
                 (gidney_interior_bit_reverse_post_state (p + 1) (update f (carry_idx m) v)) q
              = gidney_propagation_reverse_post_state (p + 1)
                 (gidney_interior_bit_reverse_post_state (p + 1) f) q
          have hcomm : gidney_interior_bit_reverse_post_state (p + 1) (update f (carry_idx m) v)
              = update (gidney_interior_bit_reverse_post_state (p + 1) f) (carry_idx m)
                  (gidney_interior_bit_reverse_post_state (p + 1) (update f (carry_idx m) v) (carry_idx m)) := by
            funext q'
            by_cases hq' : q' = carry_idx m
            · subst hq'; rw [update_eq]
            · rw [update_neq _ _ _ _ hq']
              exact interior_reverse_clear_carry_insensitive (p + 1) m (by omega) (by omega) v f q' hq'
          rw [hcomm, ih _ _ q (by omega) hq]

/-! ## §4. Measured reverse cascade = unitary reverse on read/target, with cleared carries. -/

/-- **Measured propagation reverse = unitary on `read`/`target`.**  At any position
`q` that is not a carry index, the measured propagation-reverse cascade produces
exactly the unitary one's value. -/
theorem gidneyMeasPropReverse_rt :
    ∀ (K : Nat) (f : Nat → Bool) (q : Nat), (∀ m, q ≠ carry_idx m) →
      EGate.applyNat (gidneyMeasPropReverse K) f q
        = gidney_propagation_reverse_post_state K f q := by
  intro K
  induction K with
  | zero => intro f q _; rfl
  | succ k ih =>
      match k with
      | 0 =>
          intro f q hq
          show EGate.applyNat gidneyMeasFirstReverse f q = gidney_first_bit_reverse_post_state f q
          rw [gidneyMeasFirstReverse_eq, update_neq _ _ _ _ (hq 0)]
      | p + 1 =>
          intro f q hq
          show EGate.applyNat (gidneyMeasPropReverse (p + 1))
                 (EGate.applyNat (gidneyMeasInteriorReverse (p + 1)) f) q
              = gidney_propagation_reverse_post_state (p + 1)
                 (gidney_interior_bit_reverse_post_state (p + 1) f) q
          rw [gidneyMeasInteriorReverse_eq, ih _ q hq]
          exact propagation_reverse_clear_carry_insensitive (p + 1) (p + 1) false
            (gidney_interior_bit_reverse_post_state (p + 1) f) q (le_refl _) (hq (p + 1))

/-- **Measured full reverse = unitary on `read`/`target`.** -/
theorem gidneyMeasFullReverse_rt
    (n : Nat) (f : Nat → Bool) (q : Nat) (hq : ∀ m, q ≠ carry_idx m) :
    EGate.applyNat (gidneyMeasFullReverse (n + 2)) f q
      = gidney_full_reverse_post_state (n + 2) f q := by
  show EGate.applyNat (gidneyMeasPropReverse (n + 1))
        (EGate.applyNat (gidneyMeasLastReverse (n + 1)) f) q
      = gidney_propagation_reverse_post_state (n + 1)
        (gidney_last_bit_reverse_post_state (n + 1) f) q
  rw [gidneyMeasLastReverse_eq, gidneyMeasPropReverse_rt _ _ q hq]
  exact propagation_reverse_clear_carry_insensitive (n + 1) (n + 1) false
    (gidney_last_bit_reverse_post_state (n + 1) f) q (le_refl _) (hq (n + 1))

/-! ## §5. Carry clearance: the measured reverse releases every carry ancilla. -/

/-- The measured propagation reverse clears carries `0 .. K-1`; carries `≥ K` are
preserved.  (Each step `gidneyMeas*Reverse i` ends in `mz (carry i)`, and lower
steps never touch a higher carry.) -/
theorem gidneyMeasPropReverse_carry :
    ∀ (K : Nat) (f : Nat → Bool) (i : Nat),
      (i < K → EGate.applyNat (gidneyMeasPropReverse K) f (carry_idx i) = false)
      ∧ (K ≤ i → EGate.applyNat (gidneyMeasPropReverse K) f (carry_idx i) = f (carry_idx i)) := by
  intro K
  induction K with
  | zero => intro f i; exact ⟨fun h => by omega, fun _ => rfl⟩
  | succ k ih =>
      match k with
      | 0 =>
          intro f i
          refine ⟨?_, ?_⟩
          · intro hi
            have hi0 : i = 0 := by omega
            subst hi0
            show EGate.applyNat gidneyMeasFirstReverse f (carry_idx 0) = false
            rw [gidneyMeasFirstReverse_eq, update_eq]
          · intro hi
            show EGate.applyNat gidneyMeasFirstReverse f (carry_idx i) = f (carry_idx i)
            rw [gidneyMeasFirstReverse_eq, update_neq _ _ _ _ (by unfold carry_idx; omega)]
            -- first_reverse at carry_i for i ≥ 1: only carry_0 is touched
            unfold gidney_first_bit_reverse_post_state
            rw [update_neq _ _ _ _ (by unfold carry_idx; omega),
                update_neq _ _ _ _ (by unfold carry_idx read_idx; omega),
                update_neq _ _ _ _ (by unfold carry_idx target_idx; omega)]
      | p + 1 =>
          intro f i
          show (i < p + 2 → EGate.applyNat (gidneyMeasPropReverse (p + 1))
                  (EGate.applyNat (gidneyMeasInteriorReverse (p + 1)) f) (carry_idx i) = false)
            ∧ (p + 2 ≤ i → EGate.applyNat (gidneyMeasPropReverse (p + 1))
                  (EGate.applyNat (gidneyMeasInteriorReverse (p + 1)) f) (carry_idx i) = f (carry_idx i))
          rw [gidneyMeasInteriorReverse_eq]
          refine ⟨?_, ?_⟩
          · intro hi
            by_cases hip1 : i < p + 1
            · exact (ih _ i).1 hip1
            · -- i = p+1: cleared by the interior step itself, preserved by the rest
              have hieq : i = p + 1 := by omega
              subst hieq
              rw [(ih _ (p + 1)).2 (le_refl _), update_eq]
          · intro hi
            rw [(ih _ i).2 (by omega), update_neq _ _ _ _ (by unfold carry_idx; omega)]
            exact gidney_interior_bit_reverse_post_state_preserves_outside (p + 1) f (carry_idx i)
              (by unfold carry_idx; omega)
              (by unfold carry_idx read_idx; omega)
              (by unfold carry_idx target_idx; omega)

/-- The measured full reverse clears every carry `i < n+2`. -/
theorem gidneyMeasFullReverse_carry_clear
    (n : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n + 2) :
    EGate.applyNat (gidneyMeasFullReverse (n + 2)) f (carry_idx i) = false := by
  show EGate.applyNat (gidneyMeasPropReverse (n + 1))
        (EGate.applyNat (gidneyMeasLastReverse (n + 1)) f) (carry_idx i) = false
  by_cases hin1 : i < n + 1
  · exact (gidneyMeasPropReverse_carry (n + 1) _ i).1 hin1
  · -- i = n+1: cleared by the last-reverse, preserved by the propagation reverse
    have hieq : i = n + 1 := by omega
    subst hieq
    rw [(gidneyMeasPropReverse_carry (n + 1) _ (n + 1)).2 (le_refl _),
        gidneyMeasLastReverse_eq, update_eq]

/-! ## §6. THE measured adder. -/

/-- **The measured Gidney ripple-carry adder** (`n`-bit, `n` Toffoli): the faithful
forward carry sweep, the sum-stamping final-CX cascade, then the MEASURED reverse
cascade (`gidneyMeasFullReverse`) — the reversible reverse with each carry
AND-uncompute `CCX` swapped for a measurement `mz`.  The forward sweep computes
the carries (`n` Toffolis); the final-CX and the measured reverse are Toffoli-free,
so the total is the forward's `n` — HALF the reversible
`gidney_adder_full_faithful_no_measurement`.  Computes `(a+b) % 2^n` on the
target with the carry register released. -/
def gidneyAdderMeasured (n _q_start : Nat) : EGate :=
  EGate.seq
    (EGate.base (Gate.seq (gidney_adder_forward_faithful_full n)
                          (gidney_final_cx_cascade n)))
    (gidneyMeasFullReverse n)

/-- The measured adder splits as: apply `forward ; final_cx` (as a base `Gate`),
then the measured reverse cascade. -/
theorem gidneyAdderMeasured_applyNat (n q_start : Nat) (f : Nat → Bool) :
    EGate.applyNat (gidneyAdderMeasured (n + 2) q_start) f
      = EGate.applyNat (gidneyMeasFullReverse (n + 2))
          (gidney_final_cx_cascade_post_state (n + 2)
            (gidney_forward_faithful_full_post_state (n + 2) f)) := by
  show EGate.applyNat (gidneyMeasFullReverse (n + 2))
        (Gate.applyNat (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
            (gidney_final_cx_cascade (n + 2))) f) = _
  rw [Gate.applyNat_seq, gidney_adder_forward_faithful_full_applyNat,
      gidney_final_cx_cascade_applyNat]

/-! ## §7. Generic index-congruence for `Gate` / `EGate`.

A circuit whose gates only reference indices `< B` produces, at any index `< B`,
an output that depends only on the input restricted to indices `< B`.  We capture
"all referenced indices `< B`" by `Gate.boundedBy` / `EGate.boundedBy` and prove
the two congruence lemmas.  These are the ONLY new pieces of infrastructure; they
let us discharge the high-index junk (control + source register) and reuse the
uncontrolled adder's correctness verbatim. -/

/-- All qubit indices referenced by a `Gate` are `< B`. -/
def Gate.boundedBy (B : Nat) : Gate → Prop
  | Gate.I         => True
  | Gate.X q       => q < B
  | Gate.CX c t    => c < B ∧ t < B
  | Gate.CCX a b c => a < B ∧ b < B ∧ c < B
  | Gate.seq g₁ g₂ => Gate.boundedBy B g₁ ∧ Gate.boundedBy B g₂

/-- **`Gate.applyNat` congruence below `B`.**  If `f` and `g` agree on all indices
`< B` and the gate only touches indices `< B`, the outputs agree on all `< B`. -/
theorem Gate.applyNat_congr_lt (B : Nat) :
    ∀ (gate : Gate), Gate.boundedBy B gate →
      ∀ (f g : Nat → Bool), (∀ q, q < B → f q = g q) →
        ∀ q, q < B → Gate.applyNat gate f q = Gate.applyNat gate g q := by
  intro gate
  induction gate with
  | I => intro _ f g hfg q hq; exact hfg q hq
  | X p =>
      intro hb f g hfg q hq
      have hpB : p < B := hb
      simp only [Gate.applyNat_X]
      by_cases hqp : q = p
      · rw [hqp, update_eq, update_eq, hfg p hpB]
      · rw [update_neq _ _ _ _ hqp, update_neq _ _ _ _ hqp]; exact hfg q hq
  | CX c t =>
      intro hb f g hfg q hq
      obtain ⟨hc, ht⟩ := hb
      simp only [Gate.applyNat_CX]
      by_cases hqt : q = t
      · rw [hqt, update_eq, update_eq, hfg t ht, hfg c hc]
      · rw [update_neq _ _ _ _ hqt, update_neq _ _ _ _ hqt]; exact hfg q hq
  | CCX a b c =>
      intro hb f g hfg q hq
      obtain ⟨ha, hb', hc⟩ := hb
      simp only [Gate.applyNat_CCX]
      by_cases hqc : q = c
      · rw [hqc, update_eq, update_eq, hfg c hc, hfg a ha, hfg b hb']
      · rw [update_neq _ _ _ _ hqc, update_neq _ _ _ _ hqc]; exact hfg q hq
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hb f g hfg q hq
      obtain ⟨hb₁, hb₂⟩ := hb
      show Gate.applyNat g₂ (Gate.applyNat g₁ f) q = Gate.applyNat g₂ (Gate.applyNat g₁ g) q
      exact ih₂ hb₂ _ _ (fun q' hq' => ih₁ hb₁ f g hfg q' hq') q hq

/-- All qubit indices referenced by an `EGate` are `< B`. -/
def EGate.boundedBy (B : Nat) : EGate → Prop
  | EGate.base g  => Gate.boundedBy B g
  | EGate.mz q    => q < B
  | EGate.seq a b => EGate.boundedBy B a ∧ EGate.boundedBy B b

/-- **`EGate.applyNat` congruence below `B`.** -/
theorem EGate.applyNat_congr_lt (B : Nat) :
    ∀ (eg : EGate), EGate.boundedBy B eg →
      ∀ (f g : Nat → Bool), (∀ q, q < B → f q = g q) →
        ∀ q, q < B → EGate.applyNat eg f q = EGate.applyNat eg g q := by
  intro eg
  induction eg with
  | base gate =>
      intro hb f g hfg q hq
      exact Gate.applyNat_congr_lt B gate hb f g hfg q hq
  | mz p =>
      intro hb f g hfg q hq
      show Function.update f p false q = Function.update g p false q
      by_cases hqp : q = p
      · subst hqp; simp [Function.update]
      · simp only [Function.update, hqp]; exact hfg q hq
  | seq a b iha ihb =>
      intro hb f g hfg q hq
      obtain ⟨hba, hbb⟩ := hb
      show EGate.applyNat b (EGate.applyNat a f) q = EGate.applyNat b (EGate.applyNat a g) q
      exact ihb hbb _ _ (fun q' hq' => iha hba f g hfg q' hq') q hq

/-! ## §8. Boundedness of the uncontrolled measured adder.

Every gate in `gidneyAdderMeasured (n+2) q_start` references only `read/target/
carry` indices `j = 3i, 3i+1, 3i+2` with `i ≤ n+1`, i.e. `< 3*(n+2) =
adder_n_qubits (n+2)`.  We prove this once for the whole construction; it is the
hypothesis that powers the congruence swap. -/

/-- Monotonicity of `Gate.boundedBy` in the bound. -/
theorem Gate.boundedBy_mono {B B' : Nat} (h : B ≤ B') :
    ∀ (g : Gate), Gate.boundedBy B g → Gate.boundedBy B' g := by
  intro g
  induction g with
  | I => intro _; trivial
  | X q => intro hq; exact Nat.lt_of_lt_of_le hq h
  | CX c t => intro hb; exact ⟨Nat.lt_of_lt_of_le hb.1 h, Nat.lt_of_lt_of_le hb.2 h⟩
  | CCX a b c =>
      intro hb
      exact ⟨Nat.lt_of_lt_of_le hb.1 h, Nat.lt_of_lt_of_le hb.2.1 h, Nat.lt_of_lt_of_le hb.2.2 h⟩
  | seq g₁ g₂ ih₁ ih₂ => intro hb; exact ⟨ih₁ hb.1, ih₂ hb.2⟩

/-- Monotonicity of `EGate.boundedBy` in the bound. -/
theorem EGate.boundedBy_mono {B B' : Nat} (h : B ≤ B') :
    ∀ (eg : EGate), EGate.boundedBy B eg → EGate.boundedBy B' eg := by
  intro eg
  induction eg with
  | base g => intro hb; exact Gate.boundedBy_mono h g hb
  | mz q => intro hq; exact Nat.lt_of_lt_of_le hq h
  | seq a b iha ihb => intro hb; exact ⟨iha hb.1, ihb hb.2⟩

/-! ### Per-step boundedness.  Each forward/reverse step at bit `i` touches only
indices `≤ target_idx (i+1) = 3i+4`, hence `< 3i+5`. -/

private theorem first_step_bounded :
    Gate.boundedBy 5 gidney_adder_bit_step_faithful_first := by
  simp only [gidney_adder_bit_step_faithful_first, Gate.boundedBy, read_idx, target_idx, carry_idx]
  omega

private theorem interior_step_bounded (i : Nat) :
    Gate.boundedBy (3 * i + 5) (gidney_adder_bit_step_faithful_interior i) := by
  simp only [gidney_adder_bit_step_faithful_interior, Gate.boundedBy, read_idx, target_idx,
    carry_idx]
  omega

private theorem last_step_bounded (i : Nat) :
    Gate.boundedBy (3 * i + 3) (gidney_adder_bit_step_faithful_last i) := by
  simp only [gidney_adder_bit_step_faithful_last, Gate.boundedBy, read_idx, target_idx, carry_idx]
  omega

/-- The propagation forward cascade of length `k` is bounded by `3*k + 2`. -/
private theorem forward_with_propagation_bounded :
    ∀ k, Gate.boundedBy (3 * k + 2) (gidney_adder_forward_with_propagation k)
  | 0 => trivial
  | 1 => Gate.boundedBy_mono (by omega) _ first_step_bounded
  | n + 2 => by
      refine ⟨Gate.boundedBy_mono (by omega) _ (forward_with_propagation_bounded (n + 1)), ?_⟩
      exact Gate.boundedBy_mono (by omega) _ (interior_step_bounded (n + 1))

/-- The faithful forward sweep at width `n+2` is bounded by `adder_n_qubits (n+2)`. -/
theorem gidney_adder_forward_faithful_full_boundedBy (n : Nat) :
    Gate.boundedBy (adder_n_qubits (n + 2)) (gidney_adder_forward_faithful_full (n + 2)) := by
  show Gate.boundedBy (adder_n_qubits (n + 2))
    (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
              (gidney_adder_bit_step_faithful_last (n + 1)))
  unfold adder_n_qubits
  refine ⟨Gate.boundedBy_mono (by omega) _ (forward_with_propagation_bounded (n + 1)), ?_⟩
  exact Gate.boundedBy_mono (by omega) _ (last_step_bounded (n + 1))

/-- The final-CX cascade of length `k` is bounded by `3*k`
(it uses `read_idx j, target_idx j` for `j < k`, max `target_idx (k-1) = 3k-2 < 3k`). -/
private theorem final_cx_cascade_bounded :
    ∀ k, Gate.boundedBy (3 * k) (gidney_final_cx_cascade k)
  | 0 => trivial
  | k + 1 => by
      show Gate.boundedBy (3 * (k + 1))
        (Gate.seq (gidney_final_cx_cascade k) (Gate.CX (read_idx k) (target_idx k)))
      refine ⟨Gate.boundedBy_mono (by omega) _ (final_cx_cascade_bounded k), ?_⟩
      simp only [Gate.boundedBy, read_idx, target_idx]; omega

/-! ### Boundedness of the measured reverse cascade. -/

private theorem measFirstReverse_bounded :
    EGate.boundedBy 5 gidneyMeasFirstReverse := by
  simp only [gidneyMeasFirstReverse, EGate.boundedBy, Gate.boundedBy, read_idx, target_idx,
    carry_idx]
  omega

private theorem measInteriorReverse_bounded (i : Nat) :
    EGate.boundedBy (3 * i + 5) (gidneyMeasInteriorReverse i) := by
  simp only [gidneyMeasInteriorReverse, EGate.boundedBy, Gate.boundedBy, read_idx, target_idx,
    carry_idx]
  omega

private theorem measLastReverse_bounded (i : Nat) :
    EGate.boundedBy (3 * i + 3) (gidneyMeasLastReverse i) := by
  simp only [gidneyMeasLastReverse, EGate.boundedBy, Gate.boundedBy, carry_idx]
  omega

/-- The measured propagation-reverse cascade of length `K` is bounded by `3*K + 2`. -/
private theorem measPropReverse_bounded :
    ∀ K, EGate.boundedBy (3 * K + 2) (gidneyMeasPropReverse K)
  | 0 => by simp [gidneyMeasPropReverse, EGate.boundedBy, Gate.boundedBy]
  | 1 => EGate.boundedBy_mono (by omega) _ measFirstReverse_bounded
  | n + 2 => by
      show EGate.boundedBy (3 * (n + 2) + 2)
        (EGate.seq (gidneyMeasInteriorReverse (n + 1)) (gidneyMeasPropReverse (n + 1)))
      exact ⟨EGate.boundedBy_mono (by omega) _ (measInteriorReverse_bounded (n + 1)),
             EGate.boundedBy_mono (by omega) _ (measPropReverse_bounded (n + 1))⟩

/-- The measured full-reverse cascade at width `n+2` is bounded by `adder_n_qubits (n+2)`. -/
private theorem measFullReverse_bounded (n : Nat) :
    EGate.boundedBy (adder_n_qubits (n + 2)) (gidneyMeasFullReverse (n + 2)) := by
  show EGate.boundedBy (adder_n_qubits (n + 2))
    (EGate.seq (gidneyMeasLastReverse (n + 1)) (gidneyMeasPropReverse (n + 1)))
  unfold adder_n_qubits
  exact ⟨EGate.boundedBy_mono (by omega) _ (measLastReverse_bounded (n + 1)),
         EGate.boundedBy_mono (by omega) _ (measPropReverse_bounded (n + 1))⟩

/-- **The uncontrolled measured Gidney adder is bounded by `adder_n_qubits (n+2)`.**
Every gate touches only read/target/carry indices `< 3*(n+2)`; this is the
locality fact that lets the controlled wrapper discharge its high-index control +
source register and reuse `gidneyAdderMeasured_correct` verbatim. -/
theorem gidneyAdderMeasured_boundedBy (n q_start : Nat) :
    EGate.boundedBy (adder_n_qubits (n + 2)) (gidneyAdderMeasured (n + 2) q_start) := by
  show EGate.boundedBy (adder_n_qubits (n + 2))
    (EGate.seq
      (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                            (gidney_final_cx_cascade (n + 2))))
      (gidneyMeasFullReverse (n + 2)))
  refine ⟨⟨?_, ?_⟩, measFullReverse_bounded n⟩
  · exact gidney_adder_forward_faithful_full_boundedBy n
  · unfold adder_n_qubits
    exact Gate.boundedBy_mono (by omega) _ (final_cx_cascade_bounded (n + 2))

/-- **TIGHT locality bound: the uncontrolled measured Gidney adder touches only indices
`< 3*(n+2)`.**  The `adder_n_qubits (n+2) = 3*(n+2)+2` total leaves the two slack indices
`3*(n+2)` and `3*(n+2)+1` UNTOUCHED — every gate references a read/target/carry index of bit
`i ≤ n+1`, i.e. `≤ carry_idx (n+1) = 3*(n+1)+2 < 3*(n+2)`.  This tighter bound lets a caller frame
those two slack indices (and anything above) with a single `EGate.boundedBy`-above argument. -/
theorem gidneyAdderMeasured_boundedBy_tight (n q_start : Nat) :
    EGate.boundedBy (3 * (n + 2)) (gidneyAdderMeasured (n + 2) q_start) := by
  show EGate.boundedBy (3 * (n + 2))
    (EGate.seq
      (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                            (gidney_final_cx_cascade (n + 2))))
      (gidneyMeasFullReverse (n + 2)))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show Gate.boundedBy (3 * (n + 2))
      (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                (gidney_adder_bit_step_faithful_last (n + 1)))
    exact ⟨Gate.boundedBy_mono (by omega) _ (forward_with_propagation_bounded (n + 1)),
           Gate.boundedBy_mono (by omega) _ (last_step_bounded (n + 1))⟩
  · exact final_cx_cascade_bounded (n + 2)
  · show EGate.boundedBy (3 * (n + 2))
      (EGate.seq (gidneyMeasLastReverse (n + 1)) (gidneyMeasPropReverse (n + 1)))
    exact ⟨EGate.boundedBy_mono (by omega) _ (measLastReverse_bounded (n + 1)),
           EGate.boundedBy_mono (by omega) _ (measPropReverse_bounded (n + 1))⟩

/-! ## §9. The controlled core: register layout, source register, and CCX mask.

The control qubit lives at index `ctrl` and the addend `a` lives in a dedicated
SOURCE register `srcA_idx ctrl i = ctrl + 1 + i`.  Both are placed ABOVE the
adder block (`ctrl ≥ adder_n_qubits (n+2)`), so the measured adder never touches
them.  The CCX mask `read_idx i := ctrl ∧ a.testBit i` is the controlled,
genuinely-Toffoli core that the control forces (`n` Toffoli). -/

/-- Qubit index of the `i`-th bit of the SOURCE register holding the addend `a`
(placed just above the control qubit). -/
def srcA_idx (ctrl i : Nat) : Nat := ctrl + 1 + i

/-- The controlled-mask cascade: for `i < k`, `CCX(ctrl, srcA_idx ctrl i,
read_idx i)`.  Applied to a clean (`read = 0`) input it sets
`read_idx i := ctrl ∧ srcA_idx ctrl i`. -/
def ctrlMaskRead (ctrl : Nat) : Nat → Gate
  | 0     => Gate.I
  | k + 1 => Gate.seq (ctrlMaskRead ctrl k)
                      (Gate.CCX ctrl (srcA_idx ctrl k) (read_idx k))

/-- Toffoli count of the mask: one CCX (`7` T) per bit. -/
theorem tcount_ctrlMaskRead (ctrl : Nat) : ∀ k, Gate.tcount (ctrlMaskRead ctrl k) = 7 * k
  | 0     => rfl
  | k + 1 => by
      simp only [ctrlMaskRead, Gate.tcount, tcount_ctrlMaskRead ctrl k]; ring

/-! ## §10. The clean controlled-adder input.

`ctrlAdder_input_F n a b ctrl cval`:
  • adder block (`< adder_n_qubits n`): `read = 0`, `target = b`, `carry = 0`
    (i.e. `adder_input_F n 0 b`);
  • control qubit `ctrl`  := `cval`;
  • source register `srcA_idx ctrl i` (`i < n`) := `a.testBit i`;
  • everything else `false`.

The `cval` argument is the classical control BIT.  The construction `ctrl ∈ ℕ`
is the qubit INDEX. -/

/-- The clean two-operand + control + source input for the controlled adder. -/
def ctrlAdder_input_F (n a b ctrl cval : Nat) (k : Nat) : Bool :=
  if k = ctrl then decide (cval = 1)
  else if ctrl + 1 ≤ k ∧ k < ctrl + 1 + n then a.testBit (k - (ctrl + 1))
  else adder_input_F n 0 b k

/-! ## §11. The mask action on the adder block.

`ctrl` is the (high) control index, disjoint from the block.  We show the masked
clean input equals `adder_input_F (n+2) (if cval=1 then a else 0) b` on every
adder-block index. -/

/-- The mask cascade of length `k` leaves any index `q` disjoint from its read
targets (`q ≠ read_idx j` for `j < k`) unchanged. -/
private theorem ctrlMaskRead_preserves_non_read (ctrl : Nat) :
    ∀ (k : Nat) (f : Nat → Bool) (q : Nat), (∀ j, j < k → q ≠ read_idx j) →
      Gate.applyNat (ctrlMaskRead ctrl k) f q = f q := by
  intro k
  induction k with
  | zero => intro f q _; rfl
  | succ m ih =>
      intro f q hq
      show Gate.applyNat (Gate.CCX ctrl (srcA_idx ctrl m) (read_idx m))
             (Gate.applyNat (ctrlMaskRead ctrl m) f) q = f q
      rw [Gate.applyNat_CCX, update_neq _ _ _ _ (hq m (by omega)),
          ih f q (fun j hj => hq j (by omega))]

/-- The mask cascade of length `k` preserves `read_idx j` for `j ≥ k`
(it only targets `read_idx 0 .. read_idx (k-1)`). -/
private theorem ctrlMaskRead_preserves_high_read (ctrl : Nat) :
    ∀ (k : Nat) (f : Nat → Bool) (j : Nat), k ≤ j →
      Gate.applyNat (ctrlMaskRead ctrl k) f (read_idx j) = f (read_idx j) := by
  intro k
  induction k with
  | zero => intro f j _; rfl
  | succ m ih =>
      intro f j hj
      show Gate.applyNat (Gate.CCX ctrl (srcA_idx ctrl m) (read_idx m))
             (Gate.applyNat (ctrlMaskRead ctrl m) f) (read_idx j) = f (read_idx j)
      rw [Gate.applyNat_CCX, update_neq _ _ _ _ (by unfold read_idx; omega), ih f j (by omega)]

/-- The mask cascade sets `read_idx j` (for `j < k`) to
`f (read_idx j) ⊕ (f ctrl ∧ f (srcA_idx ctrl j))`, provided `ctrl` and the source
register are disjoint from every read index (`ctrl, srcA_idx ctrl _ ≠ read_idx _`),
which holds when `ctrl` is above the block. -/
private theorem ctrlMaskRead_read (ctrl : Nat) :
    ∀ (k : Nat),
      (∀ j, j < k → ctrl ≠ read_idx j) →
      (∀ i j, j < k → srcA_idx ctrl i ≠ read_idx j) →
      ∀ (f : Nat → Bool) (j : Nat), j < k →
        Gate.applyNat (ctrlMaskRead ctrl k) f (read_idx j)
          = xor (f (read_idx j)) (f ctrl && f (srcA_idx ctrl j)) := by
  intro k
  induction k with
  | zero => intro _ _ f j hj; omega
  | succ m ih =>
      intro hctrl hsrc f j hj
      show Gate.applyNat (Gate.CCX ctrl (srcA_idx ctrl m) (read_idx m))
             (Gate.applyNat (ctrlMaskRead ctrl m) f) (read_idx j) = _
      rw [Gate.applyNat_CCX]
      by_cases hjm : j = m
      · rw [hjm, update_eq]
        -- the controls (ctrl, srcA) and read_idx m are untouched by the prefix cascade
        rw [ctrlMaskRead_preserves_non_read ctrl m f ctrl (fun j' hj' => hctrl j' (by omega)),
            ctrlMaskRead_preserves_non_read ctrl m f (srcA_idx ctrl m)
              (fun j' hj' => hsrc m j' (by omega)),
            ctrlMaskRead_preserves_high_read ctrl m f m (le_refl _)]
      · have hjm' : read_idx j ≠ read_idx m := by unfold read_idx; omega
        rw [update_neq _ _ _ _ hjm',
            ih (fun j' hj' => hctrl j' (by omega)) (fun i' j' hj' => hsrc i' j' (by omega))
               f j (by omega)]

/-- **The mask turns the clean input into the gated-addend `adder_input_F`.**  On
every adder-block index `q < adder_n_qubits (n+2)`, the masked clean input equals
`adder_input_F (n+2) (if cval = 1 then a else 0) b` — read register = the gated
addend, target = `b`, carries = 0.  Requires the control register placed above the
block (`adder_n_qubits (n+2) ≤ ctrl`). -/
theorem ctrlMaskRead_eq_adder_input
    (n a b ctrl cval : Nat) (hctrl : adder_n_qubits (n + 2) ≤ ctrl)
    (q : Nat) (hq : q < adder_n_qubits (n + 2)) :
    Gate.applyNat (ctrlMaskRead ctrl (n + 2)) (ctrlAdder_input_F (n + 2) a b ctrl cval) q
      = adder_input_F (n + 2) (if cval = 1 then a else 0) b q := by
  -- disjointness facts from `ctrl` being above the block (for read targets j < n+2)
  have hdisj_ctrl : ∀ j, j < n + 2 → ctrl ≠ read_idx j := by
    intro j hj; unfold read_idx adder_n_qubits at *; omega
  have hdisj_src : ∀ i j, j < n + 2 → srcA_idx ctrl i ≠ read_idx j := by
    intro i j hj; unfold srcA_idx read_idx adder_n_qubits at *; omega
  -- the clean input at a block index is `adder_input_F (n+2) 0 b` (not ctrl, not src)
  have hin_block : ∀ p, p < adder_n_qubits (n + 2) →
      ctrlAdder_input_F (n + 2) a b ctrl cval p = adder_input_F (n + 2) 0 b p := by
    intro p hp; unfold ctrlAdder_input_F
    rw [if_neg (by unfold adder_n_qubits at hp hctrl; omega),
        if_neg (by unfold adder_n_qubits at hp hctrl; omega)]
  have hin_ctrl : ctrlAdder_input_F (n + 2) a b ctrl cval ctrl = decide (cval = 1) := by
    simp [ctrlAdder_input_F]
  obtain ⟨j, hj⟩ : ∃ j, j = q / 3 := ⟨_, rfl⟩
  have hqlt : q < 3 * (n + 2) + 2 := by unfold adder_n_qubits at hq; exact hq
  have hjlt : j ≤ n + 2 := by omega
  have hctrl' : 3 * (n + 2) + 2 ≤ ctrl := by unfold adder_n_qubits at hctrl; exact hctrl
  have h3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h3 with hmod | hmod | hmod
  · -- read index q = read_idx j
    have hqread : q = read_idx j := by unfold read_idx; omega
    have hRHS : adder_input_F (n + 2) (if cval = 1 then a else 0) b q
        = (decide (j < n + 2) && (if cval = 1 then a else 0).testBit j) := by
      rw [hqread]; unfold adder_input_F read_idx
      rw [show (3 * j) % 3 = 0 by omega, show (3 * j) / 3 = j by omega]
    rw [hRHS]
    by_cases hjn : j < n + 2
    · -- a genuine read register bit
      rw [hqread, ctrlMaskRead_read ctrl (n + 2) hdisj_ctrl hdisj_src
            (ctrlAdder_input_F (n + 2) a b ctrl cval) j hjn]
      have hin_read : ctrlAdder_input_F (n + 2) a b ctrl cval (read_idx j) = false := by
        rw [hin_block _ (by unfold read_idx adder_n_qubits; omega)]
        unfold adder_input_F read_idx
        rw [show (3 * j) % 3 = 0 by omega]; simp
      have hin_src : ctrlAdder_input_F (n + 2) a b ctrl cval (srcA_idx ctrl j) = a.testBit j := by
        unfold ctrlAdder_input_F srcA_idx
        rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega
      rw [hin_read, hin_ctrl, hin_src, Bool.false_xor, decide_eq_true hjn, Bool.true_and]
      cases cval with
      | zero => simp
      | succ c => cases c <;> simp
    · -- one of the two free slots (j = n+2): masked = input = false, RHS = false
      rw [hqread, ctrlMaskRead_preserves_high_read ctrl (n + 2) _ j (by omega),
          hin_block _ (hqread ▸ hq)]
      rw [show decide (j < n + 2) = false by simp [hjn], Bool.false_and]
      unfold adder_input_F read_idx
      rw [show (3 * j) % 3 = 0 by omega, show decide ((3 * j) / 3 < n + 2) = false by
        rw [show (3 * j) / 3 = j by omega]; simp [hjn]]
      simp
  · -- target index q = target_idx j: mask preserves; both sides depend only on b
    have hqtarget : q = target_idx j := by unfold target_idx; omega
    rw [hqtarget, ctrlMaskRead_preserves_non_read ctrl (n + 2) _ _
          (fun j' _ => by unfold target_idx read_idx; omega),
        hin_block _ (hqtarget ▸ hq)]
    unfold adder_input_F target_idx
    rw [show (3 * j + 1) % 3 = 1 by omega]
  · -- carry index q = carry_idx j: mask preserves; both false
    have hqcarry : q = carry_idx j := by unfold carry_idx; omega
    rw [hqcarry, ctrlMaskRead_preserves_non_read ctrl (n + 2) _ _
          (fun j' _ => by unfold carry_idx read_idx; omega),
        hin_block _ (hqcarry ▸ hq)]
    unfold adder_input_F carry_idx
    rw [show (3 * j + 2) % 3 = 2 by omega]

/-! ## §12. THE controlled measured Gidney adder. -/

/-- **The faithful controlled measured Gidney adder** (`2n` Toffoli).  The control
qubit lives at index `ctrl` (placed above the adder block) and the addend `a`
lives in the source register `srcA_idx ctrl i`.  The gate is the controlled core
`ctrlMaskRead` (`n` CCX = `n` Toffoli) — which gates the addend into the read
register under `ctrl` — followed by the REUSED uncontrolled measured Gidney adder
`gidneyAdderMeasured` (`n` Toffoli).  Net Toffoli = `2n`, realising Cain–Xu E4.

When `ctrl = 1` it adds the addend (`target := a + b`); when `ctrl = 0` the read
register is gated to `0` and the adder is the identity on the value (`target := b`).
-/
def gidneyAdderMeasuredControlled (n q_start ctrl : Nat) : EGate :=
  EGate.seq (EGate.base (ctrlMaskRead ctrl n)) (gidneyAdderMeasured n q_start)

end FormalRV.Arithmetic.MeasuredAdder
