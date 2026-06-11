/-
  FormalRV.Arithmetic.MeasuredAdder.GidneyMeasured
  ────────────────────────────────────────────────
  THE **measured** Gidney ripple-carry adder — `n` Toffoli per add (vs our
  reversible `2n`), realising the cost Cain–Xu 2026 / Gidney 2018 charge to an
  adder.  It computes the FAITHFUL sum `(a + b) % 2^bits` on the target register,
  with the carry ancillas released by MEASUREMENT-based AND-uncompute instead of
  a second (reversible) Toffoli sweep.

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

  ## Why the value is still `a + b` (the frame argument)

  Each measured reverse step equals the unitary reverse step followed by clearing
  its own carry (`*_eq` lemmas: `measured_step i f = update (unitary_step i f)
  (carry i) false`).  Crucially, the carry an interior step writes is read by NO
  later (lower-index) step, so forcing it to `false` is INVISIBLE to every
  `read`/`target` output of the remaining cascade
  (`gidneyMeasuredReverse_rt_eq`, via the insensitivity lemma
  `propagation_reverse_clear_carry_insensitive`).  Hence:
    • `target` after the measured adder = `target` after the reversible adder
      = `(a + b) % 2^bits`  (REUSING `gidney_adder_full_faithful_no_measurement_target_correct`);
    • the carry register is `false` everywhere (`gidneyMeasuredReverse` clears it).

  This is `gidneyAdderMeasured_correct` — a FAITHFUL `a + b`, at `n+2` Toffolis,
  matching Cain–Xu's `n`-Toffoli-per-add adder.

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

/-! ## §7. Count: `n` Toffoli — final-CX and the measured reverse are Toffoli-free. -/

/-- **Toffoli count of the measured adder is exactly the forward sweep's `n`** (here
`n+2` at width `n+2`): the final-CX cascade and the measured reverse cascade
contribute `0`.  Derived from `tcount_gidney_adder_forward_faithful_full`
(`7·(n+2)` T = `(n+2)` Toffolis), `tcount_gidney_final_cx_cascade = 0`, and
`tcount_gidneyMeasFullReverse = 0`. -/
theorem toffoli_gidneyAdderMeasured (n q_start : Nat) :
    EGate.toffoli (gidneyAdderMeasured (n + 2) q_start) = n + 2 := by
  unfold EGate.toffoli gidneyAdderMeasured
  simp only [EGate.tcount, Gate.tcount, tcount_gidneyMeasFullReverse, Nat.add_zero,
             tcount_gidney_adder_forward_faithful_full, tcount_gidney_final_cx_cascade]
  rw [Nat.mul_div_cancel_left _ (by norm_num)]

/-- **★ HEADLINE — the measurement-uncompute HALVES the adder Toffoli count.**  The
measured Gidney adder costs exactly HALF the Toffolis of the reversible faithful
`gidney_adder_full_faithful_no_measurement` (`n+2` vs `2·(n+2)`) — the verified
statement that Gidney's measurement-based carry-uncompute realises Cain–Xu's
`n`-Toffoli-per-add adder, closing the factor-2 of the reversible version, while
STILL computing the FAITHFUL sum `(a+b) % 2^bits` (`gidneyAdderMeasured_correct`). -/
theorem gidneyAdderMeasured_halves (n q_start : Nat) :
    EGate.toffoli (gidneyAdderMeasured (n + 2) q_start)
      = tcount (gidney_adder_full_faithful_no_measurement (n + 2)) / 7 / 2 := by
  rw [toffoli_gidneyAdderMeasured, tcount_gidney_adder_full_faithful_no_measurement,
      show 14 * (n + 2) = (n + 2) * 2 * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num), Nat.mul_div_cancel _ (by norm_num)]

/-! ## §8. Value correctness: the FAITHFUL sum `(a+b) % 2^bits` on the target. -/

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

/-- **Value correctness of the measured adder — FAITHFUL `a + b`.**  On the clean
two-operand input `adder_input_F (n+2) a b`, the measured Gidney adder writes the
true sum bits `(a + b).testBit i` to the target register for every `i < n+2`, AND
releases every carry ancilla to `false`:

  • `target[i] = (a + b).testBit i`   (= `adder_sum_bit_classical a b i`),
  • `carry[i]  = false`.

The target value is REUSED verbatim from the reversible adder's correctness
(`gidney_adder_full_faithful_no_measurement_target_correct`): the measured reverse
agrees with the reversible reverse on every `target` position
(`gidneyMeasFullReverse_rt`), and the reversible adder's target is the sum.  The
carries are released by the measurement-uncompute (`gidneyMeasFullReverse_carry_clear`),
citing `MeasuredANDUncompute.measANDUncompute_perfect` for the quantum
justification that this reset IS the perfect AND-uncompute. -/
theorem gidneyAdderMeasured_correct
    (n a b q_start : Nat) (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    ∀ i, i < n + 2 →
      (EGate.applyNat (gidneyAdderMeasured (n + 2) q_start)
          (adder_input_F (n + 2) a b) (target_idx i)
        = adder_sum_bit_classical a b i)
      ∧ (EGate.applyNat (gidneyAdderMeasured (n + 2) q_start)
          (adder_input_F (n + 2) a b) (carry_idx i) = false) := by
  intro i hi
  refine ⟨?_, ?_⟩
  · -- target = sum: route through the reversible adder's proven target correctness.
    rw [gidneyAdderMeasured_applyNat,
        gidneyMeasFullReverse_rt n _ (target_idx i) (by intro m; unfold target_idx carry_idx; omega)]
    -- now the goal is the reversible reverse post-state target = sum
    have hrev : gidney_full_reverse_post_state (n + 2)
        (gidney_final_cx_cascade_post_state (n + 2)
          (gidney_forward_faithful_full_post_state (n + 2) (adder_input_F (n + 2) a b))) (target_idx i)
        = adder_sum_bit_classical a b i := by
      rw [← gidney_adder_full_faithful_no_measurement_applyNat n (adder_input_F (n + 2) a b)]
      exact gidney_adder_full_faithful_no_measurement_target_correct (n + 2) a b
        (by omega) ha hb i hi
    exact hrev
  · -- carry = false: the measured reverse clears it.
    rw [gidneyAdderMeasured_applyNat]
    exact gidneyMeasFullReverse_carry_clear n _ i hi

/-- **Decoded value form: the target register holds `(a + b) % 2^(n+2)`.**  The
LSB-first `gidney_target_val` decoder of the measured adder's output equals
`(a + b) % 2^(n+2)` — the faithful arithmetic sum.  Derived from the per-bit
`gidneyAdderMeasured_correct` and the reversible adder's decoded-value theorem
`gidney_adder_correct_full` (which both equal `(a+b) % 2^bits` bit-for-bit). -/
theorem gidneyAdderMeasured_target_val
    (n a b q_start : Nat) (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    gidney_target_val (n + 2)
        (EGate.applyNat (gidneyAdderMeasured (n + 2) q_start) (adder_input_F (n + 2) a b))
      = (a + b) % 2 ^ (n + 2) := by
  -- Each target bit equals `(a+b).testBit i` (= `adder_sum_bit_classical`), so the
  -- LSB-first decoder evaluates to `(a+b) % 2^bits` by `gidney_target_val_eq_sum_when_bits_match`.
  apply gidney_target_val_eq_sum_when_bits_match (n + 2) (a + b)
  intro i hi
  have := (gidneyAdderMeasured_correct n a b q_start ha hb i hi).1
  rwa [adder_sum_bit_classical] at this

end FormalRV.Arithmetic.MeasuredAdder
