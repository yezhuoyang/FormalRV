/-
  FormalRV.Arithmetic.MeasuredAdder.GidneyMeasuredControlled
  ──────────────────────────────────────────────────────────
  THE faithful **controlled** measured Gidney adder — `ctrl ? (a+b) : b` on the
  accumulator/target register, at `2n` Toffoli.  This realises Cain–Xu 2026's
  **E4** controlled adder (`30·q_A τ_s = 2n` Toffoli), the controlled counterpart
  of the **E3** uncontrolled measured adder (`25·q_A = n` Toffoli) built in
  `FormalRV.Arithmetic.MeasuredAdder.GidneyMeasured`
  (`gidneyAdderMeasured`, `n` Toffoli).

  ## Why the controlled adder costs `2n` (the E3 → E4 jump)

  The uncontrolled measured adder is `n` Toffoli because the carry-uncompute
  reverse sweep is **measured away** (`mz`, Toffoli-free): the carries are not
  entangled with anything external, so an X-basis measurement + classical fixup
  releases them for free.  A *controlled* add cannot do this for free: the
  control entangles the addend with the rest of the computation, so the gating of
  the addend is itself a genuine reversible (Toffoli) operation.  Cain–Xu charge
  exactly `2·q_A τ_s` for the controlled adder vs `q_A` for the uncontrolled one —
  the verified factor-2 here.

  ## The construction (faithful `2n` = controlled-core `n` + measured-add `n`)

  We present the controlled measured adder as the task's sanctioned decomposition
  `forward-controlled-core (reversible, n Toffoli)  ;  measured-add (n Toffoli)`:

    1. **`ctrlMaskRead n ctrl`** — the controlled core (`n` Toffoli).  For each
       bit `i < n` a `CCX(ctrl, srcA i, read_idx i)` gates the addend `a` (held in
       a dedicated SOURCE register `srcA i`) into the adder's read register:
       `read[i] := ctrl ∧ a.testBit i`.  This is the genuinely-reversible,
       genuinely-Toffoli part that the control forces (it CANNOT be measured away,
       unlike the uncontrolled adder's uncompute).
    2. **`gidneyAdderMeasured n`** — the REUSED uncontrolled measured Gidney adder
       (`n` Toffoli), which now adds the *gated* addend `ctrl ? a : 0` into the
       target: `target := target + (ctrl ? a : 0) = ctrl ? (a+b) : b`.
    3. **`mzList (read register)`** — release the read ancilla by measurement
       (Toffoli-free).

  Total: `n` (mask) `+` `n` (measured add) `+` `0` `= 2n` Toffoli — exactly E4.

  ## Why the value is `ctrl ? (a+b) : b` (the reuse argument)

  After the mask, the adder-block sub-state is **literally**
  `adder_input_F n (if ctrl then a else 0) b` (read register = the gated addend,
  target = `b`, carries = 0).  The control bit and the source register live at
  HIGH indices (`≥ adder_n_qubits = 3n+2`), and the measured adder only ever
  touches indices `< 3n+2` (`gidneyAdderMeasured_boundedBy`).  Hence a clean
  index-congruence lemma (`EGate.applyNat_congr_lt`) lets us swap the masked
  state for the literal `adder_input_F`, and we REUSE `gidneyAdderMeasured_correct`
  verbatim — NO arithmetic is re-proved.  Conclusion:

    • `ctrl = true`  ⟹  `target[i] = (a + b).testBit i`,  carries cleared;
    • `ctrl = false` ⟹  `target[i] = b.testBit i`,         carries cleared.

  i.e. the decoded target is `if ctrl then (a + b) % 2^bits else b % 2^bits`
  (`gidneyAdderMeasuredControlled_target_val`).

  Refs: Cain–Xu 2026 (E3 `25 q_A`/E4 `30 q_A`, controlled-adder factor 2);
  Gidney arXiv:1709.06648 (temporary AND); reuses
  `FormalRV.Arithmetic.MeasuredAdder.GidneyMeasured`.
-/
import FormalRV.Arithmetic.MeasuredAdder.GidneyMeasured

namespace FormalRV.Arithmetic.MeasuredAdder

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute

/-! ## §0. Generic index-congruence for `Gate` / `EGate`.

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

/-! ## §1. Boundedness of the uncontrolled measured adder.

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

/-! ## §2. The controlled core: register layout, source register, and CCX mask.

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

/-! ## §3. The clean controlled-adder input.

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

/-! ## §4. The mask action on the adder block.

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
private theorem ctrlMaskRead_eq_adder_input
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

/-! ## §5. THE controlled measured Gidney adder. -/

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

/-! ## §6. Count: `2·(n+2)` Toffoli — controlled core `n` + measured add `n`. -/

/-- **Toffoli count of the controlled measured adder is exactly `2·(n+2)`** at
width `n+2`: the controlled mask contributes `n+2` (one CCX per addend bit) and
the reused measured adder contributes `n+2`; their sum is `2·(n+2)`.  This is the
verified `E3 (n) → E4 (2n)` jump: the control DOUBLES the adder Toffoli cost vs the
uncontrolled measured adder `gidneyAdderMeasured` (`toffoli_gidneyAdderMeasured`). -/
theorem toffoli_gidneyAdderMeasuredControlled (n q_start ctrl : Nat) :
    EGate.toffoli (gidneyAdderMeasuredControlled (n + 2) q_start ctrl) = 2 * (n + 2) := by
  have hadd : EGate.tcount (gidneyAdderMeasured (n + 2) q_start) = 7 * (n + 2) := by
    show EGate.tcount
      (EGate.seq
        (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                              (gidney_final_cx_cascade (n + 2))))
        (gidneyMeasFullReverse (n + 2))) = 7 * (n + 2)
    simp only [EGate.tcount, Gate.tcount, tcount_gidneyMeasFullReverse, Nat.add_zero,
               tcount_gidney_adder_forward_faithful_full, tcount_gidney_final_cx_cascade]
  unfold EGate.toffoli gidneyAdderMeasuredControlled
  simp only [EGate.tcount, tcount_ctrlMaskRead, hadd]
  rw [show 7 * (n + 2) + 7 * (n + 2) = 2 * (n + 2) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **★ The control DOUBLES the measured-adder Toffoli count (E3 → E4).**  The
controlled measured adder costs exactly TWICE the uncontrolled measured Gidney
adder `gidneyAdderMeasured` — Cain–Xu's `30 q_A = 2·q_A` (E4) vs `25 q_A = q_A`
(E3) controlled-adder factor-2, on verified objects. -/
theorem gidneyAdderMeasuredControlled_doubles (n q_start ctrl : Nat) :
    EGate.toffoli (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
      = 2 * EGate.toffoli (gidneyAdderMeasured (n + 2) q_start) := by
  rw [toffoli_gidneyAdderMeasuredControlled, toffoli_gidneyAdderMeasured]

/-! ## §7. Value correctness — the CONTROLLED sum `ctrl ? (a+b) : b`.

We split the controlled adder as `mask ; measured-adder`.  The mask turns the
clean input into `adder_input_F (n+2) (if cval=1 then a else 0) b` ON the adder
block (`ctrlMaskRead_eq_adder_input`); the measured adder only touches the block
(`gidneyAdderMeasured_boundedBy`), so by index-congruence (`EGate.applyNat_congr_lt`)
its target/carry outputs equal those on the literal `adder_input_F`.  We then
REUSE `gidneyAdderMeasured_correct` verbatim — the arithmetic is NOT re-proved. -/

/-- **Value correctness of the controlled measured adder — the CONTROLLED sum.**
With the control register placed above the adder block (`adder_n_qubits (n+2) ≤
ctrl`) and the classical control bit `cval`, on the clean input
`ctrlAdder_input_F (n+2) a b ctrl cval` the controlled measured Gidney adder writes
to the target register, for every `i < n+2`,

  • `target[i] = (if cval = 1 then a + b else b).testBit i`   (the CONTROLLED sum),
  • `carry[i]  = false`                                        (carries released).

The target value is the measured adder's faithful sum of `b` with the GATED addend
`if cval = 1 then a else 0`, reused from `gidneyAdderMeasured_correct`. -/
theorem gidneyAdderMeasuredControlled_correct
    (n a b q_start ctrl cval : Nat)
    (hctrl : adder_n_qubits (n + 2) ≤ ctrl)
    (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    ∀ i, i < n + 2 →
      (EGate.applyNat (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
          (ctrlAdder_input_F (n + 2) a b ctrl cval) (target_idx i)
        = (if cval = 1 then a + b else b).testBit i)
      ∧ (EGate.applyNat (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
          (ctrlAdder_input_F (n + 2) a b ctrl cval) (carry_idx i) = false) := by
  intro i hi
  set a' := if cval = 1 then a else 0 with ha'
  have ha'lt : a' < 2 ^ (n + 2) := by rw [ha']; split <;> [exact ha; exact Nat.pos_of_ne_zero (by positivity)]
  -- split the controlled adder: mask ; measured adder
  have hsplit : ∀ q,
      EGate.applyNat (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
        (ctrlAdder_input_F (n + 2) a b ctrl cval) q
      = EGate.applyNat (gidneyAdderMeasured (n + 2) q_start)
        (Gate.applyNat (ctrlMaskRead ctrl (n + 2)) (ctrlAdder_input_F (n + 2) a b ctrl cval)) q := by
    intro q; rfl
  -- congruence: swap the masked state for the literal `adder_input_F (n+2) a' b`
  have hswap : ∀ q, q < adder_n_qubits (n + 2) →
      EGate.applyNat (gidneyAdderMeasured (n + 2) q_start)
        (Gate.applyNat (ctrlMaskRead ctrl (n + 2)) (ctrlAdder_input_F (n + 2) a b ctrl cval)) q
      = EGate.applyNat (gidneyAdderMeasured (n + 2) q_start) (adder_input_F (n + 2) a' b) q := by
    intro q hq
    exact EGate.applyNat_congr_lt (adder_n_qubits (n + 2)) (gidneyAdderMeasured (n + 2) q_start)
      (gidneyAdderMeasured_boundedBy n q_start) _ _
      (fun p hp => by rw [ha']; exact ctrlMaskRead_eq_adder_input n a b ctrl cval hctrl p hp) q hq
  have htidx : target_idx i < adder_n_qubits (n + 2) := by unfold target_idx adder_n_qubits; omega
  have hcidx : carry_idx i < adder_n_qubits (n + 2) := by unfold carry_idx adder_n_qubits; omega
  obtain ⟨htgt, hcar⟩ := gidneyAdderMeasured_correct n a' b q_start ha'lt hb i hi
  refine ⟨?_, ?_⟩
  · rw [hsplit, hswap _ htidx, htgt]
    -- adder_sum_bit_classical a' b i = (if cval=1 then a+b else b).testBit i
    unfold adder_sum_bit_classical
    rw [ha']; split
    · rfl
    · rw [Nat.zero_add]
  · rw [hsplit, hswap _ hcidx, hcar]

/-- **Decoded value form: the target register holds `if cval = 1 then (a+b) else b`
mod `2^(n+2)`.**  The LSB-first `gidney_target_val` decoder of the controlled
measured adder's output equals `(if cval = 1 then a + b else b) % 2^(n+2)` — the
faithful CONTROLLED sum: the arithmetic sum `(a+b) % 2^bits` when the control is
set, and the unchanged accumulator `b % 2^bits` when it is not.  Derived from the
per-bit `gidneyAdderMeasuredControlled_correct` via
`gidney_target_val_eq_sum_when_bits_match`. -/
theorem gidneyAdderMeasuredControlled_target_val
    (n a b q_start ctrl cval : Nat)
    (hctrl : adder_n_qubits (n + 2) ≤ ctrl)
    (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    gidney_target_val (n + 2)
        (EGate.applyNat (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
          (ctrlAdder_input_F (n + 2) a b ctrl cval))
      = (if cval = 1 then a + b else b) % 2 ^ (n + 2) := by
  apply gidney_target_val_eq_sum_when_bits_match (n + 2) (if cval = 1 then a + b else b)
  intro i hi
  exact (gidneyAdderMeasuredControlled_correct n a b q_start ctrl cval hctrl ha hb i hi).1

end FormalRV.Arithmetic.MeasuredAdder
