/-
  FormalRV.Shor.WindowedCopySemantics — window-copy semantics + window-bit bridge.

  Boolean-function (`Gate.applyNat`) semantics of `copyWindow` — the CX cascade
  that copies window `j` of the `y`-register into the unary-lookup address
  register — plus the bridge from the `encodeReg` qubit encoding of `y` to the
  pure windowed digits `WindowedArith.window`.

  Contents:
  * `applyNat_cx_cascade_frame` / `applyNat_cx_cascade_at` — generic semantics of
    a parallel-CX cascade `foldl (fun g i => seq g (CX (ctrl i) (addr i)))` with
    pairwise-distinct targets and controls disjoint from targets;
  * `copyWindow_at_addr` / `copyWindow_frame` — full post-state of `copyWindow`;
  * `copyWindow_copies` — on a clean address register the copy writes the y-bits;
  * `copyWindow_involutive(_apply)` — re-applying `copyWindow` uncopies;
  * `window_testBit` / `encodeReg_window_bit` — bit `i` of `window w y j` is bit
    `j·w + i` of `y`, hence the `encodeReg`-encoded y-register qubit
    `yBase + j·w + i` carries exactly bit `i` of the window digit.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms.
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuit

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §1. Generic parallel-CX cascade semantics.

`copyWindow` is an instance of the cascade
`(List.range n).foldl (fun g i => Gate.seq g (Gate.CX (ctrl i) (addr i))) Gate.I`.
As long as the targets `addr i` are pairwise distinct and no control `ctrl i` is a
target, the cascade acts as `n` independent CXs: each target picks up the XOR of
its control's ORIGINAL value, and every other wire is untouched. -/

/-- **Cascade frame.** A position that is not one of the CX targets is untouched
    (no disjointness hypotheses needed: only targets are ever written). -/
theorem applyNat_cx_cascade_frame (ctrl addr : Nat → Nat) (f : Nat → Bool) :
    ∀ (n p : Nat), (∀ i, i < n → p ≠ addr i) →
      Gate.applyNat ((List.range n).foldl
          (fun g i => Gate.seq g (Gate.CX (ctrl i) (addr i))) Gate.I) f p = f p := by
  intro n
  induction n with
  | zero =>
      intro p _
      simp
  | succ n ih =>
      intro p hp
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                 Gate.applyNat_seq, Gate.applyNat_CX]
      rw [update_neq _ _ _ _ (hp n (Nat.lt_succ_self n))]
      exact ih p (fun i hi => hp i (Nat.lt_succ_of_lt hi))

/-- **Cascade post-state at a target.** With pairwise-distinct targets and controls
    disjoint from targets, target `addr i` ends as the XOR of its original value
    with the ORIGINAL control value `f (ctrl i)` (later steps never read a wire an
    earlier step wrote). -/
theorem applyNat_cx_cascade_at (ctrl addr : Nat → Nat) (f : Nat → Bool) :
    ∀ (n : Nat),
      (∀ i k, i < n → k < n → i ≠ k → addr i ≠ addr k) →
      (∀ i k, i < n → k < n → ctrl i ≠ addr k) →
      ∀ i, i < n →
        Gate.applyNat ((List.range n).foldl
            (fun g i => Gate.seq g (Gate.CX (ctrl i) (addr i))) Gate.I) f (addr i)
          = xor (f (addr i)) (f (ctrl i)) := by
  intro n
  induction n with
  | zero =>
      intro _ _ i hi
      exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro haddr hctrl i hi
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                 Gate.applyNat_seq, Gate.applyNat_CX]
      by_cases hi' : i < n
      · -- earlier target: the last CX writes a DIFFERENT wire
        rw [update_neq _ _ _ _
              (haddr i n (Nat.lt_succ_of_lt hi') (Nat.lt_succ_self n) (Nat.ne_of_lt hi'))]
        exact ih
          (fun a b ha hb => haddr a b (Nat.lt_succ_of_lt ha) (Nat.lt_succ_of_lt hb))
          (fun a b ha hb => hctrl a b (Nat.lt_succ_of_lt ha) (Nat.lt_succ_of_lt hb))
          i hi'
      · -- the last target: its own wire and its control are untouched by the prefix
        have hin : i = n := by omega
        rw [hin, update_eq,
            applyNat_cx_cascade_frame ctrl addr f n (addr n)
              (fun k hk => haddr n k (Nat.lt_succ_self n) (Nat.lt_succ_of_lt hk)
                (Nat.ne_of_gt hk)),
            applyNat_cx_cascade_frame ctrl addr f n (ctrl n)
              (fun k hk => hctrl n k (Nat.lt_succ_self n) (Nat.lt_succ_of_lt hk))]

/-! ## §2. `copyWindow` post-state. -/

/-- Distinct address indices live on distinct wires (`1 + 2i` is injective). -/
theorem ulookup_address_idx_ne (i k : Nat) (hne : i ≠ k) :
    ulookup_address_idx i ≠ ulookup_address_idx k := by
  unfold ulookup_address_idx
  omega

/-- The standing disjointness hypothesis — the CX controls (y-register wires
    `yBase + j·w + i`) are not address wires — holds whenever `2·w ≤ yBase`
    (every address wire `1 + 2k ≤ 2w − 1 < yBase`). -/
theorem ctrl_ne_addr_of_le_yBase (w yBase j : Nat) (hyBase : 2 * w ≤ yBase) :
    ∀ i k, i < w → k < w → yBase + j * w + i ≠ ulookup_address_idx k := by
  intro i k _ hk
  unfold ulookup_address_idx
  omega

/-- **`copyWindow` frame.** Any wire that is not an address wire `ulookup_address_idx i`
    (`i < w`) is untouched by `copyWindow` — no disjointness hypothesis needed. -/
theorem copyWindow_frame (w yBase j : Nat) (f : Nat → Bool) (p : Nat)
    (hp : ∀ i, i < w → p ≠ ulookup_address_idx i) :
    Gate.applyNat (copyWindow w yBase j) f p = f p := by
  unfold copyWindow
  exact applyNat_cx_cascade_frame (fun i => yBase + j * w + i) ulookup_address_idx f w p hp

/-- **`copyWindow` post-state at an address wire.** Provided no CX control is an
    address wire (`hctrl`; holds when `2·w ≤ yBase` by `ctrl_ne_addr_of_le_yBase`),
    address wire `i` ends as the XOR of its original value with y-register bit
    `f (yBase + j·w + i)`. -/
theorem copyWindow_at_addr (w yBase j : Nat) (f : Nat → Bool)
    (hctrl : ∀ i k, i < w → k < w → yBase + j * w + i ≠ ulookup_address_idx k)
    (i : Nat) (hi : i < w) :
    Gate.applyNat (copyWindow w yBase j) f (ulookup_address_idx i)
      = xor (f (ulookup_address_idx i)) (f (yBase + j * w + i)) := by
  unfold copyWindow
  exact applyNat_cx_cascade_at (fun i => yBase + j * w + i) ulookup_address_idx f w
    (fun a b _ _ hne => ulookup_address_idx_ne a b hne) hctrl i hi

/-- **`copyWindow` copies.** On a CLEAN address register (all address wires `false`),
    `copyWindow` writes the y-register bits verbatim:
    address wire `i` ends as `f (yBase + j·w + i)`. -/
theorem copyWindow_copies (w yBase j : Nat) (f : Nat → Bool)
    (hctrl : ∀ i k, i < w → k < w → yBase + j * w + i ≠ ulookup_address_idx k)
    (hclean : ∀ i, i < w → f (ulookup_address_idx i) = false)
    (i : Nat) (hi : i < w) :
    Gate.applyNat (copyWindow w yBase j) f (ulookup_address_idx i)
      = f (yBase + j * w + i) := by
  rw [copyWindow_at_addr w yBase j f hctrl i hi, hclean i hi, Bool.false_xor]

/-- **`copyWindow` is self-inverse (pointwise).** Re-applying the copy uncopies:
    each address wire XORs in the SAME control bit twice (the controls are outside
    the address region, so the first pass leaves them intact), and all other wires
    are framed. -/
theorem copyWindow_involutive_apply (w yBase j : Nat) (f : Nat → Bool)
    (hctrl : ∀ i k, i < w → k < w → yBase + j * w + i ≠ ulookup_address_idx k)
    (p : Nat) :
    Gate.applyNat (copyWindow w yBase j) (Gate.applyNat (copyWindow w yBase j) f) p
      = f p := by
  by_cases hp : ∃ i, i < w ∧ p = ulookup_address_idx i
  · obtain ⟨i, hi, rfl⟩ := hp
    rw [copyWindow_at_addr w yBase j _ hctrl i hi,
        copyWindow_at_addr w yBase j f hctrl i hi,
        copyWindow_frame w yBase j f (yBase + j * w + i) (fun k hk => hctrl i k hi hk)]
    cases f (ulookup_address_idx i) <;> cases f (yBase + j * w + i) <;> rfl
  · push Not at hp
    rw [copyWindow_frame w yBase j _ p hp, copyWindow_frame w yBase j f p hp]

/-- **`copyWindow` is self-inverse (function form).** -/
theorem copyWindow_involutive (w yBase j : Nat) (f : Nat → Bool)
    (hctrl : ∀ i k, i < w → k < w → yBase + j * w + i ≠ ulookup_address_idx k) :
    Gate.applyNat (copyWindow w yBase j) (Gate.applyNat (copyWindow w yBase j) f) = f :=
  funext (copyWindow_involutive_apply w yBase j f hctrl)

/-! ## §3. Window-bit bridge: `encodeReg` qubits ↔ `WindowedArith.window` digits. -/

/-- **Window bit = global bit.** Bit `i` of the `j`-th width-`w` window of `y` is
    bit `j·w + i` of `y` (for `i < w`).  The Nat fact underlying the y-register ↔
    window-digit bridge. -/
theorem window_testBit (w y j i : Nat) (hi : i < w) :
    (WindowedArith.window w y j).testBit i = y.testBit (j * w + i) := by
  unfold WindowedArith.window
  rw [← Nat.pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
      decide_eq_true hi, Bool.true_and]
  congr 1
  ring

/-- **y-register qubit ↔ window digit.** In the `encodeReg yBase (numWin·w) y`
    encoding of the y-register, the qubit at `yBase + j·w + i` carries exactly bit
    `i` of the window digit `window w y j` (for `i < w`, `j < numWin`).  Combined
    with `copyWindow_copies`, the address register receives precisely the binary
    expansion of `window w y j` — the lookup address. -/
theorem encodeReg_window_bit (yBase w numWin y j i : Nat) (hi : i < w) (hj : j < numWin) :
    encodeReg yBase (numWin * w) y (yBase + j * w + i)
      = (WindowedArith.window w y j).testBit i := by
  rw [window_testBit w y j i hi]
  unfold encodeReg
  have hlt : j * w + i < numWin * w := by
    have h1 : j * w + i < (j + 1) * w := by
      have hexp : (j + 1) * w = j * w + w := by ring
      omega
    have h2 : (j + 1) * w ≤ numWin * w := Nat.mul_le_mul (by omega) (Nat.le_refl w)
    omega
  rw [if_pos ⟨by omega, by omega⟩]
  congr 1
  omega

/-- **The copy loads the window digit.** End-to-end corollary: on a state whose
    y-register region holds `encodeReg`-encoded `y` and whose address register is
    clean, `copyWindow w yBase j` leaves bit `i` of `window w y j` on address wire
    `i`.  (Stated against an abstract `f` that AGREES with the encoding on the
    y-register region, so it applies to full-circuit states like `mulInput`.) -/
theorem copyWindow_loads_window (w yBase numWin y j : Nat) (f : Nat → Bool)
    (hctrl : ∀ i k, i < w → k < w → yBase + j * w + i ≠ ulookup_address_idx k)
    (hclean : ∀ i, i < w → f (ulookup_address_idx i) = false)
    (henc : ∀ i, i < w → f (yBase + j * w + i) = encodeReg yBase (numWin * w) y (yBase + j * w + i))
    (hj : j < numWin) (i : Nat) (hi : i < w) :
    Gate.applyNat (copyWindow w yBase j) f (ulookup_address_idx i)
      = (WindowedArith.window w y j).testBit i := by
  rw [copyWindow_copies w yBase j f hctrl hclean i hi, henc i hi,
      encodeReg_window_bit yBase w numWin y j i hi hj]

end FormalRV.Shor.WindowedCircuit
