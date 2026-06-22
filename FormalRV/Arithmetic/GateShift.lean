/-
  FormalRV.Arithmetic.GateShift — relabel every qubit of a `Gate` by a constant base offset `+b`,
  with the transport law for `Gate.applyNat`, count-invariance, and the disjointness frame.

  A general reusable utility for placing a circuit at an arbitrary base in a wider register (the
  qubit-index analogue of the `Adder`'s `q_start` parameter, but for ANY `Gate`).  Its purpose here
  is the CFS multi-register fold: `shiftGate (j·width) residueGate` puts residue register `j` at its
  own disjoint base, and the transport law lets `residueGate_verified` (proven at base 0) carry to
  every base — "reuse-via-transport", no re-derivation of the windowed multiplier internals.

  Key lemmas:
    * `applyNat_shiftGate` — the shifted gate, at index `i ≥ b`, acts like `g` on the down-shifted
      register `(·+b)`; at `i < b` it is the identity.
    * `tcount_shiftGate`   — relabeling preserves the T/Toffoli count.
    * `shiftGate_frame`    — the shifted gate fixes every qubit below `b` (left disjointness).
-/
import FormalRV.Arithmetic.Correctness
import FormalRV.Arithmetic.GateToUCom

namespace FormalRV.Arithmetic

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open Function (update)

/-- Relabel every qubit index of `g` by `+b`. -/
def shiftGate (b : Nat) : Gate → Gate
  | Gate.I            => Gate.I
  | Gate.X q          => Gate.X (q + b)
  | Gate.CX c t       => Gate.CX (c + b) (t + b)
  | Gate.CCX a c d    => Gate.CCX (a + b) (c + b) (d + b)
  | Gate.seq g₁ g₂    => Gate.seq (shiftGate b g₁) (shiftGate b g₂)

/-- Relabeling preserves the T-count (only `CCX` count, index-independent). -/
theorem tcount_shiftGate (b : Nat) (g : Gate) : tcount (shiftGate b g) = tcount g := by
  induction g with
  | I => rfl
  | X => rfl
  | CX => rfl
  | CCX => rfl
  | seq g₁ g₂ ih₁ ih₂ => simp only [shiftGate, tcount, ih₁, ih₂]

/-- **The transport law.**  The base-`b`-shifted gate acts on every index `i`:
    for `i ≥ b` it is `g` applied to the down-shifted register `(·+b)` read at `i - b`; for `i < b`
    it leaves `f i` untouched.  Proven by induction on `g` (each `update` becomes an `ite`). -/
theorem applyNat_shiftGate (b : Nat) (g : Gate) :
    ∀ (f : Nat → Bool) (i : Nat),
      Gate.applyNat (shiftGate b g) f i
        = if b ≤ i then Gate.applyNat g (fun j => f (j + b)) (i - b) else f i := by
  induction g with
  | I =>
      intro f i; by_cases h : b ≤ i
      · simp only [shiftGate, Gate.applyNat, if_pos h, Nat.sub_add_cancel h]
      · simp only [shiftGate, Gate.applyNat, if_neg h]
  | X q =>
      intro f i
      simp only [shiftGate, Gate.applyNat, update_apply]
      by_cases h : b ≤ i
      · rw [if_pos h]
        by_cases hi : i = q + b
        · subst hi; simp
        · rw [if_neg hi, if_neg (show ¬ i - b = q by omega), Nat.sub_add_cancel h]
      · rw [if_neg h, if_neg (show ¬ i = q + b by omega)]
  | CX c t =>
      intro f i
      simp only [shiftGate, Gate.applyNat, update_apply]
      by_cases h : b ≤ i
      · rw [if_pos h]
        by_cases hi : i = t + b
        · subst hi; simp
        · rw [if_neg hi, if_neg (show ¬ i - b = t by omega), Nat.sub_add_cancel h]
      · rw [if_neg h, if_neg (show ¬ i = t + b by omega)]
  | CCX a c d =>
      intro f i
      simp only [shiftGate, Gate.applyNat, update_apply]
      by_cases h : b ≤ i
      · rw [if_pos h]
        by_cases hi : i = d + b
        · subst hi; simp
        · rw [if_neg hi, if_neg (show ¬ i - b = d by omega), Nat.sub_add_cancel h]
      · rw [if_neg h, if_neg (show ¬ i = d + b by omega)]
  | seq g₁ g₂ ih₁ ih₂ =>
      intro f i
      simp only [shiftGate, Gate.applyNat]
      rw [ih₂ (Gate.applyNat (shiftGate b g₁) f) i]
      by_cases h : b ≤ i
      · rw [if_pos h, if_pos h]
        have hAB : (fun j => Gate.applyNat (shiftGate b g₁) f (j + b))
            = Gate.applyNat g₁ (fun k => f (k + b)) := by
          funext j; rw [ih₁ f (j + b), if_pos (Nat.le_add_left b j), Nat.add_sub_cancel]
        rw [hAB]
      · rw [if_neg h, if_neg h, ih₁ f i, if_neg h]

/-- **Left disjointness frame.**  The base-`b`-shifted gate fixes every qubit strictly below `b`. -/
theorem shiftGate_frame (b : Nat) (g : Gate) (f : Nat → Bool) (i : Nat) (hi : i < b) :
    Gate.applyNat (shiftGate b g) f i = f i := by
  rw [applyNat_shiftGate b g f i, if_neg (by omega)]

/-- The shifted gate, read at a shifted index, is the down-shifted action — the clean corollary the
    multi-register fold consumes. -/
theorem applyNat_shiftGate_at (b : Nat) (g : Gate) (f : Nat → Bool) (i : Nat) :
    Gate.applyNat (shiftGate b g) f (i + b) = Gate.applyNat g (fun j => f (j + b)) i := by
  rw [applyNat_shiftGate b g f (i + b), if_pos (by omega), Nat.add_sub_cancel]

/-- **Input locality.**  A `dim`-well-typed gate's action on every qubit `< dim` depends ONLY on the
    input restricted to `[0, dim)` — it never reads or writes outside its declared register.  Proven
    by induction over the `Gate` IR, using that `WellTyped` bounds every qubit index by `dim`.  This is
    what lets a circuit placed in a wider register (the CFS multi-register fold) be reasoned about from
    its own block alone, even though the surrounding qubits hold other registers' data. -/
theorem applyNat_congr_lt (dim : Nat) :
    ∀ (g : Gate), Gate.WellTyped dim g → ∀ (f f' : Nat → Bool),
      (∀ p, p < dim → f p = f' p) → ∀ q, q < dim → Gate.applyNat g f q = Gate.applyNat g f' q := by
  intro g
  induction g with
  | I => intro _ f f' hff q hq; exact hff q hq
  | X a =>
      intro hwt f f' hff q hq
      have ha : a < dim := hwt
      simp only [Gate.applyNat, update_apply]
      by_cases h : q = a
      · rw [if_pos h, if_pos h, hff a ha]
      · rw [if_neg h, if_neg h]; exact hff q hq
  | CX a b =>
      intro hwt f f' hff q hq
      obtain ⟨ha, hb, _⟩ := hwt
      simp only [Gate.applyNat, update_apply]
      by_cases h : q = b
      · rw [if_pos h, if_pos h, hff b hb, hff a ha]
      · rw [if_neg h, if_neg h]; exact hff q hq
  | CCX a b c =>
      intro hwt f f' hff q hq
      obtain ⟨ha, hb, hc, _, _, _⟩ := hwt
      simp only [Gate.applyNat, update_apply]
      by_cases h : q = c
      · rw [if_pos h, if_pos h, hff c hc, hff a ha, hff b hb]
      · rw [if_neg h, if_neg h]; exact hff q hq
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hwt f f' hff q hq
      obtain ⟨hwt1, hwt2⟩ := hwt
      simp only [Gate.applyNat]
      exact ih₂ hwt2 (Gate.applyNat g₁ f) (Gate.applyNat g₁ f')
        (fun p hp => ih₁ hwt1 f f' hff p hp) q hq

end FormalRV.Arithmetic
