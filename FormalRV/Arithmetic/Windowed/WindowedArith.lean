/-
  FormalRV.Shor.WindowedArith — Phase D, the parametric windowed-arithmetic core.

  Gidney's windowed multiplication (arXiv:1905.07682) computes `k · x` by splitting
  `x` into `w`-bit windows and, for each window, looking up `k · windowⱼ(x)` from a
  precomputed table and adding it shifted by `j·w`.  The reason this computes the
  right product is the base-`2^w` (windowed) digit expansion — pure number theory,
  independent of the QROM gate realization:

      x = Σⱼ windowⱼ(x) · (2^w)^j,     windowⱼ(x) = (x / (2^w)^j) % 2^w   (x < (2^w)^n)

  hence  k · x = Σⱼ (k · windowⱼ(x)) · (2^w)^j.

  This file proves both (parametric in window size `w` and window count `n`),
  generalizing the hard-wired `windowSize = 2` model in `WindowedShorConnection`.
  Kernel-clean.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace FormalRV.Shor.WindowedArith

open scoped BigOperators

/-- The `j`-th width-`w` window (base-`2^w` digit) of `x`. -/
def window (w x j : Nat) : Nat := (x / (2 ^ w) ^ j) % 2 ^ w

/-- **Windowed digit expansion.**  Any `x < (2^w)^n` is the sum of its `n` width-`w`
    windows, each weighted by `(2^w)^j`.  (The base-`2^w` positional expansion.) -/
theorem windowed_expansion (w : Nat) :
    ∀ (n x : Nat), x < (2 ^ w) ^ n →
      x = ∑ j ∈ Finset.range n, window w x j * (2 ^ w) ^ j
  | 0, x, hx => by
      simp only [pow_zero, Nat.lt_one_iff] at hx
      simp [hx]
  | n + 1, x, hx => by
    have hb1 : 0 < 2 ^ w := by positivity
    have hxb : x / 2 ^ w < (2 ^ w) ^ n := by
      rw [Nat.div_lt_iff_lt_mul hb1]
      calc x < (2 ^ w) ^ (n + 1) := hx
        _ = (2 ^ w) ^ n * 2 ^ w := by rw [pow_succ]
    have ih := windowed_expansion w n (x / 2 ^ w) hxb
    rw [Finset.sum_range_succ']
    have hsum : ∑ j ∈ Finset.range n, window w x (j + 1) * (2 ^ w) ^ (j + 1)
        = 2 ^ w * (x / 2 ^ w) := by
      rw [ih, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hdiv : x / (2 ^ w) ^ (j + 1) = (x / 2 ^ w) / (2 ^ w) ^ j := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      simp only [window, hdiv]
      rw [pow_succ]
      ring
    have h0 : window w x 0 * (2 ^ w) ^ 0 = x % 2 ^ w := by
      simp only [window, pow_zero, Nat.div_one, mul_one]
    rw [hsum, h0]
    exact (Nat.div_add_mod x (2 ^ w)).symm

/-- **Windowed multiplication identity.**  Multiplying by `k` distributes over the
    windowed expansion: `k · x = Σⱼ (k · windowⱼ(x)) · (2^w)^j`.  Each summand
    `k · windowⱼ(x)` is exactly the value the QROM table provides at window `j`. -/
theorem windowed_mul (w n k x : Nat) (hx : x < (2 ^ w) ^ n) :
    k * x = ∑ j ∈ Finset.range n, (k * window w x j) * (2 ^ w) ^ j := by
  conv_lhs => rw [windowed_expansion w n x hx]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Each window is a `w`-bit value (`< 2^w`): the lookup address space. -/
theorem window_lt (w x j : Nat) : window w x j < 2 ^ w :=
  Nat.mod_lt _ (Nat.two_pow_pos w)

/-! ### The `c_exp` level: exponentiation windowing (arbitrary exponent window).

Everything above (`window`, `windowed_mul`, `windowed_modProductAdd`) is parametric in
the window size `w` — set `w := c_mul` for the multiplication level.  The *exponentiation*
level windows the exponent into `c_exp`-bit windows; because the exponent appears in an
exponent, the decomposition is MULTIPLICATIVE (a product of partial multiplicands), the
exact analogue of `windowed_mul`.  Both levels are arbitrary-window. -/

/-- **`c_exp` exponentiation windowing (arbitrary `c_exp`), proved.**  `g^e` factors over
    the `c_exp`-bit windows of `e`: each window `i` contributes the partial multiplicand
    `g^{windowᵢ(e) · 2^{i·c_exp}}` — exactly the value looked up for that exponent window
    (8-hours `main.tex:581`).  Multiplicative analogue of `windowed_mul`. -/
theorem windowed_exp (cexp n g e : Nat) (he : e < (2 ^ cexp) ^ n) :
    g ^ e = ∏ i ∈ Finset.range n, g ^ (window cexp e i * (2 ^ cexp) ^ i) := by
  conv_lhs => rw [windowed_expansion cexp n e he]
  exact (Finset.prod_pow_eq_pow_sum _ _ _).symm

/-- The modular form: multiplying the per-exponent-window partial multiplicands
    (each reduced mod `N`) computes `g^e mod N` — the windowed modular exponentiation. -/
theorem windowed_exp_modProduct (cexp n g N e : Nat) (he : e < (2 ^ cexp) ^ n) :
    (∏ i ∈ Finset.range n, g ^ (window cexp e i * (2 ^ cexp) ^ i) % N) % N = g ^ e % N := by
  rw [← Finset.prod_nat_mod, ← windowed_exp cexp n g e he]

/-- The QROM table entry for window `j` of the modular product-add `acc += a·y mod N`
    (Gidney 1905.07682 l.408–411; matches `VerifiedShor.tableValue`): the value
    `a · 2^{jw} · v` reduced mod `N`, looked up at address `v = windowⱼ(y)`. -/
def tableValue (a N w j v : Nat) : Nat := (a * (2 ^ w) ^ j * v) % N

/-- **Windowed modular product-addition (parametric `w`), proved.**  Summing the
    per-window table lookups and reducing mod `N` computes `a·y mod N` — the
    correctness of the windowed multiplier, generalizing the hard-wired `w = 2`
    model.  (Gidney 1905.07682 l.296: the windowed `x += k·y`.) -/
theorem windowed_modProductAdd (w n a N y : Nat) (hy : y < (2 ^ w) ^ n) :
    (∑ j ∈ Finset.range n, tableValue a N w j (window w y j)) % N = (a * y) % N := by
  simp only [tableValue]
  rw [← Finset.sum_nat_mod]
  congr 1
  rw [windowed_mul w n a y hy]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- With a running accumulator: the windowed lookup-add nets `(acc + a·y) mod N`. -/
theorem windowed_modProductAdd_acc (w n a N y acc : Nat) (hy : y < (2 ^ w) ^ n) :
    (acc + ∑ j ∈ Finset.range n, tableValue a N w j (window w y j)) % N
      = (acc + a * y) % N := by
  rw [Nat.add_mod, windowed_modProductAdd w n a N y hy, ← Nat.add_mod]

/-- The **circuit-aligned fold**: process windows one at a time, each window doing a
    modular lookup-add `acc ← (acc + tableValueⱼ) mod N`.  This is exactly the
    accumulator update the multi-window lookup-add circuit produces (one
    `lookupAddGate` per window, mod-reducing after each), so its value-correctness
    transfers to the Boolean circuit layer. -/
def windowedLookupFold (a N w : Nat) (val : Nat → Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => (windowedLookupFold a N w val n acc + tableValue a N w n (val n)) % N

/-- The fold (per-step mod-add) agrees with the sum-then-mod form. -/
theorem windowedLookupFold_eq (a N w : Nat) (val : Nat → Nat) (acc : Nat) (hacc : acc < N) :
    ∀ n, windowedLookupFold a N w val n acc
        = (acc + ∑ j ∈ Finset.range n, tableValue a N w j (val j)) % N := by
  intro n
  induction n with
  | zero => simp [windowedLookupFold, Nat.mod_eq_of_lt hacc]
  | succ m ih =>
    rw [windowedLookupFold, ih, Finset.sum_range_succ,
        show acc + (∑ j ∈ Finset.range m, tableValue a N w j (val j)
              + tableValue a N w m (val m))
          = (acc + ∑ j ∈ Finset.range m, tableValue a N w j (val j))
              + tableValue a N w m (val m) by ring]
    exact (Nat.mod_modEq _ N).add_right _

/-- **Phase-D windowed-multiplier value-correctness (parametric `w`), proved.**
    Folding modular lookup-adds over the `n` windows of `y` computes `(acc + a·y) mod N`. -/
theorem windowedLookupFold_modProductAdd (a N w n y acc : Nat) (hacc : acc < N)
    (hy : y < (2 ^ w) ^ n) :
    windowedLookupFold a N w (window w y) n acc = (acc + a * y) % N := by
  rw [windowedLookupFold_eq a N w (window w y) acc hacc n,
      windowed_modProductAdd_acc w n a N y acc hy]

/-- **Interface to the Shor oracle contract `MultiplyCircuitProperty`.**  Starting from
    a zero accumulator, the windowed multiplier computes exactly `(a·x) mod N` — the
    value `MultiplyCircuitProperty a N` requires of a modular-multiplication oracle.
    So the parametric windowed circuit produces the SAME modmul value the existing
    `ModMulImpl`/`VerifiedModMulFamily` interface consumes (lifted to `uc_eval` via the
    `Gate → BaseUCom` basis-action adapter). -/
theorem windowedLookupFold_eq_modmul (a N w n x : Nat) (hN : 0 < N) (hx : x < (2 ^ w) ^ n) :
    windowedLookupFold a N w (window w x) n 0 = (a * x) % N := by
  rw [windowedLookupFold_modProductAdd a N w n x 0 hN hx, Nat.zero_add]

/-! ## c_exp: folding exponent bits into the lookup address.

The second windowing level (`c_exp`, 8-hours `main.tex:581–583`; 1905.07682 l.467–493)
makes the multiplicand itself looked-up: the lookup address concatenates an exponent
window `ei` (high bits) with a factor window `mi` (low bits), so the SAME lookup
primitive reads a 2-argument table `T[ei, mi]`.  The address split is elementary. -/

/-- **c_exp address concatenation (proved).**  An address built as `ei·2^{mWin} + mi`
    (exponent window in the high bits, factor window in the low bits) splits back into
    its two windows.  This is why one lookup over the concatenated address realizes the
    two-argument `c_exp` table — no new circuit, just a wider address. -/
theorem address_concat (mWin ei mi : Nat) (hmi : mi < 2 ^ mWin) :
    (ei * 2 ^ mWin + mi) / 2 ^ mWin = ei ∧ (ei * 2 ^ mWin + mi) % 2 ^ mWin = mi := by
  have hc : 0 < 2 ^ mWin := Nat.two_pow_pos mWin
  rw [show ei * 2 ^ mWin + mi = mi + 2 ^ mWin * ei by ring]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt hmi, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmi]

/-- Modular exponentiation `g^e mod N` (the value the windowed exponentiation targets). -/
def modPow (g e N : Nat) : Nat := g ^ e % N

/-- **Named obligation — Gidney 1905.07682 l.502** ("we have tested that the above code
    returns the correct result in randomly chosen cases").  A value map `windowedExp`
    realizes windowed modular EXPONENTIATION when, on input `x` and exponent `e`, it
    yields `(x · g^e) mod N`.  The single exponent-window multiply-add is now
    PROVEN at the Gate level (`expWindowPassOf_correct`, `WindowedExpStep.lean` —
    adder-generic, via the concatenated exp‖mul lookup address); what this named
    obligation still tracks is the GLOBAL composition over all `n_e/c_exp`
    windows (per-pass accumulator hand-off + inverse-clear + swap), the
    empirically-validated fact of Gidney l.502. -/
def WindowedExpCorrect (windowedExp : Nat → Nat → Nat) (g N : Nat) : Prop :=
  ∀ e x, windowedExp e x = (x * modPow g e N) % N

end FormalRV.Shor.WindowedArith
