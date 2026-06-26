/- E2RunwayDivider — Â§5-5c decode spec + input encoding + value-split bridge.  Part of the `E2RunwayDivider` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider.Divider

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
  (compareConstXor_state_general condSub_state_general)


/-! ## §5. The DECODE specification (target deliverable), with the inductive
    invariant, base case, and the step reduced to `divStep_decode`.

  INPUT.  The support representative `v = z + j·N`, `z < N`, `j < 2^cm`,
  `2^cm·N ≤ 2^bits`, encoded as the running value in the DATA band
  (Cuccaro target register at `q_start = 0`), clean read/carry/flag/quotient.

  OUTPUT (the decode the brief asks for).
    • DATA band  → `z = v % N`           (read by `cuccaro_target_val bits 0`),
    • QUOTIENT band wire `qBase bits + k` → bit `k` of `j = v / N`, k ∈ [0,cm),
    • TRANSIENT workspace (read band, carry, flag) → clean (false).

  STATUS.  The arithmetic spec is `v = z + j·N, z < N ⇒ v/N = j ∧ v%N = z`
  (`divModN_arith`, proved).  The circuit-to-spec bridge is the cm-step induction
  whose invariant / base case / step are stated below; the step is reduced to the
  proven `divStep_decode`.  The REMAINING blocker is the bit-window lemma relating
  the windowed divstep's local target value `⌊running/2^k⌋ mod 2^(bits−k)` to the
  global running value (see `divModN_decode` and the note at the bottom). -/

/-- **Division arithmetic (proved).**  `v = z + j·N` with `z < N` ⇒
    `v / N = j` and `v % N = z`. -/
theorem divModN_arith (N z j : Nat) (hN : 0 < N) (hz : z < N) :
    (z + j * N) / N = j ∧ (z + j * N) % N = z := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_right z j hN, Nat.div_eq_of_lt hz, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]

/-! ### §5a. Input encoding + base case. -/

/-- The clean input state: running value `v` in the DATA band (Cuccaro target,
    `q_start = 0`), everything else (carry, read band, flag, quotient band) clean. -/
def encDiv (bits v : Nat) : Nat → Bool :=
  fun q =>
    if q = 0 then false                                  -- carry-in
    else if q % 2 = 1 ∧ q < 2 * bits + 1 then v.testBit ((q - 1) / 2)  -- data band
    else false                                           -- read band / flag / quotient / above

theorem encDiv_data (bits v i : Nat) (hi : i < bits) :
    encDiv bits v (0 + 2 * i + 1) = v.testBit i := by
  unfold encDiv
  have h1 : ¬ (0 + 2 * i + 1 = 0) := by omega
  have h2 : (0 + 2 * i + 1) % 2 = 1 := by omega
  have h3 : 0 + 2 * i + 1 < 2 * bits + 1 := by omega
  rw [if_neg h1, if_pos ⟨h2, h3⟩]
  congr 1; omega

theorem encDiv_read (bits v i : Nat) (_hi : i < bits) :
    encDiv bits v (0 + 2 * i + 2) = false := by
  unfold encDiv
  have h1 : ¬ (0 + 2 * i + 2 = 0) := by omega
  have h2 : (0 + 2 * i + 2) % 2 ≠ 1 := by omega
  rw [if_neg h1, if_neg (by tauto)]

theorem encDiv_cin (bits v : Nat) : encDiv bits v 0 = false := by unfold encDiv; simp

theorem encDiv_flag (bits v : Nat) : encDiv bits v (flagW bits) = false := by
  unfold encDiv flagW
  have h1 : ¬ (2 * bits + 1 = 0) := by omega
  rw [if_neg h1, if_neg (by omega)]

theorem encDiv_qbit (bits v k : Nat) : encDiv bits v (qBase bits + k) = false := by
  unfold encDiv qBase
  have h1 : ¬ (2 * bits + 2 + k = 0) := by omega
  rw [if_neg h1, if_neg (by omega)]

/-- The data-band decode of the clean input is `v` (for `v < 2^bits`). -/
theorem cuccaro_target_val_encDiv (bits v : Nat) (hv : v < 2 ^ bits) :
    cuccaro_target_val bits 0 (encDiv bits v) = v := by
  rw [cuccaro_target_val_eq_sum_when_bits_match bits 0 v (encDiv bits v)
        (fun i hi => by rw [encDiv_data bits v i hi])]
  exact Nat.mod_eq_of_lt hv

/-- **BASE CASE (`cm = 0`).**  The divider is the identity; the data band still
    decodes to `v` and there is no quotient band.  (`v / N = 0`, `v % N = v` when
    `v < N`, matching `divModN_arith` at `j = 0`.) -/
theorem divModN_decode_base (bits N v : Nat) (hv : v < 2 ^ bits) :
    Gate.applyNat (divModN bits 0 N) (encDiv bits v) = encDiv bits v
    ∧ cuccaro_target_val bits 0
        (Gate.applyNat (divModN bits 0 N) (encDiv bits v)) = v := by
  have hI : divModN bits 0 N = Gate.I := rfl
  rw [hI]
  exact ⟨rfl, cuccaro_target_val_encDiv bits v hv⟩

/-! ### §5b. The full decode goal (general cm) and the step reduction.

  The headline deliverable (general `cm`).  On the support `v = z + j·N`
  (`z < N`, `j < 2^cm`, `2^cm·N ≤ 2^bits`):

      cuccaro_target_val bits 0 (applyNat (divModN bits cm N) (encDiv bits v)) = v % N = z
    ∧ (∀ k < cm, applyNat (divModN bits cm N) (encDiv bits v) (qBase bits + k)
                  = (v / N).testBit k)        -- = j.testBit k
    ∧ (transient workspace — carry/read/flag — clean)
    ∧ Gate.WellTyped (dimDiv bits cm) (divModN bits cm N)   -- ✓ divModN_wellTyped

  The WellTyped conjunct is `divModN_wellTyped`.  The value conjuncts follow from
  the cm-step INDUCTION whose step is one `divStep_decode`; the remaining blocker
  is the bit-window arithmetic linking the windowed divstep's local view to the
  global running value (see `divModN_step_reduces` and the BLOCKER note). -/

/-- **STEP REDUCTION (the inductive step, reduced to `divStep_decode`).**
    The `(cm+1)`-step divider is the `cm`-step divider followed by the TOP step
    `divStepAt bits N cm` (the descending fold processes `k = cm` first).  Hence
    any decode statement for `divModN bits (cm+1) N` reduces, via
    `Gate.applyNat_seq`, to applying `divStep_decode` (on the width-`(bits−cm)`
    window at base `2·cm`) to the output of `divModN bits cm N`.

    This lemma exhibits the reduction structurally; closing the induction needs the
    window/global-value bridge described in the BLOCKER note. -/
theorem divModN_succ_eq (bits cm N : Nat) :
    divModN bits (cm + 1) N
      = Gate.seq (divStepAt bits N cm) (divModN bits cm N) := rfl

/-! ### §5c. The window/global value-split bridge (the crux for the induction). -/

/-- Definitional succ-equation for the target decoder. -/
theorem cuccaro_target_val_succ (n q : Nat) (f : Nat → Bool) :
    cuccaro_target_val (n + 1) q f
      = cuccaro_target_val n q f + (if f (q + 2 * n + 1) then 2 ^ n else 0) := rfl

/-- **Value split (proved).**  The global data-band value splits at any `k ≤ bits`
    into the low `k` bits and `2^k ·` (the window value at base `2k`, width `bits−k`):
        `cuccaro_target_val bits 0 f`
          = `cuccaro_target_val k 0 f + 2^k · cuccaro_target_val (bits−k) (2·k) f`.
    Both sub-decoders read the SAME wires (`0+2i+1`) as the global one; the window
    at base `2k` reads `2k+2i+1 = 0+2(k+i)+1`.  Proved by induction on `bits − k`. -/
theorem cuccaro_target_val_split (bits k : Nat) (f : Nat → Bool) (hk : k ≤ bits) :
    cuccaro_target_val bits 0 f
      = cuccaro_target_val k 0 f
        + 2 ^ k * cuccaro_target_val (bits - k) (2 * k) f := by
  induction bits with
  | zero =>
    have : k = 0 := by omega
    subst this; simp [cuccaro_target_val]
  | succ b ih =>
    rcases Nat.lt_or_ge k (b + 1) with hlt | hge
    · -- k ≤ b : peel the top bit `b` off the global decoder; it belongs to the window.
      have hkb : k ≤ b := by omega
      have ihb := ih hkb
      -- Peel the global decoder's top bit.
      rw [cuccaro_target_val_succ b 0 f, ihb]
      -- RHS window: (b+1)-k = (b-k)+1, peel its top.
      have hwin : b + 1 - k = (b - k) + 1 := by omega
      rw [hwin, cuccaro_target_val_succ (b - k) (2 * k) f]
      have hpos : 2 * k + 2 * (b - k) + 1 = 0 + 2 * b + 1 := by omega
      rw [hpos, Nat.mul_add, ← Nat.add_assoc]
      congr 1
      by_cases hfb : f (0 + 2 * b + 1)
      · simp only [hfb, if_true]
        rw [← pow_add]; congr 2; omega
      · simp only [hfb, Bool.false_eq_true, if_false, Nat.mul_zero]
    · -- k = b+1 : the window is empty, low part is everything.
      have hkb : k = b + 1 := by omega
      subst hkb
      rw [Nat.sub_self]
      simp [cuccaro_target_val]

/-- Low-`k`-bits decoder is `< 2^k`. -/
theorem cuccaro_target_val_lt' (k q : Nat) (f : Nat → Bool) :
    cuccaro_target_val k q f < 2 ^ k := cuccaro_target_val_lt k q f

/-- **Window value of the clean input = `v / 2^k`** (for `v < 2^bits`, `k ≤ bits`).
    The window at base `2k` reads global bits `k…bits−1`, i.e. `⌊v / 2^k⌋`.
    From the value split + the low part `< 2^k`. -/
theorem window_val_encDiv (bits v k : Nat) (hv : v < 2 ^ bits) (hk : k ≤ bits) :
    cuccaro_target_val (bits - k) (2 * k) (encDiv bits v) = v / 2 ^ k := by
  have hsplit := cuccaro_target_val_split bits k (encDiv bits v) hk
  rw [cuccaro_target_val_encDiv bits v hv] at hsplit
  -- v = low + 2^k * window, low < 2^k  ⇒  window = v / 2^k.
  set low := cuccaro_target_val k 0 (encDiv bits v) with hlow
  set win := cuccaro_target_val (bits - k) (2 * k) (encDiv bits v) with hwin
  have hlow_lt : low < 2 ^ k := cuccaro_target_val_lt k 0 (encDiv bits v)
  -- from v = low + 2^k * win
  rw [hsplit, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ k),
      Nat.div_eq_of_lt hlow_lt, Nat.zero_add]


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
