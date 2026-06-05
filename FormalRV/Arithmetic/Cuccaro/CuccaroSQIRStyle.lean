/-
  FormalRV.BQAlgo.CuccaroSQIRStyle — SQIR-style compute-CNOT-uncompute
  comparator candidate.

  Tick 49 / Recovery of SQIR/RCIR exact-budget construction.

  CRITICAL DISCOVERY (Tick 49 source inspection of
  `SQIR/examples/shor/ModMult.v`):
  - **SQIR's actual `modmult_rev_anc n = 3 * n + 11`** (line 72 of
    `ModMult.v`), NOT `2 * n + 1` as the Lean placeholder in
    `SQIRPort/Shor.lean:4563` claims.
  - The Lean comment at line 4560-4562 incorrectly says "the specific
    RCIR implementation in Coq uses a similar linear-in-n count" —
    the actual SQIR value is `3n + 11`, with `3` non-overlapping
    n-bit registers + 2 designated flag bits at positions 0 and 1
    + additional scratch.

  Consequence: the "exact-budget" framing in Ticks 41-48 was based on
  a too-tight Lean placeholder. The real SQIR budget gives substantial
  room for a designated flag qubit.

  SQIR's comparator01 (ModMult.v line 121-124):
  ```
  comparator01 n := (bcx 0; negator0 n); highb01 n; bcinv (bcx 0; negator0 n).
  highb01 n := MAJseq n; bccnot (1 + n) 1; bcinv (MAJseq n).
  ```
  - Position 1 is the designated FLAG bit.
  - `bccnot (1 + n) 1`: CNOT from the top carry (at position `1 + n`)
    to the flag (position 1).
  - The compute-CNOT-uncompute pattern: MAJseq forward, copy carry to
    flag, MAJseq reverse.

  This file ports the compute-CNOT-uncompute structure to our Cuccaro
  Gate IR.  We:
  - Define `cuccaro_MAJ_inv` (the gate-level inverse of MAJ).
  - Define `cuccaro_maj_chain_inv` (the chain-level inverse).
  - Prove the local MAJ inverse identity: `MAJ ; MAJ_inv = id`.
  - Define `sqir_style_compareConst_candidate` matching SQIR's pattern,
    parameterized over an explicit flag qubit position `flagPos`.
  - Prove WellTyped (assuming `flagPos < dim`).
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroCompare
import FormalRV.Shor.MainAlgorithm

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Inverse MAJ at the gate level. -/

/-- **Inverse of the Cuccaro MAJ gate.**  Since each component
gate (CX, CCX) is self-inverse, the inverse is the reversed sequence. -/
def cuccaro_MAJ_inv (a b c : Nat) : Gate :=
  seq (CCX a b c) (seq (CX c a) (CX c b))

/-! ## Inverse MAJ chain.

The chain inverse processes the same MAJ gates in reverse order. The
recursion: `cuccaro_maj_chain_inv (n+1) q_start` first applies the
inverse sub-chain on the suffix `q_start + 2`, then `cuccaro_MAJ_inv`
at `q_start`. -/

/-- **Inverse of the n-step Cuccaro MAJ chain.** -/
def cuccaro_maj_chain_inv : Nat → Nat → Gate
  | 0,     _       => I
  | n + 1, q_start =>
      seq (cuccaro_maj_chain_inv n (q_start + 2))
          (cuccaro_MAJ_inv q_start (q_start + 1) (q_start + 2))

/-! ## WellTyped for the inverses. -/

theorem cuccaro_MAJ_inv_wellTyped
    (dim a b c : Nat) (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) :
    Gate.WellTyped dim (cuccaro_MAJ_inv a b c) := by
  refine ⟨⟨ha, hb, hc, h_ab, h_ac, h_bc⟩, ⟨hc, ha, ?_⟩, ⟨hc, hb, ?_⟩⟩
  · exact fun h => h_ac h.symm
  · exact fun h => h_bc h.symm

theorem cuccaro_maj_chain_inv_wellTyped
    (n q_start dim : Nat) (h : q_start + 2 * n + 1 ≤ dim) :
    Gate.WellTyped dim (cuccaro_maj_chain_inv n q_start) := by
  induction n generalizing q_start with
  | zero =>
    show Gate.WellTyped dim Gate.I
    show 0 < dim
    omega
  | succ k ih =>
    show Gate.WellTyped dim
        (seq (cuccaro_maj_chain_inv k (q_start + 2))
              (cuccaro_MAJ_inv q_start (q_start + 1) (q_start + 2)))
    refine ⟨?_, ?_⟩
    · exact ih (q_start + 2) (by omega)
    · apply cuccaro_MAJ_inv_wellTyped
      all_goals omega

/-! ## Tick 50 — SQIR-faithful ancilla count. -/

/-- **SQIR-faithful ancilla count** (Coq `ModMult.v` line 72).
SQIR uses `3 * n + 11` ancilla qubits for `modmult_rev`, NOT the
`2 * n + 1` Lean placeholder.  We expose this separately to avoid
silently patching the Lean placeholder while still making the real
SQIR value available for parallel SQIR-faithful Lean development. -/
def sqir_modmult_rev_anc (n : Nat) : Nat := 3 * n + 11

/-- Total dimension under SQIR-faithful ancilla count: `4 * n + 11`. -/
theorem sqir_modmult_total_dim (n : Nat) :
    n + sqir_modmult_rev_anc n = 4 * n + 11 := by
  unfold sqir_modmult_rev_anc
  omega

/-- Arithmetic gap between Lean placeholder and SQIR source.
The placeholder undercounts ancilla by `n + 10`. -/
theorem sqir_modmult_anc_diff_from_lean_placeholder (n : Nat) :
    sqir_modmult_rev_anc n
      = FormalRV.SQIRPort.modmult_rev_anc n + (n + 10) := by
  unfold sqir_modmult_rev_anc FormalRV.SQIRPort.modmult_rev_anc
  omega

/-! ## Tick 50 — Local at-position semantics for `cuccaro_MAJ_inv`.

Analogous to the Tick 41 `cuccaro_MAJ_at_*` lemmas for `cuccaro_MAJ`. -/

/-- **MAJ_inv at the `a` wire.**  Composes CCX, CX c a, CX c b
left-to-right; at position a only the CX c a step writes a new value. -/
theorem cuccaro_MAJ_inv_at_a
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_MAJ_inv a b c) f a
      = xor (f a) (xor (f c) (f a && f b)) := by
  unfold cuccaro_MAJ_inv
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [h_ab, h_ac, h_bc, h_ab.symm, h_ac.symm, h_bc.symm]

/-- **MAJ_inv at the `b` wire.** -/
theorem cuccaro_MAJ_inv_at_b
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_MAJ_inv a b c) f b
      = xor (f b) (xor (f c) (f a && f b)) := by
  unfold cuccaro_MAJ_inv
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [h_ab, h_ac, h_bc, h_ab.symm, h_ac.symm, h_bc.symm]

/-- **MAJ_inv at the `c` wire.**  Only the first CCX writes here. -/
theorem cuccaro_MAJ_inv_at_c
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_MAJ_inv a b c) f c
      = xor (f c) (f a && f b) := by
  unfold cuccaro_MAJ_inv
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [h_ab, h_ac, h_bc, h_ab.symm, h_ac.symm, h_bc.symm]

/-- **MAJ_inv at any unrelated wire.** -/
theorem cuccaro_MAJ_inv_at_other
    (a b c q : Nat) (h_qa : q ≠ a) (h_qb : q ≠ b) (h_qc : q ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_MAJ_inv a b c) f q = f q := by
  unfold cuccaro_MAJ_inv
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [h_qa, h_qb, h_qc]

/-! ## Tick 50 — Local inverse identity: MAJ ; MAJ_inv = identity. -/

/-- **Local inverse identity** (per position).  Applying MAJ followed by
MAJ_inv to a state restores the original at every position. -/
theorem cuccaro_MAJ_followed_by_MAJ_inv_eq_id
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c)
    (f : Nat → Bool) (q : Nat) :
    Gate.applyNat (seq (cuccaro_MAJ a b c) (cuccaro_MAJ_inv a b c)) f q = f q := by
  simp only [Gate.applyNat_seq]
  -- Let G = applyNat (cuccaro_MAJ a b c) f.  Case-split on q's position.
  by_cases hqa : q = a
  · rw [hqa]
    rw [cuccaro_MAJ_inv_at_a a b c h_ab h_ac h_bc]
    rw [cuccaro_MAJ_at_a a b c h_ab h_ac h_bc f]
    rw [cuccaro_MAJ_at_b a b c h_ab h_ac h_bc f]
    rw [cuccaro_MAJ_at_c a b c h_ab h_ac h_bc f]
    unfold Boolean.majority
    cases f a <;> cases f b <;> cases f c <;> rfl
  · by_cases hqb : q = b
    · rw [hqb]
      rw [cuccaro_MAJ_inv_at_b a b c h_ab h_ac h_bc]
      rw [cuccaro_MAJ_at_a a b c h_ab h_ac h_bc f]
      rw [cuccaro_MAJ_at_b a b c h_ab h_ac h_bc f]
      rw [cuccaro_MAJ_at_c a b c h_ab h_ac h_bc f]
      unfold Boolean.majority
      cases f a <;> cases f b <;> cases f c <;> rfl
    · by_cases hqc : q = c
      · rw [hqc]
        rw [cuccaro_MAJ_inv_at_c a b c h_ab h_ac h_bc]
        rw [cuccaro_MAJ_at_a a b c h_ab h_ac h_bc f]
        rw [cuccaro_MAJ_at_b a b c h_ab h_ac h_bc f]
        rw [cuccaro_MAJ_at_c a b c h_ab h_ac h_bc f]
        unfold Boolean.majority
        cases f a <;> cases f b <;> cases f c <;> rfl
      · rw [cuccaro_MAJ_inv_at_other a b c q hqa hqb hqc]
        exact cuccaro_MAJ_at_other a b c q hqa hqb hqc f

/-! ## Tick 50 — Chain-level inverse identity.

By induction on n, applying the n-step MAJ chain followed by its
inverse is the identity at every position. -/

/-- **Chain inverse identity (function-level).**  Applying the chain
followed by its inverse to any state returns the original state. -/
theorem cuccaro_maj_chain_inv_after_chain_eq_id
    (n q_start : Nat) (g : Nat → Bool) :
    Gate.applyNat (cuccaro_maj_chain_inv n q_start)
        (Gate.applyNat (cuccaro_maj_chain n q_start) g) = g := by
  induction n generalizing q_start g with
  | zero => rfl
  | succ k ih =>
    -- Unfold: chain (k+1) = seq MAJ_0 sub_chain_k.
    -- chain_inv (k+1) = seq sub_chain_inv_k MAJ_0_inv.
    -- composition: applyNat MAJ_0_inv (applyNat sub_chain_inv_k
    --   (applyNat sub_chain_k (applyNat MAJ_0 g))) = g.
    show Gate.applyNat (cuccaro_MAJ_inv q_start (q_start + 1) (q_start + 2))
         (Gate.applyNat (cuccaro_maj_chain_inv k (q_start + 2))
          (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
           (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) g))) = g
    -- Apply IH to the inner pair (substitution at function level).
    rw [ih (q_start + 2) (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) g)]
    -- Now: applyNat MAJ_0_inv (applyNat MAJ_0 g) = g.
    funext q
    exact cuccaro_MAJ_followed_by_MAJ_inv_eq_id
            q_start (q_start + 1) (q_start + 2)
            (by omega) (by omega) (by omega) g q

/-- **Chain inverse identity** (per position).  Pointwise corollary. -/
theorem cuccaro_maj_chain_followed_by_inv_eq_id
    (n q_start : Nat) (f : Nat → Bool) (q : Nat) :
    Gate.applyNat
        (seq (cuccaro_maj_chain n q_start)
             (cuccaro_maj_chain_inv n q_start)) f q = f q := by
  show Gate.applyNat (cuccaro_maj_chain_inv n q_start)
        (Gate.applyNat (cuccaro_maj_chain n q_start) f) q = f q
  rw [cuccaro_maj_chain_inv_after_chain_eq_id n q_start f]

/-! ## SQIR-style compute-CNOT-uncompute comparator candidate.

The pattern (from SQIR's `comparator01` + `highb01`):
1. Prepare constant `K = 2^bits - N` in the read register.
2. Forward MAJ chain.
3. CNOT from top carry to designated flag qubit.
4. Inverse MAJ chain (undoes step 2's workspace modifications).
5. Unprepare constant (undoes step 1).

After this:
- All workspace positions q_start..q_start + 2*bits are restored to input.
- `flagPos` qubit's value is XOR'd with `decide (N ≤ x)`.

The flag qubit `flagPos` must be OUTSIDE the workspace range
`[q_start, q_start + 2*bits]`. -/

/-- **SQIR-style compare-constant candidate gate** with explicit flag
position.  Uses the compute-CNOT-uncompute pattern: workspace restored,
flag XOR'd with the comparison result. -/
def sqir_style_compareConst_candidate
    (bits q_start N flagPos : Nat) : Gate :=
  seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
      (seq (cuccaro_maj_chain bits q_start)
           (seq (Gate.CX (q_start + 2 * bits) flagPos)
                (seq (cuccaro_maj_chain_inv bits q_start)
                     (cuccaro_prepareConstRead bits q_start (2^bits - N)))))

/-- **WellTyped for the SQIR-style comparator candidate.**  Requires
both the workspace range `q_start + 2*bits + 1 ≤ dim` AND
`flagPos < dim`, plus `flagPos ≠ q_start + 2 * bits` (the CNOT's
controls and targets must differ). -/
theorem sqir_style_compareConst_candidate_wellTyped
    (bits q_start N flagPos dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_distinct : flagPos ≠ q_start + 2 * bits) :
    Gate.WellTyped dim
        (sqir_style_compareConst_candidate bits q_start N flagPos) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact cuccaro_prepareConstRead_wellTyped bits q_start (2^bits - N) dim h_workspace
  · exact cuccaro_maj_chain_wellTyped bits q_start dim h_workspace
  · refine ⟨?_, h_flag, ?_⟩
    · omega
    · exact fun h => h_distinct h.symm
  · exact cuccaro_maj_chain_inv_wellTyped bits q_start dim h_workspace
  · exact cuccaro_prepareConstRead_wellTyped bits q_start (2^bits - N) dim h_workspace

/-! ## Tick 51 — Frame lemmas for `cuccaro_maj_chain_inv`. -/

/-- The inverse MAJ chain doesn't touch positions strictly above its
support (i.e., `q ≥ q_start + 2*n + 1`). -/
theorem cuccaro_maj_chain_inv_frame_above
    (n q_start : Nat) (f : Nat → Bool) (q : Nat)
    (h : q_start + 2 * n + 1 ≤ q) :
    Gate.applyNat (cuccaro_maj_chain_inv n q_start) f q = f q := by
  induction n generalizing q_start f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_maj_chain_inv k (q_start + 2))
              (cuccaro_MAJ_inv q_start (q_start + 1) (q_start + 2))) f q = _
    simp only [Gate.applyNat_seq]
    rw [cuccaro_MAJ_inv_at_other q_start (q_start + 1) (q_start + 2) q
        (by omega) (by omega) (by omega)]
    apply ih
    omega

/-- The inverse MAJ chain doesn't touch positions strictly below its
support (i.e., `q < q_start`). -/
theorem cuccaro_maj_chain_inv_frame_below
    (n q_start : Nat) (f : Nat → Bool) (q : Nat) (h : q < q_start) :
    Gate.applyNat (cuccaro_maj_chain_inv n q_start) f q = f q := by
  induction n generalizing q_start f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_maj_chain_inv k (q_start + 2))
              (cuccaro_MAJ_inv q_start (q_start + 1) (q_start + 2))) f q = _
    simp only [Gate.applyNat_seq]
    rw [cuccaro_MAJ_inv_at_other q_start (q_start + 1) (q_start + 2) q
        (by omega) (by omega) (by omega)]
    apply ih
    omega

/-! ## Tick 51 — `cuccaro_input_F` outside b-register is false. -/

/-- For an input `cuccaro_input_F q_start false 0 x` with `x < 2^bits`,
all positions strictly above `q_start + 2*bits` evaluate to `false`. -/
theorem cuccaro_input_F_above_eq_false
    (q_start bits x q : Nat) (h_above : q_start + 2 * bits + 1 ≤ q) (hx : x < 2^bits) :
    cuccaro_input_F q_start false 0 x q = false := by
  unfold cuccaro_input_F
  have h1 : ¬ (q < q_start) := by omega
  rw [if_neg h1]
  -- i := q - q_start
  have hi : q - q_start ≥ 2 * bits + 1 := by omega
  have hi_ne : q - q_start ≠ 0 := by omega
  rw [if_neg hi_ne]
  by_cases hi_odd : (q - q_start) % 2 = 1
  · rw [if_pos hi_odd]
    -- x.testBit ((q - q_start - 1) / 2) where the index ≥ bits.
    apply Nat.testBit_lt_two_pow
    have h_idx : (q - q_start - 1) / 2 ≥ bits := by omega
    exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h_idx)
  · rw [if_neg hi_odd]
    simp [Nat.zero_testBit]

/-! ## Tick 51 — Flag theorem.

The SQIR-style candidate's output at `flagPos` equals
`decide (N ≤ x)`, when the input is `cuccaro_input_F q_start false 0 x`
and `flagPos > q_start + 2*bits`. -/

/-- **HEADLINE — flag-copy theorem.**  After running the SQIR-style
comparator candidate on the input encoding `cuccaro_input_F q_start
false 0 x`, the external flag qubit at `flagPos` holds
`decide (N ≤ x)`. -/
theorem sqir_style_compareConst_candidate_flag
    (bits q_start N x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x) flagPos
      = decide (N ≤ x) := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (cuccaro_prepareConstRead bits q_start (2^bits - N))))))
      (cuccaro_input_F q_start false 0 x) flagPos = _
  simp only [Gate.applyNat_seq]
  -- Push outer P (the last applied gate at flagPos doesn't touch).
  rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos
      (by intros j _ heq; omega)]
  -- Push Minv (frame_above at flagPos > q_start + 2*bits).
  rw [cuccaro_maj_chain_inv_frame_above bits q_start _ flagPos (by omega)]
  -- Apply CX at flagPos: applyNat (CX c t) g t = update g t (xor (g t) (g c)) t.
  simp only [Gate.applyNat_CX, update_eq]
  -- Now goal: xor (state at flagPos) (state at q_start + 2*bits) = decide (N ≤ x).
  -- Compute (state at flagPos) = false (frame chain).
  have h_flag_state : Gate.applyNat (cuccaro_maj_chain bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N))
          (cuccaro_input_F q_start false 0 x)) flagPos = false := by
    rw [cuccaro_maj_chain_frame_above bits q_start _ flagPos (by omega)]
    rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos
        (by intros j _ heq; omega)]
    exact cuccaro_input_F_above_eq_false q_start bits x flagPos h_flag_above hx
  rw [h_flag_state]
  simp only [Bool.false_xor]
  -- Now: state at q_start + 2*bits = decide (N ≤ x). This is the top carry.
  have h_carry := cuccaro_compareConstForward_top_carry
                    bits q_start N x hN_pos hN hx
  unfold cuccaro_compareConstForwardGate at h_carry
  simp only [Gate.applyNat_seq] at h_carry
  exact h_carry

/-! ## Tick 51 — Underflow polarity corollary. -/

/-- **Underflow polarity**: negation of the flag gives `decide (x < N)`. -/
theorem sqir_style_compareConst_candidate_underflow_flag
    (bits q_start N x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    !(Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x) flagPos)
      = decide (x < N) := by
  rw [sqir_style_compareConst_candidate_flag bits q_start N x flagPos
        hN_pos hN hx h_flag_above]
  by_cases h : N ≤ x
  · simp [h, Nat.not_lt.mpr h]
  · push_neg at h
    simp [h.le, h, Nat.not_le.mpr h]

/-! ## Tick 51 — Packaged comparator primitive (flag + WellTyped). -/

/-- **HEADLINE — packaged SQIR-style comparator primitive (flag-only).**
Combines WellTyped at the SQIR-faithful dimension with the flag-copy
theorem.  Workspace restoration is established structurally by
construction (forward-CX-uncompute pattern) but the full per-position
bit-level workspace-restoration theorem requires a "function locality"
lemma not yet proved — see status note below. -/
theorem sqir_style_compareConst_candidate_clean_flag
    (bits q_start N x flagPos dim : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.WellTyped dim
        (sqir_style_compareConst_candidate bits q_start N flagPos)
    ∧ Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (cuccaro_input_F q_start false 0 x) flagPos
        = decide (N ≤ x) := by
  refine ⟨?_, ?_⟩
  · apply sqir_style_compareConst_candidate_wellTyped bits q_start N flagPos dim
      h_workspace h_flag
    omega
  · exact sqir_style_compareConst_candidate_flag bits q_start N x flagPos
      hN_pos hN hx h_flag_above

/-! ## Tick 52 — `cuccaro_prepareConstRead` self-inverse.

Each step of the prepare gate is a conditional X (self-inverse). The
whole composition `P ; P` therefore reduces to the identity. -/

/-- **Prepare self-inverse (per position).** -/
theorem cuccaro_prepareConstRead_self_inverse_at
    (bits q_start c : Nat) (f : Nat → Bool) (q : Nat) :
    Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f) q
      = f q := by
  -- Case-split on whether q is a read position.
  by_cases hq : ∃ i, i < bits ∧ q = q_start + 2 * i + 2
  · obtain ⟨i, hi, hq_eq⟩ := hq
    rw [hq_eq]
    rw [cuccaro_prepareConstRead_at_read bits q_start c i hi]
    rw [cuccaro_prepareConstRead_at_read bits q_start c i hi]
    -- (f q XOR c.testBit i) XOR c.testBit i = f q.
    cases f (q_start + 2 * i + 2) <;> cases c.testBit i <;> rfl
  · push_neg at hq
    have h_neq : ∀ i, i < bits → q ≠ q_start + 2 * i + 2 := by
      intros i hi h_eq
      exact hq i hi h_eq
    rw [cuccaro_prepareConstRead_at_other bits q_start c q h_neq]
    rw [cuccaro_prepareConstRead_at_other bits q_start c q h_neq]

/-- **Prepare self-inverse (function-level).** -/
theorem cuccaro_prepareConstRead_self_inverse
    (bits q_start c : Nat) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f) = f := by
  funext q
  exact cuccaro_prepareConstRead_self_inverse_at bits q_start c f q

/-! ## Tick 52 — Locality of `cuccaro_maj_chain_inv`.

The inverse MAJ chain operates only on positions in `[q_start, q_start
+ 2*bits]`.  Modifying the input at any position outside this workspace
range does not affect the output at workspace positions.

This is the "function locality" lemma needed to prove that
`applyNat Minv (applyNat CX h) = applyNat Minv h` at workspace
positions (where CX only modifies an external `flagPos`). -/

/-- **Locality / commute-with-outside-update**: the inverse MAJ chain
commutes with updating the input at any position outside its
workspace range, when queried at any workspace position. -/
theorem cuccaro_maj_chain_inv_commute_update_outside_workspace
    (bits q_start flagPos : Nat) (v : Bool)
    (f : Nat → Bool)
    (hflag_outside : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (p : Nat) (hp_lower : q_start ≤ p) (hp_upper : p < q_start + 2 * bits + 1) :
    Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
        (update f flagPos v) p
      = Gate.applyNat (cuccaro_maj_chain_inv bits q_start) f p := by
  induction bits generalizing q_start f p with
  | zero =>
    -- chain_inv 0 = I. p = q_start. flagPos ≠ p (outside [q_start, q_start+1)).
    show (update f flagPos v) p = f p
    have hp_eq : p = q_start := by omega
    subst hp_eq
    have h_neq : flagPos ≠ p := by
      rcases hflag_outside with h | h
      · omega
      · omega
    exact update_neq _ _ _ _ (fun h => h_neq h.symm)
  | succ k ih =>
    show Gate.applyNat (seq (cuccaro_maj_chain_inv k (q_start + 2))
                              (cuccaro_MAJ_inv q_start (q_start + 1) (q_start + 2)))
                       (update f flagPos v) p
        = Gate.applyNat (seq (cuccaro_maj_chain_inv k (q_start + 2))
                              (cuccaro_MAJ_inv q_start (q_start + 1) (q_start + 2)))
                       f p
    simp only [Gate.applyNat_seq]
    -- Helper: agreement at q_start, q_start+1, q_start+2 after inner chain_inv.
    have h_eq_q_start :
        Gate.applyNat (cuccaro_maj_chain_inv k (q_start + 2))
            (update f flagPos v) q_start
          = Gate.applyNat (cuccaro_maj_chain_inv k (q_start + 2)) f q_start := by
      rw [cuccaro_maj_chain_inv_frame_below k (q_start + 2) _ q_start (by omega)]
      rw [cuccaro_maj_chain_inv_frame_below k (q_start + 2) _ q_start (by omega)]
      have h_neq : flagPos ≠ q_start := by
        rcases hflag_outside with h | h
        · omega
        · omega
      exact update_neq _ _ _ _ (fun h => h_neq h.symm)
    have h_eq_q_start1 :
        Gate.applyNat (cuccaro_maj_chain_inv k (q_start + 2))
            (update f flagPos v) (q_start + 1)
          = Gate.applyNat (cuccaro_maj_chain_inv k (q_start + 2)) f (q_start + 1) := by
      rw [cuccaro_maj_chain_inv_frame_below k (q_start + 2) _ (q_start + 1) (by omega)]
      rw [cuccaro_maj_chain_inv_frame_below k (q_start + 2) _ (q_start + 1) (by omega)]
      have h_neq : flagPos ≠ q_start + 1 := by
        rcases hflag_outside with h | h
        · omega
        · omega
      exact update_neq _ _ _ _ (fun h => h_neq h.symm)
    have hflag_sub : flagPos < q_start + 2 ∨ q_start + 2 + 2 * k + 1 ≤ flagPos := by
      rcases hflag_outside with h | h
      · left; omega
      · right; omega
    have h_eq_q_start2 :
        Gate.applyNat (cuccaro_maj_chain_inv k (q_start + 2))
            (update f flagPos v) (q_start + 2)
          = Gate.applyNat (cuccaro_maj_chain_inv k (q_start + 2)) f (q_start + 2) :=
      ih (q_start + 2) f hflag_sub (q_start + 2) (Nat.le_refl _) (by omega)
    -- Case analysis on p's relation to MAJ_inv's wires.
    by_cases hpa : p = q_start
    · rw [show p = q_start from hpa]
      rw [cuccaro_MAJ_inv_at_a q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      rw [cuccaro_MAJ_inv_at_a q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      rw [h_eq_q_start, h_eq_q_start1, h_eq_q_start2]
    · by_cases hpb : p = q_start + 1
      · rw [show p = q_start + 1 from hpb]
        rw [cuccaro_MAJ_inv_at_b q_start (q_start + 1) (q_start + 2)
            (by omega) (by omega) (by omega)]
        rw [cuccaro_MAJ_inv_at_b q_start (q_start + 1) (q_start + 2)
            (by omega) (by omega) (by omega)]
        rw [h_eq_q_start, h_eq_q_start1, h_eq_q_start2]
      · by_cases hpc : p = q_start + 2
        · rw [show p = q_start + 2 from hpc]
          rw [cuccaro_MAJ_inv_at_c q_start (q_start + 1) (q_start + 2)
              (by omega) (by omega) (by omega)]
          rw [cuccaro_MAJ_inv_at_c q_start (q_start + 1) (q_start + 2)
              (by omega) (by omega) (by omega)]
          rw [h_eq_q_start, h_eq_q_start1, h_eq_q_start2]
        · -- p ∉ MAJ_inv's wires.  p ∈ [q_start + 3, q_start + 2k + 3).
          rw [cuccaro_MAJ_inv_at_other q_start (q_start + 1) (q_start + 2) p
              hpa hpb hpc]
          rw [cuccaro_MAJ_inv_at_other q_start (q_start + 1) (q_start + 2) p
              hpa hpb hpc]
          -- Apply IH with sub_p = p.
          exact ih (q_start + 2) f hflag_sub p (by omega) (by omega)

/-! ## Tick 52 — Workspace restoration. -/

/-- **HEADLINE — workspace restoration (at-position).**  At any
workspace position `q ∈ [q_start, q_start + 2*bits]`, the
SQIR-style comparator candidate restores the input value. -/
theorem sqir_style_compareConst_candidate_workspace_restored_at
    (bits q_start N flagPos : Nat) (f : Nat → Bool)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos)
    (q : Nat) (hq_lower : q_start ≤ q) (hq_upper : q < q_start + 2 * bits + 1) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos) f q
      = f q := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (cuccaro_prepareConstRead bits q_start (2^bits - N))))))
      f q = _
  simp only [Gate.applyNat_seq, Gate.applyNat_CX]
  -- Case-split on whether q is a read position.
  by_cases hq_read : ∃ i, i < bits ∧ q = q_start + 2 * i + 2
  · -- q is a read position. Apply outer P_at_read.
    obtain ⟨i, hi, hq_eq⟩ := hq_read
    rw [hq_eq]
    rw [cuccaro_prepareConstRead_at_read bits q_start (2^bits - N) i hi]
    -- Now: inner_value XOR K.testBit i = f (q_start + 2*i+2).
    -- Reduce inner_value via locality + chain inverse + inner prepare at_read.
    rw [cuccaro_maj_chain_inv_commute_update_outside_workspace
          bits q_start flagPos _ _ (Or.inr (by omega))
          (q_start + 2 * i + 2) (by omega) (by omega)]
    rw [show Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f))
          (q_start + 2 * i + 2)
          = Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f
              (q_start + 2 * i + 2) from ?_]
    · rw [cuccaro_prepareConstRead_at_read bits q_start (2^bits - N) i hi]
      cases f (q_start + 2 * i + 2) <;> cases (2^bits - N).testBit i <;> rfl
    · rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start
          (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f)]
  · -- q is NOT a read position. Outer P at_other.
    push_neg at hq_read
    have h_not_read : ∀ i, i < bits → q ≠ q_start + 2 * i + 2 := by
      intros i hi h_eq
      exact hq_read i hi h_eq
    rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) q h_not_read]
    rw [cuccaro_maj_chain_inv_commute_update_outside_workspace
          bits q_start flagPos _ _ (Or.inr (by omega)) q hq_lower hq_upper]
    rw [show Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f)) q
          = Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f q from ?_]
    · rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) q h_not_read]
    · rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start
          (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f)]

/-! ### Specialized restoration theorems for target / read / carry. -/

/-- **Target register restored**: at each target position `q_start + 2*i
+ 1` for `i < bits`, the output equals `x.testBit i`. -/
theorem sqir_style_compareConst_candidate_target_restored
    (bits q_start N x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    ∀ i, i < bits →
      Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 1)
      = x.testBit i := by
  intro i hi
  rw [sqir_style_compareConst_candidate_workspace_restored_at bits q_start N
        flagPos (cuccaro_input_F q_start false 0 x) h_flag_above
        (q_start + 2 * i + 1) (by omega) (by omega)]
  exact cuccaro_input_F_at_b q_start i false 0 x

/-- **Read register restored**: at each read position `q_start + 2*i +
2` for `i < bits`, the output equals `false`. -/
theorem sqir_style_compareConst_candidate_read_restored
    (bits q_start N x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    ∀ i, i < bits →
      Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 2)
      = false := by
  intro i hi
  rw [sqir_style_compareConst_candidate_workspace_restored_at bits q_start N
        flagPos (cuccaro_input_F q_start false 0 x) h_flag_above
        (q_start + 2 * i + 2) (by omega) (by omega)]
  rw [cuccaro_input_F_at_a q_start i false 0 x]
  simp [Nat.zero_testBit]

/-- **Carry-in qubit restored**: at position `q_start`, the output
equals `false`. -/
theorem sqir_style_compareConst_candidate_carry_in_restored
    (bits q_start N x flagPos : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x) q_start = false := by
  rw [sqir_style_compareConst_candidate_workspace_restored_at bits q_start N
        flagPos (cuccaro_input_F q_start false 0 x) h_flag_above
        q_start (by omega) (by omega)]
  exact cuccaro_input_F_at_c_in q_start false 0 x

/-- **Top-carry qubit restored**: at position `q_start + 2*bits`, the
output equals the input value (= `0.testBit (bits - 1)` for `a = 0`,
which is `false`). -/
theorem sqir_style_compareConst_candidate_top_carry_restored
    (bits q_start N x flagPos : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits) = false := by
  rw [sqir_style_compareConst_candidate_workspace_restored_at bits q_start N
        flagPos (cuccaro_input_F q_start false 0 x) h_flag_above
        (q_start + 2 * bits) (by omega) (by omega)]
  -- input at q_start + 2*bits = q_start + 2*(bits-1) + 2 = a.testBit (bits-1) = 0.
  -- For bits ≥ 1, q_start + 2*bits = q_start + 2*(bits-1) + 2.
  have h_eq : q_start + 2 * bits = q_start + 2 * (bits - 1) + 2 := by omega
  rw [h_eq]
  rw [cuccaro_input_F_at_a q_start (bits - 1) false 0 x]
  simp [Nat.zero_testBit]

/-! ## Tick 52 — Fully clean comparator bundle. -/

/-- **HEADLINE — FULLY CLEAN SQIR-style comparator primitive.**
At the SQIR-faithful dimension `3*bits + 11`:
- WellTyped;
- `flagPos` gets `decide (N ≤ x)`;
- read register fully restored to `0`;
- target register fully restored to `x.testBit`;
- carry-in qubit restored to `false`;
- top-carry qubit restored to `false`. -/
theorem sqir_style_compareConst_candidate_clean
    (bits q_start N x flagPos : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (h_workspace : q_start + 2 * bits + 1 ≤ sqir_modmult_rev_anc bits)
    (h_flag : flagPos < sqir_modmult_rev_anc bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_compareConst_candidate bits q_start N flagPos)
    ∧ Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (cuccaro_input_F q_start false 0 x) flagPos
        = decide (N ≤ x)
    ∧ (∀ i, i < bits →
        Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 1)
          = x.testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 2)
          = false)
    ∧ Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (cuccaro_input_F q_start false 0 x) q_start = false
    ∧ Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply sqir_style_compareConst_candidate_wellTyped bits q_start N flagPos
      (sqir_modmult_rev_anc bits) h_workspace h_flag
    omega
  · exact sqir_style_compareConst_candidate_flag bits q_start N x flagPos
      hN_pos hN hx h_flag_above
  · exact sqir_style_compareConst_candidate_target_restored bits q_start N x
      flagPos hN_pos hN hx h_flag_above
  · exact sqir_style_compareConst_candidate_read_restored bits q_start N x
      flagPos hN_pos hN hx h_flag_above
  · exact sqir_style_compareConst_candidate_carry_in_restored bits q_start N x
      flagPos hbits hN_pos hN hx h_flag_above
  · exact sqir_style_compareConst_candidate_top_carry_restored bits q_start N x
      flagPos hbits hN_pos hN hx h_flag_above

/-! ## Tick 52 — Decoded target restoration corollary. -/

/-- **Decoded target restoration**: the decoded target register after
the comparator equals `x`. -/
theorem sqir_style_compareConst_candidate_target_decode_restored
    (bits q_start N x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (cuccaro_input_F q_start false 0 x))
      = x := by
  have h_eq : cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (cuccaro_input_F q_start false 0 x))
      = x % 2^bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match bits q_start x _
    intro i hi
    exact sqir_style_compareConst_candidate_target_restored bits q_start N x
      flagPos hN_pos hN hx h_flag_above i hi
  rw [h_eq]
  exact Nat.mod_eq_of_lt hx

/-! ## Tick 51 — WellTyped at SQIR-faithful dimension. -/

/-- **WellTyped at the SQIR-faithful dimension `sqir_modmult_rev_anc bits
= 3 * bits + 11`.**  The SQIR-style candidate fits comfortably: it uses
`q_start + 2*bits + 1` workspace + 1 flag qubit = much less than the
full SQIR ancilla budget. -/
theorem sqir_style_compareConst_candidate_wellTyped_sqir_dim
    (bits q_start N flagPos : Nat) (hbits : 1 ≤ bits)
    (h_workspace : q_start + 2 * bits + 1 ≤ sqir_modmult_rev_anc bits)
    (h_flag : flagPos < sqir_modmult_rev_anc bits)
    (h_distinct : flagPos ≠ q_start + 2 * bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_compareConst_candidate bits q_start N flagPos) :=
  sqir_style_compareConst_candidate_wellTyped bits q_start N flagPos
    (sqir_modmult_rev_anc bits) h_workspace h_flag h_distinct

/-! ## Status note (Tick 49).

Landed:
- Discovery: SQIR's actual `modmult_rev_anc = 3 * n + 11`, much
  larger than the Lean placeholder `2 * n + 1`. This means the
  "exact-budget" framing of Ticks 41-48 was based on a too-tight
  Lean placeholder.
- `cuccaro_MAJ_inv`, `cuccaro_maj_chain_inv` definitions.
- WellTyped for both.
- `sqir_style_compareConst_candidate`: gate matching SQIR's
  `comparator01` structure, parameterized by external flag position.
- `sqir_style_compareConst_candidate_wellTyped`: WellTyped.

NOT YET landed (next-tick work):
- Local MAJ inverse identity: `MAJ ; MAJ_inv = id` (per position).
  The proof requires either (a) computing the six-gate composition
  symbolically with case analysis over (q, a, b, c) and Boolean
  cases on `f a, f b, f c`, or (b) building `cuccaro_MAJ_inv_at_*`
  lemmas analogous to `cuccaro_MAJ_at_*` from Tick 41.
- Chain inverse identity (by induction on n using the local).
- Workspace-restoration theorem for the SQIR-style candidate.
- Flag-copy theorem.
- Connection to the actual SQIR axiom dimension (would require
  changing `modmult_rev_anc` Lean def to `3 * n + 11`, propagating
  the change through `f_modmult_circuit`'s type).

The current Lean infrastructure is now compatible with the SQIR
construction once the budget mismatch is resolved at a higher
level (either fix the Lean placeholder, or build a tighter custom
modular multiplier). -/

end FormalRV.BQAlgo
