/-
  FormalRV.QFT.IQFTCount
  ──────────────────────
  CLOSED-FORM, ANCHORED resource counts for the inverse-QFT circuit — the
  independent `Resource` counters applied to THE actual `BaseUCom` syntax tree
  `real_QFTinv_layer n` (= `QFTinv n` = `IQFT n`), proven equal to closed forms
  by induction over the circuit's own recursion.  This closes the audit gap
  "no gate counter on BaseUCom / QFT resource is only a predicate + an error
  budget": the IQFT now has honest TIME counts (gates) and a SPACE count
  (qubits), all forced by the tree.

  THE headlines (for every `n`; width needs `n ≥ 1`):
    • `cnotCountU_IQFT`  : CNOTs   = `3·⌊n/2⌋ + n·(n−1)`
                           (3 per bit-reversal SWAP + 2 per controlled phase,
                            with `n(n−1)/2` controlled phases)
    • `oneQCountU_IQFT`  : 1q gates = `3·(n·(n−1)/2) + n + 2`
                           (3 per controlled phase + n Hadamards + 2 SKIPs)
    • `gateCountU_IQFT`  : total = the sum of the two
    • `widthU_IQFT`      : qubits  = `n` — exactly n qubits, NO hidden ancilla
    • `iqft_verified_with_resources` : the TRIPLE — semantics (`= IQFT_matrix n`)
      AND time AND space, all about the SAME syntactic object.

  The counters live in `Resource/` and import only the IR — they cannot be
  influenced by anything here; these theorems merely reveal what the counters
  return on this circuit.  Independent cross-check: the emitted OpenQASM
  (`IQFTGadget.emitQASM n`, computable) lists exactly `⌊n/2⌋` `swap`,
  `n(n−1)/2` `cu1` and `n` `h` lines — countable by `#eval` with no proofs.
-/
import FormalRV.Resource.UComCombinators
import FormalRV.QFT.IQFTCorrectness

namespace FormalRV.Resource

open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ## §1. Equation lemmas for the circuit's recursive loops. -/

private theorem ladder_loop_eq {dim : Nat} (n target j : Nat) :
    (inverse_qft_phase_ladder.loop n target j : BaseUCom dim)
      = if j < n then
          UCom.seq (controlled_Rz j target (-(Real.pi / (2 ^ (j - target) : ℝ))))
                   (inverse_qft_phase_ladder.loop n target (j + 1))
        else H target := by
  conv_lhs => unfold inverse_qft_phase_ladder.loop

private theorem ladder_eq {dim : Nat} (n target : Nat) :
    (inverse_qft_phase_ladder n target : BaseUCom dim)
      = inverse_qft_phase_ladder.loop n target (target + 1) := by
  conv_lhs => unfold inverse_qft_phase_ladder

private theorem brs_loop_eq {dim : Nat} (n k : Nat) :
    (bit_reversal_swaps.loop n k : BaseUCom dim)
      = if k + k + 1 < n then
          UCom.seq (SWAP k (n - 1 - k)) (bit_reversal_swaps.loop n (k + 1))
        else SKIP := by
  conv_lhs => unfold bit_reversal_swaps.loop

private theorem brs_eq {dim : Nat} (n : Nat) :
    (bit_reversal_swaps n : BaseUCom dim) = bit_reversal_swaps.loop n 0 := by
  conv_lhs => unfold bit_reversal_swaps

private theorem countdown_zero_eq {dim : Nat} (n : Nat) :
    (real_QFTinv_layer.countdown n 0 : BaseUCom dim) = SKIP := by
  conv_lhs => unfold real_QFTinv_layer.countdown

private theorem countdown_succ_eq {dim : Nat} (n k : Nat) :
    (real_QFTinv_layer.countdown n (k + 1) : BaseUCom dim)
      = UCom.seq (inverse_qft_phase_ladder n k) (real_QFTinv_layer.countdown n k) := by
  conv_lhs => unfold real_QFTinv_layer.countdown

private theorem layer_eq {dim : Nat} (n : Nat) :
    (real_QFTinv_layer n : BaseUCom dim)
      = UCom.seq (bit_reversal_swaps n) (real_QFTinv_layer.countdown n n) := by
  conv_lhs => unfold real_QFTinv_layer

/-! ## §2. Atom counts: the controlled phase. -/

@[simp] theorem oneQCountU_controlled_Rz {dim : Nat} (q t : Nat) (lam : ℝ) :
    oneQCountU (controlled_Rz q t lam : BaseUCom dim) = 3 := rfl

@[simp] theorem cnotCountU_controlled_Rz {dim : Nat} (q t : Nat) (lam : ℝ) :
    cnotCountU (controlled_Rz q t lam : BaseUCom dim) = 2 := rfl

theorem widthU_controlled_Rz {dim : Nat} (q t : Nat) (lam : ℝ) :
    widthU (controlled_Rz q t lam : BaseUCom dim) = max (q + 1) (t + 1) := by
  simp only [controlled_Rz, Rz, CNOT, widthU]
  omega

/-! ## §3. The phase ladder: `n − (target+1)` controlled phases, then one `H`. -/

private theorem ladder_loop_counts {dim : Nat} (n target : Nat) :
    ∀ (fuel j : Nat), n - j = fuel →
      oneQCountU (inverse_qft_phase_ladder.loop n target j : BaseUCom dim)
          = 3 * (n - j) + 1
      ∧ cnotCountU (inverse_qft_phase_ladder.loop n target j : BaseUCom dim)
          = 2 * (n - j) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro j hj
    rw [ladder_loop_eq]
    by_cases h : j < n
    · rw [if_pos h]
      obtain ⟨ih1, ih2⟩ := ih (n - (j + 1)) (by omega) (j + 1) rfl
      refine ⟨?_, ?_⟩
      · rw [oneQCountU_seq, oneQCountU_controlled_Rz, ih1]; omega
      · rw [cnotCountU_seq, cnotCountU_controlled_Rz, ih2]; omega
    · rw [if_neg h]
      have hnj : n - j = 0 := by omega
      rw [hnj]
      exact ⟨rfl, rfl⟩

/-- One-qubit gates of one phase ladder: 3 per kept rotation, plus the `H`. -/
theorem oneQCountU_ladder {dim : Nat} (n target : Nat) :
    oneQCountU (inverse_qft_phase_ladder n target : BaseUCom dim)
      = 3 * (n - (target + 1)) + 1 := by
  rw [ladder_eq]
  exact (ladder_loop_counts n target (n - (target + 1)) (target + 1) rfl).1

/-- CNOTs of one phase ladder: 2 per kept rotation. -/
theorem cnotCountU_ladder {dim : Nat} (n target : Nat) :
    cnotCountU (inverse_qft_phase_ladder n target : BaseUCom dim)
      = 2 * (n - (target + 1)) := by
  rw [ladder_eq]
  exact (ladder_loop_counts n target (n - (target + 1)) (target + 1) rfl).2

/-! ## §4. The bit-reversal cascade: `⌊n/2⌋` SWAPs (3 CNOTs each), then `SKIP`. -/

private theorem brs_loop_counts {dim : Nat} (n : Nat) :
    ∀ (fuel k : Nat), n - 2 * k = fuel →
      oneQCountU (bit_reversal_swaps.loop n k : BaseUCom dim) = 1
      ∧ cnotCountU (bit_reversal_swaps.loop n k : BaseUCom dim) = 3 * (n / 2 - k) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro k hk
    rw [brs_loop_eq]
    by_cases h : k + k + 1 < n
    · rw [if_pos h]
      obtain ⟨ih1, ih2⟩ := ih (n - 2 * (k + 1)) (by omega) (k + 1) rfl
      refine ⟨?_, ?_⟩
      · rw [oneQCountU_seq, oneQCountU_SWAP, ih1]
      · rw [cnotCountU_seq, cnotCountU_SWAP, ih2]; omega
    · rw [if_neg h]
      refine ⟨rfl, ?_⟩
      have hz : n / 2 - k = 0 := by omega
      rw [hz]
      simp

/-- CNOTs of the bit-reversal cascade: 3 per SWAP, `⌊n/2⌋` SWAPs. -/
theorem cnotCountU_bit_reversal_swaps {dim : Nat} (n : Nat) :
    cnotCountU (bit_reversal_swaps n : BaseUCom dim) = 3 * (n / 2) := by
  rw [brs_eq]
  have h := (brs_loop_counts (dim := dim) n n 0 (by omega)).2
  simpa using h

/-- One-qubit gates of the bit-reversal cascade: just the terminal `SKIP`. -/
theorem oneQCountU_bit_reversal_swaps {dim : Nat} (n : Nat) :
    oneQCountU (bit_reversal_swaps n : BaseUCom dim) = 1 := by
  rw [brs_eq]
  exact (brs_loop_counts (dim := dim) n n 0 (by omega)).1

/-! ## §5. The countdown of ladders. -/

private theorem countdown_cnot {dim : Nat} (n : Nat) :
    ∀ k, k ≤ n →
      cnotCountU (real_QFTinv_layer.countdown n k : BaseUCom dim)
        = k * (2 * n - k - 1) := by
  intro k
  induction k with
  | zero => intro _; rw [countdown_zero_eq]; simp
  | succ m ih =>
    intro hm
    rw [countdown_succ_eq, cnotCountU_seq, cnotCountU_ladder, ih (by omega)]
    have c1 : m + 1 ≤ n := hm
    have c2 : m ≤ 2 * n := by omega
    have c3 : 1 ≤ 2 * n - m := by omega
    have c4 : m + 1 ≤ 2 * n := by omega
    have c5 : 1 ≤ 2 * n - (m + 1) := by omega
    zify [c1, c2, c3, c4, c5]
    ring

private theorem countdown_oneQ_doubled {dim : Nat} (n : Nat) :
    ∀ k, k ≤ n →
      2 * oneQCountU (real_QFTinv_layer.countdown n k : BaseUCom dim)
        = 3 * (k * (2 * n - k - 1)) + 2 * k + 2 := by
  intro k
  induction k with
  | zero => intro _; rw [countdown_zero_eq]; simp
  | succ m ih =>
    intro hm
    rw [countdown_succ_eq, oneQCountU_seq, oneQCountU_ladder]
    have hcd := ih (by omega)
    have c1 : m + 1 ≤ n := hm
    have c2 : m ≤ 2 * n := by omega
    have c3 : 1 ≤ 2 * n - m := by omega
    have c4 : m + 1 ≤ 2 * n := by omega
    have c5 : 1 ≤ 2 * n - (m + 1) := by omega
    zify [c1, c2, c3, c4, c5] at hcd ⊢
    linarith [hcd]

/-! ## §6. THE assembled inverse-QFT counts (TIME). -/

/-- **IQFT CNOT count (THE headline, time).**  The full n-qubit inverse QFT has
exactly `3·⌊n/2⌋ + n·(n−1)` CNOTs: 3 per bit-reversal SWAP, plus 2 per
controlled phase with `n(n−1)/2` controlled phases.  Anchored: the LHS is the
independent counter walking THE verified circuit's syntax tree. -/
theorem cnotCountU_real_QFTinv_layer {dim : Nat} (n : Nat) :
    cnotCountU (real_QFTinv_layer n : BaseUCom dim) = 3 * (n / 2) + n * (n - 1) := by
  rw [layer_eq, cnotCountU_seq, cnotCountU_bit_reversal_swaps,
      countdown_cnot n n le_rfl]
  have h : 2 * n - n - 1 = n - 1 := by omega
  rw [h]

/-- **IQFT one-qubit-gate count (time).**  `3·(n(n−1)/2) + n + 2`: 3 rotations
per controlled phase, `n` Hadamards, and the 2 structural `SKIP`s. -/
theorem oneQCountU_real_QFTinv_layer {dim : Nat} (n : Nat) :
    oneQCountU (real_QFTinv_layer n : BaseUCom dim)
      = 3 * (n * (n - 1) / 2) + n + 2 := by
  have h2 : 2 * oneQCountU (real_QFTinv_layer n : BaseUCom dim)
      = 3 * (n * (n - 1)) + 2 * n + 4 := by
    rw [layer_eq, oneQCountU_seq, oneQCountU_bit_reversal_swaps]
    have hcd := countdown_oneQ_doubled (dim := dim) n n le_rfl
    have h : 2 * n - n - 1 = n - 1 := by omega
    rw [h] at hcd
    omega
  have heven : n * (n - 1) % 2 = 0 := by
    cases n with
    | zero => rfl
    | succ m =>
      have h : (m + 1) * (m + 1 - 1) = m * (m + 1) := by
        simp [Nat.mul_comm]
      rw [h, ← Nat.even_iff]
      exact Nat.even_mul_succ_self m
  omega

/-- **IQFT total gate count (time).**  One-qubit gates + CNOTs. -/
theorem gateCountU_real_QFTinv_layer {dim : Nat} (n : Nat) :
    gateCountU (real_QFTinv_layer n : BaseUCom dim)
      = (3 * (n * (n - 1) / 2) + n + 2) + (3 * (n / 2) + n * (n - 1)) := by
  rw [gateCountU_eq_oneQ_add_cnot, oneQCountU_real_QFTinv_layer,
      cnotCountU_real_QFTinv_layer]

/-! ## §7. SPACE: the IQFT uses exactly `n` qubits — no hidden ancilla. -/

private theorem ladder_loop_width {dim : Nat} (n target : Nat) (ht : target < n) :
    ∀ (fuel j : Nat), n - j = fuel →
      widthU (inverse_qft_phase_ladder.loop n target j : BaseUCom dim)
        = if j < n then n else target + 1 := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro j hj
    rw [ladder_loop_eq]
    by_cases h : j < n
    · rw [if_pos h, if_pos h]
      have ihw := ih (n - (j + 1)) (by omega) (j + 1) rfl
      rw [widthU, widthU_controlled_Rz, ihw]
      by_cases h2 : j + 1 < n
      · rw [if_pos h2]; omega
      · rw [if_neg h2]; omega
    · rw [if_neg h, if_neg h]
      show target + 1 = target + 1
      rfl

/-- One ladder spans the whole `n`-qubit register (its controls run up to
`n−1`; for `target = n−1` the lone `H` sits on qubit `n−1`). -/
theorem widthU_ladder {dim : Nat} (n target : Nat) (ht : target < n) :
    widthU (inverse_qft_phase_ladder n target : BaseUCom dim) = n := by
  rw [ladder_eq, ladder_loop_width n target ht (n - (target + 1)) (target + 1) rfl]
  by_cases h : target + 1 < n
  · rw [if_pos h]
  · rw [if_neg h]; omega

private theorem brs_loop_width {dim : Nat} (n : Nat) :
    ∀ (fuel k : Nat), n - 2 * k = fuel →
      widthU (bit_reversal_swaps.loop n k : BaseUCom dim)
        = if k + k + 1 < n then n - k else 1 := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro k hk
    rw [brs_loop_eq]
    by_cases h : k + k + 1 < n
    · rw [if_pos h, if_pos h]
      have ihw := ih (n - 2 * (k + 1)) (by omega) (k + 1) rfl
      rw [widthU, widthU_SWAP, ihw]
      by_cases h2 : (k + 1) + (k + 1) + 1 < n
      · rw [if_pos h2]; omega
      · rw [if_neg h2]; omega
    · rw [if_neg h, if_neg h]
      rfl

/-- The bit-reversal cascade spans the register (for `n ≥ 1`). -/
theorem widthU_bit_reversal_swaps {dim : Nat} (n : Nat) (hn : 0 < n) :
    widthU (bit_reversal_swaps n : BaseUCom dim) = n := by
  rw [brs_eq, brs_loop_width n n 0 (by omega)]
  by_cases h : 0 + 0 + 1 < n
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

private theorem countdown_width {dim : Nat} (n : Nat) :
    ∀ k, 0 < k → k ≤ n →
      widthU (real_QFTinv_layer.countdown n k : BaseUCom dim) = n := by
  intro k
  induction k with
  | zero => intro h _; omega
  | succ m ih =>
    intro _ hm
    rw [countdown_succ_eq, widthU, widthU_ladder n m (by omega)]
    by_cases h : 0 < m
    · rw [ih h (by omega)]; omega
    · have : m = 0 := by omega
      subst this
      rw [countdown_zero_eq, widthU_SKIP]
      omega

/-- **IQFT qubit count (THE headline, space).**  The full n-qubit inverse QFT
touches EXACTLY `n` qubits — no hidden ancilla.  Anchored: the LHS is the
independent space counter walking THE verified circuit's syntax tree. -/
theorem widthU_real_QFTinv_layer {dim : Nat} (n : Nat) (hn : 0 < n) :
    widthU (real_QFTinv_layer n : BaseUCom dim) = n := by
  rw [layer_eq, widthU, widthU_bit_reversal_swaps n hn,
      countdown_width n n hn le_rfl]
  omega

/-! ## §8. Transfer to `QFTinv` (the framework def QPE uses) and `IQFT` (the
QFT spine's headline object). -/

/-- The counts transfer to `QFTinv` by definitional equality. -/
theorem cnotCountU_QFTinv {dim : Nat} (n : Nat) :
    cnotCountU (QFTinv n : BaseUCom dim) = 3 * (n / 2) + n * (n - 1) :=
  cnotCountU_real_QFTinv_layer n

theorem oneQCountU_QFTinv {dim : Nat} (n : Nat) :
    oneQCountU (QFTinv n : BaseUCom dim) = 3 * (n * (n - 1) / 2) + n + 2 :=
  oneQCountU_real_QFTinv_layer n

theorem widthU_QFTinv {dim : Nat} (n : Nat) (hn : 0 < n) :
    widthU (QFTinv n : BaseUCom dim) = n :=
  widthU_real_QFTinv_layer n hn

/-- **CNOT count of `IQFT n`** (the QFT spine's headline circuit, via the
SQIRPort↔Framework bridge — the two are the SAME syntax tree). -/
theorem cnotCountU_IQFT (n : Nat) :
    cnotCountU (FormalRV.SQIRPort.IQFT n) = 3 * (n / 2) + n * (n - 1) := by
  rw [show FormalRV.SQIRPort.IQFT n = _ from FormalRV.SQIRPort.real_QFTinv_layer_bridge n]
  exact cnotCountU_real_QFTinv_layer n

/-- **One-qubit-gate count of `IQFT n`.** -/
theorem oneQCountU_IQFT (n : Nat) :
    oneQCountU (FormalRV.SQIRPort.IQFT n) = 3 * (n * (n - 1) / 2) + n + 2 := by
  rw [show FormalRV.SQIRPort.IQFT n = _ from FormalRV.SQIRPort.real_QFTinv_layer_bridge n]
  exact oneQCountU_real_QFTinv_layer n

/-- **Qubit count of `IQFT n`** — exactly `n`, no hidden ancilla. -/
theorem widthU_IQFT (n : Nat) (hn : 0 < n) :
    widthU (FormalRV.SQIRPort.IQFT n) = n := by
  rw [show FormalRV.SQIRPort.IQFT n = _ from FormalRV.SQIRPort.real_QFTinv_layer_bridge n]
  exact widthU_real_QFTinv_layer n hn

/-! ## §9. THE TRIPLE — semantics + time + space about ONE syntactic object. -/

/-- **The inverse QFT, verified with resources.**  The single syntactic object
`IQFT n` is simultaneously:
  1. **semantically correct** — its unitary is exactly the ideal `IQFT_matrix n`;
  2. **time-counted** — the independent CNOT counter walks its tree to
     `3·⌊n/2⌋ + n·(n−1)` (and the 1-qubit counter to `3·(n(n−1)/2) + n + 2`);
  3. **space-counted** — the independent width counter walks its tree to `n`.
No resource number floats free of the object; nothing here can cheat, because
the counters live in `Resource/` and import only the IR. -/
theorem iqft_verified_with_resources (n : Nat) (hn : 0 < n) :
    FormalRV.Framework.uc_eval (FormalRV.SQIRPort.IQFT n) = FormalRV.SQIRPort.IQFT_matrix n
    ∧ cnotCountU (FormalRV.SQIRPort.IQFT n) = 3 * (n / 2) + n * (n - 1)
    ∧ oneQCountU (FormalRV.SQIRPort.IQFT n) = 3 * (n * (n - 1) / 2) + n + 2
    ∧ widthU (FormalRV.SQIRPort.IQFT n) = n :=
  ⟨FormalRV.SQIRPort.iqft_correct n hn, cnotCountU_IQFT n, oneQCountU_IQFT n,
   widthU_IQFT n hn⟩

/-! ## §10. Small-instance smokes (instances of the headline, not `decide` —
the circuit's well-founded loops don't kernel-reduce; the closed form is the
proof, and the computable emitted QASM is the independent `#eval` cross-check). -/

example : cnotCountU (FormalRV.SQIRPort.IQFT 2) = 5 := cnotCountU_IQFT 2    -- 1 swap + 1 cu1
example : cnotCountU (FormalRV.SQIRPort.IQFT 3) = 9 := cnotCountU_IQFT 3    -- 1 swap + 3 cu1
example : widthU (FormalRV.SQIRPort.IQFT 3) = 3 := widthU_IQFT 3 (by omega)

end FormalRV.Resource
