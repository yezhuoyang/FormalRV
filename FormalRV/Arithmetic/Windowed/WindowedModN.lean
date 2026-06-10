/-
  FormalRV.Shor.WindowedCircuit.WindowedModN — the PER-WINDOW mod-N windowed
  multiplier.

  The existing windowed multiplier (`WindowedCircuitCorrect.lean`) is a
  PRODUCT adder: each window does `acc ← (acc + T_j[v]) mod 2^bits`, and the
  final value is `(a·y) mod 2^bits`.  Gidney's windowed multiplication
  (arXiv:1905.07682) instead reduces mod N after EVERY window:
  `acc ← (acc + T_j[v]) mod N` with table entries `T_j[v] = a·(2^w)^j·v mod N`,
  so the multiplier computes `(a·y) mod N` directly.  This file closes that
  gap at the Cuccaro layout.

  HEADLINE (`windowedModNMulCircuit_correct`): on the SAME clean input family
  `mulInputOf cuccaroAdder w bits numWin y` as the product-adder theorem, the
  per-window mod-N circuit leaves

      (a · y) mod N

  in the accumulator, provided `0 < w`, `0 < N`, `2·N ≤ 2^bits` and
  `y < 2^(w·numWin)`.

  Per-window structure (`modNLookupAddStep`): the Cuccaro comparator borrows
  the addend (read) register for its two's-complement constant, so the QROM
  word must be cleared before the constant-compare stage and re-supplied for
  the flag-uncompute stage:

      read(T) ; add ; unread(T)                -- acc ← acc + t   (t = T_j[v] < N)
      ; compareConst(N) → flag                 -- flag ^= [N ≤ acc]
      ; conditionalSub(N)                      -- acc ← acc mod N
      ; read(T) ; regCompareXor ; unread(T)    -- flag ^= [acc < t] = flag  (flag → 0)

  The flag-uncompute works because `acc_out = (s+t) mod N < t  ⟺  N ≤ s+t`
  when `s, t < N` — the standard modular-adder uncompute comparison, here
  realized as a REGISTER-register comparator (`regCompareXor`, new in this
  file: X-conjugated MAJ chain, top carry of `¬acc + t` = `[acc < t]`).

  New general-state (any `f : Nat → Bool`) reduction-stage lemmas, re-derived
  from the per-position Cuccaro primitives (the Tick-59/60 stage lemmas are
  tied to the `cuccaro_input_F` input family and do not apply inside the
  windowed frame):
  * `compareConstXor_state_general`  — the SQIR-style constant comparator;
  * `condSub_state_general`          — the flag-conditional subtract;
  * `regCompareXor_state_general`    — the register-register comparator.

  Follow-up (NOT in this pass): factor the reduction pipeline into a
  `ModAdder` interface so the Gidney `ModularAdder` pipeline (which has the
  same compare/conditional-subtract/uncompute shape) instantiates it too —
  this file is deliberately Cuccaro-specific.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroDirtyFlagStageCorrectness

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §1. Arithmetic helpers. -/

/-- **Complemented-carry = strict comparison (mod-windows form).**  The
    ripple carry of `(¬u) + t` through the low `k` bits equals
    `[u mod 2^k < t mod 2^k]`. -/
private theorem carry_compl_eq_decide_lt (u t : Nat) :
    ∀ k, Adder.carry false k (fun i => !u.testBit i) (fun i => t.testBit i)
      = decide (u % 2 ^ k < t % 2 ^ k)
  | 0 => by simp [Adder.carry, Nat.mod_one]
  | k + 1 => by
    rw [Adder.carry_succ, carry_compl_eq_decide_lt u t k]
    have hu : u % 2 ^ (k + 1) = u % 2 ^ k + 2 ^ k * (u / 2 ^ k % 2) := by
      rw [pow_succ, Nat.mod_mul]
    have ht : t % 2 ^ (k + 1) = t % 2 ^ k + 2 ^ k * (t / 2 ^ k % 2) := by
      rw [pow_succ, Nat.mod_mul]
    have hum : u % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have htm : t % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    rw [show u.testBit k = decide (u / 2 ^ k % 2 = 1) from
          Nat.testBit_eq_decide_div_mod_eq,
        show t.testBit k = decide (t / 2 ^ k % 2 = 1) from
          Nat.testBit_eq_decide_div_mod_eq,
        hu, ht]
    have hud : u / 2 ^ k % 2 = 0 ∨ u / 2 ^ k % 2 = 1 := by omega
    have htd : t / 2 ^ k % 2 = 0 ∨ t / 2 ^ k % 2 = 1 := by omega
    rcases hud with h1 | h1 <;> rcases htd with h2 | h2 <;> rw [h1, h2] <;>
      cases hc : decide (u % 2 ^ k < t % 2 ^ k) <;>
      (try have hcp := of_decide_eq_true hc) <;>
      (try have hcn := of_decide_eq_false hc) <;>
      simp only [show decide ((0 : Nat) = 1) = false from rfl,
                 Bool.not_false, Bool.true_and,
                 Bool.and_true, Bool.and_false, Bool.xor_false, Bool.false_xor,
                 Bool.xor_true, Bool.xor_self] <;>
      first
        | rfl
        | (symm; exact decide_eq_true (by omega))
        | (symm; exact decide_eq_false (by omega))

/-- **Complemented-carry = strict comparison.**  For `u, t < 2^n`, the carry
    out of `(¬u) + t` over `n` bits is `[u < t]`. -/
private theorem carry_compl_lt (n u t : Nat) (hu : u < 2 ^ n) (ht : t < 2 ^ n) :
    Adder.carry false n (fun i => !u.testBit i) (fun i => t.testBit i)
      = decide (u < t) := by
  rw [carry_compl_eq_decide_lt u t n, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt ht]

/-- **The flag-uncompute comparison.**  For `s, t < N`, the reduced sum is
    below the addend exactly when the reduction fired:
    `(s+t) mod N < t  ⟺  N ≤ s+t`. -/
private theorem modReduce_lt_decide (N s t : Nat) (hs : s < N) (ht : t < N) :
    decide ((s + t) % N < t) = decide (N ≤ s + t) := by
  by_cases h : N ≤ s + t
  · have hmod : (s + t) % N = s + t - N := by
      conv_lhs => rw [show s + t = N + (s + t - N) from by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have h1 : decide (s + t - N < t) = true := by
      rw [decide_eq_true_iff]; omega
    have h2 : decide (N ≤ s + t) = true := by
      rw [decide_eq_true_iff]; omega
    rw [h1, h2]
  · push Not at h
    rw [Nat.mod_eq_of_lt h]
    have h1 : decide (s + t < t) = false := by
      rw [decide_eq_false_iff_not]; omega
    have h2 : decide (N ≤ s + t) = false := by
      rw [decide_eq_false_iff_not]; omega
    rw [h1, h2]

/-- **General-state sum bits of the full Cuccaro adder.**  If the carry-in is
    clear and the target/read registers hold the bits of `x`/`y` (below
    `bits`), the adder leaves `(x+y).testBit i` at target position `i`.
    (The general-state analogue of the decoded `sumCorrect`, at bit level.) -/
theorem cuccaro_adder_sum_bits_general
    (bits q_start x y : Nat) (f : Nat → Bool)
    (h_cin : f q_start = false)
    (h_tgt : ∀ i, i < bits → f (q_start + 2 * i + 1) = x.testBit i)
    (h_read : ∀ i, i < bits → f (q_start + 2 * i + 2) = y.testBit i)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) f (q_start + 2 * i + 1)
      = (x + y).testBit i := by
  rw [(cuccaro_n_bit_adder_full_correct bits q_start f).2.1 i hi]
  rw [cuccaro_carry_eq_Adder_carry, h_cin]
  rw [Adder.carry_ext_below false i
        (fun j => f (q_start + 2 * j + 1)) (fun j => f (q_start + 2 * j + 2))
        (fun j => x.testBit j) (fun j => y.testBit j)
        (fun j hj => h_tgt j (by omega)) (fun j hj => h_read j (by omega))]
  rw [h_tgt i hi, h_read i hi]
  have h := Adder.sumfb_eq_testBit_add_gen false x y i
  unfold Adder.sumfb at h
  simpa [Bool.toNat] using h

/-! ## §2. The target-complement gate (X on every accumulator bit). -/

/-- X on each target/augend position `q_start + 2i + 1`, `i < bits`.  Used to
    conjugate the MAJ chain so its top carry computes `¬acc + t ≥ 2^bits`,
    i.e. the strict comparison `acc < t`. -/
def targetComplement : Nat → Nat → Gate
  | 0, _ => Gate.I
  | n + 1, q_start =>
      Gate.seq (targetComplement n q_start) (Gate.X (q_start + 2 * n + 1))

/-- Frame: `targetComplement` only touches the target positions. -/
theorem targetComplement_at_other
    (bits q_start q : Nat)
    (hq : ∀ i, i < bits → q ≠ q_start + 2 * i + 1)
    (f : Nat → Bool) :
    Gate.applyNat (targetComplement bits q_start) f q = f q := by
  induction bits generalizing f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (Gate.seq (targetComplement k q_start) (Gate.X (q_start + 2 * k + 1))) f q = _
    simp only [Gate.applyNat_seq, Gate.applyNat_X]
    rw [update_neq _ _ _ _ (hq k (by omega))]
    exact ih (fun i hi => hq i (by omega)) f

/-- Action at a target position: bit `j < bits` is complemented. -/
theorem targetComplement_at_target
    (bits q_start j : Nat) (hj : j < bits) (f : Nat → Bool) :
    Gate.applyNat (targetComplement bits q_start) f (q_start + 2 * j + 1)
      = !(f (q_start + 2 * j + 1)) := by
  induction bits generalizing f with
  | zero => omega
  | succ k ih =>
    show Gate.applyNat
        (Gate.seq (targetComplement k q_start) (Gate.X (q_start + 2 * k + 1))) f
        (q_start + 2 * j + 1) = _
    simp only [Gate.applyNat_seq, Gate.applyNat_X]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [update_neq _ _ _ _ (by omega)]
      exact ih hjk f
    · have hjk_eq : j = k := by omega
      subst hjk_eq
      rw [update_eq]
      congr 1
      exact targetComplement_at_other j q_start (q_start + 2 * j + 1)
        (fun i hi => by omega) f

/-! ## §3. General-state constant comparator.

`sqir_style_compareConst_candidate` (prepare K=2^bits−N ; MAJ chain ;
CX top→flag ; inverse MAJ chain ; unprepare) on an ARBITRARY state whose
carry-in is clear, read register is clear, and target register holds `x`:
the whole state is preserved except the flag, which is XOR'd with
`[N ≤ x]`.  (The Tick-59/61 stage lemmas prove this only on the
`cuccaro_input_F` input family; the windowed frame needs general `f`.) -/

theorem compareConstXor_state_general
    (bits q_start N flagPos x : Nat) (f : Nat → Bool)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hx : x < 2 ^ bits)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (h_cin : f q_start = false)
    (h_tgt : ∀ i, i < bits → f (q_start + 2 * i + 1) = x.testBit i)
    (h_read : ∀ i, i < bits → f (q_start + 2 * i + 2) = false) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos) f
      = update f flagPos (xor (f flagPos) (decide (N ≤ x))) := by
  funext q
  by_cases hq : q = flagPos
  · -- The flag position: peel the layers and read off the top carry.
    subst hq
    rw [update_eq]
    show Gate.applyNat
        (seq (cuccaro_prepareConstRead bits q_start (2 ^ bits - N))
              (seq (cuccaro_maj_chain bits q_start)
                   (seq (Gate.CX (q_start + 2 * bits) q)
                        (seq (cuccaro_maj_chain_inv bits q_start)
                             (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)))))) f q
        = _
    simp only [Gate.applyNat_seq]
    have h_flag_not_read : ∀ i, i < bits → q ≠ q_start + 2 * i + 2 := by
      intro i hi
      rcases hflag_out with h | h <;> omega
    rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) q h_flag_not_read]
    rcases hflag_out with h_below | h_above
    · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ q h_below]
      simp only [Gate.applyNat_CX, update_eq]
      rw [cuccaro_maj_chain_frame_below bits q_start _ q h_below]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) q h_flag_not_read]
      rw [cuccaro_maj_chain_at_top_carry bits q_start
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f)]
      congr 1
      -- top carry of the prepared state = decide (N ≤ x)
      rw [cuccaro_carry_eq_Adder_carry]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) q_start
            (fun i _ => by omega), h_cin]
      rw [Adder.carry_ext_below false bits
            (fun j => Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
              (q_start + 2 * j + 1))
            (fun j => Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
              (q_start + 2 * j + 2))
            (fun j => x.testBit j) (fun j => (2 ^ bits - N).testBit j)
            (fun j hj => by
              show Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
                  (q_start + 2 * j + 1) = x.testBit j
              rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) _
                    (fun i _ => by omega)]
              exact h_tgt j hj)
            (fun j hj => by
              show Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
                  (q_start + 2 * j + 2) = (2 ^ bits - N).testBit j
              rw [cuccaro_prepareConstRead_at_read bits q_start (2 ^ bits - N) j hj,
                  h_read j hj, Bool.false_xor])]
      rw [Adder.carry_sym]
      exact add_twos_complement_carry_out_eq bits N x hN_pos hN hx
    · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ q h_above]
      simp only [Gate.applyNat_CX, update_eq]
      rw [cuccaro_maj_chain_frame_above bits q_start _ q h_above]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) q h_flag_not_read]
      rw [cuccaro_maj_chain_at_top_carry bits q_start
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f)]
      congr 1
      rw [cuccaro_carry_eq_Adder_carry]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) q_start
            (fun i _ => by omega), h_cin]
      rw [Adder.carry_ext_below false bits
            (fun j => Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
              (q_start + 2 * j + 1))
            (fun j => Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
              (q_start + 2 * j + 2))
            (fun j => x.testBit j) (fun j => (2 ^ bits - N).testBit j)
            (fun j hj => by
              show Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
                  (q_start + 2 * j + 1) = x.testBit j
              rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) _
                    (fun i _ => by omega)]
              exact h_tgt j hj)
            (fun j hj => by
              show Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
                  (q_start + 2 * j + 2) = (2 ^ bits - N).testBit j
              rw [cuccaro_prepareConstRead_at_read bits q_start (2 ^ bits - N) j hj,
                  h_read j hj, Bool.false_xor])]
      rw [Adder.carry_sym]
      exact add_twos_complement_carry_out_eq bits N x hN_pos hN hx
  · rw [update_neq _ _ _ _ hq]
    by_cases h_q_ws : q_start ≤ q ∧ q < q_start + 2 * bits + 1
    · exact sqir_style_compareConst_candidate_workspace_restored_at_general
        bits q_start N flagPos f hflag_out q h_q_ws.1 h_q_ws.2
    · push Not at h_q_ws
      have h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q := by
        by_cases h : q < q_start
        · left; exact h
        · push Not at h
          right; exact h_q_ws h
      exact sqir_style_compareConst_candidate_frame_outside bits q_start N flagPos
        f q hq h_q_outside

/-! ## §4. The register-register comparator (NEW primitive).

`regCompareXor` XORs `[acc < addend]` into the flag, where BOTH operands are
register values: it conjugates the MAJ chain by X on every accumulator bit,
so the top carry computes `¬acc + addend ≥ 2^bits ⟺ acc < addend`
(`carry_compl_lt`).  Compute–CX–uncompute: the workspace is fully restored.
This is the repo's first register-register comparator (the existing
comparators take one CONSTANT operand). -/

def regCompareXor (bits q_start flagPos : Nat) : Gate :=
  Gate.seq (targetComplement bits q_start)
    (Gate.seq (cuccaro_maj_chain bits q_start)
      (Gate.seq (Gate.CX (q_start + 2 * bits) flagPos)
        (Gate.seq (cuccaro_maj_chain_inv bits q_start)
          (targetComplement bits q_start))))

/-- Frame: `regCompareXor` is the identity outside workspace ∪ {flag}. -/
theorem regCompareXor_frame_outside
    (bits q_start flagPos : Nat) (f : Nat → Bool)
    (q : Nat) (h_q_ne : q ≠ flagPos)
    (h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q) :
    Gate.applyNat (regCompareXor bits q_start flagPos) f q = f q := by
  show Gate.applyNat
      (seq (targetComplement bits q_start)
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (targetComplement bits q_start))))) f q = _
  simp only [Gate.applyNat_seq]
  have h_q_not_tgt : ∀ i, i < bits → q ≠ q_start + 2 * i + 1 := by
    intro i hi
    rcases h_q_outside with h | h <;> omega
  rw [targetComplement_at_other bits q_start q h_q_not_tgt]
  rcases h_q_outside with h_below | h_above
  · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ q h_below]
    rw [Gate.applyNat_CX]
    rw [update_neq _ _ _ _ h_q_ne]
    rw [cuccaro_maj_chain_frame_below bits q_start _ q h_below]
    exact targetComplement_at_other bits q_start q h_q_not_tgt f
  · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ q h_above]
    rw [Gate.applyNat_CX]
    rw [update_neq _ _ _ _ h_q_ne]
    rw [cuccaro_maj_chain_frame_above bits q_start _ q h_above]
    exact targetComplement_at_other bits q_start q h_q_not_tgt f

/-- Workspace restoration: at any workspace position, `regCompareXor`
    restores the input value (compute–CX–uncompute). -/
theorem regCompareXor_workspace_restored_at
    (bits q_start flagPos : Nat) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (q : Nat) (hq_lower : q_start ≤ q) (hq_upper : q < q_start + 2 * bits + 1) :
    Gate.applyNat (regCompareXor bits q_start flagPos) f q = f q := by
  show Gate.applyNat
      (seq (targetComplement bits q_start)
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (targetComplement bits q_start))))) f q = _
  simp only [Gate.applyNat_seq, Gate.applyNat_CX]
  by_cases hq_tgt : ∃ i, i < bits ∧ q = q_start + 2 * i + 1
  · obtain ⟨i, hi, hq_eq⟩ := hq_tgt
    rw [hq_eq]
    rw [targetComplement_at_target bits q_start i hi]
    rw [cuccaro_maj_chain_inv_commute_update_outside_workspace
          bits q_start flagPos _ _ hflag_out
          (q_start + 2 * i + 1) (by omega) (by omega)]
    rw [show Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (targetComplement bits q_start) f))
          (q_start + 2 * i + 1)
          = Gate.applyNat (targetComplement bits q_start) f
              (q_start + 2 * i + 1) from ?_]
    · rw [targetComplement_at_target bits q_start i hi, Bool.not_not]
    · rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start
          (Gate.applyNat (targetComplement bits q_start) f)]
  · push Not at hq_tgt
    have h_not_tgt : ∀ i, i < bits → q ≠ q_start + 2 * i + 1 :=
      fun i hi h => hq_tgt i hi h
    rw [targetComplement_at_other bits q_start q h_not_tgt]
    rw [cuccaro_maj_chain_inv_commute_update_outside_workspace
          bits q_start flagPos _ _ hflag_out q hq_lower hq_upper]
    rw [show Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (targetComplement bits q_start) f)) q
          = Gate.applyNat (targetComplement bits q_start) f q from ?_]
    · exact targetComplement_at_other bits q_start q h_not_tgt f
    · rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start
          (Gate.applyNat (targetComplement bits q_start) f)]

/-- **HEADLINE state equation for the register-register comparator.**
    On any state with carry-in clear, accumulator `u` and addend `t`,
    `regCompareXor` is exactly `flag ^= [u < t]` (everything else fixed). -/
theorem regCompareXor_state_general
    (bits q_start flagPos u t : Nat) (f : Nat → Bool)
    (hu : u < 2 ^ bits) (ht : t < 2 ^ bits)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (h_cin : f q_start = false)
    (h_tgt : ∀ i, i < bits → f (q_start + 2 * i + 1) = u.testBit i)
    (h_read : ∀ i, i < bits → f (q_start + 2 * i + 2) = t.testBit i) :
    Gate.applyNat (regCompareXor bits q_start flagPos) f
      = update f flagPos (xor (f flagPos) (decide (u < t))) := by
  funext q
  by_cases hq : q = flagPos
  · subst hq
    rw [update_eq]
    show Gate.applyNat
        (seq (targetComplement bits q_start)
              (seq (cuccaro_maj_chain bits q_start)
                   (seq (Gate.CX (q_start + 2 * bits) q)
                        (seq (cuccaro_maj_chain_inv bits q_start)
                             (targetComplement bits q_start))))) f q = _
    simp only [Gate.applyNat_seq]
    have h_flag_not_tgt : ∀ i, i < bits → q ≠ q_start + 2 * i + 1 := by
      intro i hi
      rcases hflag_out with h | h <;> omega
    rw [targetComplement_at_other bits q_start q h_flag_not_tgt]
    rcases hflag_out with h_below | h_above
    · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ q h_below]
      simp only [Gate.applyNat_CX, update_eq]
      rw [cuccaro_maj_chain_frame_below bits q_start _ q h_below]
      rw [targetComplement_at_other bits q_start q h_flag_not_tgt]
      rw [cuccaro_maj_chain_at_top_carry bits q_start
            (Gate.applyNat (targetComplement bits q_start) f)]
      congr 1
      rw [cuccaro_carry_eq_Adder_carry]
      rw [targetComplement_at_other bits q_start q_start (fun i _ => by omega), h_cin]
      rw [Adder.carry_ext_below false bits
            (fun j => Gate.applyNat (targetComplement bits q_start) f (q_start + 2 * j + 1))
            (fun j => Gate.applyNat (targetComplement bits q_start) f (q_start + 2 * j + 2))
            (fun j => !u.testBit j) (fun j => t.testBit j)
            (fun j hj => by
              show Gate.applyNat (targetComplement bits q_start) f (q_start + 2 * j + 1)
                  = !u.testBit j
              rw [targetComplement_at_target bits q_start j hj, h_tgt j hj])
            (fun j hj => by
              show Gate.applyNat (targetComplement bits q_start) f (q_start + 2 * j + 2)
                  = t.testBit j
              rw [targetComplement_at_other bits q_start _ (fun i _ => by omega)]
              exact h_read j hj)]
      exact carry_compl_lt bits u t hu ht
    · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ q h_above]
      simp only [Gate.applyNat_CX, update_eq]
      rw [cuccaro_maj_chain_frame_above bits q_start _ q h_above]
      rw [targetComplement_at_other bits q_start q h_flag_not_tgt]
      rw [cuccaro_maj_chain_at_top_carry bits q_start
            (Gate.applyNat (targetComplement bits q_start) f)]
      congr 1
      rw [cuccaro_carry_eq_Adder_carry]
      rw [targetComplement_at_other bits q_start q_start (fun i _ => by omega), h_cin]
      rw [Adder.carry_ext_below false bits
            (fun j => Gate.applyNat (targetComplement bits q_start) f (q_start + 2 * j + 1))
            (fun j => Gate.applyNat (targetComplement bits q_start) f (q_start + 2 * j + 2))
            (fun j => !u.testBit j) (fun j => t.testBit j)
            (fun j hj => by
              show Gate.applyNat (targetComplement bits q_start) f (q_start + 2 * j + 1)
                  = !u.testBit j
              rw [targetComplement_at_target bits q_start j hj, h_tgt j hj])
            (fun j hj => by
              show Gate.applyNat (targetComplement bits q_start) f (q_start + 2 * j + 2)
                  = t.testBit j
              rw [targetComplement_at_other bits q_start _ (fun i _ => by omega)]
              exact h_read j hj)]
      exact carry_compl_lt bits u t hu ht
  · rw [update_neq _ _ _ _ hq]
    by_cases h_q_ws : q_start ≤ q ∧ q < q_start + 2 * bits + 1
    · exact regCompareXor_workspace_restored_at bits q_start flagPos f hflag_out
        q h_q_ws.1 h_q_ws.2
    · push Not at h_q_ws
      have h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q := by
        by_cases h : q < q_start
        · left; exact h
        · push Not at h
          right; exact h_q_ws h
      exact regCompareXor_frame_outside bits q_start flagPos f q hq h_q_outside

/-! ## §5. General-state conditional subtract.

`sqir_conditionalSubConstGate` (masked-prepare `2^bits−N` ; adder ;
masked-unprepare) on an ARBITRARY state with clear carry-in and clear read
register: subtracts `N` from the accumulator iff the flag is set, restores
read/carry, preserves the flag and everything outside the workspace. -/

theorem condSub_state_general
    (bits q_start N flagPos x : Nat) (f : Nat → Bool)
    (hx : x < 2 ^ bits)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (h_cin : f q_start = false)
    (h_tgt : ∀ i, i < bits → f (q_start + 2 * i + 1) = x.testBit i)
    (h_read : ∀ i, i < bits → f (q_start + 2 * i + 2) = false) :
    (∀ i, i < bits →
        Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f
            (q_start + 2 * i + 1)
          = ((x + if f flagPos then 2 ^ bits - N else 0) % 2 ^ bits).testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f
            (q_start + 2 * i + 2) = false)
    ∧ Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f q_start
        = false
    ∧ (∀ p, p < q_start ∨ q_start + 2 * bits + 1 ≤ p →
        Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f p = f p) := by
  have h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intro i hi
    rcases hflag_out with h | h <;> omega
  unfold sqir_conditionalSubConstGate
  by_cases hfl : f flagPos
  · -- Flag set: the gate acts as `cuccaro_addConstGate (2^bits − N)`.
    rw [sqir_conditionalAddConstGate_apply_true_fun bits q_start (2 ^ bits - N) flagPos f
          h_flag_distinct hfl hflag_out]
    unfold cuccaro_addConstGate
    simp only [Gate.applyNat_seq]
    -- The prepared state: read register holds `K := 2^bits − N`.
    have h1_read : ∀ i, i < bits →
        Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
            (q_start + 2 * i + 2) = (2 ^ bits - N).testBit i := by
      intro i hi
      rw [cuccaro_prepareConstRead_at_read bits q_start (2 ^ bits - N) i hi,
          h_read i hi, Bool.false_xor]
    have h1_tgt : ∀ i, i < bits →
        Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
            (q_start + 2 * i + 1) = x.testBit i := by
      intro i hi
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) _
            (fun k _ => by omega)]
      exact h_tgt i hi
    have h1_cin : Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
        q_start = false := by
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) q_start
            (fun k _ => by omega)]
      exact h_cin
    -- The adder output on the prepared state.
    have h2_tgt : ∀ i, i < bits →
        Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f)
            (q_start + 2 * i + 1) = (x + (2 ^ bits - N)).testBit i :=
      fun i hi => cuccaro_adder_sum_bits_general bits q_start x (2 ^ bits - N) _
        h1_cin h1_tgt h1_read i hi
    have h2_read : ∀ i, i < bits →
        Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f)
            (q_start + 2 * i + 2) = (2 ^ bits - N).testBit i := by
      intro i hi
      rw [(cuccaro_n_bit_adder_full_correct bits q_start _).2.2 i hi]
      exact h1_read i hi
    have h2_cin : Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f)
        q_start = false := by
      rw [(cuccaro_n_bit_adder_full_correct bits q_start _).1]
      exact h1_cin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) _
            (fun k _ => by omega)]
      rw [h2_tgt i hi, hfl, if_pos rfl]
      rw [Nat.testBit_mod_two_pow,
          show decide (i < bits) = true from decide_eq_true hi, Bool.true_and]
    · intro i hi
      rw [cuccaro_prepareConstRead_at_read bits q_start (2 ^ bits - N) i hi,
          h2_read i hi, Bool.xor_self]
    · rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) q_start
            (fun k _ => by omega)]
      exact h2_cin
    · intro p hp
      have hp_not_read : ∀ k, k < bits → p ≠ q_start + 2 * k + 2 := by
        intro k hk
        rcases hp with h | h <;> omega
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) p hp_not_read]
      rcases hp with h | h
      · rw [cuccaro_n_bit_adder_full_frame_below bits q_start _ p h]
        exact cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) p hp_not_read f
      · rw [cuccaro_n_bit_adder_full_frame_above bits q_start _ p h]
        exact cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) p hp_not_read f
  · -- Flag clear: the gate acts as the bare adder with a zero addend.
    have hfl' : f flagPos = false := by
      revert hfl
      cases f flagPos <;> simp
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start (2 ^ bits - N) flagPos f
          h_flag_distinct hfl' hflag_out]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [cuccaro_adder_sum_bits_general bits q_start x 0 f h_cin h_tgt
            (fun k hk => by rw [h_read k hk, Nat.zero_testBit]) i hi]
      rw [hfl', if_neg (by simp), Nat.add_zero, Nat.mod_eq_of_lt hx]
    · intro i hi
      rw [(cuccaro_n_bit_adder_full_correct bits q_start f).2.2 i hi]
      exact h_read i hi
    · rw [(cuccaro_n_bit_adder_full_correct bits q_start f).1]
      exact h_cin
    · intro p hp
      rcases hp with h | h
      · exact cuccaro_n_bit_adder_full_frame_below bits q_start f p h
      · exact cuccaro_n_bit_adder_full_frame_above bits q_start f p h

/-! ## §6. The register mod-N reduction primitive. -/

/-- Reduction arithmetic: for `x < 2N ≤ 2^bits`,
    `(x + [N ≤ x]·(2^bits − N)) mod 2^bits = x mod N`. -/
private theorem modNReduce_arith (bits N x : Nat)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hx : x < 2 * N) :
    (x + if decide (N ≤ x) then 2 ^ bits - N else 0) % 2 ^ bits = x % N := by
  by_cases h : N ≤ x
  · rw [if_pos (by simp [h] : decide (N ≤ x) = true)]
    have h_eq : x + (2 ^ bits - N) = (x - N) + 2 ^ bits := by omega
    rw [h_eq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x - N < 2 ^ bits)]
    have h_xN : x % N = x - N := by
      conv_lhs => rw [show x = N + (x - N) from by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : x - N < N)]
    rw [h_xN]
  · push Not at h
    rw [if_neg (by simp [Nat.not_le.mpr h] : ¬ decide (N ≤ x) = true)]
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega : x < 2 ^ bits), Nat.mod_eq_of_lt h]

/-- **The register mod-N reduction with comparison flag**:
    constant-compare against `N`, then flag-conditional subtract of `N`.
    Takes an accumulator in `[0, 2N)` to `[0, N)`; the flag picks up
    `[N ≤ acc]` (uncomputed later by `regCompareXor` against the addend). -/
def modNReduceFlag (bits q_start N flagPos : Nat) : Gate :=
  Gate.seq (sqir_style_compareConst_candidate bits q_start N flagPos)
           (sqir_conditionalSubConstGate bits q_start N flagPos)

/-- **HEADLINE general-state bundle for the mod-N reduction.**  On any state
    with clear carry-in / read register / flag and accumulator `x < 2N`:
    accumulator becomes `x mod N`, read and carry stay clear, the flag holds
    `[N ≤ x]`, and everything outside workspace ∪ {flag} is untouched. -/
theorem modNReduceFlag_state_general
    (bits q_start N flagPos x : Nat) (f : Nat → Bool)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hx : x < 2 * N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (h_cin : f q_start = false)
    (h_flag : f flagPos = false)
    (h_tgt : ∀ i, i < bits → f (q_start + 2 * i + 1) = x.testBit i)
    (h_read : ∀ i, i < bits → f (q_start + 2 * i + 2) = false) :
    (∀ i, i < bits →
        Gate.applyNat (modNReduceFlag bits q_start N flagPos) f (q_start + 2 * i + 1)
          = (x % N).testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (modNReduceFlag bits q_start N flagPos) f (q_start + 2 * i + 2)
          = false)
    ∧ Gate.applyNat (modNReduceFlag bits q_start N flagPos) f q_start = false
    ∧ Gate.applyNat (modNReduceFlag bits q_start N flagPos) f flagPos
        = decide (N ≤ x)
    ∧ (∀ p, p ≠ flagPos → p < q_start ∨ q_start + 2 * bits + 1 ≤ p →
        Gate.applyNat (modNReduceFlag bits q_start N flagPos) f p = f p) := by
  have hx' : x < 2 ^ bits := by omega
  have hN : N ≤ 2 ^ bits := by omega
  have h_flag_ne_tgt : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 1 := by
    intro i hi
    rcases hflag_out with h | h <;> omega
  have h_flag_ne_read : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intro i hi
    rcases hflag_out with h | h <;> omega
  have h_flag_ne_cin : flagPos ≠ q_start := by
    rcases hflag_out with h | h <;> omega
  unfold modNReduceFlag
  simp only [Gate.applyNat_seq]
  rw [compareConstXor_state_general bits q_start N flagPos x f
        hN_pos hN hx' hflag_out h_cin h_tgt h_read, h_flag, Bool.false_xor]
  -- The post-compare state: `f` with the flag set to `[N ≤ x]`.
  have hg1_tgt : ∀ i, i < bits →
      update f flagPos (decide (N ≤ x)) (q_start + 2 * i + 1) = x.testBit i := by
    intro i hi
    rw [update_neq _ _ _ _ (fun h => h_flag_ne_tgt i hi h.symm)]
    exact h_tgt i hi
  have hg1_read : ∀ i, i < bits →
      update f flagPos (decide (N ≤ x)) (q_start + 2 * i + 2) = false := by
    intro i hi
    rw [update_neq _ _ _ _ (fun h => h_flag_ne_read i hi h.symm)]
    exact h_read i hi
  have hg1_cin : update f flagPos (decide (N ≤ x)) q_start = false := by
    rw [update_neq _ _ _ _ (fun h => h_flag_ne_cin h.symm)]
    exact h_cin
  have hsub := condSub_state_general bits q_start N flagPos x
    (update f flagPos (decide (N ≤ x))) hx' hflag_out hg1_cin hg1_tgt hg1_read
  refine ⟨?_, hsub.2.1, hsub.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hsub.1 i hi, update_eq]
    rw [modNReduce_arith bits N x hN_pos hN2 hx]
  · rw [hsub.2.2.2 flagPos hflag_out, update_eq]
  · intro p hp_ne hp_out
    rw [hsub.2.2.2 p hp_out]
    exact update_neq _ _ _ _ hp_ne

/-! ## §7. The per-window mod-N lookup-add step and the full circuit.

Layout (Cuccaro, exactly the product-adder multiplier's layout plus one flag):
`ctrl = 0`; address bits `1,3,…,2w−1`; AND-ancillas `2,4,…,2w`;
Cuccaro block at `q_start = 1+2w` (carry-in, then interleaved acc/addend up
to `q_start + 2·bits`); `y`-register at `yBase = q_start + 2·bits + 1`;
the comparison flag at `flagPos = yBase + numWin·w` (one fresh qubit above
the `y`-register — clean in `mulInputOf`). -/

/-- One mod-N lookup-ADD: `acc ← (acc + T[v]) mod N` for the table row
    selected by the address register (Gidney l.296 with per-window
    reduction).  The Cuccaro comparator borrows the addend register for its
    two's-complement constant, so the QROM word is cleared before the
    reduction and re-read for the flag-uncompute register-compare. -/
def modNLookupAddStep (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) : Gate :=
  Gate.seq (lookupReadAt w (addendIdx q_start) bits T)
    (Gate.seq (cuccaro_n_bit_adder_full bits q_start)
      (Gate.seq (lookupReadAt w (addendIdx q_start) bits T)
        (Gate.seq (modNReduceFlag bits q_start N flagPos)
          (Gate.seq (lookupReadAt w (addendIdx q_start) bits T)
            (Gate.seq (regCompareXor bits q_start flagPos)
              (lookupReadAt w (addendIdx q_start) bits T))))))

/-- One mod-N window step: copy window `j` into the address register,
    mod-N lookup-add the entry `T_j[v] = a·(2^w)^j·v mod N`, uncopy. -/
def windowedModNStep (w bits a N q_start yBase flagPos j : Nat) : Gate :=
  Gate.seq (copyWindow w yBase j)
    (Gate.seq (modNLookupAddStep w bits N (WindowedArith.tableValue a N w j)
                q_start flagPos)
      (copyWindow w yBase j))

/-- The per-window mod-N windowed multiplier: a fold of mod-N window steps. -/
def windowedModNMul (w bits a N q_start yBase flagPos numWin : Nat) : Gate :=
  (List.range numWin).foldl
    (fun g j => Gate.seq g (windowedModNStep w bits a N q_start yBase flagPos j))
    Gate.I

/-- **The full per-window mod-N windowed-multiplier circuit** at the standard
    layout (flag above the `y`-register).  On `acc = 0` it leaves
    `(a·y) mod N` in the accumulator. -/
def windowedModNMulCircuit (w bits a N numWin : Nat) : Gate :=
  windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
    (1 + 2 * w + (2 * bits + 1) + numWin * w) numWin

/-! ## §8. The mod-N window-step invariant. -/

/-- **The mod-N window-step invariant.**  After some window-steps starting
    from `mulInputOf cuccaroAdder w bits numWin y`, the state `g` satisfies:
    (F) frame off the Cuccaro block and the flag;
    (D) the addend register is clean;
    (C) the carry-in is clean;
    (G) the flag is clean;
    (V) the accumulator holds the bits of the running mod-N sum `s`. -/
def ModNStepInv (w bits numWin y s : Nat) (g : Nat → Bool) : Prop :=
  (∀ p, ¬ inBlock (1 + 2 * w) (2 * bits + 1) p →
      p ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w →
      g p = mulInputOf cuccaroAdder w bits numWin y p)
  ∧ (∀ i, i < bits → g (1 + 2 * w + 2 * i + 2) = false)
  ∧ g (1 + 2 * w) = false
  ∧ g (1 + 2 * w + (2 * bits + 1) + numWin * w) = false
  ∧ (∀ i, i < bits → g (1 + 2 * w + 2 * i + 1) = s.testBit i)

/-- Invariant initialization: the clean input satisfies the invariant at `0`. -/
theorem modNStepInv_init (w bits numWin y : Nat) :
    ModNStepInv w bits numWin y 0 (mulInputOf cuccaroAdder w bits numWin y) := by
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  refine ⟨fun p _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by rw [hspan]; omega)
  · exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by rw [hspan]; omega)
  · show mulInputOf cuccaroAdder w bits numWin y
        (1 + 2 * w + (2 * bits + 1) + numWin * w) = false
    unfold mulInputOf encodeReg
    rw [if_neg (by unfold ulookup_ctrl_idx; omega), if_neg (by rw [hspan]; omega)]
  · intro i hi
    rw [Nat.zero_testBit]
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by rw [hspan]; omega)

/-! ## §9. The mod-N window step preserves the invariant. -/

theorem modNStepInv_step (w bits a N numWin y : Nat) (hw : 0 < w)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (j : Nat) (hj : j < numWin) (s : Nat) (hs : s < N) (g : Nat → Bool)
    (hg : ModNStepInv w bits numWin y s g) :
    ModNStepInv w bits numWin y
      ((s + WindowedArith.tableValue a N w j (WindowedArith.window w y j)) % N)
      (Gate.applyNat
        (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) j) g) := by
  obtain ⟨hF, hD, hC, hG, hV⟩ := hg
  -- ── Values ─────────────────────────────────────────────────────────────
  have hv : WindowedArith.window w y j < 2 ^ w := WindowedArith.window_lt w y j
  have ht_lt : WindowedArith.tableValue a N w j (WindowedArith.window w y j) < N := by
    unfold WindowedArith.tableValue
    exact Nat.mod_lt _ hN_pos
  -- ── Standing position facts ────────────────────────────────────────────
  have hjw_le : j * w + w ≤ numWin * w := by
    have h1 : (j + 1) * w ≤ numWin * w := Nat.mul_le_mul_right w (by omega)
    have h2 : (j + 1) * w = j * w + w := by ring
    omega
  have hctrl_addr : ∀ i k, i < w → k < w →
      (1 + 2 * w + (2 * bits + 1)) + j * w + i ≠ ulookup_address_idx k :=
    ctrl_ne_addr_of_le_yBase w (1 + 2 * w + (2 * bits + 1)) j (by omega)
  have hpos_high : ∀ k, k < bits → 2 * w < addendIdx (1 + 2 * w) k := by
    intro k hk
    unfold addendIdx
    omega
  have hpos_inj : ∀ k l, k < bits → l < bits →
      addendIdx (1 + 2 * w) k = addendIdx (1 + 2 * w) l → k = l := by
    intro k l _ _ h
    unfold addendIdx at h
    omega
  have hflag_out : 1 + 2 * w + (2 * bits + 1) + numWin * w < 1 + 2 * w ∨
      1 + 2 * w + 2 * bits + 1 ≤ 1 + 2 * w + (2 * bits + 1) + numWin * w := by
    right
    omega
  -- ── Pre-step register values, from the invariant ───────────────────────
  have hg_ctrl : g ulookup_ctrl_idx = true := by
    rw [hF ulookup_ctrl_idx (by unfold inBlock ulookup_ctrl_idx; omega)
          (by unfold ulookup_ctrl_idx; omega)]
    exact mulInputOf_ctrl cuccaroAdder w bits numWin y
  have hg_addr : ∀ i, i < w → g (ulookup_address_idx i) = false := by
    intro i hi
    rw [hF _ (by unfold inBlock ulookup_address_idx; omega)
          (by unfold ulookup_address_idx; omega)]
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx ulookup_address_idx; omega)
      (by unfold ulookup_address_idx; omega)
  have hg_and : ∀ i, i < w → g (ulookup_and_idx i) = false := by
    intro i hi
    rw [hF _ (by unfold inBlock ulookup_and_idx; omega)
          (by unfold ulookup_and_idx; omega)]
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx ulookup_and_idx; omega)
      (by unfold ulookup_and_idx; omega)
  have hg_y : ∀ i, i < w →
      g ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hF _ (by unfold inBlock; omega) (by omega)]
    exact mulInputOf_eq_encodeReg cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega)
  -- ── Expose the nine-fold composition ───────────────────────────────────
  simp only [windowedModNStep, modNLookupAddStep, Gate.applyNat_seq]
  set g1 : Nat → Bool :=
    Gate.applyNat (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) g with hg1def
  set g2 : Nat → Bool :=
    Gate.applyNat (lookupReadAt w (addendIdx (1 + 2 * w)) bits
      (WindowedArith.tableValue a N w j)) g1 with hg2def
  set g3 : Nat → Bool :=
    Gate.applyNat (cuccaro_n_bit_adder_full bits (1 + 2 * w)) g2 with hg3def
  set g4 : Nat → Bool :=
    Gate.applyNat (lookupReadAt w (addendIdx (1 + 2 * w)) bits
      (WindowedArith.tableValue a N w j)) g3 with hg4def
  set g5 : Nat → Bool :=
    Gate.applyNat (modNReduceFlag bits (1 + 2 * w) N
      (1 + 2 * w + (2 * bits + 1) + numWin * w)) g4 with hg5def
  set g6 : Nat → Bool :=
    Gate.applyNat (lookupReadAt w (addendIdx (1 + 2 * w)) bits
      (WindowedArith.tableValue a N w j)) g5 with hg6def
  set g7 : Nat → Bool :=
    Gate.applyNat (regCompareXor bits (1 + 2 * w)
      (1 + 2 * w + (2 * bits + 1) + numWin * w)) g6 with hg7def
  set g8 : Nat → Bool :=
    Gate.applyNat (lookupReadAt w (addendIdx (1 + 2 * w)) bits
      (WindowedArith.tableValue a N w j)) g7 with hg8def
  -- ── g₁ = copyWindow: the address register receives the window digit ────
  have hg1_frame : ∀ p, (∀ i, i < w → p ≠ ulookup_address_idx i) → g1 p = g p :=
    fun p hp => copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j g p hp
  have hg1_addr : ∀ i, i < w →
      g1 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i :=
    fun i hi => copyWindow_loads_window w (1 + 2 * w + (2 * bits + 1)) numWin y j g
      hctrl_addr hg_addr hg_y hj i hi
  have hg1_ctrl : g1 ulookup_ctrl_idx = true := by
    rw [hg1_frame _ (fun i hi => by unfold ulookup_ctrl_idx ulookup_address_idx; omega)]
    exact hg_ctrl
  have hg1_and : ∀ i, i < w → g1 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg1_frame _ (fun k hk => by unfold ulookup_and_idx ulookup_address_idx; omega)]
    exact hg_and i hi
  have hg1_read : ∀ i, i < bits → g1 (addendIdx (1 + 2 * w) i) = false := by
    intro i hi
    rw [hg1_frame _ (fun k hk => by unfold addendIdx ulookup_address_idx; omega)]
    exact hD i hi
  have hg1_tgt : ∀ i, i < bits → g1 (1 + 2 * w + 2 * i + 1) = s.testBit i := by
    intro i hi
    rw [hg1_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hV i hi
  have hg1_cin : g1 (1 + 2 * w) = false := by
    rw [hg1_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hC
  have hg1_flag : g1 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hg1_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hG
  have hg1_y : ∀ i, i < w →
      g1 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg1_frame _ (fun k hk => hctrl_addr i k hi hk)]
    exact hg_y i hi
  -- ── g₂ = QROM read: the table row lands in the addend register ─────────
  have hg2_frame : ∀ p, (∀ k, k < bits → p ≠ addendIdx (1 + 2 * w) k) → g2 p = g1 p :=
    fun p hp => lookupReadAt_frame w bits (WindowedArith.tableValue a N w j)
      (addendIdx (1 + 2 * w)) g1 hpos_high p hp
  have hg2_read : ∀ i, i < bits →
      g2 (addendIdx (1 + 2 * w) i)
        = (WindowedArith.tableValue a N w j (WindowedArith.window w y j)).testBit i := by
    intro i hi
    rw [hg2def,
        lookupReadAt_selects_word w bits (WindowedArith.tableValue a N w j)
          (addendIdx (1 + 2 * w)) g1 (WindowedArith.window w y j)
          hw hv hg1_ctrl hg1_addr hg1_and hpos_high hpos_inj i hi,
        hg1_read i hi, Bool.false_xor]
  have hg2_ctrl : g2 ulookup_ctrl_idx = true := by
    rw [hg2_frame _ (fun k hk => by unfold ulookup_ctrl_idx addendIdx; omega)]
    exact hg1_ctrl
  have hg2_addr : ∀ i, i < w →
      g2 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg2_frame _ (fun k hk => by unfold ulookup_address_idx addendIdx; omega)]
    exact hg1_addr i hi
  have hg2_and : ∀ i, i < w → g2 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg2_frame _ (fun k hk => by unfold ulookup_and_idx addendIdx; omega)]
    exact hg1_and i hi
  have hg2_tgt : ∀ i, i < bits → g2 (1 + 2 * w + 2 * i + 1) = s.testBit i := by
    intro i hi
    rw [hg2_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg1_tgt i hi
  have hg2_cin : g2 (1 + 2 * w) = false := by
    rw [hg2_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg1_cin
  have hg2_flag : g2 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hg2_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg1_flag
  have hg2_y : ∀ i, i < w →
      g2 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg2_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg1_y i hi
  -- ── g₃ = the adder: acc ← s + t (no overflow: s + t < 2N ≤ 2^bits) ─────
  have hg3_frame : ∀ p, p < 1 + 2 * w ∨ 1 + 2 * w + 2 * bits + 1 ≤ p →
      g3 p = g2 p := by
    intro p hp
    rcases hp with h | h
    · exact cuccaro_n_bit_adder_full_frame_below bits (1 + 2 * w) g2 p h
    · exact cuccaro_n_bit_adder_full_frame_above bits (1 + 2 * w) g2 p h
  have hg3_tgt : ∀ i, i < bits →
      g3 (1 + 2 * w + 2 * i + 1)
        = (s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)).testBit i := by
    intro i hi
    show Gate.applyNat (cuccaro_n_bit_adder_full bits (1 + 2 * w)) g2
        (1 + 2 * w + 2 * i + 1) = _
    exact cuccaro_adder_sum_bits_general bits (1 + 2 * w) s
      (WindowedArith.tableValue a N w j (WindowedArith.window w y j)) g2
      hg2_cin hg2_tgt hg2_read i hi
  have hg3_read : ∀ i, i < bits →
      g3 (addendIdx (1 + 2 * w) i)
        = (WindowedArith.tableValue a N w j (WindowedArith.window w y j)).testBit i := by
    intro i hi
    show Gate.applyNat (cuccaro_n_bit_adder_full bits (1 + 2 * w)) g2
        (1 + 2 * w + 2 * i + 2) = _
    rw [(cuccaro_n_bit_adder_full_correct bits (1 + 2 * w) g2).2.2 i hi]
    exact hg2_read i hi
  have hg3_cin : g3 (1 + 2 * w) = false := by
    show Gate.applyNat (cuccaro_n_bit_adder_full bits (1 + 2 * w)) g2 (1 + 2 * w) = _
    rw [(cuccaro_n_bit_adder_full_correct bits (1 + 2 * w) g2).1]
    exact hg2_cin
  have hg3_ctrl : g3 ulookup_ctrl_idx = true := by
    rw [hg3_frame _ (by unfold ulookup_ctrl_idx; omega)]
    exact hg2_ctrl
  have hg3_addr : ∀ i, i < w →
      g3 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg3_frame _ (by unfold ulookup_address_idx; omega)]
    exact hg2_addr i hi
  have hg3_and : ∀ i, i < w → g3 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg3_frame _ (by unfold ulookup_and_idx; omega)]
    exact hg2_and i hi
  have hg3_flag : g3 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hg3_frame _ (by omega)]
    exact hg2_flag
  have hg3_y : ∀ i, i < w →
      g3 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg3_frame _ (by omega)]
    exact hg2_y i hi
  -- ── g₄ = QROM read again: the addend register is cleared ───────────────
  have hg4_frame : ∀ p, (∀ k, k < bits → p ≠ addendIdx (1 + 2 * w) k) → g4 p = g3 p :=
    fun p hp => lookupReadAt_frame w bits (WindowedArith.tableValue a N w j)
      (addendIdx (1 + 2 * w)) g3 hpos_high p hp
  have hg4_read : ∀ i, i < bits → g4 (addendIdx (1 + 2 * w) i) = false := by
    intro i hi
    rw [hg4def,
        lookupReadAt_selects_word w bits (WindowedArith.tableValue a N w j)
          (addendIdx (1 + 2 * w)) g3 (WindowedArith.window w y j)
          hw hv hg3_ctrl hg3_addr hg3_and hpos_high hpos_inj i hi,
        hg3_read i hi, Bool.xor_self]
  have hg4_tgt : ∀ i, i < bits →
      g4 (1 + 2 * w + 2 * i + 1)
        = (s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)).testBit i := by
    intro i hi
    rw [hg4_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg3_tgt i hi
  have hg4_cin : g4 (1 + 2 * w) = false := by
    rw [hg4_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg3_cin
  have hg4_flag : g4 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hg4_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg3_flag
  have hg4_ctrl : g4 ulookup_ctrl_idx = true := by
    rw [hg4_frame _ (fun k hk => by unfold ulookup_ctrl_idx addendIdx; omega)]
    exact hg3_ctrl
  have hg4_addr : ∀ i, i < w →
      g4 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg4_frame _ (fun k hk => by unfold ulookup_address_idx addendIdx; omega)]
    exact hg3_addr i hi
  have hg4_and : ∀ i, i < w → g4 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg4_frame _ (fun k hk => by unfold ulookup_and_idx addendIdx; omega)]
    exact hg3_and i hi
  have hg4_y : ∀ i, i < w →
      g4 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg4_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg3_y i hi
  -- ── g₅ = mod-N reduction: acc ← (s+t) mod N, flag ← [N ≤ s+t] ──────────
  have hred := modNReduceFlag_state_general bits (1 + 2 * w) N
    (1 + 2 * w + (2 * bits + 1) + numWin * w)
    (s + WindowedArith.tableValue a N w j (WindowedArith.window w y j)) g4
    hN_pos hN2 (by omega) hflag_out hg4_cin hg4_flag hg4_tgt hg4_read
  have hg5_tgt : ∀ i, i < bits →
      g5 (1 + 2 * w + 2 * i + 1)
        = ((s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)) % N).testBit i :=
    fun i hi => hred.1 i hi
  have hg5_read : ∀ i, i < bits → g5 (addendIdx (1 + 2 * w) i) = false :=
    fun i hi => hred.2.1 i hi
  have hg5_cin : g5 (1 + 2 * w) = false := hred.2.2.1
  have hg5_flag : g5 (1 + 2 * w + (2 * bits + 1) + numWin * w)
      = decide (N ≤ s + WindowedArith.tableValue a N w j
          (WindowedArith.window w y j)) := hred.2.2.2.1
  have hg5_frame : ∀ p, p ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w →
      p < 1 + 2 * w ∨ 1 + 2 * w + 2 * bits + 1 ≤ p → g5 p = g4 p :=
    fun p hp hout => hred.2.2.2.2 p hp hout
  have hg5_ctrl : g5 ulookup_ctrl_idx = true := by
    rw [hg5_frame _ (by unfold ulookup_ctrl_idx; omega)
          (by unfold ulookup_ctrl_idx; omega)]
    exact hg4_ctrl
  have hg5_addr : ∀ i, i < w →
      g5 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg5_frame _ (by unfold ulookup_address_idx; omega)
          (by unfold ulookup_address_idx; omega)]
    exact hg4_addr i hi
  have hg5_and : ∀ i, i < w → g5 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg5_frame _ (by unfold ulookup_and_idx; omega)
          (by unfold ulookup_and_idx; omega)]
    exact hg4_and i hi
  have hg5_y : ∀ i, i < w →
      g5 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg5_frame _ (by omega) (by omega)]
    exact hg4_y i hi
  -- ── g₆ = QROM read: the addend register reloads the table row ──────────
  have hg6_frame : ∀ p, (∀ k, k < bits → p ≠ addendIdx (1 + 2 * w) k) → g6 p = g5 p :=
    fun p hp => lookupReadAt_frame w bits (WindowedArith.tableValue a N w j)
      (addendIdx (1 + 2 * w)) g5 hpos_high p hp
  have hg6_read : ∀ i, i < bits →
      g6 (addendIdx (1 + 2 * w) i)
        = (WindowedArith.tableValue a N w j (WindowedArith.window w y j)).testBit i := by
    intro i hi
    rw [hg6def,
        lookupReadAt_selects_word w bits (WindowedArith.tableValue a N w j)
          (addendIdx (1 + 2 * w)) g5 (WindowedArith.window w y j)
          hw hv hg5_ctrl hg5_addr hg5_and hpos_high hpos_inj i hi,
        hg5_read i hi, Bool.false_xor]
  have hg6_tgt : ∀ i, i < bits →
      g6 (1 + 2 * w + 2 * i + 1)
        = ((s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)) % N).testBit i := by
    intro i hi
    rw [hg6_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg5_tgt i hi
  have hg6_cin : g6 (1 + 2 * w) = false := by
    rw [hg6_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg5_cin
  have hg6_flag : g6 (1 + 2 * w + (2 * bits + 1) + numWin * w)
      = decide (N ≤ s + WindowedArith.tableValue a N w j
          (WindowedArith.window w y j)) := by
    rw [hg6_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg5_flag
  have hg6_ctrl : g6 ulookup_ctrl_idx = true := by
    rw [hg6_frame _ (fun k hk => by unfold ulookup_ctrl_idx addendIdx; omega)]
    exact hg5_ctrl
  have hg6_addr : ∀ i, i < w →
      g6 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg6_frame _ (fun k hk => by unfold ulookup_address_idx addendIdx; omega)]
    exact hg5_addr i hi
  have hg6_and : ∀ i, i < w → g6 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg6_frame _ (fun k hk => by unfold ulookup_and_idx addendIdx; omega)]
    exact hg5_and i hi
  have hg6_y : ∀ i, i < w →
      g6 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg6_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg5_y i hi
  -- ── g₇ = register-compare: the flag is uncomputed ──────────────────────
  have happ7 : Gate.applyNat (regCompareXor bits (1 + 2 * w)
      (1 + 2 * w + (2 * bits + 1) + numWin * w)) g6
      = update g6 (1 + 2 * w + (2 * bits + 1) + numWin * w) false := by
    rw [regCompareXor_state_general bits (1 + 2 * w)
          (1 + 2 * w + (2 * bits + 1) + numWin * w)
          ((s + WindowedArith.tableValue a N w j (WindowedArith.window w y j)) % N)
          (WindowedArith.tableValue a N w j (WindowedArith.window w y j)) g6
          (by have := Nat.mod_lt (s + WindowedArith.tableValue a N w j
                (WindowedArith.window w y j)) hN_pos; omega)
          (by omega) hflag_out hg6_cin hg6_tgt hg6_read]
    rw [hg6_flag,
        modReduce_lt_decide N s
          (WindowedArith.tableValue a N w j (WindowedArith.window w y j)) hs ht_lt,
        Bool.xor_self]
  have hg7_other : ∀ p, p ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w →
      g7 p = g6 p := by
    intro p hp
    show Gate.applyNat (regCompareXor bits (1 + 2 * w)
        (1 + 2 * w + (2 * bits + 1) + numWin * w)) g6 p = _
    rw [happ7]
    exact update_neq _ _ _ _ hp
  have hg7_flag : g7 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    show Gate.applyNat (regCompareXor bits (1 + 2 * w)
        (1 + 2 * w + (2 * bits + 1) + numWin * w)) g6
        (1 + 2 * w + (2 * bits + 1) + numWin * w) = _
    rw [happ7]
    exact update_eq _ _ _
  have hg7_ctrl : g7 ulookup_ctrl_idx = true := by
    rw [hg7_other _ (by unfold ulookup_ctrl_idx; omega)]
    exact hg6_ctrl
  have hg7_addr : ∀ i, i < w →
      g7 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg7_other _ (by unfold ulookup_address_idx; omega)]
    exact hg6_addr i hi
  have hg7_and : ∀ i, i < w → g7 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg7_other _ (by unfold ulookup_and_idx; omega)]
    exact hg6_and i hi
  have hg7_read : ∀ i, i < bits →
      g7 (addendIdx (1 + 2 * w) i)
        = (WindowedArith.tableValue a N w j (WindowedArith.window w y j)).testBit i := by
    intro i hi
    rw [hg7_other _ (by unfold addendIdx; omega)]
    exact hg6_read i hi
  have hg7_tgt : ∀ i, i < bits →
      g7 (1 + 2 * w + 2 * i + 1)
        = ((s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)) % N).testBit i := by
    intro i hi
    rw [hg7_other _ (by omega)]
    exact hg6_tgt i hi
  have hg7_cin : g7 (1 + 2 * w) = false := by
    rw [hg7_other _ (by omega)]
    exact hg6_cin
  have hg7_y : ∀ i, i < w →
      g7 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg7_other _ (by omega)]
    exact hg6_y i hi
  -- ── g₈ = QROM read: the addend register is cleared again ───────────────
  have hg8_frame : ∀ p, (∀ k, k < bits → p ≠ addendIdx (1 + 2 * w) k) → g8 p = g7 p :=
    fun p hp => lookupReadAt_frame w bits (WindowedArith.tableValue a N w j)
      (addendIdx (1 + 2 * w)) g7 hpos_high p hp
  have hg8_read : ∀ i, i < bits → g8 (addendIdx (1 + 2 * w) i) = false := by
    intro i hi
    rw [hg8def,
        lookupReadAt_selects_word w bits (WindowedArith.tableValue a N w j)
          (addendIdx (1 + 2 * w)) g7 (WindowedArith.window w y j)
          hw hv hg7_ctrl hg7_addr hg7_and hpos_high hpos_inj i hi,
        hg7_read i hi, Bool.xor_self]
  have hg8_addr : ∀ i, i < w →
      g8 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg8_frame _ (fun k hk => by unfold ulookup_address_idx addendIdx; omega)]
    exact hg7_addr i hi
  have hg8_tgt : ∀ i, i < bits →
      g8 (1 + 2 * w + 2 * i + 1)
        = ((s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)) % N).testBit i := by
    intro i hi
    rw [hg8_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg7_tgt i hi
  have hg8_cin : g8 (1 + 2 * w) = false := by
    rw [hg8_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg7_cin
  have hg8_flag : g8 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hg8_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg7_flag
  have hg8_y : ∀ i, i < w →
      g8 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg8_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg7_y i hi
  -- ── g₉ = copyWindow again: the address register is cleared ─────────────
  have hg9_frame : ∀ p, (∀ i, i < w → p ≠ ulookup_address_idx i) →
      Gate.applyNat (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) g8 p = g8 p :=
    fun p hp => copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j g8 p hp
  have hg9_addr : ∀ i, i < w →
      Gate.applyNat (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) g8
        (ulookup_address_idx i) = false := by
    intro i hi
    rw [copyWindow_at_addr w (1 + 2 * w + (2 * bits + 1)) j g8 hctrl_addr i hi,
        hg8_addr i hi, hg8_y i hi,
        encodeReg_window_bit (1 + 2 * w + (2 * bits + 1)) w numWin y j i hi hj,
        Bool.xor_self]
  -- ── Reassemble the invariant ───────────────────────────────────────────
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (F) frame off the block and the flag.
    intro p hpb hpf
    by_cases hpaddr : ∃ i, i < w ∧ p = ulookup_address_idx i
    · obtain ⟨i, hi, rfl⟩ := hpaddr
      rw [hg9_addr i hi]
      exact (mulInputOf_low cuccaroAdder w bits numWin y _
        (by unfold ulookup_ctrl_idx ulookup_address_idx; omega)
        (by unfold ulookup_address_idx; omega)).symm
    · push Not at hpaddr
      have hp_not_addr : ∀ i, i < w → p ≠ ulookup_address_idx i :=
        fun i hi => hpaddr i hi
      have hp_not_pos : ∀ k, k < bits → p ≠ addendIdx (1 + 2 * w) k := by
        intro k hk heq
        apply hpb
        unfold addendIdx at heq
        unfold inBlock
        omega
      have hp_out : p < 1 + 2 * w ∨ 1 + 2 * w + 2 * bits + 1 ≤ p := by
        unfold inBlock at hpb
        omega
      rw [hg9_frame p hp_not_addr, hg8_frame p hp_not_pos, hg7_other p hpf,
          hg6_frame p hp_not_pos, hg5_frame p hpf hp_out, hg4_frame p hp_not_pos,
          hg3_frame p hp_out, hg2_frame p hp_not_pos, hg1_frame p hp_not_addr]
      exact hF p hpb hpf
  · -- (D) the addend register is clean again.
    intro i hi
    rw [hg9_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hg8_read i hi
  · -- (C) the carry-in is clean.
    rw [hg9_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hg8_cin
  · -- (G) the flag is clean again (uncomputed by the register-compare).
    rw [hg9_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hg8_flag
  · -- (V) the accumulator holds the new mod-N partial sum.
    intro i hi
    rw [hg9_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hg8_tgt i hi

/-! ## §10. The fold: the invariant holds after every prefix of window steps. -/

/-- Running the first `n ≤ numWin` mod-N window steps establishes the
    invariant with running value `windowedLookupFold a N w (window w y) n 0`
    — the circuit-aligned per-window mod-N fold of `WindowedArith`. -/
theorem modNStepInv_fold (w bits a N numWin y : Nat) (hw : 0 < w)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) :
    ∀ n, n ≤ numWin →
      ModNStepInv w bits numWin y
        (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) n 0)
        (Gate.applyNat
          (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
          (mulInputOf cuccaroAdder w bits numWin y)) := by
  intro n
  induction n with
  | zero =>
    intro _
    show ModNStepInv w bits numWin y
      (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) 0 0)
      (Gate.applyNat Gate.I (mulInputOf cuccaroAdder w bits numWin y))
    rw [Gate.applyNat_I]
    exact modNStepInv_init w bits numWin y
  | succ n ih =>
    intro hn
    have hsplit : windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = Gate.seq
            (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold windowedModNMul
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq]
    have hfold_lt : WindowedArith.windowedLookupFold a N w
        (WindowedArith.window w y) n 0 < N := by
      cases n with
      | zero => exact hN_pos
      | succ m => exact Nat.mod_lt _ hN_pos
    exact modNStepInv_step w bits a N numWin y hw hN_pos hN2 n (by omega) _
      hfold_lt _ (ih (by omega))

/-! ## §11. HEADLINE — the per-window mod-N windowed multiplier is correct. -/

/-- **HEADLINE — per-window mod-N windowed-multiplier VALUE theorem.**
    The full per-window mod-N circuit (each window doing
    `acc ← (acc + T_j[v]) mod N` with `T_j[v] = a·(2^w)^j·v mod N`),
    run on the SAME clean encoded input as the product-adder multiplier
    (`mulInputOf cuccaroAdder`: ctrl set, `y` in the y-register, everything
    else — including the new comparison-flag qubit — clean), leaves

        (a · y) mod N

    in the accumulator, provided `0 < w`, `0 < N`, `2·N ≤ 2^bits`, and
    `y < 2^(w·numWin)`.  This closes the "product-adder only" gap: the
    multiplier reduces mod N after EVERY window, exactly as in Gidney
    (arXiv:1905.07682). -/
theorem windowedModNMulCircuit_correct (w bits a N numWin y : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < 2 ^ (w * numWin)) :
    decodeAccOf cuccaroAdder
        (Gate.applyNat (windowedModNMulCircuit w bits a N numWin)
          (mulInputOf cuccaroAdder w bits numWin y)) (1 + 2 * w) bits
      = (a * y) % N := by
  have hy' : y < (2 ^ w) ^ numWin := by
    rw [← pow_mul]
    exact hy
  have hfold := (modNStepInv_fold w bits a N numWin y hw hN_pos hN2 numWin
    (le_refl numWin)).2.2.2.2
  have hfold_lt : WindowedArith.windowedLookupFold a N w
      (WindowedArith.window w y) numWin 0 < N := by
    rw [WindowedArith.windowedLookupFold_eq a N w (WindowedArith.window w y) 0
          hN_pos numWin]
    exact Nat.mod_lt _ hN_pos
  have hval : WindowedArith.windowedLookupFold a N w
      (WindowedArith.window w y) numWin 0 = (a * y) % N :=
    WindowedArith.windowedLookupFold_eq_modmul a N w numWin y hN_pos hy'
  show decodeReg (cuccaroAdder.augendIdx (1 + 2 * w)) bits
      (Gate.applyNat (windowedModNMulCircuit w bits a N numWin)
        (mulInputOf cuccaroAdder w bits numWin y)) = (a * y) % N
  unfold windowedModNMulCircuit
  rw [decodeReg_eq_mod_of_testBit (cuccaroAdder.augendIdx (1 + 2 * w)) bits
        (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) numWin 0)
        _ (fun i hi => hfold i hi)]
  rw [Nat.mod_eq_of_lt (by omega :
        WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) numWin 0
          < 2 ^ bits)]
  exact hval

/-! ## §12. Toffoli/T-counts (kernel-clean, exact).

Per window: four table reads (`4·14·w·2^w` T), one Cuccaro add (`14·bits`),
one constant compare (`14·bits`), one conditional subtract (`14·bits`), one
register-compare flag-uncompute (`14·bits`) — copies/prepares are T-free.
Versus the product-adder step (`28·w·2^w + 14·bits`), the per-window mod-N
reduction costs two extra table reads and three extra MAJ-chain passes. -/

private theorem tcount_targetComplement :
    ∀ (n q_start : Nat), tcount (targetComplement n q_start) = 0
  | 0, _ => rfl
  | n + 1, q_start => by
    show tcount (targetComplement n q_start) + tcount (Gate.X (q_start + 2 * n + 1)) = 0
    rw [tcount_targetComplement n q_start]
    rfl

private theorem tcount_majChain :
    ∀ (n q_start : Nat), tcount (cuccaro_maj_chain n q_start) = 7 * n
  | 0, _ => rfl
  | n + 1, q_start => by
    show tcount (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
        + tcount (cuccaro_maj_chain n (q_start + 2)) = 7 * (n + 1)
    rw [tcount_majChain n (q_start + 2)]
    show 7 + 7 * n = 7 * (n + 1)
    ring

private theorem tcount_majChainInv :
    ∀ (n q_start : Nat), tcount (cuccaro_maj_chain_inv n q_start) = 7 * n
  | 0, _ => rfl
  | n + 1, q_start => by
    show tcount (cuccaro_maj_chain_inv n (q_start + 2))
        + tcount (cuccaro_MAJ_inv q_start (q_start + 1) (q_start + 2)) = 7 * (n + 1)
    rw [tcount_majChainInv n (q_start + 2)]
    show 7 * n + 7 = 7 * (n + 1)
    ring

private theorem tcount_prep0 :
    ∀ (n q_start c : Nat), tcount (cuccaro_prepareConstRead n q_start c) = 0
  | 0, _, _ => rfl
  | n + 1, q_start, c => by
    show tcount (cuccaro_prepareConstRead n q_start c)
        + tcount (cond (c.testBit n) (Gate.X (q_start + 2 * n + 2)) Gate.I) = 0
    rw [tcount_prep0 n q_start c]
    cases c.testBit n <;> rfl

private theorem tcount_maskedPrep0 :
    ∀ (n q_start N flagPos : Nat),
      tcount (sqir_prepareMaskedConstRead n q_start N flagPos) = 0
  | 0, _, _, _ => rfl
  | n + 1, q_start, N, flagPos => by
    show tcount (sqir_prepareMaskedConstRead n q_start N flagPos)
        + tcount (cond (N.testBit n) (Gate.CX flagPos (q_start + 2 * n + 2)) Gate.I) = 0
    rw [tcount_maskedPrep0 n q_start N flagPos]
    cases N.testBit n <;> rfl

/-- The register-register comparator costs two MAJ-chain passes: `14·bits` T. -/
theorem tcount_regCompareXor (bits q_start flagPos : Nat) :
    tcount (regCompareXor bits q_start flagPos) = 14 * bits := by
  show tcount (targetComplement bits q_start)
      + (tcount (cuccaro_maj_chain bits q_start)
        + (tcount (Gate.CX (q_start + 2 * bits) flagPos)
          + (tcount (cuccaro_maj_chain_inv bits q_start)
            + tcount (targetComplement bits q_start)))) = 14 * bits
  rw [tcount_targetComplement, tcount_majChain, tcount_majChainInv]
  show 0 + (7 * bits + (0 + (7 * bits + 0))) = 14 * bits
  ring

private theorem tcount_compareConstC (bits q_start N flagPos : Nat) :
    tcount (sqir_style_compareConst_candidate bits q_start N flagPos) = 14 * bits := by
  show tcount (cuccaro_prepareConstRead bits q_start (2 ^ bits - N))
      + (tcount (cuccaro_maj_chain bits q_start)
        + (tcount (Gate.CX (q_start + 2 * bits) flagPos)
          + (tcount (cuccaro_maj_chain_inv bits q_start)
            + tcount (cuccaro_prepareConstRead bits q_start (2 ^ bits - N))))) = 14 * bits
  rw [tcount_prep0, tcount_majChain, tcount_majChainInv]
  show 0 + (7 * bits + (0 + (7 * bits + 0))) = 14 * bits
  ring

private theorem tcount_condSub (bits q_start N flagPos : Nat) :
    tcount (sqir_conditionalSubConstGate bits q_start N flagPos) = 14 * bits := by
  show tcount (sqir_prepareMaskedConstRead bits q_start (2 ^ bits - N) flagPos)
      + (tcount (cuccaro_n_bit_adder_full bits q_start)
        + tcount (sqir_prepareMaskedConstRead bits q_start (2 ^ bits - N) flagPos))
      = 14 * bits
  rw [tcount_maskedPrep0, tcount_cuccaro_n_bit_adder_full]
  ring

/-- The mod-N reduction (compare + conditional subtract): `28·bits` T. -/
theorem tcount_modNReduceFlag (bits q_start N flagPos : Nat) :
    tcount (modNReduceFlag bits q_start N flagPos) = 28 * bits := by
  show tcount (sqir_style_compareConst_candidate bits q_start N flagPos)
      + tcount (sqir_conditionalSubConstGate bits q_start N flagPos) = 28 * bits
  rw [tcount_compareConstC, tcount_condSub]
  ring

/-- One mod-N lookup-add: `56·w·2^w + 56·bits` T (four table reads, one add,
    one compare, one conditional subtract, one register-compare). -/
theorem tcount_modNLookupAddStep (w bits N : Nat) (T : Nat → Nat)
    (q_start flagPos : Nat) :
    tcount (modNLookupAddStep w bits N T q_start flagPos)
      = 56 * w * 2 ^ w + 56 * bits := by
  show tcount (lookupReadAt w (addendIdx q_start) bits T)
      + (tcount (cuccaro_n_bit_adder_full bits q_start)
        + (tcount (lookupReadAt w (addendIdx q_start) bits T)
          + (tcount (modNReduceFlag bits q_start N flagPos)
            + (tcount (lookupReadAt w (addendIdx q_start) bits T)
              + (tcount (regCompareXor bits q_start flagPos)
                + tcount (lookupReadAt w (addendIdx q_start) bits T))))))
      = 56 * w * 2 ^ w + 56 * bits
  rw [tcount_lookupReadAt, tcount_cuccaro_n_bit_adder_full, tcount_modNReduceFlag,
      tcount_regCompareXor]
  ring

/-- One mod-N window step: copies are T-free, so `56·w·2^w + 56·bits` T. -/
theorem tcount_windowedModNStep (w bits a N q_start yBase flagPos j : Nat) :
    tcount (windowedModNStep w bits a N q_start yBase flagPos j)
      = 56 * w * 2 ^ w + 56 * bits := by
  show tcount (copyWindow w yBase j)
      + (tcount (modNLookupAddStep w bits N (WindowedArith.tableValue a N w j)
          q_start flagPos)
        + tcount (copyWindow w yBase j)) = 56 * w * 2 ^ w + 56 * bits
  rw [tcount_copyWindow, tcount_modNLookupAddStep]
  ring

/-- **Closed-form T-count of the per-window mod-N windowed multiplier**:
    `numWin · (56·w·2^w + 56·bits)`. -/
theorem tcount_windowedModNMulCircuit (w bits a N numWin : Nat) :
    tcount (windowedModNMulCircuit w bits a N numWin)
      = numWin * (56 * w * 2 ^ w + 56 * bits) := by
  rw [windowedModNMulCircuit, windowedModNMul,
      tcount_foldl_seq_const
        (fun j => windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) j)
        (56 * w * 2 ^ w + 56 * bits)
        (fun j => tcount_windowedModNStep w bits a N (1 + 2 * w)
          (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) j)]
  simp [tcount, List.length_range]

end FormalRV.Shor.WindowedCircuit
