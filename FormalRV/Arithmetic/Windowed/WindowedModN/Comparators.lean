/- WindowedModN — §3-4 constant + register-register comparators.
   Part of `WindowedModN` (the `WindowedModN.lean` shim re-exports all parts). -/
import FormalRV.Arithmetic.Windowed.WindowedModN.Helpers

namespace FormalRV.Shor.WindowedCircuit
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

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


end FormalRV.Shor.WindowedCircuit
