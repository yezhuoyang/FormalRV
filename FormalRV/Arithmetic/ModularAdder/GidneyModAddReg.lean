/-
  FormalRV.Arithmetic.ModularAdder.GidneyModAddReg — the KEYSTONE: a value-correct
  REGISTER-register MEASURED modular adder `target := (target + read) % p`.

  ## Why this exists

  `GidneySubtractFixup.gidneyModAddFixup` adds a *constant* `(x + c) % p`.  The faithful
  windowed multiplier needs to add the *looked-up register value* `T[window]` into the
  accumulator mod `N` — a register-register modular add.  This file builds it, reusing the
  subtract-fixup machinery: the front adds the read register (`gidneyAdderMeasured`), clears the
  read word (`mz`), and subtracts `p` (`addConstMeasured (2^W − p)`); the result is the SAME
  intermediate the constant fixup produces with `c := read`, so stages 2–4 (copy underflow flag,
  conditional `+p`, measure-clear) reuse `fixup_value`/`conditionalAddP_bundle` verbatim.

  `gidneyModAddRegMeasured_correct`: on the clean input `adder_input_F (bits+1) b x` (read `= b`,
  target `= x`, both `< p`), the low `bits` register decodes to `(x + b) % p`, and the top qubit
  and the fixup-flag ancilla are released to `0`.  Every Toffoli is a measured temporary AND.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Correctness
import FormalRV.Shor.GidneyRunwayMul

namespace FormalRV.Arithmetic.ModularAdder.GidneyModAddReg

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup
open FormalRV.Shor.GidneyRunwayMul

/-- **The COST-OPTIMAL register-register measured modular adder.**  `target := (target + b) % p`
    where the read register holds the **biased addend** `2^W − (p − b)` (the lookup writes this,
    folding the `−p` into the table — free).  Then: add read into target (`gidneyAdderMeasured`,
    which directly lands `x + b − p (mod 2^W)` with the top qubit `Q = target_idx bits` the underflow
    flag), clear read (`mz`), copy `Q` into the flag, conditionally add `p` back, measure-clear the
    flag.  TWO measured adds — matching Gidney-2025's `2.5n` register modular-add `addCost`; the
    separate `addConstMeasured (2^W − p)` of the naive 3-add version is eliminated by the bias. -/
def gidneyModAddRegMeasured (bits p : Nat) : EGate :=
  EGate.seq
    (EGate.seq
      (EGate.seq
        (gidneyAdderMeasured (bits + 1) 0)
        (mzList ((List.range (bits + 1)).map read_idx)))
      (EGate.base (Gate.CX (target_idx bits) (adder_n_qubits (bits + 1)))))
    (EGate.seq
      (conditionalAddP (bits + 1) (adder_n_qubits (bits + 1)) p)
      (EGate.mz (adder_n_qubits (bits + 1))))

/-- **★ KEYSTONE VALUE-CORRECTNESS ★** — on the read register pre-loaded with the BIASED addend
    `2^(bits+1) − (p − b)` (`b < p`), the gate computes `target := (x + b) % p`, with the top qubit
    `Q` and the fixup-flag ancilla released to `0`.  TWO measured adds. -/
theorem gidneyModAddRegMeasured_correct
    (bits p b x : Nat) (hbits : 1 ≤ bits)
    (hp : 0 < p) (hpH : p ≤ 2 ^ bits) (hx : x < p) (hb : b < p) :
    gidney_target_val bits
        (EGate.applyNat (gidneyModAddRegMeasured bits p)
          (adder_input_F (bits + 1) (2 ^ (bits + 1) - (p - b)) x))
      = (x + b) % p
    ∧ EGate.applyNat (gidneyModAddRegMeasured bits p)
        (adder_input_F (bits + 1) (2 ^ (bits + 1) - (p - b)) x) (target_idx bits) = false
    ∧ EGate.applyNat (gidneyModAddRegMeasured bits p)
        (adder_input_F (bits + 1) (2 ^ (bits + 1) - (p - b)) x) (adder_n_qubits (bits + 1)) = false
    ∧ (∀ i, i < bits → EGate.applyNat (gidneyModAddRegMeasured bits p)
        (adder_input_F (bits + 1) (2 ^ (bits + 1) - (p - b)) x) (target_idx i) = ((x + b) % p).testBit i)
    ∧ (∀ i, i < bits + 1 → EGate.applyNat (gidneyModAddRegMeasured bits p)
        (adder_input_F (bits + 1) (2 ^ (bits + 1) - (p - b)) x) (read_idx i) = false)
    ∧ (∀ i, i < bits + 1 → EGate.applyNat (gidneyModAddRegMeasured bits p)
        (adder_input_F (bits + 1) (2 ^ (bits + 1) - (p - b)) x) (carry_idx i) = false) := by
  obtain ⟨n, rfl⟩ : ∃ n, bits = n + 1 := ⟨bits - 1, by omega⟩
  set W := n + 2 with hW
  set H := 2 ^ (n + 1) with hH
  set flagIdx := adder_n_qubits W with hflagIdx
  have hpow : (2 : Nat) ^ W = 2 * H := by rw [hW, hH, pow_succ]; ring
  have h2W : (0 : Nat) < 2 ^ W := Nat.two_pow_pos W
  have hxlt : x < 2 ^ W := by
    rw [hW]; calc x < p := hx
      _ ≤ 2 ^ (n + 1) := hpH
      _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hplt : p < 2 ^ W := by
    rw [hW]; calc p ≤ 2 ^ (n + 1) := hpH
      _ < 2 ^ (n + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpHval : p ≤ H := by rw [hH]; exact hpH
  -- the BIASED addend `ba = 2^W − (p − b)` ∈ [2^(W-1), 2^W) folds the `−p` reduction in
  set ba := 2 ^ W - (p - b) with hba
  have hba_lt : ba < 2 ^ W := by rw [hba]; omega
  -- one measured add lands `v1 = (x + ba) % 2^W = (x + b − p) (mod 2^W)` directly
  set v1 := (x + ba) % 2 ^ W with hv1def
  have hv1lt : v1 < 2 ^ W := Nat.mod_lt _ (Nat.two_pow_pos _)
  -- ===== FRONT stage A : add the biased read into the target =====
  have hflag_ge : adder_n_qubits W ≤ flagIdx := le_of_eq hflagIdx.symm
  set sA := EGate.applyNat (gidneyAdderMeasured W 0) (adder_input_F W ba x) with hsA
  have hsA_tgt : ∀ i, i < W → sA (target_idx i) = v1.testBit i := by
    intro i hi
    rw [hsA, (gidneyAdderMeasured_correct n ba x 0 hba_lt hxlt i hi).1, adder_sum_bit_classical,
        hv1def, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and, Nat.add_comm ba x]
  have hsA_carry : ∀ i, i < W → sA (carry_idx i) = false := fun i hi => by
    rw [hsA]; exact (gidneyAdderMeasured_correct n ba x 0 hba_lt hxlt i hi).2
  have hsA_ge : ∀ q, 3 * W ≤ q → sA q = adder_input_F W ba x q := by
    intro q hq
    rw [hsA]
    exact FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.EGate_boundedBy_preserves_ge (3 * W) (gidneyAdderMeasured W 0)
      (FormalRV.Arithmetic.MeasuredAdder.gidneyAdderMeasured_boundedBy_tight n 0) (adder_input_F W ba x) q hq
  -- ===== FRONT stage B : measure-clear the read register → block-clean `adder_input_F W 0 v1` =====
  set s1 := EGate.applyNat (mzList ((List.range W).map read_idx)) sA with hs1
  have notin_read : ∀ q : Nat, (∀ i, i < W → q ≠ read_idx i) →
      q ∉ (List.range W).map read_idx := by
    intro q hq hmem
    obtain ⟨i, hir, hqi⟩ := List.mem_map.mp hmem
    exact hq i (List.mem_range.mp hir) hqi.symm
  have hs1_block : ∀ q, q < adder_n_qubits W → s1 q = adder_input_F W 0 v1 q := by
    intro q hq
    have h3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases h3 with h | h | h
    · have hqr : q = read_idx (q / 3) := by simp only [read_idx]; omega
      by_cases hjW : q / 3 < W
      · rw [hqr, hs1, applyNat_mzList_clears _ sA
              (List.mem_map.mpr ⟨q / 3, List.mem_range.mpr hjW, rfl⟩),
            adder_input_F_at_read]; simp
      · have hjeq : q / 3 = W := by simp only [adder_n_qubits] at hq; omega
        rw [hqr, hs1, applyNat_mzList_preserves _ sA
              (notin_read _ (fun i hi => by simp only [read_idx]; omega)),
            hsA_ge _ (by rw [hjeq]; simp only [read_idx]; omega),
            adder_input_F_at_read, adder_input_F_at_read]; simp [hjeq]
    · have hqt : q = target_idx (q / 3) := by simp only [target_idx]; omega
      by_cases hjW : q / 3 < W
      · rw [hqt, hs1, applyNat_mzList_preserves _ sA
              (notin_read _ (fun i _ => by simp only [target_idx, read_idx]; omega)),
            hsA_tgt _ hjW, adder_input_F_at_target, decide_eq_true hjW, Bool.true_and]
      · have hjeq : q / 3 = W := by simp only [adder_n_qubits] at hq; omega
        rw [hqt, hs1, applyNat_mzList_preserves _ sA
              (notin_read _ (fun i _ => by simp only [target_idx, read_idx]; omega)),
            hsA_ge _ (by rw [hjeq]; simp only [target_idx]; omega),
            adder_input_F_at_target, adder_input_F_at_target]; simp [hjeq]
    · have hqc : q = carry_idx (q / 3) := by simp only [carry_idx]; omega
      have hjW : q / 3 < W := by simp only [adder_n_qubits] at hq; omega
      rw [hqc, hs1, applyNat_mzList_preserves _ sA
            (notin_read _ (fun i _ => by simp only [carry_idx, read_idx]; omega)),
          hsA_carry _ hjW, adder_input_F_at_carry]
  have hs1_tgt : ∀ i, i < W → s1 (target_idx i) = v1.testBit i := by
    intro i hi
    rw [hs1, applyNat_mzList_preserves _ sA
          (notin_read _ (fun j _ => by simp only [target_idx, read_idx]; omega)), hsA_tgt i hi]
  have hs1_flag : s1 flagIdx = false := by
    rw [hs1, applyNat_mzList_preserves _ sA
          (notin_read _ (fun i hi => by rw [hflagIdx]; simp only [read_idx, adder_n_qubits]; omega)),
        hsA_ge _ (by rw [hflagIdx]; simp only [adder_n_qubits]; omega)]
    simp only [adder_input_F, flagIdx, adder_n_qubits, show (3 * W + 2) % 3 = 2 by omega]
  -- ===== from here, identical to `gidneyModAddFixup_correct` stages 2–4, with `c := b` =====
  -- stage 2 : copy Q (top target bit) into the flag
  set s2 := Gate.applyNat (Gate.CX (target_idx (n + 1)) flagIdx) s1 with hs2
  have htgt_ne_flag : target_idx (n + 1) ≠ flagIdx := by
    rw [hflagIdx]; simp only [target_idx, adder_n_qubits]; omega
  have hs2_off : ∀ q, q ≠ flagIdx → s2 q = s1 q := by
    intro q hq; rw [hs2, Gate.applyNat_CX, update_neq _ _ _ _ hq]
  have hs2_flag : s2 flagIdx = decide (H ≤ v1) := by
    rw [hs2, Gate.applyNat_CX, update_eq, hs1_flag, Bool.false_xor, hs1_tgt (n + 1) (by omega)]
    exact testBit_top_eq_threshold (n + 1) v1 (by rw [← hW]; exact hv1lt)
  have hs2_block : ∀ q, q < adder_n_qubits W → s2 q = adder_input_F W 0 v1 q := fun q hq => by
    rw [hs2_off q (by rw [hflagIdx]; omega)]; exact hs1_block q hq
  -- stage 3 : conditional +p
  obtain ⟨hb3, _hb3flag⟩ := conditionalAddP_bundle n p v1 flagIdx s2 hflag_ge hs2_block hplt hv1lt
  set s3 := EGate.applyNat (conditionalAddP W flagIdx p) s2 with hs3
  have hcond : (if s2 flagIdx then p else 0) = (if H ≤ v1 then p else 0) := by
    rw [hs2_flag]; by_cases h : H ≤ v1 <;> simp [h]
  set v2 := (v1 + (if H ≤ v1 then p else 0)) % 2 ^ W with hv2def
  have hv1eq : v1 = (x + (2 * H - (p - b))) % (2 * H) := by
    rw [hv1def, hba, hpow]
  obtain ⟨hfix_val, hfix_lt⟩ := fixup_value H p b x hp hpHval hx hb
  have hv2_alt : v2 = ((x + (2 * H - (p - b))) % (2 * H)
      + (if (x + (2 * H - (p - b))) % (2 * H) ≥ H then p else 0)) % (2 * H) := by
    rw [hv2def, hpow, hv1eq]
  have hv2_eq : v2 = (x + b) % p := by rw [hv2_alt]; exact hfix_val
  have hv2_lt : v2 < H := by rw [hv2_alt]; exact hfix_lt
  -- stage 4 : measure-clear the flag ; assemble the whole gate
  have hgate : EGate.applyNat (gidneyModAddRegMeasured (n + 1) p) (adder_input_F W ba x)
        = Function.update s3 flagIdx false := by
    show Function.update
          (EGate.applyNat (conditionalAddP W flagIdx p)
            (Gate.applyNat (Gate.CX (target_idx (n + 1)) flagIdx)
              (EGate.applyNat (mzList ((List.range W).map read_idx))
                (EGate.applyNat (gidneyAdderMeasured W 0) (adder_input_F W ba x)))))
          flagIdx false = _
    rw [hs3, hs2, hs1, hsA]
  have hflag_ne_tgt : ∀ i, i < n + 1 → flagIdx ≠ target_idx i := by
    intro i hi; rw [hflagIdx]; unfold target_idx adder_n_qubits; omega
  have hflag_ne_tgt2 : ∀ i, i < n + 2 → flagIdx ≠ target_idx i := by
    intro i hi; rw [hflagIdx]; simp only [target_idx, adder_n_qubits]; omega
  have hflag_ne_read : ∀ i, i < n + 2 → flagIdx ≠ read_idx i := by
    intro i hi; rw [hflagIdx]; simp only [read_idx, adder_n_qubits]; omega
  have hflag_ne_carry : ∀ i, i < n + 2 → flagIdx ≠ carry_idx i := by
    intro i hi; rw [hflagIdx]; simp only [carry_idx, adder_n_qubits]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgate]
    have hdecode : gidney_target_val (n + 1) (Function.update s3 flagIdx false)
        = (x + b) % p % 2 ^ (n + 1) := by
      apply gidney_target_val_low (n + 1) ((x + b) % p)
      intro i hi
      rw [Function.update_of_ne (hflag_ne_tgt i hi).symm]
      have := (hb3 i (by omega)).1
      rw [this, hcond]
      have hbit : ((x + b) % p).testBit i = v2.testBit i := by rw [hv2_eq]
      rw [hbit, hv2def, Nat.testBit_mod_two_pow, decide_eq_true (show i < W by omega), Bool.true_and]
    rw [hdecode, Nat.mod_eq_of_lt (by calc (x + b) % p < p := Nat.mod_lt _ hp
                                      _ ≤ 2 ^ (n + 1) := hpH)]
  · rw [hgate, Function.update_of_ne htgt_ne_flag]
    have h := (hb3 (n + 1) (by omega)).1
    rw [h, hcond]
    have hbit : (v1 + (if H ≤ v1 then p else 0)).testBit (n + 1) = v2.testBit (n + 1) := by
      rw [hv2def, Nat.testBit_mod_two_pow, decide_eq_true (show n + 1 < W by omega), Bool.true_and]
    rw [hbit]
    exact Nat.testBit_lt_two_pow (by rw [hH] at hv2_lt; exact hv2_lt)
  · rw [hgate, Function.update_self]
  · -- per-bit target (i < n+1): final(target_idx i) = ((x+b)%p).testBit i
    intro i hi
    rw [hgate, Function.update_of_ne (hflag_ne_tgt2 i (by omega)).symm, (hb3 i (by omega)).1, hcond]
    have hb : (v1 + (if H ≤ v1 then p else 0)).testBit i = v2.testBit i := by
      rw [hv2def, Nat.testBit_mod_two_pow, decide_eq_true (show i < W by omega), Bool.true_and]
    rw [hb, hv2_eq]
  · -- read register clean (i < n+2)
    intro i hi
    rw [hgate, Function.update_of_ne (hflag_ne_read i hi).symm, (hb3 i hi).2.1]
  · -- carry register clean (i < n+2)
    intro i hi
    rw [hgate, Function.update_of_ne (hflag_ne_carry i hi).symm, (hb3 i hi).2.2]

/-! ## §2. Locality — the modular adder touches nothing above its flag ancilla. -/

theorem mzList_boundedBy (B : Nat) :
    ∀ (L : List Nat), (∀ x ∈ L, x < B) → EGate.boundedBy B (mzList L)
  | [], _ => by simp [mzList, EGate.boundedBy, Gate.boundedBy]
  | q :: qs, h => by
      show EGate.boundedBy B (EGate.seq (mzList qs) (EGate.mz q))
      exact ⟨mzList_boundedBy B qs (fun x hx => h x (List.mem_cons.mpr (Or.inr hx))),
             h q (List.mem_cons.mpr (Or.inl rfl))⟩

theorem prepareMaskedP_boundedBy (flagIdx B : Nat) (hflag : flagIdx < B) :
    ∀ (W p : Nat), (∀ k, k < W → read_idx k < B) → Gate.boundedBy B (prepareMaskedP flagIdx W p)
  | 0, _, _ => by simp [prepareMaskedP, Gate.boundedBy]
  | W + 1, p, h => by
      show Gate.boundedBy B (Gate.seq (prepareMaskedP flagIdx W p)
        (if p.testBit W then Gate.CX flagIdx (read_idx W) else Gate.I))
      refine ⟨prepareMaskedP_boundedBy flagIdx B hflag W p (fun k hk => h k (by omega)), ?_⟩
      by_cases hpw : p.testBit W
      · simp only [hpw, if_true]; exact ⟨hflag, h W (by omega)⟩
      · simp only [hpw, Bool.false_eq_true, if_false, Gate.boundedBy]

theorem conditionalAddP_boundedBy (n flagIdx B p : Nat) (hflag : flagIdx < B)
    (hadd : adder_n_qubits (n + 2) ≤ B) (hread : ∀ k, k < n + 2 → read_idx k < B) :
    EGate.boundedBy B (conditionalAddP (n + 2) flagIdx p) := by
  show EGate.boundedBy B (EGate.seq
    (EGate.seq (EGate.base (prepareMaskedP flagIdx (n + 2) p)) (gidneyAdderMeasured (n + 2) 0))
    (EGate.base (prepareMaskedP flagIdx (n + 2) p)))
  refine ⟨⟨prepareMaskedP_boundedBy flagIdx B hflag (n + 2) p hread, ?_⟩,
          prepareMaskedP_boundedBy flagIdx B hflag (n + 2) p hread⟩
  exact EGate.boundedBy_mono hadd _ (gidneyAdderMeasured_boundedBy n 0)

/-- **The register-register measured modular adder touches only indices `≤ adder_n_qubits (bits+1)`**
    (the fixup-flag ancilla), so it fixes everything strictly above — the locality that lets a fold
    frame the y-register / lookup ancilla / control. -/
theorem gidneyModAddRegMeasured_boundedBy (n p : Nat) :
    EGate.boundedBy (adder_n_qubits (n + 2) + 1) (gidneyModAddRegMeasured (n + 1) p) := by
  have hB : adder_n_qubits (n + 2) < adder_n_qubits (n + 2) + 1 := by omega
  have hle : adder_n_qubits (n + 2) ≤ adder_n_qubits (n + 2) + 1 := by omega
  have hread : ∀ k, k < n + 2 → read_idx k < adder_n_qubits (n + 2) + 1 := by
    intro k hk; simp only [read_idx, adder_n_qubits]; omega
  show EGate.boundedBy (adder_n_qubits (n + 2) + 1) (EGate.seq
    (EGate.seq
      (EGate.seq (gidneyAdderMeasured (n + 2) 0) (mzList ((List.range (n + 2)).map read_idx)))
      (EGate.base (Gate.CX (target_idx (n + 1)) (adder_n_qubits (n + 2)))))
    (EGate.seq (conditionalAddP (n + 2) (adder_n_qubits (n + 2)) p)
      (EGate.mz (adder_n_qubits (n + 2)))))
  refine ⟨⟨⟨EGate.boundedBy_mono hle _ (gidneyAdderMeasured_boundedBy n 0), ?_⟩,
           ⟨by simp only [target_idx, adder_n_qubits]; omega, hB⟩⟩,
          conditionalAddP_boundedBy n (adder_n_qubits (n + 2)) (adder_n_qubits (n + 2) + 1) p hB hle hread,
          hB⟩
  exact mzList_boundedBy _ _ (fun x hx => by
    obtain ⟨i, hir, rfl⟩ := List.mem_map.mp hx
    exact hread i (List.mem_range.mp hir))

/-- **★ SLACK PRESERVATION ★** — `gidneyModAddRegMeasured (n+1) p` is the identity on the two
    "middle slots" `{3·(n+2), 3·(n+2)+1}` strictly between the adder's tight bound `3·(n+2)` and
    the fixup-flag ancilla `adder_n_qubits (n+2) = 3·(n+2)+2`.  Neither the front adder/subtract
    (tight-bounded by `3·(n+2)`), the read-clearing `mz`s (touch `read_idx < 3·(n+2)`), the
    flag-copy `CX` (control `target_idx (n+1) < 3·(n+2)`, target the flag), the conditional `+p`
    (touches only the block and the flag), nor the flag-`mz` writes these slots.  This is the
    locality the fold needs at the keystone's FULL congruence range `adder_n_qubits (n+2) + 1`: it
    pins the slots the value lemma (which speaks of `i < n+1`) and the boundedBy (`≤ flag + 1`)
    leave unconstrained. -/
theorem gidneyModAddRegMeasured_preserves_slack
    (n p q : Nat) (hq_lo : 3 * (n + 2) ≤ q) (hq_hi : q < adder_n_qubits (n + 2))
    (f : Nat → Bool) :
    EGate.applyNat (gidneyModAddRegMeasured (n + 1) p) f q = f q := by
  -- index facts: q sits strictly above every read/target index and strictly below the flag
  have hq_ne_flag : q ≠ adder_n_qubits (n + 2) := by omega
  have hq_read : ∀ i, i < n + 2 → q ≠ read_idx i := fun i hi => by
    simp only [read_idx]; omega
  have hflag_read : ∀ i, i < n + 2 → adder_n_qubits (n + 2) ≠ read_idx i := fun i hi => by
    simp only [read_idx, adder_n_qubits]; omega
  have hqnotin : q ∉ (List.range (n + 2)).map read_idx := by
    intro hmem
    obtain ⟨i, hir, hqi⟩ := List.mem_map.mp hmem
    exact hq_read i (List.mem_range.mp hir) hqi.symm
  -- per-component "preserves q" lemmas
  have P1 : ∀ h, EGate.applyNat (gidneyAdderMeasured (n + 2) 0) h q = h q := fun h =>
    FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.EGate_boundedBy_preserves_ge (3 * (n + 2))
      (gidneyAdderMeasured (n + 2) 0)
      (FormalRV.Arithmetic.MeasuredAdder.gidneyAdderMeasured_boundedBy_tight n 0) h q hq_lo
  have P2 : ∀ h, EGate.applyNat (mzList ((List.range (n + 2)).map read_idx)) h q = h q := fun h =>
    applyNat_mzList_preserves _ h hqnotin
  have P4 : ∀ h, EGate.applyNat
      (EGate.base (Gate.CX (target_idx (n + 1)) (adder_n_qubits (n + 2)))) h q = h q := fun h => by
    show Gate.applyNat (Gate.CX (target_idx (n + 1)) (adder_n_qubits (n + 2))) h q = h q
    simp only [Gate.applyNat_CX]
    exact update_neq _ _ _ _ hq_ne_flag
  have P5 : ∀ h,
      EGate.applyNat (conditionalAddP (n + 2) (adder_n_qubits (n + 2)) p) h q = h q := by
    intro h
    have hinner : Gate.applyNat (prepareMaskedP (adder_n_qubits (n + 2)) (n + 2) p) h q = h q :=
      prepareMaskedP_preserves_outside (adder_n_qubits (n + 2)) (n + 2) p h q hflag_read hq_read
    have hmid : EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
                  (Gate.applyNat (prepareMaskedP (adder_n_qubits (n + 2)) (n + 2) p) h) q
                = Gate.applyNat (prepareMaskedP (adder_n_qubits (n + 2)) (n + 2) p) h q :=
      FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.EGate_boundedBy_preserves_ge (3 * (n + 2))
        (gidneyAdderMeasured (n + 2) 0)
        (FormalRV.Arithmetic.MeasuredAdder.gidneyAdderMeasured_boundedBy_tight n 0) _ q hq_lo
    have houter : Gate.applyNat (prepareMaskedP (adder_n_qubits (n + 2)) (n + 2) p)
                    (EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
                      (Gate.applyNat (prepareMaskedP (adder_n_qubits (n + 2)) (n + 2) p) h)) q
                  = EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
                      (Gate.applyNat (prepareMaskedP (adder_n_qubits (n + 2)) (n + 2) p) h) q :=
      prepareMaskedP_preserves_outside (adder_n_qubits (n + 2)) (n + 2) p _ q hflag_read hq_read
    show Gate.applyNat (prepareMaskedP (adder_n_qubits (n + 2)) (n + 2) p)
          (EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
            (Gate.applyNat (prepareMaskedP (adder_n_qubits (n + 2)) (n + 2) p) h)) q = h q
    rw [houter, hmid, hinner]
  have P6 : ∀ h, EGate.applyNat (EGate.mz (adder_n_qubits (n + 2))) h q = h q := fun h => by
    show Function.update h (adder_n_qubits (n + 2)) false q = h q
    rw [funupd_eq_update]; exact update_neq _ _ _ _ hq_ne_flag
  -- assemble: the gate reduces to G6 ∘ G5 ∘ G4 ∘ G3 ∘ G2 ∘ G1, each preserving q
  show EGate.applyNat (EGate.mz (adder_n_qubits (n + 2)))
        (EGate.applyNat (conditionalAddP (n + 2) (adder_n_qubits (n + 2)) p)
          (EGate.applyNat (EGate.base (Gate.CX (target_idx (n + 1)) (adder_n_qubits (n + 2))))
            (EGate.applyNat (mzList ((List.range (n + 2)).map read_idx))
              (EGate.applyNat (gidneyAdderMeasured (n + 2) 0) f)))) q = f q
  rw [P6, P5, P4, P2, P1]

end FormalRV.Arithmetic.ModularAdder.GidneyModAddReg
