/-
  FormalRV.Shor.MeasuredBabbushRead — the POSITION-MAPPED Babbush unary-iteration QROM
  read, fitted to the in-place windowed-multiplier layout.

  ## Why this file exists

  `MeasUncomputeAt.unaryQROMAt` is the Babbush merged-AND QROM read (arXiv:1805.03662
  §III.A/§III.C) with `2^w − 1` temporary ANDs, but it hard-codes its address bits at
  the STRIDE-1 positions `addrBase + i` and its AND-ancillas at `ancBase + i`.  The
  verified in-place windowed multiplier (`WindowedCircuit`) instead interleaves them:
  the address bit `i` lives at `ulookup_address_idx i = 1 + 2·i` and the AND-ancilla `i`
  at `ulookup_and_idx i = 2 + 2·i` (the layout that the flat unary `lookupReadAt` reads).

  `unaryQROMPos` takes the address and ancilla as position MAPS `aIdx, cIdx : ℕ → ℕ`
  (exactly as the word already is a map `pos`), so the SAME merged-AND tree fits the
  in-place layout with NO change to its dim, registers, or count.  The three structural
  lemmas (`_frame`, `_anc_cleared`, `_selects_word`) are the depth induction of
  `MeasUncomputeAt`, with the only stride-1 `omega` facts (`cIdx i ≠ cIdx d`) replaced
  by a `cIdx`-injectivity hypothesis.

  From them we assemble `babbushReadInPlace_selects`, which has EXACTLY the shape of
  `WindowedLookupSelect.lookupReadAt_selects` — so the babbush read is a drop-in
  replacement for the flat read in the measured in-place value proof, at the cheaper
  `2^w − 1` (Babbush) Toffoli count instead of `2·w·2^w`.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasUncomputeAt
import FormalRV.Shor.EGateToUnitaryBridge
import FormalRV.Shor.SplitPhaseFixup

namespace FormalRV.Shor.MeasuredBabbushRead

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit FormalRV.Shor.WindowedLookupAdd
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasUncomputeValue
open FormalRV.Shor.MeasUncomputeAt
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.Shor.SplitPhaseFixup

/-! ## §1. The position-mapped read. -/

/-- **Position-mapped Babbush unary-iteration QROM read.**  Like `unaryQROMAt` but with
    the address bit `i` at `aIdx i` and the AND-ancilla `i` at `cIdx i` (both maps,
    matching the in-place layout) instead of `addrBase + i` / `ancBase + i`.  The
    merged-AND recursion is otherwise identical, so all counts are preserved. -/
def unaryQROMPos (aIdx cIdx pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    Nat → Nat → Nat → EGate
  | 0,     ctrl, base =>
      EGate.base (cx_gates_from_indices ctrl (wordCnotsAt pos W (T base)))
  | d + 1, ctrl, base =>
      EGate.seq (EGate.seq (EGate.seq (EGate.seq (EGate.seq
        (EGate.base (Gate.CCX ctrl (aIdx d) (cIdx d)))
        (unaryQROMPos aIdx cIdx pos W T d (cIdx d) (base + 2 ^ d)))
        (EGate.base (Gate.CX ctrl (cIdx d))))
        (unaryQROMPos aIdx cIdx pos W T d (cIdx d) base))
        (EGate.base (Gate.CX ctrl (cIdx d))))
        (EGate.mz (cIdx d))

/-! ## §2. Counts (position maps cost nothing — identical to `unaryQROMAt`). -/

theorem tcount_unaryQROMPos (aIdx cIdx pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    ∀ (d ctrl base : Nat),
      EGate.tcount (unaryQROMPos aIdx cIdx pos W T d ctrl base) = 7 * (2 ^ d - 1)
  | 0, ctrl, base => by
      simp [unaryQROMPos, EGate.tcount, tcount_cx_gates_zero]
  | d + 1, ctrl, base => by
      simp only [unaryQROMPos, EGate.tcount, Gate.tcount,
                 tcount_unaryQROMPos aIdx cIdx pos W T d]
      have h2d : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega

theorem toffoli_unaryQROMPos (aIdx cIdx pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (d ctrl base : Nat) :
    EGate.toffoli (unaryQROMPos aIdx cIdx pos W T d ctrl base) = 2 ^ d - 1 := by
  unfold EGate.toffoli
  rw [tcount_unaryQROMPos, Nat.mul_div_cancel_left _ (by norm_num)]

/-! ## §3. Frame: positions off the word and the ancilla register are untouched. -/

theorem unaryQROMPos_frame (aIdx cIdx pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    ∀ (d ctrl base : Nat) (f : Nat → Bool) (p : Nat),
      (∀ j, j < W → p ≠ pos j) →
      (∀ i, i < d → p ≠ cIdx i) →
      EGate.applyNat (unaryQROMPos aIdx cIdx pos W T d ctrl base) f p = f p
  | 0, ctrl, base, f, p, hp_out, _ => by
    show Gate.applyNat (cx_gates_from_indices ctrl (wordCnotsAt pos W (T base))) f p = f p
    rw [applyNat_cx_gates_from_indices]
    apply Lookup.cnot_layer_post_state_frame
    intro hmem
    obtain ⟨j, hj, _, hpj⟩ := (mem_wordCnotsAt pos W (T base) p).mp hmem
    exact hp_out j hj hpj
  | d + 1, ctrl, base, f, p, hp_out, hp_anc => by
    have hp_d : p ≠ cIdx d := hp_anc d (Nat.lt_succ_self d)
    have hp_anc' : ∀ i, i < d → p ≠ cIdx i :=
      fun i hi => hp_anc i (Nat.lt_succ_of_lt hi)
    show Function.update
        (Gate.applyNat (Gate.CX ctrl (cIdx d))
          (EGate.applyNat (unaryQROMPos aIdx cIdx pos W T d (cIdx d) base)
            (Gate.applyNat (Gate.CX ctrl (cIdx d))
              (EGate.applyNat (unaryQROMPos aIdx cIdx pos W T d (cIdx d) (base + 2 ^ d))
                (Gate.applyNat (Gate.CCX ctrl (aIdx d) (cIdx d)) f)))))
        (cIdx d) false p = f p
    rw [Function.update_of_ne hp_d, Gate.applyNat_CX, update_neq _ _ _ _ hp_d,
        unaryQROMPos_frame aIdx cIdx pos W T d (cIdx d) base _ p hp_out hp_anc',
        Gate.applyNat_CX, update_neq _ _ _ _ hp_d,
        unaryQROMPos_frame aIdx cIdx pos W T d (cIdx d) (base + 2 ^ d) _ p hp_out hp_anc',
        Gate.applyNat_CCX, update_neq _ _ _ _ hp_d]

/-! ## §4. The AND-ancillas come back cleared. -/

theorem unaryQROMPos_anc_cleared (aIdx cIdx pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (hc_inj : ∀ i i', cIdx i = cIdx i' → i = i') :
    ∀ (d ctrl base : Nat) (f : Nat → Bool) (i : Nat), i < d →
      EGate.applyNat (unaryQROMPos aIdx cIdx pos W T d ctrl base) f (cIdx i) = false
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | d + 1, ctrl, base, f, i, hi => by
    show Function.update
        (Gate.applyNat (Gate.CX ctrl (cIdx d))
          (EGate.applyNat (unaryQROMPos aIdx cIdx pos W T d (cIdx d) base)
            (Gate.applyNat (Gate.CX ctrl (cIdx d))
              (EGate.applyNat (unaryQROMPos aIdx cIdx pos W T d (cIdx d) (base + 2 ^ d))
                (Gate.applyNat (Gate.CCX ctrl (aIdx d) (cIdx d)) f)))))
        (cIdx d) false (cIdx i) = false
    by_cases hid : i = d
    · subst hid
      exact Function.update_self _ _ _
    · have hne : cIdx i ≠ cIdx d := fun h => hid (hc_inj i d h)
      rw [Function.update_of_ne hne, Gate.applyNat_CX, update_neq _ _ _ _ hne,
          unaryQROMPos_anc_cleared aIdx cIdx pos W T hc_inj d (cIdx d) base _ i
            (by omega)]

/-! ## §5. The selection lemma. -/

theorem unaryQROMPos_selects_word (aIdx cIdx pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k)
    (hc_inj : ∀ i i', cIdx i = cIdx i' → i = i') :
    ∀ (d ctrl base : Nat) (f : Nat → Bool),
      (∀ i j, i < d → j < W → cIdx i ≠ pos j) →
      (∀ i i', i < d → i' < d → cIdx i ≠ aIdx i') →
      (∀ i j, i < d → j < W → aIdx i ≠ pos j) →
      (∀ j, j < W → ctrl ≠ pos j) →
      (∀ i, i < d → ctrl ≠ cIdx i) →
      (∀ i, i < d → f (cIdx i) = false) →
      ∀ j, j < W →
        EGate.applyNat (unaryQROMPos aIdx cIdx pos W T d ctrl base) f (pos j)
          = xor (f (pos j))
              (f ctrl && (T (base + decodeReg aIdx d f)).testBit j)
  | 0, ctrl, base, f, _, _, _, h_ctrl_out, _, _ => by
    intro j hj
    show Gate.applyNat (cx_gates_from_indices ctrl
        (wordCnotsAt pos W (T base))) f (pos j) = _
    have hctrl_not_mem : ctrl ∉ wordCnotsAt pos W (T base) := by
      intro hmem
      obtain ⟨j', hj', _, hcj⟩ := (mem_wordCnotsAt pos W (T base) ctrl).mp hmem
      exact h_ctrl_out j' hj' hcj
    have hdec0 : decodeReg aIdx 0 f = 0 := by simp [decodeReg]
    rw [applyNat_cx_gates_from_indices, hdec0, Nat.add_zero]
    by_cases hb : (T base).testBit j = true
    · rw [Lookup.cnot_layer_post_state_at ctrl _
            (wordCnotsAt_nodup pos W (T base) hpos_inj) hctrl_not_mem f (pos j)
            ((pos_mem_wordCnotsAt_iff pos W (T base) j hj hpos_inj).mpr hb),
          hb, Bool.and_true]
    · have hbf : (T base).testBit j = false := (Bool.not_eq_true _).mp hb
      rw [Lookup.cnot_layer_post_state_frame ctrl _ f (pos j)
            (fun hmem =>
              hb ((pos_mem_wordCnotsAt_iff pos W (T base) j hj hpos_inj).mp hmem)),
          hbf, Bool.and_false, Bool.xor_false]
  | d + 1, ctrl, base, f, h_anc_out, h_anc_addr, h_addr_out, h_ctrl_out, h_ctrl_anc,
      h_clean => by
    have hlt := Nat.lt_succ_self d
    have H1 : ∀ i j, i < d → j < W → cIdx i ≠ pos j :=
      fun i j hi hj => h_anc_out i j (Nat.lt_succ_of_lt hi) hj
    have H2 : ∀ i i', i < d → i' < d → cIdx i ≠ aIdx i' :=
      fun i i' hi hi' => h_anc_addr i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi')
    have H3 : ∀ i j, i < d → j < W → aIdx i ≠ pos j :=
      fun i j hi hj => h_addr_out i j (Nat.lt_succ_of_lt hi) hj
    have H4 : ∀ j, j < W → cIdx d ≠ pos j := fun j hj => h_anc_out d j hlt hj
    have H5 : ∀ i, i < d → cIdx d ≠ cIdx i := fun i hi h => by
      have := hc_inj d i h; omega
    set s1 := Gate.applyNat (Gate.CCX ctrl (aIdx d) (cIdx d)) f with hs1
    set s2 := EGate.applyNat
      (unaryQROMPos aIdx cIdx pos W T d (cIdx d) (base + 2 ^ d)) s1 with hs2
    set s3 := Gate.applyNat (Gate.CX ctrl (cIdx d)) s2 with hs3
    set s4 := EGate.applyNat
      (unaryQROMPos aIdx cIdx pos W T d (cIdx d) base) s3 with hs4
    set s5 := Gate.applyNat (Gate.CX ctrl (cIdx d)) s4 with hs5
    have hg : EGate.applyNat (unaryQROMPos aIdx cIdx pos W T (d + 1) ctrl base) f
        = Function.update s5 (cIdx d) false := by
      rw [hs5, hs4, hs3, hs2, hs1]; rfl
    have hs1_ne : ∀ p, p ≠ cIdx d → s1 p = f p := by
      intro p hp
      rw [hs1, Gate.applyNat_CCX]
      exact update_neq _ _ _ _ hp
    have hs1_at : s1 (cIdx d) = (f ctrl && f (aIdx d)) := by
      rw [hs1, Gate.applyNat_CCX, update_eq, h_clean d hlt, Bool.false_xor]
    have hs1_addr : decodeReg aIdx d s1 = decodeReg aIdx d f :=
      decodeReg_ext _ _ _ _ (fun i hi =>
        hs1_ne _ (Ne.symm (h_anc_addr d i hlt (Nat.lt_succ_of_lt hi))))
    have hs1_clean : ∀ i, i < d → s1 (cIdx i) = false := by
      intro i hi
      rw [hs1_ne _ (fun h => by have := hc_inj i d h; omega)]
      exact h_clean i (Nat.lt_succ_of_lt hi)
    have v2 : ∀ j, j < W → s2 (pos j)
        = xor (f (pos j))
            ((f ctrl && f (aIdx d))
              && (T (base + 2 ^ d + decodeReg aIdx d f)).testBit j) := by
      intro j hj
      rw [hs2, unaryQROMPos_selects_word aIdx cIdx pos W T hpos_inj hc_inj d (cIdx d)
            (base + 2 ^ d) s1 H1 H2 H3 H4 H5 hs1_clean j hj,
          hs1_ne _ (Ne.symm (H4 j hj)), hs1_at, hs1_addr]
    have hs2_ctrl : s2 ctrl = f ctrl := by
      rw [hs2, unaryQROMPos_frame aIdx cIdx pos W T d (cIdx d)
            (base + 2 ^ d) s1 ctrl h_ctrl_out
            (fun i hi => h_ctrl_anc i (Nat.lt_succ_of_lt hi)),
          hs1_ne ctrl (h_ctrl_anc d hlt)]
    have hs2_anc : s2 (cIdx d) = (f ctrl && f (aIdx d)) := by
      rw [hs2, unaryQROMPos_frame aIdx cIdx pos W T d (cIdx d)
            (base + 2 ^ d) s1 (cIdx d) H4 H5, hs1_at]
    have hs2_addrpt : ∀ i, i < d → s2 (aIdx i) = f (aIdx i) := by
      intro i hi
      rw [hs2, unaryQROMPos_frame aIdx cIdx pos W T d (cIdx d)
            (base + 2 ^ d) s1 (aIdx i)
            (fun j hj => h_addr_out i j (Nat.lt_succ_of_lt hi) hj)
            (fun i' hi' =>
              Ne.symm (h_anc_addr i' i (Nat.lt_succ_of_lt hi') (Nat.lt_succ_of_lt hi))),
          hs1_ne _ (Ne.symm (h_anc_addr d i hlt (Nat.lt_succ_of_lt hi)))]
    have hs3_ne : ∀ p, p ≠ cIdx d → s3 p = s2 p := by
      intro p hp
      rw [hs3, Gate.applyNat_CX]
      exact update_neq _ _ _ _ hp
    have hs3_at : s3 (cIdx d) = (f ctrl && !(f (aIdx d))) := by
      rw [hs3, Gate.applyNat_CX, update_eq, hs2_anc, hs2_ctrl]
      cases f ctrl <;> cases f (aIdx d) <;> rfl
    have hs3_clean : ∀ i, i < d → s3 (cIdx i) = false := by
      intro i hi
      rw [hs3_ne _ (fun h => by have := hc_inj i d h; omega), hs2]
      exact unaryQROMPos_anc_cleared aIdx cIdx pos W T hc_inj d (cIdx d)
        (base + 2 ^ d) s1 i hi
    have hs3_addr : decodeReg aIdx d s3 = decodeReg aIdx d f :=
      decodeReg_ext _ _ _ _ (fun i hi => by
        rw [hs3_ne _ (Ne.symm (h_anc_addr d i hlt (Nat.lt_succ_of_lt hi))),
            hs2_addrpt i hi])
    have hs3_out : ∀ j, j < W → s3 (pos j) = s2 (pos j) :=
      fun j hj => hs3_ne _ (Ne.symm (H4 j hj))
    have v4 : ∀ j, j < W → s4 (pos j)
        = xor (s3 (pos j))
            ((f ctrl && !(f (aIdx d)))
              && (T (base + decodeReg aIdx d f)).testBit j) := by
      intro j hj
      rw [hs4, unaryQROMPos_selects_word aIdx cIdx pos W T hpos_inj hc_inj d (cIdx d)
            base s3 H1 H2 H3 H4 H5 hs3_clean j hj, hs3_at, hs3_addr]
    intro j hj
    have hne_out : pos j ≠ cIdx d := Ne.symm (h_anc_out d j hlt hj)
    rw [hg, Function.update_of_ne hne_out, hs5, Gate.applyNat_CX,
        update_neq _ _ _ _ hne_out, v4 j hj, hs3_out j hj, v2 j hj]
    simp only [decodeReg_succ]
    by_cases hb : f (aIdx d) = true
    · have hidx : decodeReg aIdx d f
          + (if f (aIdx d) = true then 2 ^ d else 0)
          = 2 ^ d + decodeReg aIdx d f := by
        rw [if_pos hb]; omega
      rw [hidx, ← Nat.add_assoc, hb]
      simp only [Bool.and_true, Bool.not_true, Bool.and_false, Bool.false_and,
                 Bool.xor_false]
    · have hbf : f (aIdx d) = false := (Bool.not_eq_true _).mp hb
      have hidx : decodeReg aIdx d f
          + (if f (aIdx d) = true then 2 ^ d else 0)
          = decodeReg aIdx d f := by
        rw [if_neg hb]; omega
      rw [hidx, hbf]
      simp only [Bool.and_false, Bool.false_and, Bool.xor_false, Bool.not_false,
                 Bool.and_true]

/-! ## §6. Well-typedness of the position-mapped read. -/

theorem unaryQROMPos_wellTypedAt (aIdx cIdx pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (dim : Nat) (hc_inj : ∀ i i', cIdx i = cIdx i' → i = i') :
    ∀ (d ctrl base : Nat), ctrl < dim →
      (∀ i, i < d → aIdx i < dim) → (∀ i, i < d → cIdx i < dim) →
      (∀ j, j < W → pos j < dim) →
      (∀ i i', i < d → i' < d → aIdx i ≠ cIdx i') →
      (∀ i j, i < d → j < W → aIdx i ≠ pos j) →
      (∀ i j, i < d → j < W → cIdx i ≠ pos j) →
      (∀ i, i < d → ctrl ≠ aIdx i) → (∀ i, i < d → ctrl ≠ cIdx i) →
      (∀ j, j < W → ctrl ≠ pos j) →
      EGate.WellTypedAt dim (unaryQROMPos aIdx cIdx pos W T d ctrl base)
  | 0, ctrl, base, hctrl, _, _, hp_lt, _, _, _, _, _, h_ctrl_pos => by
    show Gate.WellTyped dim (cx_gates_from_indices ctrl (wordCnotsAt pos W (T base)))
    apply cxGates_wellTyped dim ctrl _ (by omega) hctrl
    intro t ht
    obtain ⟨j, hj, _, rfl⟩ := (mem_wordCnotsAt pos W (T base) t).mp ht
    exact ⟨hp_lt j hj, h_ctrl_pos j hj⟩
  | d + 1, ctrl, base, hctrl, ha_lt, hc_lt, hp_lt, hac, hap, hcp,
      h_ctrl_a, h_ctrl_c, h_ctrl_pos => by
    have hlt := Nat.lt_succ_self d
    have hcd_lt : cIdx d < dim := hc_lt d hlt
    have had_lt : aIdx d < dim := ha_lt d hlt
    have hctrl_ad : ctrl ≠ aIdx d := h_ctrl_a d hlt
    have hctrl_cd : ctrl ≠ cIdx d := h_ctrl_c d hlt
    have had_cd : aIdx d ≠ cIdx d := hac d d hlt hlt
    -- shrunk hypotheses for the two depth-`d` recursive calls (control `cIdx d`)
    have ha_lt' : ∀ i, i < d → aIdx i < dim := fun i hi => ha_lt i (Nat.lt_succ_of_lt hi)
    have hc_lt' : ∀ i, i < d → cIdx i < dim := fun i hi => hc_lt i (Nat.lt_succ_of_lt hi)
    have hac' : ∀ i i', i < d → i' < d → aIdx i ≠ cIdx i' :=
      fun i i' hi hi' => hac i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi')
    have hap' : ∀ i j, i < d → j < W → aIdx i ≠ pos j :=
      fun i j hi hj => hap i j (Nat.lt_succ_of_lt hi) hj
    have hcp' : ∀ i j, i < d → j < W → cIdx i ≠ pos j :=
      fun i j hi hj => hcp i j (Nat.lt_succ_of_lt hi) hj
    have hcd_a : ∀ i, i < d → cIdx d ≠ aIdx i :=
      fun i hi => Ne.symm (hac i d (Nat.lt_succ_of_lt hi) hlt)
    have hcd_c : ∀ i, i < d → cIdx d ≠ cIdx i :=
      fun i hi h => by have := hc_inj d i h; omega
    have hcd_pos : ∀ j, j < W → cIdx d ≠ pos j := fun j hj => hcp d j hlt hj
    have hrec : ∀ b, EGate.WellTypedAt dim (unaryQROMPos aIdx cIdx pos W T d (cIdx d) b) :=
      fun b => unaryQROMPos_wellTypedAt aIdx cIdx pos W T dim hc_inj d (cIdx d) b hcd_lt
        ha_lt' hc_lt' hp_lt hac' hap' hcp' hcd_a hcd_c hcd_pos
    refine ⟨⟨⟨⟨⟨?_, hrec _⟩, ?_⟩, hrec _⟩, ?_⟩, ?_⟩
    · exact ⟨hctrl, had_lt, hcd_lt, hctrl_ad, hctrl_cd, had_cd⟩
    · exact ⟨hctrl, hcd_lt, hctrl_cd⟩
    · exact ⟨hctrl, hcd_lt, hctrl_cd⟩
    · exact hcd_lt

/-! ## §7. The in-place instantiation: a DROP-IN for the flat `lookupReadAt`. -/

/-- The Babbush merged-AND read at the in-place windowed-multiplier layout: address
    bits at `ulookup_address_idx`, AND-ancillas at `ulookup_and_idx`, root control
    `ulookup_ctrl_idx`, word at `pos`.  The cheaper (`2^w − 1`) Babbush replacement for
    `WindowedCircuit.lookupReadAt` (`2·w·2^w`). -/
def babbushReadInPlace (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) : EGate :=
  unaryQROMPos ulookup_address_idx ulookup_and_idx pos W T w ulookup_ctrl_idx 0

theorem toffoli_babbushReadInPlace (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    EGate.toffoli (babbushReadInPlace w pos W T) = 2 ^ w - 1 :=
  toffoli_unaryQROMPos _ _ _ _ _ _ _ _

theorem tcount_babbushReadInPlace (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    EGate.tcount (babbushReadInPlace w pos W T) = 7 * (2 ^ w - 1) :=
  tcount_unaryQROMPos _ _ _ _ _ _ _ _

private theorem ucand_inj : ∀ i i', ulookup_and_idx i = ulookup_and_idx i' → i = i' := by
  intro i i' h; simp only [ulookup_and_idx] at h; omega

/-- **★ DROP-IN SELECTION LEMMA ★** — EXACTLY the shape of
    `WindowedLookupSelect.lookupReadAt_selects`, with the Babbush read in place of the
    flat read: on a clean-ancilla state with address `= v`, the read XORs `T v` onto the
    word `pos` and preserves everything else. -/
theorem babbushReadInPlace_selects
    (w W : Nat) (T : Nat → Nat) (pos : Nat → Nat) (f : Nat → Bool) (v : Nat)
    (hw : 0 < w) (hv : v < 2 ^ w)
    (hctrl : f ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w → f (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w → f (ulookup_and_idx i) = false)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k) :
    (∀ j, j < W →
      EGate.applyNat (babbushReadInPlace w pos W T) f (pos j)
        = xor (f (pos j)) ((T v).testBit j))
    ∧ (∀ p, (∀ j, j < W → p ≠ pos j) →
        EGate.applyNat (babbushReadInPlace w pos W T) f p = f p) := by
  have hdec : decodeReg ulookup_address_idx w f = v := by
    rw [decodeReg_eq_mod_of_testBit ulookup_address_idx w v f haddr, Nat.mod_eq_of_lt hv]
  -- disjointness side-conditions of the selection lemma at the interleaved layout
  have h_anc_out : ∀ i j, i < w → j < W → ulookup_and_idx i ≠ pos j := by
    intro i j hi hj; have := hpos_high j hj; simp only [ulookup_and_idx]; omega
  have h_anc_addr : ∀ i i', i < w → i' < w → ulookup_and_idx i ≠ ulookup_address_idx i' := by
    intro i i' _ _; simp only [ulookup_and_idx, ulookup_address_idx]; omega
  have h_addr_out : ∀ i j, i < w → j < W → ulookup_address_idx i ≠ pos j := by
    intro i j hi hj; have := hpos_high j hj; simp only [ulookup_address_idx]; omega
  have h_ctrl_out : ∀ j, j < W → ulookup_ctrl_idx ≠ pos j := by
    intro j hj; have := hpos_high j hj; simp only [ulookup_ctrl_idx]; omega
  have h_ctrl_anc : ∀ i, i < w → ulookup_ctrl_idx ≠ ulookup_and_idx i := by
    intro i _; simp only [ulookup_ctrl_idx, ulookup_and_idx]; omega
  refine ⟨fun j hj => ?_, fun p hp => ?_⟩
  · have hsel := unaryQROMPos_selects_word ulookup_address_idx ulookup_and_idx pos W T
      hpos_inj ucand_inj w ulookup_ctrl_idx 0 f h_anc_out h_anc_addr h_addr_out
      h_ctrl_out h_ctrl_anc hand j hj
    show EGate.applyNat (unaryQROMPos ulookup_address_idx ulookup_and_idx pos W T w
        ulookup_ctrl_idx 0) f (pos j) = _
    rw [hsel, hctrl, Bool.true_and, Nat.zero_add, hdec]
  · by_cases hex : ∃ i, i < w ∧ p = ulookup_and_idx i
    · obtain ⟨i, hi, rfl⟩ := hex
      show EGate.applyNat (unaryQROMPos ulookup_address_idx ulookup_and_idx pos W T w
          ulookup_ctrl_idx 0) f (ulookup_and_idx i) = f (ulookup_and_idx i)
      rw [unaryQROMPos_anc_cleared ulookup_address_idx ulookup_and_idx pos W T ucand_inj
            w ulookup_ctrl_idx 0 f i hi, hand i hi]
    · simp only [not_exists, not_and] at hex
      exact unaryQROMPos_frame ulookup_address_idx ulookup_and_idx pos W T w
        ulookup_ctrl_idx 0 f p hp hex

/-- Well-typedness of the in-place Babbush read on any dimension covering the
    interleaved ctrl/address/ancilla block (`2w + 1`) and the word positions. -/
theorem babbushReadInPlace_wellTypedAt (w W : Nat) (T : Nat → Nat) (pos : Nat → Nat)
    (dim : Nat) (hw : 0 < w) (hdim : 2 * w + 1 ≤ dim)
    (hpos : ∀ j, j < W → pos j < dim ∧ 2 * w < pos j) :
    EGate.WellTypedAt dim (babbushReadInPlace w pos W T) := by
  apply unaryQROMPos_wellTypedAt ulookup_address_idx ulookup_and_idx pos W T dim ucand_inj
    w ulookup_ctrl_idx 0
  · simp only [ulookup_ctrl_idx]; omega
  · intro i hi; simp only [ulookup_address_idx]; omega
  · intro i hi; simp only [ulookup_and_idx]; omega
  · intro j hj; exact (hpos j hj).1
  · intro i i' _ _; simp only [ulookup_address_idx, ulookup_and_idx]; omega
  · intro i j hi hj; have := (hpos j hj).2; simp only [ulookup_address_idx]; omega
  · intro i j hi hj; have := (hpos j hj).2; simp only [ulookup_and_idx]; omega
  · intro i hi; simp only [ulookup_ctrl_idx, ulookup_address_idx]; omega
  · intro i hi; simp only [ulookup_ctrl_idx, ulookup_and_idx]; omega
  · intro j hj; have := (hpos j hj).2; simp only [ulookup_ctrl_idx]; omega

end FormalRV.Shor.MeasuredBabbushRead
