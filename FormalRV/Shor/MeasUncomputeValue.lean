/-
  FormalRV.Shor.MeasUncomputeValue — discharging the named obligation
  `BabbushLookupAddValueSpec` (Boolean value-correctness of the measured
  lookup-add `babbushLookupAdd`), HONESTLY.

  ## What is proven here

  1. **The general `unaryQROM` selection lemma** (`unaryQROM_selects_word`,
     plus `unaryQROM_frame` / `unaryQROM_anc_cleared`): the recursive
     measurement-uncompute babbush QROM `MeasUncompute.unaryQROM` reads
     EXACTLY the addressed table row — on any state with clean AND-ancillas,
     each output position `outBase + j` is XOR'd with
     `f ctrl && (T address).testBit j`, the ancillas come back `false`, and
     every other position is untouched.  This is the `EGate` analogue of the
     Gate-level `lookupReadAt_selects`, proven by induction on the recursion
     depth (it does NOT follow from `lookupReadAt_selects`: `unaryQROM` is a
     different circuit — the `2^w − 1`-Toffoli merged-AND tree, not the flat
     `2w·2^w` multi-iteration).

  2. **The unguarded `BabbushLookupAddValueSpec` is UNINSTANTIABLE**
     (`babbushLookupAddValueSpec_unsatisfiable`): for ANY table `T` that is
     everywhere positive and ANY parameters, NO decoder pair `decAcc`/`decAddr`
     satisfies the `∀ f` spec — the all-`false` state is a fixed point of the
     whole circuit (`babbushLookupAdd_const_false`), so the spec would force
     `decAcc f₀ = decAcc f₀ + T (decAddr f₀) > decAcc f₀`.

  3. **A LAYOUT finding** (`babbushLookupAdd_misses_table`): `unaryQROM`
     deposits the table word at the STRIDE-1 positions `outBase + j`, while
     the Cuccaro adder consumes its addend at the STRIDE-2 positions
     `q_start + 2·j + 2`.  Whenever the output word is disjoint from the
     adder block (the natural reading of the parameter list), the adder adds
     the state's own addend register — the looked-up value NEVER reaches the
     accumulator, and the final accumulator is provably independent of `T`.
     A contiguous word can meet a stride-2 register in at most one position,
     so the only width at which `babbushLookupAdd` genuinely performs
     `acc += T[addr]` is `W = 1` with `outBase = q_start + 2` (1-bit table
     words feeding addend bit 0).  Fixing `W ≥ 2` needs `unaryQROM` to take a
     position MAP (as `lookupReadAt` does) instead of the hard-coded
     `fun j => outBase + j` — a change to `MeasUncompute.lean`, out of scope
     here (this file adds no changes to existing files).

  4. **The guarded spec, instantiated on the true regime**
     (`BabbushLookupAddValueSpecOn` + `babbushLookupAddValueSpecOn_holds`):
     with `W = 1`, `outBase = q_start + 2`, honest decoders
     `decAcc = decodeReg (fun i => q_start + 2*i + 1) bits` (the Cuccaro
     augend) and `decAddr = decodeReg (fun i => addrBase + i) w` (the QROM
     address), and `P` = the clean-input family (ctrl set, ancillas + carry +
     addend clean, table value a single bit, no overflow), every `f ∈ P`
     satisfies `decAcc (applyNat (babbushLookupAdd …) f) = decAcc f + T (decAddr f)`.
     The guard is necessary: cleanliness (dirty ancillas corrupt the read),
     `T (addr) ≤ 1` (the W = 1 layout transports one bit), and
     `acc + T addr < 2^bits` (the spec's RHS has no `% 2^bits`).
-/
import FormalRV.Shor.WindowedEndToEnd
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect

namespace FormalRV.Shor.MeasUncomputeValue

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit FormalRV.Shor.WindowedLookupAdd
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedEndToEnd

/-! ## §1. `decodeReg` recursion helper. -/

/-- `decodeReg` peels its top bit: bit `n` (at `idx n`) carries weight `2^n`. -/
theorem decodeReg_succ (idx : Nat → Nat) (n : Nat) (f : Nat → Bool) :
    decodeReg idx (n + 1) f
      = decodeReg idx n f + (if f (idx n) then 2 ^ n else 0) := by
  unfold decodeReg
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

/-! ## §2. `unaryQROM` frame: positions off the output word and the ancilla
register are untouched (no hypotheses needed). -/

/-- **`unaryQROM` frame.**  Any position that is neither an output-word
position (`outBase + j`, `j < W`) nor an AND-ancilla of the tree
(`ancBase + i`, `i < d`) is untouched — in particular the ctrl and the whole
address register are preserved. -/
theorem unaryQROM_frame (W : Nat) (T : Nat → Nat) (addrBase ancBase outBase : Nat) :
    ∀ (d ctrl base : Nat) (f : Nat → Bool) (p : Nat),
      (∀ j, j < W → p ≠ outBase + j) →
      (∀ i, i < d → p ≠ ancBase + i) →
      EGate.applyNat (unaryQROM W T addrBase ancBase outBase d ctrl base) f p = f p
  | 0, ctrl, base, f, p, hp_out, _ => by
    show Gate.applyNat (cx_gates_from_indices ctrl
        (wordCnotsAt (fun j => outBase + j) W (T base))) f p = f p
    rw [applyNat_cx_gates_from_indices]
    apply Lookup.cnot_layer_post_state_frame
    intro hmem
    obtain ⟨j, hj, _, hpj⟩ := (mem_wordCnotsAt _ W (T base) p).mp hmem
    exact hp_out j hj hpj
  | d + 1, ctrl, base, f, p, hp_out, hp_anc => by
    have hp_d : p ≠ ancBase + d := hp_anc d (Nat.lt_succ_self d)
    have hp_anc' : ∀ i, i < d → p ≠ ancBase + i :=
      fun i hi => hp_anc i (Nat.lt_succ_of_lt hi)
    show Function.update
        (Gate.applyNat (Gate.CX ctrl (ancBase + d))
          (EGate.applyNat (unaryQROM W T addrBase ancBase outBase d (ancBase + d) base)
            (Gate.applyNat (Gate.CX ctrl (ancBase + d))
              (EGate.applyNat (unaryQROM W T addrBase ancBase outBase d (ancBase + d) (base + 2 ^ d))
                (Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d)) f)))))
        (ancBase + d) false p = f p
    rw [Function.update_of_ne hp_d, Gate.applyNat_CX, update_neq _ _ _ _ hp_d,
        unaryQROM_frame W T addrBase ancBase outBase d (ancBase + d) base _ p hp_out hp_anc',
        Gate.applyNat_CX, update_neq _ _ _ _ hp_d,
        unaryQROM_frame W T addrBase ancBase outBase d (ancBase + d) (base + 2 ^ d) _ p hp_out hp_anc',
        Gate.applyNat_CCX, update_neq _ _ _ _ hp_d]

/-! ## §3. `unaryQROM` returns its AND-ancillas cleared — `EGate.mz` resets
each level's ancilla after its last use, regardless of the input state. -/

/-- **`unaryQROM` clears its AND-ancillas.**  Each level's ancilla is
measure-reset (`EGate.mz`) after its last use, so every `ancBase + i`
(`i < d`) reads `false` afterwards — for ANY input state. -/
theorem unaryQROM_anc_cleared (W : Nat) (T : Nat → Nat) (addrBase ancBase outBase : Nat) :
    ∀ (d ctrl base : Nat) (f : Nat → Bool) (i : Nat), i < d →
      EGate.applyNat (unaryQROM W T addrBase ancBase outBase d ctrl base) f (ancBase + i)
        = false
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | d + 1, ctrl, base, f, i, hi => by
    show Function.update
        (Gate.applyNat (Gate.CX ctrl (ancBase + d))
          (EGate.applyNat (unaryQROM W T addrBase ancBase outBase d (ancBase + d) base)
            (Gate.applyNat (Gate.CX ctrl (ancBase + d))
              (EGate.applyNat (unaryQROM W T addrBase ancBase outBase d (ancBase + d) (base + 2 ^ d))
                (Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d)) f)))))
        (ancBase + d) false (ancBase + i) = false
    by_cases hid : i = d
    · subst hid
      exact Function.update_self _ _ _
    · have hne : ancBase + i ≠ ancBase + d := by omega
      rw [Function.update_of_ne hne, Gate.applyNat_CX, update_neq _ _ _ _ hne,
          unaryQROM_anc_cleared W T addrBase ancBase outBase d (ancBase + d) base _ i
            (by omega)]

/-! ## §4. THE SELECTION LEMMA: `unaryQROM` XORs exactly the addressed table
row into the output word. -/

/-- **THE `unaryQROM` SELECTION LEMMA.**  On a state whose AND-ancillas
`ancBase + i` (`i < d`) are clean, with the tree's registers pairwise
disjoint and the sub-tree control `ctrl` off the output/ancilla registers,
the babbush unary-iteration QROM `unaryQROM … d ctrl base` XORs exactly the
addressed table row into the output word:

  `out_j ↦ out_j ⊕ (f ctrl ∧ (T (base + addr)).testBit j)`,

where `addr = decodeReg (fun i => addrBase + i) d f` is the value of the
`d`-bit address sub-register.  Proven by induction on the tree depth: the
level-`d` ancilla is loaded with `ctrl ∧ addr_d` (CCX), steers the
`bit_d = 1` half at `base + 2^d`, is flipped to `ctrl ∧ ¬addr_d` (CX) to
steer the `bit_d = 0` half at `base`, and exactly one of the two halves
fires.  This is the `EGate`/measurement-uncompute analogue of the Gate-level
`lookupReadAt_selects_word`. -/
theorem unaryQROM_selects_word (W : Nat) (T : Nat → Nat) (addrBase ancBase outBase : Nat) :
    ∀ (d ctrl base : Nat) (f : Nat → Bool),
      (∀ i j, i < d → j < W → ancBase + i ≠ outBase + j) →
      (∀ i i', i < d → i' < d → ancBase + i ≠ addrBase + i') →
      (∀ i j, i < d → j < W → addrBase + i ≠ outBase + j) →
      (∀ j, j < W → ctrl ≠ outBase + j) →
      (∀ i, i < d → ctrl ≠ ancBase + i) →
      (∀ i, i < d → f (ancBase + i) = false) →
      ∀ j, j < W →
        EGate.applyNat (unaryQROM W T addrBase ancBase outBase d ctrl base) f (outBase + j)
          = xor (f (outBase + j))
              (f ctrl && (T (base + decodeReg (fun i => addrBase + i) d f)).testBit j)
  | 0, ctrl, base, f, _, _, _, h_ctrl_out, _, _ => by
    intro j hj
    show Gate.applyNat (cx_gates_from_indices ctrl
        (wordCnotsAt (fun j => outBase + j) W (T base))) f (outBase + j) = _
    have hinj : ∀ j k : Nat, j < W → k < W → outBase + j = outBase + k → j = k := by
      intro j k _ _ h; omega
    have hctrl_not_mem : ctrl ∉ wordCnotsAt (fun j => outBase + j) W (T base) := by
      intro hmem
      obtain ⟨j', hj', _, hcj⟩ := (mem_wordCnotsAt _ W (T base) ctrl).mp hmem
      exact h_ctrl_out j' hj' hcj
    have hdec0 : decodeReg (fun i => addrBase + i) 0 f = 0 := by simp [decodeReg]
    rw [applyNat_cx_gates_from_indices, hdec0, Nat.add_zero]
    by_cases hb : (T base).testBit j = true
    · rw [Lookup.cnot_layer_post_state_at ctrl _
            (wordCnotsAt_nodup (fun j => outBase + j) W (T base) hinj) hctrl_not_mem f
            (outBase + j)
            ((pos_mem_wordCnotsAt_iff (fun j => outBase + j) W (T base) j hj hinj).mpr hb),
          hb, Bool.and_true]
    · have hbf : (T base).testBit j = false := (Bool.not_eq_true _).mp hb
      rw [Lookup.cnot_layer_post_state_frame ctrl _ f (outBase + j)
            (fun hmem =>
              hb ((pos_mem_wordCnotsAt_iff (fun j => outBase + j) W (T base) j hj hinj).mp hmem)),
          hbf, Bool.and_false, Bool.xor_false]
  | d + 1, ctrl, base, f, h_anc_out, h_anc_addr, h_addr_out, h_ctrl_out, h_ctrl_anc,
      h_clean => by
    have hlt := Nat.lt_succ_self d
    -- restricted hypotheses for the two depth-`d` sub-calls (control `ancBase + d`)
    have H1 : ∀ i j, i < d → j < W → ancBase + i ≠ outBase + j :=
      fun i j hi hj => h_anc_out i j (Nat.lt_succ_of_lt hi) hj
    have H2 : ∀ i i', i < d → i' < d → ancBase + i ≠ addrBase + i' :=
      fun i i' hi hi' => h_anc_addr i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi')
    have H3 : ∀ i j, i < d → j < W → addrBase + i ≠ outBase + j :=
      fun i j hi hj => h_addr_out i j (Nat.lt_succ_of_lt hi) hj
    have H4 : ∀ j, j < W → ancBase + d ≠ outBase + j := fun j hj => h_anc_out d j hlt hj
    have H5 : ∀ i, i < d → ancBase + d ≠ ancBase + i := fun i hi => by omega
    -- the five intermediate states
    set s1 := Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d)) f with hs1
    set s2 := EGate.applyNat
      (unaryQROM W T addrBase ancBase outBase d (ancBase + d) (base + 2 ^ d)) s1 with hs2
    set s3 := Gate.applyNat (Gate.CX ctrl (ancBase + d)) s2 with hs3
    set s4 := EGate.applyNat
      (unaryQROM W T addrBase ancBase outBase d (ancBase + d) base) s3 with hs4
    set s5 := Gate.applyNat (Gate.CX ctrl (ancBase + d)) s4 with hs5
    have hg : EGate.applyNat (unaryQROM W T addrBase ancBase outBase (d + 1) ctrl base) f
        = Function.update s5 (ancBase + d) false := by
      rw [hs5, hs4, hs3, hs2, hs1]; rfl
    -- s1: the CCX loads `ctrl ∧ addr_d` into the level-`d` ancilla
    have hs1_ne : ∀ p, p ≠ ancBase + d → s1 p = f p := by
      intro p hp
      rw [hs1, Gate.applyNat_CCX]
      exact update_neq _ _ _ _ hp
    have hs1_at : s1 (ancBase + d) = (f ctrl && f (addrBase + d)) := by
      rw [hs1, Gate.applyNat_CCX, update_eq, h_clean d hlt, Bool.false_xor]
    have hs1_addr : decodeReg (fun i => addrBase + i) d s1
        = decodeReg (fun i => addrBase + i) d f :=
      decodeReg_ext _ _ _ _ (fun i hi =>
        hs1_ne _ (Ne.symm (h_anc_addr d i hlt (Nat.lt_succ_of_lt hi))))
    have hs1_clean : ∀ i, i < d → s1 (ancBase + i) = false := by
      intro i hi
      rw [hs1_ne _ (by omega)]
      exact h_clean i (Nat.lt_succ_of_lt hi)
    -- first half: reads `T (base + 2^d + addr)` controlled on `ctrl ∧ addr_d`
    have v2 : ∀ j, j < W → s2 (outBase + j)
        = xor (f (outBase + j))
            ((f ctrl && f (addrBase + d))
              && (T (base + 2 ^ d + decodeReg (fun i => addrBase + i) d f)).testBit j) := by
      intro j hj
      rw [hs2, unaryQROM_selects_word W T addrBase ancBase outBase d (ancBase + d)
            (base + 2 ^ d) s1 H1 H2 H3 H4 H5 hs1_clean j hj,
          hs1_ne _ (Ne.symm (H4 j hj)), hs1_at, hs1_addr]
    -- s2 preserves ctrl, the level-`d` ancilla, and the address register
    have hs2_ctrl : s2 ctrl = f ctrl := by
      rw [hs2, unaryQROM_frame W T addrBase ancBase outBase d (ancBase + d)
            (base + 2 ^ d) s1 ctrl h_ctrl_out
            (fun i hi => h_ctrl_anc i (Nat.lt_succ_of_lt hi)),
          hs1_ne ctrl (h_ctrl_anc d hlt)]
    have hs2_anc : s2 (ancBase + d) = (f ctrl && f (addrBase + d)) := by
      rw [hs2, unaryQROM_frame W T addrBase ancBase outBase d (ancBase + d)
            (base + 2 ^ d) s1 (ancBase + d) H4 H5, hs1_at]
    have hs2_addrpt : ∀ i, i < d → s2 (addrBase + i) = f (addrBase + i) := by
      intro i hi
      rw [hs2, unaryQROM_frame W T addrBase ancBase outBase d (ancBase + d)
            (base + 2 ^ d) s1 (addrBase + i)
            (fun j hj => h_addr_out i j (Nat.lt_succ_of_lt hi) hj)
            (fun i' hi' =>
              Ne.symm (h_anc_addr i' i (Nat.lt_succ_of_lt hi') (Nat.lt_succ_of_lt hi))),
          hs1_ne _ (Ne.symm (h_anc_addr d i hlt (Nat.lt_succ_of_lt hi)))]
    -- s3: the CX flips the ancilla to `ctrl ∧ ¬addr_d`
    have hs3_ne : ∀ p, p ≠ ancBase + d → s3 p = s2 p := by
      intro p hp
      rw [hs3, Gate.applyNat_CX]
      exact update_neq _ _ _ _ hp
    have hs3_at : s3 (ancBase + d) = (f ctrl && !(f (addrBase + d))) := by
      rw [hs3, Gate.applyNat_CX, update_eq, hs2_anc, hs2_ctrl]
      cases f ctrl <;> cases f (addrBase + d) <;> rfl
    have hs3_clean : ∀ i, i < d → s3 (ancBase + i) = false := by
      intro i hi
      rw [hs3_ne _ (by omega), hs2]
      exact unaryQROM_anc_cleared W T addrBase ancBase outBase d (ancBase + d)
        (base + 2 ^ d) s1 i hi
    have hs3_addr : decodeReg (fun i => addrBase + i) d s3
        = decodeReg (fun i => addrBase + i) d f :=
      decodeReg_ext _ _ _ _ (fun i hi => by
        rw [hs3_ne _ (Ne.symm (h_anc_addr d i hlt (Nat.lt_succ_of_lt hi))),
            hs2_addrpt i hi])
    have hs3_out : ∀ j, j < W → s3 (outBase + j) = s2 (outBase + j) :=
      fun j hj => hs3_ne _ (Ne.symm (H4 j hj))
    -- second half: reads `T (base + addr)` controlled on `ctrl ∧ ¬addr_d`
    have v4 : ∀ j, j < W → s4 (outBase + j)
        = xor (s3 (outBase + j))
            ((f ctrl && !(f (addrBase + d)))
              && (T (base + decodeReg (fun i => addrBase + i) d f)).testBit j) := by
      intro j hj
      rw [hs4, unaryQROM_selects_word W T addrBase ancBase outBase d (ancBase + d)
            base s3 H1 H2 H3 H4 H5 hs3_clean j hj, hs3_at, hs3_addr]
    -- assemble: exactly one of the two halves fires
    intro j hj
    have hne_out : outBase + j ≠ ancBase + d := Ne.symm (h_anc_out d j hlt hj)
    rw [hg, Function.update_of_ne hne_out, hs5, Gate.applyNat_CX,
        update_neq _ _ _ _ hne_out, v4 j hj, hs3_out j hj, v2 j hj]
    simp only [decodeReg_succ]
    by_cases hb : f (addrBase + d) = true
    · have hidx : decodeReg (fun i => addrBase + i) d f
          + (if f (addrBase + d) = true then 2 ^ d else 0)
          = 2 ^ d + decodeReg (fun i => addrBase + i) d f := by
        rw [if_pos hb]; omega
      rw [hidx, ← Nat.add_assoc, hb]
      simp only [Bool.and_true, Bool.not_true, Bool.and_false, Bool.false_and,
                 Bool.xor_false]
    · have hbf : f (addrBase + d) = false := (Bool.not_eq_true _).mp hb
      have hidx : decodeReg (fun i => addrBase + i) d f
          + (if f (addrBase + d) = true then 2 ^ d else 0)
          = decodeReg (fun i => addrBase + i) d f := by
        rw [if_neg hb]; omega
      rw [hidx, hbf]
      simp only [Bool.and_false, Bool.false_and, Bool.xor_false, Bool.not_false,
                 Bool.and_true]

/-! ## §5. The guarded value-spec and the clean-input family. -/

/-- **The guarded value-spec** — `BabbushLookupAddValueSpec`'s step field
restricted to a family `P` of well-formed inputs.  The unguarded original
quantifies over ALL `f : Nat → Bool` with a mod-free RHS and is uninstantiable
for EVERY decoder pair (`babbushLookupAddValueSpec_unsatisfiable` below); this
is the honest per-primitive statement, instantiated in §6. -/
structure BabbushLookupAddValueSpecOn (P : (Nat → Bool) → Prop)
    (w W : Nat) (T : Nat → Nat) (bits addrBase ancBase outBase q_start : Nat)
    (decAcc decAddr : (Nat → Bool) → Nat) where
  step : ∀ (f : Nat → Bool), P f →
    decAcc (EGate.applyNat (babbushLookupAdd w W T bits addrBase ancBase outBase q_start) f)
      = decAcc f + T (decAddr f)

/-- **The clean-input family** for the measured lookup-add at `W = 1`
(`outBase = q_start + 2` = Cuccaro addend bit 0):

* ctrl qubit `0` is set (the QROM's always-on root control);
* the QROM AND-ancillas are clean;
* the Cuccaro carry-in is clean;
* the addend register (whose bit 0 IS the QROM output word) is clean;
* the looked-up table word is a single bit — the `W = 1` layout transports
  exactly one bit (see the §7 layout finding for why wider words cannot
  reach the stride-2 addend register);
* the mod-free sum does not overflow the `bits`-wide accumulator (the spec's
  RHS `decAcc f + T (decAddr f)` carries no `% 2^bits`). -/
def CleanLookupAddInput (w bits addrBase ancBase q_start : Nat) (T : Nat → Nat)
    (f : Nat → Bool) : Prop :=
  f 0 = true
  ∧ (∀ i, i < w → f (ancBase + i) = false)
  ∧ f q_start = false
  ∧ (∀ i, i < bits → f (q_start + 2 * i + 2) = false)
  ∧ T (decodeReg (fun i => addrBase + i) w f) ≤ 1
  ∧ decodeReg (fun i => q_start + 2 * i + 1) bits f
      + T (decodeReg (fun i => addrBase + i) w f) < 2 ^ bits

/-! ## §6. HEADLINE: the guarded spec HOLDS on the true regime (`W = 1`,
`outBase = q_start + 2`). -/

/-- **★ HEADLINE — the guarded value-spec HOLDS.**  At the (unique, see §7)
honest layout — `W = 1`, `outBase = q_start + 2` — with the QROM registers
off the adder block, the measured lookup-add `babbushLookupAdd` realises one
lookup-add step on every clean input, with the honest decoders

* `decAcc  = decodeReg (fun i => q_start + 2*i + 1) bits`  (Cuccaro augend),
* `decAddr = decodeReg (fun i => addrBase + i) w`          (QROM address):

`decAcc (applyNat (babbushLookupAdd …) f) = decAcc f + T (decAddr f)`.

The proof is one window-step: the `unaryQROM` selection lemma puts
`T[addr]` into the addend (§4), the Cuccaro decode-level `sumCorrect`
accumulates it, and the `mzList` measure-clear leaves the accumulator
untouched. -/
def babbushLookupAddValueSpecOn_holds
    (w bits : Nat) (T : Nat → Nat) (addrBase ancBase q_start : Nat)
    (hbits : 1 ≤ bits) (h_anc_pos : 0 < ancBase)
    (h_anc_addr : ∀ i i', i < w → i' < w → ancBase + i ≠ addrBase + i')
    (h_anc_blk : ∀ i, i < w →
      ¬ (q_start ≤ ancBase + i ∧ ancBase + i ≤ q_start + 2 * bits))
    (h_addr_blk : ∀ i, i < w →
      ¬ (q_start ≤ addrBase + i ∧ addrBase + i ≤ q_start + 2 * bits)) :
    BabbushLookupAddValueSpecOn
      (CleanLookupAddInput w bits addrBase ancBase q_start T)
      w 1 T bits addrBase ancBase (q_start + 2) q_start
      (decodeReg (fun i => q_start + 2 * i + 1) bits)
      (decodeReg (fun i => addrBase + i) w) := by
  constructor
  intro f hf
  obtain ⟨hctrl, hanc, hcarry, haddend, hTle, hover⟩ := hf
  have hA0 : f (q_start + 2) = false := by simpa using haddend 0 hbits
  -- selection-lemma side conditions for the `W = 1` word at `q_start + 2`
  have S1 : ∀ i j, i < w → j < 1 → ancBase + i ≠ q_start + 2 + j := by
    intro i j hi hj
    have := h_anc_blk i hi
    omega
  have S3 : ∀ i j, i < w → j < 1 → addrBase + i ≠ q_start + 2 + j := by
    intro i j hi hj
    have := h_addr_blk i hi
    omega
  have S4 : ∀ j, j < 1 → (0 : Nat) ≠ q_start + 2 + j := by intro j hj; omega
  have S5 : ∀ i, i < w → (0 : Nat) ≠ ancBase + i := by intro i hi; omega
  have hfr := unaryQROM_frame 1 T addrBase ancBase (q_start + 2) w 0 0 f
  -- the read writes `(T addr).testBit 0` into addend bit 0 …
  have hread : EGate.applyNat (unaryQROM 1 T addrBase ancBase (q_start + 2) w 0 0) f
      (q_start + 2) = (T (decodeReg (fun i => addrBase + i) w f)).testBit 0 := by
    have h := unaryQROM_selects_word 1 T addrBase ancBase (q_start + 2) w 0 0 f
      S1 h_anc_addr S3 S4 S5 hanc 0 (by omega)
    simpa [hctrl, hA0] using h
  -- … leaves the carry-in clean …
  have hclean1 : EGate.applyNat (unaryQROM 1 T addrBase ancBase (q_start + 2) w 0 0) f
      q_start = false := by
    rw [hfr q_start (fun j hj => by omega)
          (fun i hi => by have := h_anc_blk i hi; omega)]
    exact hcarry
  -- … leaves the augend register at `acc` …
  have haug1 : decodeReg (fun i => q_start + 2 * i + 1) bits
      (EGate.applyNat (unaryQROM 1 T addrBase ancBase (q_start + 2) w 0 0) f)
      = decodeReg (fun i => q_start + 2 * i + 1) bits f :=
    decodeReg_ext _ _ _ _ (fun i hi =>
      hfr (q_start + 2 * i + 1) (fun j hj => by omega)
        (fun i' hi' => by have := h_anc_blk i' hi'; omega))
  -- … and leaves the addend register decoding to exactly `T addr`.
  have hadd1 : decodeReg (fun i => q_start + 2 * i + 2) bits
      (EGate.applyNat (unaryQROM 1 T addrBase ancBase (q_start + 2) w 0 0) f)
      = T (decodeReg (fun i => addrBase + i) w f) := by
    have h2bits : (2 : Nat) ^ 1 ≤ 2 ^ bits := Nat.pow_le_pow_right (by omega) hbits
    rw [decodeReg_eq_mod_of_testBit (fun i => q_start + 2 * i + 2) bits
          (T (decodeReg (fun i => addrBase + i) w f)) _ ?_,
        Nat.mod_eq_of_lt (by omega)]
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      simpa using hread
    · have h2i : (2 : Nat) ^ 1 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [hfr (q_start + 2 * i + 2) (fun j hj => by omega)
            (fun i' hi' => by have := h_anc_blk i' hi'; omega),
          haddend i hi]
      exact (Nat.testBit_lt_two_pow (by omega)).symm
  -- the Cuccaro add accumulates the addend into the augend
  have hsum : decodeReg (fun i => q_start + 2 * i + 1) bits
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (EGate.applyNat (unaryQROM 1 T addrBase ancBase (q_start + 2) w 0 0) f))
      = (decodeReg (fun i => q_start + 2 * i + 1) bits
            (EGate.applyNat (unaryQROM 1 T addrBase ancBase (q_start + 2) w 0 0) f)
          + decodeReg (fun i => q_start + 2 * i + 2) bits
              (EGate.applyNat (unaryQROM 1 T addrBase ancBase (q_start + 2) w 0 0) f))
        % 2 ^ bits :=
    cuccaroAdder.sumCorrect bits q_start _ hclean1
  -- the measure-clear never touches the (odd-offset) augend register
  have hmzdec : ∀ g : Nat → Bool,
      decodeReg (fun i => q_start + 2 * i + 1) bits
        (EGate.applyNat (mzList ((List.range 1).map (fun j => q_start + 2 + j))) g)
      = decodeReg (fun i => q_start + 2 * i + 1) bits g := by
    intro g
    refine decodeReg_ext _ _ _ _ (fun i hi => ?_)
    refine applyNat_mzList_preserves _ _ ?_
    simp only [List.mem_map, List.mem_range]
    rintro ⟨j, hj, hjeq⟩
    omega
  -- assemble
  have hsplit : EGate.applyNat
      (babbushLookupAdd w 1 T bits addrBase ancBase (q_start + 2) q_start) f
      = EGate.applyNat (mzList ((List.range 1).map (fun j => q_start + 2 + j)))
          (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (EGate.applyNat (unaryQROM 1 T addrBase ancBase (q_start + 2) w 0 0) f)) :=
    rfl
  rw [hsplit, hmzdec, hsum, haug1, hadd1, Nat.mod_eq_of_lt hover]

/-- **Non-vacuity of the guard**: the clean-input family is inhabited (for
any table with `T 0 ≤ 1`) — e.g. by the state with only the ctrl qubit set. -/
theorem cleanLookupAddInput_nonempty
    (w bits addrBase ancBase q_start : Nat) (T : Nat → Nat)
    (hbits : 1 ≤ bits) (haddr_pos : 0 < addrBase) (hanc_pos : 0 < ancBase)
    (hq_pos : 0 < q_start) (hT0 : T 0 ≤ 1) :
    CleanLookupAddInput w bits addrBase ancBase q_start T
      (fun p => decide (p = 0)) := by
  have h2bits : (2 : Nat) ^ 1 ≤ 2 ^ bits := Nat.pow_le_pow_right (by omega) hbits
  have haddr0 : decodeReg (fun i => addrBase + i) w (fun p => decide (p = 0)) = 0 :=
    decodeReg_eq_zero _ _ _ (fun i _ => by simp; omega)
  have haug0 : decodeReg (fun i => q_start + 2 * i + 1) bits
      (fun p => decide (p = 0)) = 0 :=
    decodeReg_eq_zero _ _ _ (fun i _ => by simp)
  refine ⟨by simp, fun i _ => by simp; omega, by simp; omega, fun i _ => by simp,
          ?_, ?_⟩
  · rw [haddr0]; exact hT0
  · rw [haddr0, haug0]; omega

/-- **Non-vacuity of the layout hypotheses**: the standard register layout
(address register, then AND-ancillas, stacked above the adder block)
satisfies every side condition of `babbushLookupAddValueSpecOn_holds`. -/
example (w bits q_start : Nat) (T : Nat → Nat) (hbits : 1 ≤ bits) :
    BabbushLookupAddValueSpecOn
      (CleanLookupAddInput w bits (q_start + 2 * bits + 1)
        (q_start + 2 * bits + 1 + w) q_start T)
      w 1 T bits (q_start + 2 * bits + 1) (q_start + 2 * bits + 1 + w)
      (q_start + 2) q_start
      (decodeReg (fun i => q_start + 2 * i + 1) bits)
      (decodeReg (fun i => q_start + 2 * bits + 1 + i) w) :=
  babbushLookupAddValueSpecOn_holds w bits T (q_start + 2 * bits + 1)
    (q_start + 2 * bits + 1 + w) q_start hbits (by omega)
    (fun i i' _ _ => by omega) (fun i _ => by omega) (fun i _ => by omega)

/-! ## §7. The layout finding: with the output word disjoint from the adder
block, the accumulator update is independent of the table. -/

/-- **The layout finding, proven.**  `unaryQROM` deposits the looked-up word
at the STRIDE-1 positions `outBase + j`, while the Cuccaro adder consumes
its addend at the STRIDE-2 positions `q_start + 2j + 2`; a contiguous word
can meet a stride-2 register in at most ONE position, so for `W ≥ 2` the
output word cannot coincide with the addend register (and any overlap with
the block puts an out-word position on an augend bit, which the trailing
`mzList` then WIPES).  Concretely: whenever the output word and the
AND-ancillas are disjoint from the adder block — the natural reading of the
parameter list — the accumulator update is

  `acc ↦ (acc + addend_f) % 2^bits`,

the state's OWN addend register, with the table `T` NOWHERE in the result
(the read is written at `outBase`, never consumed, and measured away).  So
in this regime no decoder pair can satisfy the `acc ↦ acc + T addr` spec
for a non-trivial `T` — the only honest regime is `W = 1`,
`outBase = q_start + 2` (§6). -/
theorem babbushLookupAdd_misses_table
    (w W : Nat) (T : Nat → Nat) (bits addrBase ancBase outBase q_start : Nat)
    (f : Nat → Bool)
    (h_out_blk : ∀ j, j < W →
      ¬ (q_start ≤ outBase + j ∧ outBase + j ≤ q_start + 2 * bits))
    (h_anc_blk : ∀ i, i < w →
      ¬ (q_start ≤ ancBase + i ∧ ancBase + i ≤ q_start + 2 * bits))
    (h_carry : f q_start = false) :
    decodeReg (fun i => q_start + 2 * i + 1) bits
        (EGate.applyNat (babbushLookupAdd w W T bits addrBase ancBase outBase q_start) f)
      = (decodeReg (fun i => q_start + 2 * i + 1) bits f
          + decodeReg (fun i => q_start + 2 * i + 2) bits f) % 2 ^ bits := by
  have hfr := unaryQROM_frame W T addrBase ancBase outBase w 0 0 f
  -- the read never touches the adder block …
  have hclean1 : EGate.applyNat (unaryQROM W T addrBase ancBase outBase w 0 0) f
      q_start = false := by
    rw [hfr q_start (fun j hj => by have := h_out_blk j hj; omega)
          (fun i hi => by have := h_anc_blk i hi; omega)]
    exact h_carry
  have haug1 : decodeReg (fun i => q_start + 2 * i + 1) bits
      (EGate.applyNat (unaryQROM W T addrBase ancBase outBase w 0 0) f)
      = decodeReg (fun i => q_start + 2 * i + 1) bits f :=
    decodeReg_ext _ _ _ _ (fun i hi =>
      hfr (q_start + 2 * i + 1) (fun j hj => by have := h_out_blk j hj; omega)
        (fun i' hi' => by have := h_anc_blk i' hi'; omega))
  have hadd1 : decodeReg (fun i => q_start + 2 * i + 2) bits
      (EGate.applyNat (unaryQROM W T addrBase ancBase outBase w 0 0) f)
      = decodeReg (fun i => q_start + 2 * i + 2) bits f :=
    decodeReg_ext _ _ _ _ (fun i hi =>
      hfr (q_start + 2 * i + 2) (fun j hj => by have := h_out_blk j hj; omega)
        (fun i' hi' => by have := h_anc_blk i' hi'; omega))
  -- … the adder adds the state's own addend …
  have hsum : decodeReg (fun i => q_start + 2 * i + 1) bits
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (EGate.applyNat (unaryQROM W T addrBase ancBase outBase w 0 0) f))
      = (decodeReg (fun i => q_start + 2 * i + 1) bits
            (EGate.applyNat (unaryQROM W T addrBase ancBase outBase w 0 0) f)
          + decodeReg (fun i => q_start + 2 * i + 2) bits
              (EGate.applyNat (unaryQROM W T addrBase ancBase outBase w 0 0) f))
        % 2 ^ bits :=
    cuccaroAdder.sumCorrect bits q_start _ hclean1
  -- … and the measure-clear stays off the augend register.
  have hmzdec : ∀ g : Nat → Bool,
      decodeReg (fun i => q_start + 2 * i + 1) bits
        (EGate.applyNat (mzList ((List.range W).map (fun j => outBase + j))) g)
      = decodeReg (fun i => q_start + 2 * i + 1) bits g := by
    intro g
    refine decodeReg_ext _ _ _ _ (fun i hi => ?_)
    refine applyNat_mzList_preserves _ _ ?_
    simp only [List.mem_map, List.mem_range]
    rintro ⟨j, hj, hjeq⟩
    have := h_out_blk j hj
    omega
  have hsplit : EGate.applyNat
      (babbushLookupAdd w W T bits addrBase ancBase outBase q_start) f
      = EGate.applyNat (mzList ((List.range W).map (fun j => outBase + j)))
          (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (EGate.applyNat (unaryQROM W T addrBase ancBase outBase w 0 0) f)) :=
    rfl
  rw [hsplit, hmzdec, hsum, haug1, hadd1]

/-! ## §8. The unguarded `BabbushLookupAddValueSpec` is uninstantiable. -/

/-- Writing `false` over the all-`false` state is a no-op (project-local
`update`). -/
theorem update_false_const (q : Nat) :
    update (fun _ => false) q false = (fun _ => false) := by
  funext p
  by_cases hp : p = q
  · subst hp; rw [update_eq]
  · rw [update_neq _ _ _ _ hp]

theorem applyNat_cx_gates_const_false (ctrl : Nat) :
    ∀ L : List Nat,
      Gate.applyNat (cx_gates_from_indices ctrl L) (fun _ => false) = (fun _ => false)
  | [] => rfl
  | t :: xs => by
    show Gate.applyNat (Gate.seq (cx_gates_from_indices ctrl xs) (Gate.CX ctrl t))
        (fun _ => false) = _
    rw [Gate.applyNat_seq, applyNat_cx_gates_const_false ctrl xs, Gate.applyNat_CX]
    exact update_false_const t

/-- The all-`false` state is a fixed point of the QROM read. -/
theorem unaryQROM_const_false (W : Nat) (T : Nat → Nat) (addrBase ancBase outBase : Nat) :
    ∀ (d ctrl base : Nat),
      EGate.applyNat (unaryQROM W T addrBase ancBase outBase d ctrl base) (fun _ => false)
        = (fun _ => false)
  | 0, ctrl, _ => applyNat_cx_gates_const_false ctrl _
  | d + 1, ctrl, base => by
    show Function.update
        (Gate.applyNat (Gate.CX ctrl (ancBase + d))
          (EGate.applyNat (unaryQROM W T addrBase ancBase outBase d (ancBase + d) base)
            (Gate.applyNat (Gate.CX ctrl (ancBase + d))
              (EGate.applyNat
                (unaryQROM W T addrBase ancBase outBase d (ancBase + d) (base + 2 ^ d))
                (Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d))
                  (fun _ => false))))))
        (ancBase + d) false = (fun _ => false)
    have hCCX : Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d))
        (fun _ => false) = (fun _ => false) := by
      rw [Gate.applyNat_CCX]; exact update_false_const _
    have hCX : Gate.applyNat (Gate.CX ctrl (ancBase + d))
        (fun _ => false) = (fun _ => false) := by
      rw [Gate.applyNat_CX]; exact update_false_const _
    rw [hCCX,
        unaryQROM_const_false W T addrBase ancBase outBase d (ancBase + d) (base + 2 ^ d),
        hCX, unaryQROM_const_false W T addrBase ancBase outBase d (ancBase + d) base, hCX]
    funext p
    by_cases hp : p = ancBase + d
    · subst hp; rw [Function.update_self]
    · rw [Function.update_of_ne hp]

/-- The all-`false` state is a fixed point of the full Cuccaro adder (sum
`0 + 0`, addend and carry restored, frame elsewhere). -/
theorem cuccaro_full_const_false (bits q : Nat) :
    Gate.applyNat (cuccaro_n_bit_adder_full bits q) (fun _ => false)
      = (fun _ => false) := by
  have hsum : decodeReg (fun i => q + 2 * i + 1) bits
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q) (fun _ => false)) = 0 := by
    have h : decodeReg (fun i => q + 2 * i + 1) bits
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q) (fun _ => false))
        = (decodeReg (fun i => q + 2 * i + 1) bits (fun _ => false)
            + decodeReg (fun i => q + 2 * i + 2) bits (fun _ => false)) % 2 ^ bits :=
      cuccaroAdder.sumCorrect bits q (fun _ => false) rfl
    rw [decodeReg_eq_zero (fun i => q + 2 * i + 1) bits (fun _ => false) (fun _ _ => rfl),
        decodeReg_eq_zero (fun i => q + 2 * i + 2) bits (fun _ => false) (fun _ _ => rfl)]
      at h
    simpa using h
  funext p
  by_cases hlow : p < q
  · exact cuccaro_n_bit_adder_full_frame_below bits q _ p hlow
  by_cases hhigh : q + 2 * bits + 1 ≤ p
  · exact cuccaro_n_bit_adder_full_frame_above bits q _ p hhigh
  by_cases hp0 : p = q
  · rw [hp0]
    exact (cuccaro_n_bit_adder_full_correct bits q (fun _ => false)).1
  by_cases hodd : (p - q) % 2 = 1
  · -- augend bit: read it back out of the (zero) decoded sum
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < bits ∧ p = q + 2 * i + 1 :=
      ⟨(p - q) / 2, by omega, by omega⟩
    have hbit := cuccaro_target_val_testBit bits q
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q) (fun _ => false)) i hi
    rw [← decodeReg_augend_eq_target, hsum, Nat.zero_testBit] at hbit
    exact hbit.symm
  · -- addend bit: restored
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < bits ∧ p = q + 2 * i + 2 :=
      ⟨(p - q - 2) / 2, by omega, by omega⟩
    exact (cuccaro_n_bit_adder_full_correct bits q _).2.2 i hi

theorem mzList_const_false :
    ∀ L : List Nat, EGate.applyNat (mzList L) (fun _ => false) = (fun _ => false)
  | [] => rfl
  | q :: qs => by
    show Function.update (EGate.applyNat (mzList qs) (fun _ => false)) q false = _
    rw [mzList_const_false qs]
    funext p
    by_cases hp : p = q
    · subst hp; rw [Function.update_self]
    · rw [Function.update_of_ne hp]

/-- The all-`false` state is a fixed point of the whole measured lookup-add. -/
theorem babbushLookupAdd_const_false
    (w W : Nat) (T : Nat → Nat) (bits addrBase ancBase outBase q_start : Nat) :
    EGate.applyNat (babbushLookupAdd w W T bits addrBase ancBase outBase q_start)
        (fun _ => false)
      = (fun _ => false) := by
  show EGate.applyNat (mzList ((List.range W).map (fun j => outBase + j)))
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (EGate.applyNat (unaryQROM W T addrBase ancBase outBase w 0 0)
          (fun _ => false)))
    = (fun _ => false)
  rw [unaryQROM_const_false, cuccaro_full_const_false, mzList_const_false]

/-- **The unguarded named obligation is UNINSTANTIABLE.**  For any
everywhere-positive table (e.g. `T = fun _ => 1`) and ANY parameters, NO
decoder pair satisfies `BabbushLookupAddValueSpec`: the all-`false` state is
a fixed point of the circuit, so the `∀ f` step at `f₀ = const false` would
force `decAcc f₀ = decAcc f₀ + T (decAddr f₀)` with a positive increment.
(For honest decoders the spec also fails on overflow states — its RHS has no
`% 2^bits` — and, for `W ≥ 2`, on the layout grounds of
`babbushLookupAdd_misses_table`.  This theorem is the cheapest certificate
that the GUARDED `BabbushLookupAddValueSpecOn` is the right statement.) -/
theorem babbushLookupAddValueSpec_unsatisfiable
    (w W : Nat) (T : Nat → Nat) (bits addrBase ancBase outBase q_start : Nat)
    (hT : ∀ v, 0 < T v)
    (decAcc decAddr : (Nat → Bool) → Nat)
    (spec : BabbushLookupAddValueSpec w W T bits addrBase ancBase outBase q_start
      decAcc decAddr) :
    False := by
  have h := spec.step (fun _ => false)
  rw [babbushLookupAdd_const_false] at h
  have hpos := hT (decAddr (fun _ => false))
  omega

end FormalRV.Shor.MeasUncomputeValue
