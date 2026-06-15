/-
  FormalRV.Shor.MeasUncomputeAt — the POSITION-PARAMETERIZED measured lookup-add:
  the layout-correct supersession of `MeasUncompute.babbushLookupAdd` for VALUE purposes.

  ## Why this file exists (the W ≥ 2 layout defect, proven elsewhere)

  `MeasUncompute.unaryQROM` hard-codes its output word at the STRIDE-1 positions
  `outBase + j`, while the Cuccaro adder of `MeasUncompute.babbushLookupAdd` consumes
  its addend at the STRIDE-2 positions `q_start + 2·j + 2`.  A contiguous word meets a
  stride-2 register in at most ONE position, so for every word width `W ≥ 2` the
  looked-up value never reaches the accumulator — PROVEN in
  `MeasUncomputeValue.babbushLookupAdd_misses_table` (the accumulator update is
  independent of the table), with the only honest regime being `W = 1`,
  `outBase = q_start + 2` (`babbushLookupAddValueSpecOn_holds`).

  ## The fix (ADDITIVE: no existing file is modified)

  `unaryQROMAt` takes a position MAP `pos : Nat → Nat` (exactly as the Gate-level
  `lookupReadAt` does) in place of the hard-coded `fun j => outBase + j`; ONLY the
  leaf word-CNOT targets change — the merged-AND tree (CCX/CX/measure recursion) is
  identical.  `babbushLookupAddAt` instantiates `pos := addendIdx q_start`
  (`= fun j => q_start + 2·j + 2`), writing the table word DIRECTLY onto the Cuccaro
  addend register, then adds, then measure-clears the addend.

  ## What is proven here

  * **Selection at any depth** (`unaryQROMAt_selects_word`, `_frame`, `_anc_cleared`):
    the `pos`-parameterized QROM XORs exactly the addressed table row into the word
    positions `pos j`, clears its AND-ancillas, and touches nothing else — the same
    depth induction as `MeasUncomputeValue.unaryQROM_selects_word`, with `pos j` in
    place of `outBase + j` and an explicit `pos`-injectivity hypothesis where the
    original used stride-1 facts.
  * **Value-correctness at ARBITRARY `W ≤ bits`**
    (`babbushLookupAddAtValueSpecOn_holds`): on every clean input with the table
    value in range (`T addr < 2^W`) and no accumulator overflow, the measured
    lookup-add realises `acc ↦ acc + T addr` — the statement the original could only
    support at `W = 1`.
  * **Counts preserved** (`tcount_unaryQROMAt`, `toffoli_babbushLookupAddAt`,
    `toffoli_babbushLookupAddAt_eq_original`): the position map costs nothing — the
    babbush `2^w − 1` Toffoli read and the `(2^w − 1) + 2·bits` lookup-add total are
    unchanged, and the ×2 measurement saving vs the Gate-level double-read
    `lookupAddAt` holds for the layout-CORRECT circuit
    (`measUncomputeAt_saves_a_read`, `measUncomputeAt_read_cost_identity`).

  ## Audit guidance

  Import THIS module for the measured lookup-add with correct semantics at any word
  width.  The COUNT theorems of `MeasUncompute` (`toffoli_babbushLookupAdd`, …)
  remain valid — the defect is purely in the value layout, and the counts here agree
  with them exactly.
-/
import FormalRV.Shor.MeasUncomputeValue

namespace FormalRV.Shor.MeasUncomputeAt

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit FormalRV.Shor.WindowedLookupAdd
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedEndToEnd
open FormalRV.Shor.MeasUncomputeValue

/-! ## §1. The position-parameterized unary-iteration QROM and measured lookup-add. -/

/-- **Position-parameterized unary-iteration QROM read** (the layout-correct variant of
    `MeasUncompute.unaryQROM`): on the `d`-bit address sub-register (bit `i` at
    `addrBase + i`) with sub-tree control `ctrl` and covered base index `base`, XOR
    `T[address]` into the `W`-bit word at the positions `pos 0, …, pos (W−1)`
    (instead of the hard-coded `outBase + j`), using ancillas `ancBase + (0..d−1)`
    cleared by measurement.  ONLY the leaf word-CNOT targets differ from the
    original — the merged-AND tree is identical, so all counts are preserved. -/
def unaryQROMAt (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) (addrBase ancBase : Nat) :
    Nat → Nat → Nat → EGate
  | 0,     ctrl, base =>
      EGate.base (cx_gates_from_indices ctrl (wordCnotsAt pos W (T base)))
  | d + 1, ctrl, base =>
      EGate.seq (EGate.seq (EGate.seq (EGate.seq (EGate.seq
        (EGate.base (Gate.CCX ctrl (addrBase + d) (ancBase + d)))                    -- anc ← ctrl∧bit_d
        (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d)))       -- bit_d = 1 half
        (EGate.base (Gate.CX ctrl (ancBase + d))))                                   -- anc ← ctrl∧¬bit_d
        (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) base))                 -- bit_d = 0 half
        (EGate.base (Gate.CX ctrl (ancBase + d))))                                   -- restore anc
        (EGate.mz (ancBase + d))                                                     -- measure-uncompute anc

/-- **The layout-CORRECT measured lookup-add**: babbush unary read with the word
    written DIRECTLY onto the Cuccaro addend (`pos := addendIdx q_start`, i.e.
    `q_start + 2·j + 2`), Cuccaro add, then measure-clear the addend.  This is
    `MeasUncompute.babbushLookupAdd` with the stride-1/stride-2 mismatch repaired —
    same counts, correct value semantics at every `W` (see
    `babbushLookupAddAtValueSpecOn_holds`). -/
def babbushLookupAddAt (w W : Nat) (T : Nat → Nat) (bits addrBase ancBase q_start : Nat) :
    EGate :=
  EGate.seq (EGate.seq
    (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0)
    (EGate.base (cuccaro_n_bit_adder_full bits q_start)))
    (mzList ((List.range W).map (addendIdx q_start)))

/-! ## §2. Counts: the position map costs nothing — all counts of the original hold. -/

/-- **`unaryQROMAt` has exactly `2^d − 1` Toffolis** (`7·(2^d − 1)` T) for ANY position
    map — the babbush `L − 1` count, identical to `tcount_unaryQROM`. -/
theorem tcount_unaryQROMAt (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase : Nat) :
    ∀ (d ctrl base : Nat),
      EGate.tcount (unaryQROMAt pos W T addrBase ancBase d ctrl base) = 7 * (2 ^ d - 1)
  | 0, ctrl, base => by
      simp [unaryQROMAt, EGate.tcount, tcount_cx_gates_zero]
  | d + 1, ctrl, base => by
      simp only [unaryQROMAt, EGate.tcount, Gate.tcount,
                 tcount_unaryQROMAt pos W T addrBase ancBase d]
      have h2d : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega

theorem toffoli_unaryQROMAt (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase d ctrl base : Nat) :
    EGate.toffoli (unaryQROMAt pos W T addrBase ancBase d ctrl base) = 2 ^ d - 1 := by
  unfold EGate.toffoli
  rw [tcount_unaryQROMAt, Nat.mul_div_cancel_left _ (by norm_num)]

/-- **The layout-correct measured lookup-add keeps the paper's `2^w − 1 + 2·bits`
    Toffolis** — exactly the count of the (layout-broken) original. -/
theorem toffoli_babbushLookupAddAt (w W : Nat) (T : Nat → Nat)
    (bits addrBase ancBase q_start : Nat) :
    EGate.toffoli (babbushLookupAddAt w W T bits addrBase ancBase q_start)
      = (2 ^ w - 1) + 2 * bits := by
  unfold EGate.toffoli babbushLookupAddAt
  simp only [EGate.tcount, tcount_mzList, tcount_unaryQROMAt, tcount_cuccaro_n_bit_adder_full]
  have h2w : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  rw [show 7 * (2 ^ w - 1) + 14 * bits + 0 = ((2 ^ w - 1) + 2 * bits) * 7 by
        have : 2 ^ w - 1 + 1 = 2 ^ w := by omega
        nlinarith [this]]
  rw [Nat.mul_div_cancel _ (by norm_num)]

/-- **Counts preserved**: the layout fix is COUNT-FREE — `babbushLookupAddAt` has
    exactly the Toffoli count of the original `babbushLookupAdd` (for every
    `outBase` the original might have used). -/
theorem toffoli_babbushLookupAddAt_eq_original (w W : Nat) (T : Nat → Nat)
    (bits addrBase ancBase outBase q_start : Nat) :
    EGate.toffoli (babbushLookupAddAt w W T bits addrBase ancBase q_start)
      = EGate.toffoli (babbushLookupAdd w W T bits addrBase ancBase outBase q_start) := by
  rw [toffoli_babbushLookupAddAt, toffoli_babbushLookupAdd]

/-- **The ×2-saving accounting holds for the layout-CORRECT circuit**: the measured
    `babbushLookupAddAt` saves AT LEAST the full second table read `2·w·2^w` against
    the Gate-level double-read `lookupAddAt` (`4·w·2^w + 2·bits` Toffolis) — and more,
    since the babbush merged-AND read (`2^w − 1`) is itself cheaper than the flat read
    (`2·w·2^w`); the exact ledger is `measUncomputeAt_read_cost_identity`. -/
theorem measUncomputeAt_saves_a_read (w W : Nat) (T : Nat → Nat)
    (bits addrBase ancBase q_start : Nat) :
    EGate.toffoli (babbushLookupAddAt w W T bits addrBase ancBase q_start) + 2 * w * 2 ^ w
      ≤ toffoliCount (lookupAddAt w W T bits q_start) := by
  rw [toffoli_babbushLookupAddAt, toffoliCount, tcount_lookupAddAt,
      show 2 * (14 * w * 2 ^ w) + 14 * bits = (4 * w * 2 ^ w + 2 * bits) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  have h2w : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  have h42 : 4 * w * 2 ^ w = 2 * (2 * w * 2 ^ w) := by ring
  have hle : 2 ^ w ≤ 2 * w * 2 ^ w + 1 := by
    cases w with
    | zero => simp
    | succ k =>
        have hpos : 1 ≤ 2 * (k + 1) := by omega
        have := Nat.mul_le_mul_right (2 ^ (k + 1)) hpos
        omega
  omega

/-- **The exact read-cost ledger** (subtraction-free form): against the double-read
    `lookupAddAt`, the layout-correct measured circuit is cheaper by exactly
    `4·w·2^w − (2^w − 1)` Toffolis — one whole flat read (`2·w·2^w`, the measurement
    saving) plus the flat-vs-babbush read gap (`2·w·2^w − 2^w + 1`). -/
theorem measUncomputeAt_read_cost_identity (w W : Nat) (T : Nat → Nat)
    (bits addrBase ancBase q_start : Nat) :
    EGate.toffoli (babbushLookupAddAt w W T bits addrBase ancBase q_start)
        + 4 * w * 2 ^ w + 1
      = toffoliCount (lookupAddAt w W T bits q_start) + 2 ^ w := by
  rw [toffoli_babbushLookupAddAt, toffoliCount, tcount_lookupAddAt,
      show 2 * (14 * w * 2 ^ w) + 14 * bits = (4 * w * 2 ^ w + 2 * bits) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  have h2w : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  omega

/-! ## §3. `unaryQROMAt` frame: positions off the word and the ancilla register are
untouched (no hypotheses needed — ported from `unaryQROM_frame`). -/

/-- **`unaryQROMAt` frame.**  Any position that is neither a word position (`pos j`,
`j < W`) nor an AND-ancilla of the tree (`ancBase + i`, `i < d`) is untouched — in
particular the ctrl and the whole address register are preserved. -/
theorem unaryQROMAt_frame (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase : Nat) :
    ∀ (d ctrl base : Nat) (f : Nat → Bool) (p : Nat),
      (∀ j, j < W → p ≠ pos j) →
      (∀ i, i < d → p ≠ ancBase + i) →
      EGate.applyNat (unaryQROMAt pos W T addrBase ancBase d ctrl base) f p = f p
  | 0, ctrl, base, f, p, hp_out, _ => by
    show Gate.applyNat (cx_gates_from_indices ctrl (wordCnotsAt pos W (T base))) f p = f p
    rw [applyNat_cx_gates_from_indices]
    apply Lookup.cnot_layer_post_state_frame
    intro hmem
    obtain ⟨j, hj, _, hpj⟩ := (mem_wordCnotsAt pos W (T base) p).mp hmem
    exact hp_out j hj hpj
  | d + 1, ctrl, base, f, p, hp_out, hp_anc => by
    have hp_d : p ≠ ancBase + d := hp_anc d (Nat.lt_succ_self d)
    have hp_anc' : ∀ i, i < d → p ≠ ancBase + i :=
      fun i hi => hp_anc i (Nat.lt_succ_of_lt hi)
    show Function.update
        (Gate.applyNat (Gate.CX ctrl (ancBase + d))
          (EGate.applyNat (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) base)
            (Gate.applyNat (Gate.CX ctrl (ancBase + d))
              (EGate.applyNat (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d))
                (Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d)) f)))))
        (ancBase + d) false p = f p
    rw [Function.update_of_ne hp_d, Gate.applyNat_CX, update_neq _ _ _ _ hp_d,
        unaryQROMAt_frame pos W T addrBase ancBase d (ancBase + d) base _ p hp_out hp_anc',
        Gate.applyNat_CX, update_neq _ _ _ _ hp_d,
        unaryQROMAt_frame pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d) _ p hp_out hp_anc',
        Gate.applyNat_CCX, update_neq _ _ _ _ hp_d]

/-! ## §4. `unaryQROMAt` returns its AND-ancillas cleared (ported from
`unaryQROM_anc_cleared` — the position map plays no role here). -/

/-- **`unaryQROMAt` clears its AND-ancillas.**  Each level's ancilla is measure-reset
(`EGate.mz`) after its last use, so every `ancBase + i` (`i < d`) reads `false`
afterwards — for ANY input state. -/
theorem unaryQROMAt_anc_cleared (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase : Nat) :
    ∀ (d ctrl base : Nat) (f : Nat → Bool) (i : Nat), i < d →
      EGate.applyNat (unaryQROMAt pos W T addrBase ancBase d ctrl base) f (ancBase + i)
        = false
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | d + 1, ctrl, base, f, i, hi => by
    show Function.update
        (Gate.applyNat (Gate.CX ctrl (ancBase + d))
          (EGate.applyNat (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) base)
            (Gate.applyNat (Gate.CX ctrl (ancBase + d))
              (EGate.applyNat (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d))
                (Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d)) f)))))
        (ancBase + d) false (ancBase + i) = false
    by_cases hid : i = d
    · subst hid
      exact Function.update_self _ _ _
    · have hne : ancBase + i ≠ ancBase + d := by omega
      rw [Function.update_of_ne hne, Gate.applyNat_CX, update_neq _ _ _ _ hne,
          unaryQROMAt_anc_cleared pos W T addrBase ancBase d (ancBase + d) base _ i
            (by omega)]

/-! ## §5. THE SELECTION LEMMA: `unaryQROMAt` XORs exactly the addressed table row
into the word at `pos` — at ANY depth, for ANY injective position map. -/

/-- **THE `unaryQROMAt` SELECTION LEMMA.**  On a state whose AND-ancillas
`ancBase + i` (`i < d`) are clean, with the tree's registers pairwise disjoint from
the word positions `pos j`, the sub-tree control `ctrl` off the word/ancilla
registers, and `pos` injective below `W` (the hypothesis that replaces the
original's stride-1 facts), the position-parameterized babbush QROM
`unaryQROMAt pos … d ctrl base` XORs exactly the addressed table row into the word:

  `pos j ↦ f (pos j) ⊕ (f ctrl ∧ (T (base + addr)).testBit j)`,

where `addr = decodeReg (fun i => addrBase + i) d f`.  Same depth induction as
`MeasUncomputeValue.unaryQROM_selects_word`, with `pos j` for `outBase + j`. -/
theorem unaryQROMAt_selects_word (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase : Nat)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k) :
    ∀ (d ctrl base : Nat) (f : Nat → Bool),
      (∀ i j, i < d → j < W → ancBase + i ≠ pos j) →
      (∀ i i', i < d → i' < d → ancBase + i ≠ addrBase + i') →
      (∀ i j, i < d → j < W → addrBase + i ≠ pos j) →
      (∀ j, j < W → ctrl ≠ pos j) →
      (∀ i, i < d → ctrl ≠ ancBase + i) →
      (∀ i, i < d → f (ancBase + i) = false) →
      ∀ j, j < W →
        EGate.applyNat (unaryQROMAt pos W T addrBase ancBase d ctrl base) f (pos j)
          = xor (f (pos j))
              (f ctrl && (T (base + decodeReg (fun i => addrBase + i) d f)).testBit j)
  | 0, ctrl, base, f, _, _, _, h_ctrl_out, _, _ => by
    intro j hj
    show Gate.applyNat (cx_gates_from_indices ctrl
        (wordCnotsAt pos W (T base))) f (pos j) = _
    have hctrl_not_mem : ctrl ∉ wordCnotsAt pos W (T base) := by
      intro hmem
      obtain ⟨j', hj', _, hcj⟩ := (mem_wordCnotsAt pos W (T base) ctrl).mp hmem
      exact h_ctrl_out j' hj' hcj
    have hdec0 : decodeReg (fun i => addrBase + i) 0 f = 0 := by simp [decodeReg]
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
    -- restricted hypotheses for the two depth-`d` sub-calls (control `ancBase + d`)
    have H1 : ∀ i j, i < d → j < W → ancBase + i ≠ pos j :=
      fun i j hi hj => h_anc_out i j (Nat.lt_succ_of_lt hi) hj
    have H2 : ∀ i i', i < d → i' < d → ancBase + i ≠ addrBase + i' :=
      fun i i' hi hi' => h_anc_addr i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi')
    have H3 : ∀ i j, i < d → j < W → addrBase + i ≠ pos j :=
      fun i j hi hj => h_addr_out i j (Nat.lt_succ_of_lt hi) hj
    have H4 : ∀ j, j < W → ancBase + d ≠ pos j := fun j hj => h_anc_out d j hlt hj
    have H5 : ∀ i, i < d → ancBase + d ≠ ancBase + i := fun i hi => by omega
    -- the five intermediate states
    set s1 := Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d)) f with hs1
    set s2 := EGate.applyNat
      (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d)) s1 with hs2
    set s3 := Gate.applyNat (Gate.CX ctrl (ancBase + d)) s2 with hs3
    set s4 := EGate.applyNat
      (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) base) s3 with hs4
    set s5 := Gate.applyNat (Gate.CX ctrl (ancBase + d)) s4 with hs5
    have hg : EGate.applyNat (unaryQROMAt pos W T addrBase ancBase (d + 1) ctrl base) f
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
    have v2 : ∀ j, j < W → s2 (pos j)
        = xor (f (pos j))
            ((f ctrl && f (addrBase + d))
              && (T (base + 2 ^ d + decodeReg (fun i => addrBase + i) d f)).testBit j) := by
      intro j hj
      rw [hs2, unaryQROMAt_selects_word pos W T addrBase ancBase hpos_inj d (ancBase + d)
            (base + 2 ^ d) s1 H1 H2 H3 H4 H5 hs1_clean j hj,
          hs1_ne _ (Ne.symm (H4 j hj)), hs1_at, hs1_addr]
    -- s2 preserves ctrl, the level-`d` ancilla, and the address register
    have hs2_ctrl : s2 ctrl = f ctrl := by
      rw [hs2, unaryQROMAt_frame pos W T addrBase ancBase d (ancBase + d)
            (base + 2 ^ d) s1 ctrl h_ctrl_out
            (fun i hi => h_ctrl_anc i (Nat.lt_succ_of_lt hi)),
          hs1_ne ctrl (h_ctrl_anc d hlt)]
    have hs2_anc : s2 (ancBase + d) = (f ctrl && f (addrBase + d)) := by
      rw [hs2, unaryQROMAt_frame pos W T addrBase ancBase d (ancBase + d)
            (base + 2 ^ d) s1 (ancBase + d) H4 H5, hs1_at]
    have hs2_addrpt : ∀ i, i < d → s2 (addrBase + i) = f (addrBase + i) := by
      intro i hi
      rw [hs2, unaryQROMAt_frame pos W T addrBase ancBase d (ancBase + d)
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
      exact unaryQROMAt_anc_cleared pos W T addrBase ancBase d (ancBase + d)
        (base + 2 ^ d) s1 i hi
    have hs3_addr : decodeReg (fun i => addrBase + i) d s3
        = decodeReg (fun i => addrBase + i) d f :=
      decodeReg_ext _ _ _ _ (fun i hi => by
        rw [hs3_ne _ (Ne.symm (h_anc_addr d i hlt (Nat.lt_succ_of_lt hi))),
            hs2_addrpt i hi])
    have hs3_out : ∀ j, j < W → s3 (pos j) = s2 (pos j) :=
      fun j hj => hs3_ne _ (Ne.symm (H4 j hj))
    -- second half: reads `T (base + addr)` controlled on `ctrl ∧ ¬addr_d`
    have v4 : ∀ j, j < W → s4 (pos j)
        = xor (s3 (pos j))
            ((f ctrl && !(f (addrBase + d)))
              && (T (base + decodeReg (fun i => addrBase + i) d f)).testBit j) := by
      intro j hj
      rw [hs4, unaryQROMAt_selects_word pos W T addrBase ancBase hpos_inj d (ancBase + d)
            base s3 H1 H2 H3 H4 H5 hs3_clean j hj, hs3_at, hs3_addr]
    -- assemble: exactly one of the two halves fires
    intro j hj
    have hne_out : pos j ≠ ancBase + d := Ne.symm (h_anc_out d j hlt hj)
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

/-! ## §6. The guarded value-spec at ARBITRARY word width — what the original could
only support at `W = 1`. -/

/-- **The guarded value-spec for the layout-correct measured lookup-add** — the
`At`-analogue of `MeasUncomputeValue.BabbushLookupAddValueSpecOn` (no `outBase`:
the word lives ON the addend).  Restricted to a family `P` of well-formed inputs;
the unguarded `∀ f` form is uninstantiable for the same reasons as the original
(all-`false` fixed point, mod-free RHS). -/
structure BabbushLookupAddAtValueSpecOn (P : (Nat → Bool) → Prop)
    (w W : Nat) (T : Nat → Nat) (bits addrBase ancBase q_start : Nat)
    (decAcc decAddr : (Nat → Bool) → Nat) where
  step : ∀ (f : Nat → Bool), P f →
    decAcc (EGate.applyNat (babbushLookupAddAt w W T bits addrBase ancBase q_start) f)
      = decAcc f + T (decAddr f)

/-- **The clean-input family** for the layout-correct measured lookup-add at
arbitrary word width `W`:

* ctrl qubit `0` is set (the QROM's always-on root control);
* the QROM AND-ancillas are clean;
* the Cuccaro carry-in is clean;
* the addend register (whose low `W` bits ARE the QROM word) is clean;
* the looked-up table word fits the word width (`T addr < 2^W` — the honest
  table-width hypothesis: the read transports exactly `W` bits);
* the mod-free sum does not overflow the `bits`-wide accumulator (the spec's RHS
  `decAcc f + T (decAddr f)` carries no `% 2^bits`). -/
def CleanLookupAddAtInput (w W bits addrBase ancBase q_start : Nat) (T : Nat → Nat)
    (f : Nat → Bool) : Prop :=
  f 0 = true
  ∧ (∀ i, i < w → f (ancBase + i) = false)
  ∧ f q_start = false
  ∧ (∀ i, i < bits → f (q_start + 2 * i + 2) = false)
  ∧ T (decodeReg (fun i => addrBase + i) w f) < 2 ^ W
  ∧ decodeReg (fun i => q_start + 2 * i + 1) bits f
      + T (decodeReg (fun i => addrBase + i) w f) < 2 ^ bits

/-- **★ HEADLINE — the guarded value-spec HOLDS at EVERY word width `W ≤ bits`.**
With the QROM address/ancilla registers off the adder block, the layout-correct
measured lookup-add `babbushLookupAddAt` realises one lookup-add step on every
clean input, with the honest decoders

* `decAcc  = decodeReg (fun i => q_start + 2*i + 1) bits`  (Cuccaro augend),
* `decAddr = decodeReg (fun i => addrBase + i) w`          (QROM address):

`decAcc (applyNat (babbushLookupAddAt …) f) = decAcc f + T (decAddr f)`.

This is exactly the statement `MeasUncomputeValue.babbushLookupAddValueSpecOn_holds`
could only support at `W = 1` (the original's `W ≥ 2` layout defect is
`babbushLookupAdd_misses_table`).  The proof is one window-step: the
`unaryQROMAt` selection lemma writes the `W` bits of `T[addr]` directly onto the
clean addend (so the addend decodes to `T addr` under the table-width guard
`T addr < 2^W`), the Cuccaro decode-level `sumCorrect` accumulates it (mod-free
under the boundedness guard `acc + T addr < 2^bits`), and the `mzList`
measure-clear of the addend leaves the (odd-offset) accumulator untouched. -/
def babbushLookupAddAtValueSpecOn_holds
    (w W bits : Nat) (T : Nat → Nat) (addrBase ancBase q_start : Nat)
    (hW : W ≤ bits) (h_anc_pos : 0 < ancBase)
    (h_anc_addr : ∀ i i', i < w → i' < w → ancBase + i ≠ addrBase + i')
    (h_anc_blk : ∀ i, i < w →
      ¬ (q_start ≤ ancBase + i ∧ ancBase + i ≤ q_start + 2 * bits))
    (h_addr_blk : ∀ i, i < w →
      ¬ (q_start ≤ addrBase + i ∧ addrBase + i ≤ q_start + 2 * bits)) :
    BabbushLookupAddAtValueSpecOn
      (CleanLookupAddAtInput w W bits addrBase ancBase q_start T)
      w W T bits addrBase ancBase q_start
      (decodeReg (fun i => q_start + 2 * i + 1) bits)
      (decodeReg (fun i => addrBase + i) w) := by
  constructor
  intro f hf
  obtain ⟨hctrl, hanc, hcarry, haddend, hTlt, hover⟩ := hf
  -- the addend positions are an injective word map (stride 2)
  have hpos_inj : ∀ j k, j < W → k < W →
      addendIdx q_start j = addendIdx q_start k → j = k := by
    intro j k _ _ h; simp only [addendIdx] at h; omega
  -- selection-lemma side conditions for the word at the addend register
  have S1 : ∀ i j, i < w → j < W → ancBase + i ≠ addendIdx q_start j := by
    intro i j hi hj
    have := h_anc_blk i hi
    simp only [addendIdx]
    omega
  have S3 : ∀ i j, i < w → j < W → addrBase + i ≠ addendIdx q_start j := by
    intro i j hi hj
    have := h_addr_blk i hi
    simp only [addendIdx]
    omega
  have S4 : ∀ j, j < W → (0 : Nat) ≠ addendIdx q_start j := by
    intro j hj; simp only [addendIdx]; omega
  have S5 : ∀ i, i < w → (0 : Nat) ≠ ancBase + i := by intro i hi; omega
  have hfr := unaryQROMAt_frame (addendIdx q_start) W T addrBase ancBase w 0 0 f
  -- the read writes bit `j` of `T addr` onto addend bit `j`, for EVERY `j < W` …
  have hread : ∀ j, j < W →
      EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f
        (addendIdx q_start j)
      = (T (decodeReg (fun i => addrBase + i) w f)).testBit j := by
    intro j hj
    have hA0 : f (addendIdx q_start j) = false := by
      simpa [addendIdx] using haddend j (by omega)
    have h := unaryQROMAt_selects_word (addendIdx q_start) W T addrBase ancBase
      hpos_inj w 0 0 f S1 h_anc_addr S3 S4 S5 hanc j hj
    simpa [hctrl, hA0] using h
  -- … leaves the carry-in clean …
  have hclean1 : EGate.applyNat
      (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f q_start = false := by
    rw [hfr q_start (fun j hj => by simp only [addendIdx]; omega)
          (fun i hi => by have := h_anc_blk i hi; omega)]
    exact hcarry
  -- … leaves the augend register at `acc` …
  have haug1 : decodeReg (fun i => q_start + 2 * i + 1) bits
      (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f)
      = decodeReg (fun i => q_start + 2 * i + 1) bits f :=
    decodeReg_ext _ _ _ _ (fun i hi =>
      hfr (q_start + 2 * i + 1) (fun j hj => by simp only [addendIdx]; omega)
        (fun i' hi' => by have := h_anc_blk i' hi'; omega))
  -- … and leaves the addend register decoding to exactly `T addr` (table-width
  -- guard: bits `W ≤ i < bits` stay clean AND `T addr` has no bits there).
  have hTbits : T (decodeReg (fun i => addrBase + i) w f) < 2 ^ bits :=
    lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by omega) hW)
  have hadd1 : decodeReg (fun i => q_start + 2 * i + 2) bits
      (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f)
      = T (decodeReg (fun i => addrBase + i) w f) := by
    rw [decodeReg_eq_mod_of_testBit (fun i => q_start + 2 * i + 2) bits
          (T (decodeReg (fun i => addrBase + i) w f)) _ ?_,
        Nat.mod_eq_of_lt hTbits]
    intro i hi
    by_cases hiW : i < W
    · exact hread i hiW
    · have h2i : (2 : Nat) ^ W ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [hfr (q_start + 2 * i + 2) (fun j hj => by simp only [addendIdx]; omega)
            (fun i' hi' => by have := h_anc_blk i' hi'; omega),
          haddend i hi]
      exact (Nat.testBit_lt_two_pow (by omega)).symm
  -- the Cuccaro add accumulates the addend into the augend
  have hsum : decodeReg (fun i => q_start + 2 * i + 1) bits
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f))
      = (decodeReg (fun i => q_start + 2 * i + 1) bits
            (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f)
          + decodeReg (fun i => q_start + 2 * i + 2) bits
              (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f))
        % 2 ^ bits :=
    cuccaroAdder.sumCorrect bits q_start _ hclean1
  -- the measure-clear of the (even-offset) addend never touches the (odd-offset) augend
  have hmzdec : ∀ g : Nat → Bool,
      decodeReg (fun i => q_start + 2 * i + 1) bits
        (EGate.applyNat (mzList ((List.range W).map (addendIdx q_start))) g)
      = decodeReg (fun i => q_start + 2 * i + 1) bits g := by
    intro g
    refine decodeReg_ext _ _ _ _ (fun i hi => ?_)
    refine applyNat_mzList_preserves _ _ ?_
    simp only [List.mem_map, List.mem_range, addendIdx]
    rintro ⟨j, hj, hjeq⟩
    omega
  -- assemble
  have hsplit : EGate.applyNat
      (babbushLookupAddAt w W T bits addrBase ancBase q_start) f
      = EGate.applyNat (mzList ((List.range W).map (addendIdx q_start)))
          (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f)) :=
    rfl
  rw [hsplit, hmzdec, hsum, haug1, hadd1, Nat.mod_eq_of_lt hover]

/-! ## §7. Non-vacuity: the guard family is inhabited and the layout hypotheses are
satisfiable at EVERY word width — including the `W ≥ 2` regime the original
provably cannot serve. -/

/-- **Non-vacuity of the guard**: the clean-input family is inhabited (for any
table with `T 0 < 2^W`) — e.g. by the state with only the ctrl qubit set. -/
theorem cleanLookupAddAtInput_nonempty
    (w W bits addrBase ancBase q_start : Nat) (T : Nat → Nat)
    (hW : W ≤ bits) (haddr_pos : 0 < addrBase) (hanc_pos : 0 < ancBase)
    (hq_pos : 0 < q_start) (hT0 : T 0 < 2 ^ W) :
    CleanLookupAddAtInput w W bits addrBase ancBase q_start T
      (fun p => decide (p = 0)) := by
  have h2 : (2 : Nat) ^ W ≤ 2 ^ bits := Nat.pow_le_pow_right (by omega) hW
  have haddr0 : decodeReg (fun i => addrBase + i) w (fun p => decide (p = 0)) = 0 :=
    decodeReg_eq_zero _ _ _ (fun i _ => by simp; omega)
  have haug0 : decodeReg (fun i => q_start + 2 * i + 1) bits
      (fun p => decide (p = 0)) = 0 :=
    decodeReg_eq_zero _ _ _ (fun i _ => by simp)
  refine ⟨by simp, fun i _ => by simp; omega, by simp; omega, fun i _ => by simp,
          ?_, ?_⟩
  · rw [haddr0]; exact hT0
  · rw [haddr0, haug0]; omega

/-- **Non-vacuity of the layout hypotheses, at ARBITRARY `W ≤ bits`**: the standard
register layout (address register, then AND-ancillas, stacked above the adder
block) satisfies every side condition of `babbushLookupAddAtValueSpecOn_holds` —
in particular at `W = bits ≥ 2`, the regime where the original `babbushLookupAdd`
provably misses the table. -/
example (w W bits q_start : Nat) (T : Nat → Nat) (hW : W ≤ bits) :
    BabbushLookupAddAtValueSpecOn
      (CleanLookupAddAtInput w W bits (q_start + 2 * bits + 1)
        (q_start + 2 * bits + 1 + w) q_start T)
      w W T bits (q_start + 2 * bits + 1) (q_start + 2 * bits + 1 + w) q_start
      (decodeReg (fun i => q_start + 2 * i + 1) bits)
      (decodeReg (fun i => q_start + 2 * bits + 1 + i) w) :=
  babbushLookupAddAtValueSpecOn_holds w W bits T (q_start + 2 * bits + 1)
    (q_start + 2 * bits + 1 + w) q_start hW (by omega)
    (fun i i' _ _ => by omega) (fun i _ => by omega) (fun i _ => by omega)

end FormalRV.Shor.MeasUncomputeAt
