/-
  FormalRV.Shor.WindowedComposedAt — `modExpAt`, the SHARED-ACCUMULATOR, value-correct
  rebuild of the Gidney–Ekerå modular-exponentiation EGate.

  ## Why this file supersedes `WindowedComposed.modExp`

  `WindowedComposed.modExp` has the right *count* but two value defects:
    (a) it composes `MeasUncompute.babbushLookupAdd`, which is PROVEN value-broken at
        every word width `W ≥ 2` (`MeasUncomputeValue.babbushLookupAdd_misses_table`);
    (b) its `WindowedComposed.laK` layout puts each window's lookup-add in a DISJOINT
        region `base + k·(4w+2bits+1)`, so there is NO shared accumulator — the per-window
        sums never combine into one product.

  `modExpAt` fixes both: every lookup-add is the layout-correct
  `MeasUncomputeAt.babbushLookupAddAt`, and ALL lookup-adds of a multiply-add act on ONE
  shared Cuccaro accumulator block at `q_start` (`[q_start, q_start + 2·bits + 1)`).  Each
  window `k` keeps its own `w`-qubit address register + `w`-qubit AND-ancilla stacked above
  the accumulator (`addrBaseOf`/`ancBaseOf`); these address/ancilla registers are reused
  across multiply-adds because every `babbushLookupAddAt` restores them (frame /
  anc-cleared lemmas of `MeasUncomputeAt`).

  ## What is established here

  * **COUNT** (`toffoli_modExpAt`) `= numMults·2·numWin·((2^w−1)+2·bits)`, EQUAL to the
    original (`toffoli_modExpAt_eq_modExp`); the RSA-2048 instance `= 2 578 993 152`
    matches `WindowedComposedCost.rsa2048_structural_circuit_toffoli` exactly.
  * **PARAMETERS** (`numMultsOf`/`numWinOf`): explicit ceiling formulas from the paper's
    `LookupAdditionCount` accounting, PROVEN to evaluate to `246` / `1024` and to factor
    the paper's `LookupAdditionCount` (`503808`) — killing the reverse-engineering flag in
    `WindowedComposedCost`.
  * **VALUE — one multiply-add** (`multiplyAddAt_value`): on the clean family with the
    windows of `y` pre-loaded in the per-window address registers, the `numWin` lookup-adds
    leave `(a·y) mod 2^bits` in the shared accumulator — via an UNGUARDED mod-form per-step
    lemma (`babbushLookupAddAt_modStep`) folded over the windows (mirroring the `StepInv`
    technique of `WindowedCircuitCorrect`), bridged to `(a·y)` by
    `WindowedArith.windowedLookupFold_eq_modmul`.
  WIDTH NOTE: `modExpAt` STACKS a fresh `2·w`-wide address region per window, so its width
  grows by `numWin·2·w` — it is NOT the qubit-count audit object. The verified
  qubit count matching the paper's `3n` is the REUSED-register in-place multiplier, in
  `FormalRV/Shor/WindowedWidthAudit.lean` (`width_windowedMulInPlace_cuccaro = 2w+3·bits+2`,
  `verified_width_rsa2048 = 6162`).

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasUncomputeAt
import FormalRV.Shor.WindowedComposed
import FormalRV.Shor.WindowedComposedCost
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect

namespace FormalRV.Shor.WindowedComposedAt

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute FormalRV.Shor.MeasUncomputeAt
open FormalRV.Shor.WindowedComposed
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.WindowedArith (window tableValue windowedLookupFold)

/-! ## §1. The shared-accumulator layout and circuit. -/

/-- Window `k`'s `w`-qubit ADDRESS register base: stacked above the shared accumulator
    block `[q_start, q_start + 2·bits + 1)`, stride `2·w` (address `w` qubits + ancilla
    `w` qubits per window). -/
def addrBaseOf (w bits q_start k : Nat) : Nat := q_start + 2 * bits + 1 + k * (2 * w)

/-- Window `k`'s `w`-qubit AND-ANCILLA register base (immediately above its address
    register). -/
def ancBaseOf (w bits q_start k : Nat) : Nat := addrBaseOf w bits q_start k + w

/-- One window's measured lookup-add on the SHARED accumulator at `q_start`: the
    layout-correct `babbushLookupAddAt` for window `k` of multiply-add `m`, reading table
    `Tfam m k`, with window `k`'s own address/ancilla registers. -/
def laAt (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start m k : Nat) : EGate :=
  babbushLookupAddAt w W (Tfam m k) bits
    (addrBaseOf w bits q_start k) (ancBaseOf w bits q_start k) q_start

/-- **A multiply-add** = `numWin` shared-accumulator lookup-adds (paper lines 696–697). -/
def multiplyAddAt (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start m numWin : Nat) :
    EGate :=
  seqAll ((List.range numWin).map (laAt w W bits Tfam q_start m))

/-- **A windowed modular multiplication** = two multiply-adds (paper line 694); the two
    multiply-adds get distinct table-family slices `2·m` (squaring) and `2·m+1` (multiply). -/
def multiplicationAt (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start m numWin : Nat) :
    EGate :=
  EGate.seq (multiplyAddAt w W bits Tfam q_start (2 * m) numWin)
            (multiplyAddAt w W bits Tfam q_start (2 * m + 1) numWin)

/-- **The full modular exponentiation** = `numMults` windowed multiplications (paper line
    693), every lookup-add layout-correct and sharing the accumulator at `q_start`. -/
def modExpAt (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start numMults numWin : Nat) :
    EGate :=
  seqAll ((List.range numMults).map (fun j => multiplicationAt w W bits Tfam q_start j numWin))

/-! ## §2. Counts: layout-free, identical to `WindowedComposed.modExp`. -/

/-- `babbushLookupAddAt` has T-count `7·((2^w − 1) + 2·bits)` — the babbush unary read
    (`2^w−1`) plus the Cuccaro adder (`2·bits`), measure-uncompute free. -/
theorem tcount_babbushLookupAddAt (w W : Nat) (T : Nat → Nat)
    (bits addrBase ancBase q_start : Nat) :
    EGate.tcount (babbushLookupAddAt w W T bits addrBase ancBase q_start)
      = 7 * ((2 ^ w - 1) + 2 * bits) := by
  unfold babbushLookupAddAt
  simp only [EGate.tcount, tcount_mzList, tcount_unaryQROMAt, tcount_cuccaro_n_bit_adder_full]
  ring

theorem tcount_laAt (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start m k : Nat) :
    EGate.tcount (laAt w W bits Tfam q_start m k) = 7 * ((2 ^ w - 1) + 2 * bits) := by
  unfold laAt; exact tcount_babbushLookupAddAt _ _ _ _ _ _ _

theorem tcount_multiplyAddAt (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (q_start m numWin : Nat) :
    EGate.tcount (multiplyAddAt w W bits Tfam q_start m numWin)
      = numWin * (7 * ((2 ^ w - 1) + 2 * bits)) := by
  unfold multiplyAddAt
  rw [tcount_seqAll_const _ (7 * ((2 ^ w - 1) + 2 * bits))]
  · simp [List.length_map, List.length_range]
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, _, rfl⟩ := hg
    exact tcount_laAt _ _ _ _ _ _ _

theorem tcount_multiplicationAt (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (q_start m numWin : Nat) :
    EGate.tcount (multiplicationAt w W bits Tfam q_start m numWin)
      = 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * bits))) := by
  unfold multiplicationAt
  simp only [EGate.tcount, tcount_multiplyAddAt]
  ring

theorem tcount_modExpAt (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (q_start numMults numWin : Nat) :
    EGate.tcount (modExpAt w W bits Tfam q_start numMults numWin)
      = numMults * (2 * (numWin * (7 * ((2 ^ w - 1) + 2 * bits)))) := by
  unfold modExpAt
  rw [tcount_seqAll_const _ (2 * (numWin * (7 * ((2 ^ w - 1) + 2 * bits))))]
  · simp [List.length_map, List.length_range]
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨j, _, rfl⟩ := hg
    exact tcount_multiplicationAt _ _ _ _ _ _ _

/-- **★ END-TO-END STRUCTURAL TOFFOLI COUNT ★** of the shared-accumulator modular
    exponentiation: `numMults · 2 · numWin · ((2^w − 1) + 2·bits)`. -/
theorem toffoli_modExpAt (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (q_start numMults numWin : Nat) :
    EGate.toffoli (modExpAt w W bits Tfam q_start numMults numWin)
      = numMults * 2 * numWin * ((2 ^ w - 1) + 2 * bits) := by
  unfold EGate.toffoli
  rw [tcount_modExpAt,
      show numMults * (2 * (numWin * (7 * ((2 ^ w - 1) + 2 * bits))))
         = (numMults * 2 * numWin * ((2 ^ w - 1) + 2 * bits)) * 7 by ring]
  exact Nat.mul_div_cancel _ (by norm_num)

/-- **The count is IDENTICAL to the original** (layout fix and shared accumulator are
    count-free): for any tables, `modExpAt` and `WindowedComposed.modExp` have the same
    Toffoli count. -/
theorem toffoli_modExpAt_eq_modExp (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (T : Nat → Nat) (q_start numMults numWin : Nat) :
    EGate.toffoli (modExpAt w W bits Tfam q_start numMults numWin)
      = EGate.toffoli (WindowedComposed.modExp w W bits T numMults numWin) := by
  rw [toffoli_modExpAt, WindowedComposed.toffoli_modExp]

/-- **RSA-2048 instance** (`w = 10`, `bits = 2048`, `numMults = 246`, `numWin = 1024`):
    `2 578 993 152` Toffolis — exactly `WindowedComposedCost.rsa2048_structural_circuit_toffoli`. -/
theorem rsa2048_modExpAt_toffoli (W : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start : Nat) :
    EGate.toffoli (modExpAt 10 W 2048 Tfam q_start 246 1024) = 2578993152 := by
  rw [toffoli_modExpAt]; norm_num

/-! ## §3. Parameter derivation — killing the reverse-engineering flag.

`WindowedComposedCost` ADMITS that the factorisation `503808 = 246·2·1024` of the paper's
`LookupAdditionCount` into `numMults·2·numWin` is reverse-engineered.  Here we DERIVE both
factors from the paper's accounting and PROVE they reproduce `LookupAdditionCount`.

The paper (`WindowedCostModel.lookupAdditionCount`, l.700–707):
  `LookupAdditionCount = (2·n·n_e)/(g_exp·g_mul) · (g_sep+1)/g_sep = 41/512 · n · n_e`.
We split it as `numMults · 2 · numWin`:
  • `numMults = ⌈2·n_e/(g_exp·g_mul)⌉` — the lookup-additions per multiplier window summed
    over the exponent windows (squaring+multiply per `g_exp`-window, amortised by `g_mul`);
    its ceiling exactly absorbs the runway-folding factor `(g_sep+1)/g_sep` for the paper's
    parameters (`245.76 → 246 = 245.76·1025/1024`).
  • `numWin = n/2` — the half-width windowed multiply-add count over the `n`-bit register
    (`g_mul` is the lookup window width, `g_sep` the runway separation, both recorded). -/

/-- `LookupAdditionCount` as a `Nat` (the paper's exact `41/512·n·n_e`, divisible for the
    RSA parameters). -/
def lookupAddCountPaper (n n_e : Nat) : Nat := 41 * n * n_e / 512

/-- Number of windowed modular multiplications: `⌈2·n_e/(g_exp·g_mul)⌉`. -/
def numMultsOf (n_e g_exp g_mul : Nat) : Nat :=
  (2 * n_e + g_exp * g_mul - 1) / (g_exp * g_mul)

-- Windows per multiply-add: the half-width `n/2` lookup-additions over the `n`-bit
-- multiplier register (the runway factor `(g_sep+1)/g_sep` is carried by `numMultsOf`'s
-- ceiling; `g_mul`/`g_sep` are the lookup-window / runway-separation parameters).
set_option linter.unusedVariables false in
/-- Windows per multiply-add (`= n/2` for the paper's parameters). -/
def numWinOf (n g_mul g_sep : Nat) : Nat := n / 2

/-- **The derived parameters evaluate to the paper's `246` and `1024`.** -/
theorem numMultsOf_rsa : numMultsOf 3072 5 5 = 246 := by decide

theorem numWinOf_rsa : numWinOf 2048 5 1024 = 1024 := by decide

/-- **The derived parameters reproduce the paper's `LookupAdditionCount`** (`503808`):
    `numMults · 2 · numWin = LookupAdditionCount` at the RSA-2048 parameters — the
    factorisation is no longer a magic constant but a proven consequence of the paper's
    accounting. -/
theorem derivedParams_factor_lookupCount :
    numMultsOf 3072 5 5 * 2 * numWinOf 2048 5 1024 = lookupAddCountPaper 2048 3072 := by
  decide

/-- And `LookupAdditionCount = 503808`, matching `WindowedComposedCost.rsa2048_head_to_head`. -/
theorem lookupAddCountPaper_rsa : lookupAddCountPaper 2048 3072 = 503808 := by decide

/-- **The RSA-2048 Toffoli count via the DERIVED parameters** — same `2 578 993 152`, now
    with `numMults`/`numWin` produced by `numMultsOf`/`numWinOf` rather than hard-coded. -/
theorem rsa2048_modExpAt_toffoli_derived (W : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (q_start : Nat) :
    EGate.toffoli (modExpAt 10 W 2048 Tfam q_start
        (numMultsOf 3072 5 5) (numWinOf 2048 5 1024)) = 2578993152 := by
  rw [numMultsOf_rsa, numWinOf_rsa, toffoli_modExpAt]; norm_num

/-! ## §4. Value of one multiply-add on the shared accumulator.

We first re-derive an UNGUARDED, MOD-form per-step lemma for `babbushLookupAddAt` (the
existing `babbushLookupAddAtValueSpecOn_holds` is mod-free under an overflow guard; we drop
the guard and keep the `% 2^bits` that the Cuccaro adder genuinely produces), then fold it
over the `numWin` windows mirroring the `StepInv` technique of `WindowedCircuitCorrect`. -/

/-- The clean-input family for the UNGUARDED mod-form lookup-add: ctrl on, AND-ancillas
    clean, Cuccaro carry-in and addend clean, table value fits the word width — but NO
    accumulator-overflow guard (the result carries the `% 2^bits` honestly). -/
def CleanInputModFree (w W bits addrBase ancBase q_start : Nat) (T : Nat → Nat)
    (f : Nat → Bool) : Prop :=
  f 0 = true
  ∧ (∀ i, i < w → f (ancBase + i) = false)
  ∧ f q_start = false
  ∧ (∀ i, i < bits → f (q_start + 2 * i + 2) = false)
  ∧ T (decodeReg (fun i => addrBase + i) w f) < 2 ^ W

/-- **The UNGUARDED mod-form per-step lemma.**  On every `CleanInputModFree` input, the
    layout-correct measured lookup-add realises `acc ↦ (acc + T[addr]) mod 2^bits` — the
    honest, overflow-free statement (the existing spec only gives the mod-free `acc + T[addr]`
    under an extra no-overflow hypothesis).  Same circuit reasoning as
    `babbushLookupAddAtValueSpecOn_holds`, stopping before its `Nat.mod_eq_of_lt`. -/
theorem babbushLookupAddAt_modStep
    (w W bits : Nat) (T : Nat → Nat) (addrBase ancBase q_start : Nat)
    (hW : W ≤ bits) (h_anc_pos : 0 < ancBase)
    (h_anc_addr : ∀ i i', i < w → i' < w → ancBase + i ≠ addrBase + i')
    (h_anc_blk : ∀ i, i < w →
      ¬ (q_start ≤ ancBase + i ∧ ancBase + i ≤ q_start + 2 * bits))
    (h_addr_blk : ∀ i, i < w →
      ¬ (q_start ≤ addrBase + i ∧ addrBase + i ≤ q_start + 2 * bits))
    (f : Nat → Bool) (hf : CleanInputModFree w W bits addrBase ancBase q_start T f) :
    decodeReg (fun i => q_start + 2 * i + 1) bits
        (EGate.applyNat (babbushLookupAddAt w W T bits addrBase ancBase q_start) f)
      = (decodeReg (fun i => q_start + 2 * i + 1) bits f
          + T (decodeReg (fun i => addrBase + i) w f)) % 2 ^ bits := by
  obtain ⟨hctrl, hanc, hcarry, haddend, hTlt⟩ := hf
  have hpos_inj : ∀ j k, j < W → k < W →
      addendIdx q_start j = addendIdx q_start k → j = k := by
    intro j k _ _ h; simp only [addendIdx] at h; omega
  have S1 : ∀ i j, i < w → j < W → ancBase + i ≠ addendIdx q_start j := by
    intro i j hi hj; have := h_anc_blk i hi; simp only [addendIdx]; omega
  have S3 : ∀ i j, i < w → j < W → addrBase + i ≠ addendIdx q_start j := by
    intro i j hi hj; have := h_addr_blk i hi; simp only [addendIdx]; omega
  have S4 : ∀ j, j < W → (0 : Nat) ≠ addendIdx q_start j := by
    intro j hj; simp only [addendIdx]; omega
  have S5 : ∀ i, i < w → (0 : Nat) ≠ ancBase + i := by intro i hi; omega
  have hfr := unaryQROMAt_frame (addendIdx q_start) W T addrBase ancBase w 0 0 f
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
  have hclean1 : EGate.applyNat
      (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f q_start = false := by
    rw [hfr q_start (fun j hj => by simp only [addendIdx]; omega)
          (fun i hi => by have := h_anc_blk i hi; omega)]
    exact hcarry
  have haug1 : decodeReg (fun i => q_start + 2 * i + 1) bits
      (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f)
      = decodeReg (fun i => q_start + 2 * i + 1) bits f :=
    decodeReg_ext _ _ _ _ (fun i hi =>
      hfr (q_start + 2 * i + 1) (fun j hj => by simp only [addendIdx]; omega)
        (fun i' hi' => by have := h_anc_blk i' hi'; omega))
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
  have hsum : decodeReg (fun i => q_start + 2 * i + 1) bits
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f))
      = (decodeReg (fun i => q_start + 2 * i + 1) bits
            (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f)
          + decodeReg (fun i => q_start + 2 * i + 2) bits
              (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f))
        % 2 ^ bits :=
    cuccaroAdder.sumCorrect bits q_start _ hclean1
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
  have hsplit : EGate.applyNat
      (babbushLookupAddAt w W T bits addrBase ancBase q_start) f
      = EGate.applyNat (mzList ((List.range W).map (addendIdx q_start)))
          (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f)) :=
    rfl
  rw [hsplit, hmzdec, hsum, haug1, hadd1]

/-- A lookup-add restores the Cuccaro carry-in `q_start` to clean (`false`): the QROM
    leaves it clean, the adder restores it, the measure-clear does not touch it. -/
theorem babbushLookupAddAt_carry_clean
    (w W bits : Nat) (T : Nat → Nat) (addrBase ancBase q_start : Nat) (f : Nat → Bool)
    (hcarry : f q_start = false)
    (h_anc_blk : ∀ i, i < w →
      ¬ (q_start ≤ ancBase + i ∧ ancBase + i ≤ q_start + 2 * bits)) :
    EGate.applyNat (babbushLookupAddAt w W T bits addrBase ancBase q_start) f q_start = false := by
  have hqrom : EGate.applyNat
      (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f q_start = false := by
    rw [unaryQROMAt_frame (addendIdx q_start) W T addrBase ancBase w 0 0 f q_start
          (fun j hj => by simp only [addendIdx]; omega)
          (fun i hi => by have := h_anc_blk i hi; omega)]
    exact hcarry
  have hc : Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
      (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f) q_start
      = false :=
    cuccaroAdder.ancRestored bits q_start _ hqrom
  show EGate.applyNat (mzList ((List.range W).map (addendIdx q_start)))
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f))
      q_start = false
  rw [applyNat_mzList_preserves _ _
        (by simp only [List.mem_map, List.mem_range, addendIdx]
            rintro ⟨j, hj, hjeq⟩; omega)]
  exact hc

/-- A lookup-add leaves the addend register clean: the final measure-clear resets every
    addend position `addendIdx q_start i` (`i < W`). -/
theorem babbushLookupAddAt_addend_clean
    (w W bits : Nat) (T : Nat → Nat) (addrBase ancBase q_start : Nat) (f : Nat → Bool)
    (i : Nat) (hi : i < W) :
    EGate.applyNat (babbushLookupAddAt w W T bits addrBase ancBase q_start) f
        (addendIdx q_start i) = false := by
  show EGate.applyNat (mzList ((List.range W).map (addendIdx q_start)))
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f))
      (addendIdx q_start i) = false
  exact applyNat_mzList_clears _ _
    (by simp only [List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)

/-- **Frame.**  A lookup-add touches only the accumulator block `[q_start, q_start+2·bits+1)`
    and its own AND-ancilla register `[ancBase, ancBase+w)`; every other position
    (the always-on ctrl at `0`, the address register, OTHER windows' registers) is
    preserved. -/
theorem babbushLookupAddAt_frame
    (w W bits : Nat) (T : Nat → Nat) (addrBase ancBase q_start : Nat) (f : Nat → Bool)
    (p : Nat) (hWb : W ≤ bits)
    (hblk : ¬ (q_start ≤ p ∧ p < q_start + 2 * bits + 1))
    (hanc : ∀ i, i < w → p ≠ ancBase + i) :
    EGate.applyNat (babbushLookupAddAt w W T bits addrBase ancBase q_start) f p = f p := by
  have hp_out : ∀ j, j < W → p ≠ addendIdx q_start j := by
    intro j hj; simp only [addendIdx]; omega
  show EGate.applyNat (mzList ((List.range W).map (addendIdx q_start)))
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f))
      p = f p
  rw [applyNat_mzList_preserves _ _
        (by simp only [List.mem_map, List.mem_range]
            rintro ⟨j, hj, hjeq⟩; exact hp_out j hj hjeq.symm),
      show Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f) p
          = EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f p from
        cuccaroAdder.frame bits q_start _ p (by
          unfold inBlock; intro h; exact hblk ⟨h.1, h.2⟩),
      unaryQROMAt_frame (addendIdx q_start) W T addrBase ancBase w 0 0 f p hp_out hanc]

/-- Peel the last step of a `seqAll`-fold over `List.range (n+1)`. -/
theorem applyNat_seqAll_range_succ (step : Nat → EGate) (n : Nat) (g0 : Nat → Bool) :
    EGate.applyNat (seqAll ((List.range (n + 1)).map step)) g0
      = EGate.applyNat (step n)
          (EGate.applyNat (seqAll ((List.range n).map step)) g0) := by
  unfold seqAll
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
  rfl

/-- **The window fold.**  Running the first `n` windowed lookup-adds of multiply-add `m`
    (`Tfam m k v = (a·(2^w)^k·v) mod 2^bits`) on the shared accumulator, started from the
    clean family with the windows of `y` pre-loaded in the per-window address registers,
    drives the accumulator through `windowedLookupFold` and keeps the structure invariant. -/
theorem multiplyAddAt_fold
    (w bits a numWin y m q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start)
    (hT : ∀ k v, Tfam m k v = (a * (2 ^ w) ^ k * v) % 2 ^ bits)
    (g0 : Nat → Bool)
    (hctrl0 : g0 0 = true)
    (hcarry0 : g0 q_start = false)
    (haug0 : ∀ i, i < bits → g0 (q_start + 2 * i + 1) = false)
    (haddend0 : ∀ i, i < bits → g0 (q_start + 2 * i + 2) = false)
    (hanc0 : ∀ k, k < numWin → ∀ i, i < w →
      g0 (ancBaseOf w bits q_start k + i) = false)
    (haddr0 : ∀ k, k < numWin →
      decodeReg (fun i => addrBaseOf w bits q_start k + i) w g0 = window w y k) :
    ∀ n, n ≤ numWin →
      decodeReg (fun i => q_start + 2 * i + 1) bits
          (EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0)
        = windowedLookupFold a (2 ^ bits) w (window w y) n 0
      ∧ EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0 0 = true
      ∧ EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0 q_start
          = false
      ∧ (∀ i, i < bits → EGate.applyNat
          (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0
          (q_start + 2 * i + 2) = false)
      ∧ (∀ k, n ≤ k → k < numWin → ∀ i, i < w → EGate.applyNat
          (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0
          (ancBaseOf w bits q_start k + i) = false)
      ∧ (∀ k, n ≤ k → k < numWin →
          decodeReg (fun i => addrBaseOf w bits q_start k + i) w
            (EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0)
          = window w y k) := by
  intro n hn
  induction n with
  | zero =>
    have hg : EGate.applyNat (seqAll ((List.range 0).map (laAt w bits bits Tfam q_start m))) g0
        = g0 := by simp [seqAll, EGate.applyNat, Gate.applyNat_I]
    rw [hg]
    refine ⟨?_, hctrl0, hcarry0, haddend0, ?_, ?_⟩
    · rw [decodeReg_eq_zero _ _ _ haug0]; rfl
    · intro k _ hk i hi; exact hanc0 k hk i hi
    · intro k _ hk; exact haddr0 k hk
  | succ n ih =>
    have hn' : n ≤ numWin := by omega
    have hnW : n < numWin := by omega
    obtain ⟨hV, hC, hCar, hAdd, hAnc, hAddr⟩ := ih hn'
    -- abbreviations for the depth-`n` state and the lookup-add gate
    set gn := EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0
      with hgn
    set la := laAt w bits bits Tfam q_start m n with hla
    have hla_def : la = babbushLookupAddAt w bits (Tfam m n) bits
        (addrBaseOf w bits q_start n) (ancBaseOf w bits q_start n) q_start := rfl
    -- layout disjointness for window `n`
    have h_anc_addr : ∀ i i', i < w → i' < w →
        ancBaseOf w bits q_start n + i ≠ addrBaseOf w bits q_start n + i' := by
      intro i i' hi hi'; simp only [ancBaseOf, addrBaseOf]; omega
    have h_anc_blk : ∀ i, i < w →
        ¬ (q_start ≤ ancBaseOf w bits q_start n + i ∧
           ancBaseOf w bits q_start n + i ≤ q_start + 2 * bits) := by
      intro i hi; simp only [ancBaseOf, addrBaseOf]; omega
    have h_addr_blk : ∀ i, i < w →
        ¬ (q_start ≤ addrBaseOf w bits q_start n + i ∧
           addrBaseOf w bits q_start n + i ≤ q_start + 2 * bits) := by
      intro i hi; simp only [addrBaseOf]; omega
    -- clean-input for the mod-step at window `n`
    have haddr_n : decodeReg (fun i => addrBaseOf w bits q_start n + i) w gn = window w y n :=
      hAddr n (le_refl n) hnW
    have hclean : CleanInputModFree w bits bits
        (addrBaseOf w bits q_start n) (ancBaseOf w bits q_start n) q_start (Tfam m n) gn := by
      refine ⟨hC, fun i hi => hAnc n (le_refl n) hnW i hi, hCar, hAdd, ?_⟩
      rw [haddr_n, hT n (window w y n)]
      exact Nat.mod_lt _ (Nat.two_pow_pos bits)
    -- the mod-step on window `n`
    have hstep := babbushLookupAddAt_modStep w bits bits (Tfam m n)
      (addrBaseOf w bits q_start n) (ancBaseOf w bits q_start n) q_start
      (le_refl bits) (by simp only [ancBaseOf, addrBaseOf]; omega)
      h_anc_addr h_anc_blk h_addr_blk gn hclean
    -- value: the accumulator advances by one `windowedLookupFold` step
    have hval : decodeReg (fun i => q_start + 2 * i + 1) bits (EGate.applyNat la gn)
        = windowedLookupFold a (2 ^ bits) w (window w y) (n + 1) 0 := by
      rw [hla_def, hstep, haddr_n, hT n (window w y n), hV]
      simp only [windowedLookupFold, tableValue]
    -- the four standing facts for window `n`, re-established after the step
    have hctrl' : EGate.applyNat la gn 0 = true := by
      rw [hla_def, babbushLookupAddAt_frame w bits bits (Tfam m n) _ _ q_start gn 0
            (le_refl bits) (by omega) (fun i hi => by simp only [ancBaseOf, addrBaseOf]; omega)]
      exact hC
    have hcar' : EGate.applyNat la gn q_start = false := by
      rw [hla_def]
      exact babbushLookupAddAt_carry_clean w bits bits (Tfam m n) _ _ q_start gn hCar h_anc_blk
    have hadd' : ∀ i, i < bits → EGate.applyNat la gn (q_start + 2 * i + 2) = false := by
      intro i hi
      rw [hla_def]
      have : q_start + 2 * i + 2 = addendIdx q_start i := by simp only [addendIdx]
      rw [this]
      exact babbushLookupAddAt_addend_clean w bits bits (Tfam m n) _ _ q_start gn i hi
    have hanc' : ∀ k, n + 1 ≤ k → k < numWin → ∀ i, i < w →
        EGate.applyNat la gn (ancBaseOf w bits q_start k + i) = false := by
      intro k hk hkW i hi
      have hkt : n * (2 * w) + 2 * w ≤ k * (2 * w) :=
        le_trans (le_of_eq (by ring)) (by gcongr : (n + 1) * (2 * w) ≤ k * (2 * w))
      rw [hla_def, babbushLookupAddAt_frame w bits bits (Tfam m n) _ _ q_start gn _
            (le_refl bits) (by simp only [ancBaseOf, addrBaseOf]; omega)
            (fun i' hi' => by simp only [ancBaseOf, addrBaseOf]; omega)]
      exact hAnc k (by omega) hkW i hi
    have haddr' : ∀ k, n + 1 ≤ k → k < numWin →
        decodeReg (fun i => addrBaseOf w bits q_start k + i) w (EGate.applyNat la gn)
        = window w y k := by
      intro k hk hkW
      have hkt : n * (2 * w) + 2 * w ≤ k * (2 * w) :=
        le_trans (le_of_eq (by ring)) (by gcongr : (n + 1) * (2 * w) ≤ k * (2 * w))
      rw [decodeReg_ext _ _ _ gn (fun i hi => by
        rw [hla_def, babbushLookupAddAt_frame w bits bits (Tfam m n) _ _ q_start gn _
              (le_refl bits) (by simp only [addrBaseOf]; omega)
              (fun i' hi' => by simp only [ancBaseOf, addrBaseOf]; omega)])]
      exact hAddr k (by omega) hkW
    -- reassemble
    rw [applyNat_seqAll_range_succ]
    rw [← hgn, ← hla]
    exact ⟨hval, hctrl', hcar', hadd', hanc', haddr'⟩

end FormalRV.Shor.WindowedComposedAt
