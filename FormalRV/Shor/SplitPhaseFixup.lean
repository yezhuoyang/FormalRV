/-
  FormalRV.Shor.SplitPhaseFixup — the SPLIT `2^(w/2)` phase-lookup fixup for
  Gidney's measurement-based LOOKUP-uncompute: the construction designed (and
  deliberately not built) in `FormalRV.Shor.PhaseLookupFixup` §7.

  ## What this file builds

  The unsplit fixup `phaseLookup` costs a full table read — `2·(2^w − 1)`
  Toffolis — so the measurement-based uncompute alone saves only the EXIT half
  of a second read.  The `O(2^(w/2))` fixup Gidney–Ekerå actually charge splits
  the address `addr = hi‖lo` (`lo` = low `w2` address levels `0..w2−1`,
  `hi` = high `w1` levels `w2..w−1`, `w = w1 + w2`) and runs THREE stages:

  1. ONE-HOT (`oneHotRead`, Gate-level): the PROVEN Gray-code walk
     `grayWalk` over the HI levels with the one-hot table
     `x ↦ 2^(x / 2^w2)` and word positions `base + h` — row `hi`'s word is
     `2^hi`, whose bit `h` is `[h = hi]`, so `grayWalk_selects_word` already
     proves the one-hot contract `wire (base+h) ⊕= ctrl ∧ [addr_hi = h]` and
     `grayWalk_frame` the restoration of everything else.
     Cost: `2·(2^w1 − 1)` Toffolis.

  2. CZ-LEAF LO-WALK (`czPhaseWalk`, the only new circuit): a
     `phaseWalk`-shaped walk over the LO levels whose leaf for lo-row `ℓ`
     applies `CZ(ladderTop, base + h)` for every `h < 2^w1` with
     `F (h·2^w2 + ℓ)` set (`czRow`).  Each CZ contributes phase
     `(−1)^(ladderTop ∧ oneHot h) = (−1)^([lo = ℓ]·ctrl·[hi = h]·F(h‖ℓ))`,
     and the product over all leaves telescopes to `(−1)^(ctrl ∧ F(addr))` —
     exactly one `(ℓ, h)` pair fires (`czPhaseWalk_diagonal`).
     Cost: `2·(2^w2 − 1)` Toffolis; ALL CZs are Clifford (T-free).

  3. UN-ONE-HOT: stage 1 again — the leaf word-CNOTs are self-inverse XORs,
     so the same circuit clears the one-hot wires
     (`oneHotRead_involution_at`).  Cost: `2·(2^w1 − 1)` Toffolis.

  ## Wire layout (documented per the §7 contract)

  Stages 1–3 live on the unary-lookup layout: ctrl at `0`, address level `i`
  at `1 + 2i`, AND-ladder level `i` at `2 + 2i` (`i < w`), so wires `0..2w`
  are the lookup block.  The `2^w1` one-hot ancillas sit at `base + h`
  (`h < 2^w1`) for a caller-chosen `base` with `2·w < base` — directly above
  the lookup block, below the channel's word register (the end-to-end
  corollary requires `base + 2^w1 ≤ pos j`).  Canonical choice:
  `base = 2·w + 1`.

  ## Headlines

  * `splitPhaseLookup_diagonal` — on every basis state whose AND-ladder and
    one-hot ancillas are clean (ctrl and address arbitrary), the three-stage
    circuit is diagonal with phase `(−1)^(ctrl ∧ F(decAddr f))` — the SAME
    statement shape as the unsplit `phaseLookup_diagonal`.
  * `splitPhaseLookup_discharges_hP` / `measWordUncompute_splitPhaseLookup` —
    the guarded-`hP` discharge and the END-TO-END channel corollary, mirroring
    `phaseLookup_discharges_hP` / `measWordUncompute_phaseLookup` with the
    split circuit and the one-hot-clean `SplitGoodState`.
  * `toffoliCount_splitPhaseLookupSkeleton` — the point of the file:
    `4·(2^w1 − 1) + 2·(2^w2 − 1)` Toffolis (`= 4·2^w1 + 2·2^w2 − 6`), vs the
    unsplit `2·(2^w − 1)`; comparison corollaries
    `toffoliCount_split_le_unsplit` / `toffoliCount_split_lt_unsplit`.

  The three §7-named missing lemmas land here as `cxGates_wellTyped` +
  `grayWalk_wellTyped`, `czPhaseWalk_diagonal`, and the three-stage
  composition inside `splitPhaseLookup_diagonal`.
-/
import FormalRV.Shor.PhaseLookupFixup
import FormalRV.Shor.MeasuredANDUncompute

namespace FormalRV.Shor.SplitPhaseFixup

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Framework.BaseCom
open FormalRV.Framework.BaseUCom (proj)
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.MeasuredANDUncompute
open FormalRV.Shor.MeasuredLookupUncompute
open FormalRV.Shor.PhaseLookupFixup
open Matrix

noncomputable section

/-! ## §0. Decoder arithmetic: splitting `decAddr` into hi‖lo.

`decAddrFrom f i d` (PhaseLookupFixup §1) is the in-place value of address
wires `i..i+d−1`.  We need: the split identity, the range bound, the
`2^i`-divisibility, and — the converse of `decAddr_eq` — that the bits of
`decAddr f` ARE the address wires (`decAddrFrom_testBit`), so the PROVEN
Gray-walk selection lemma can be instantiated at `v := decAddr (w1+w2) f`. -/

/-- Split: the in-place value of `d1 + d2` levels is the value of the first
    `d1` plus the value of the remaining `d2`. -/
theorem decAddrFrom_split (f : Nat → Bool) (d1 d2 : Nat) : ∀ i,
    decAddrFrom f i (d1 + d2)
      = decAddrFrom f i d1 + decAddrFrom f (i + d1) d2 := by
  induction d1 with
  | zero => intro i; simp [decAddrFrom]
  | succ d1 ih =>
      intro i
      rw [show d1 + 1 + d2 = (d1 + d2) + 1 from by omega]
      simp only [decAddrFrom]
      rw [ih (i + 1), show i + (d1 + 1) = (i + 1) + d1 from by omega]
      omega

/-- Range: `decAddrFrom f i d + 2^i ≤ 2^(i+d)` (each level `ℓ` contributes at
    most `2^ℓ`; geometric sum). -/
theorem decAddrFrom_le (f : Nat → Bool) (d : Nat) : ∀ i,
    decAddrFrom f i d + 2 ^ i ≤ 2 ^ (i + d) := by
  induction d with
  | zero => intro i; simp [decAddrFrom]
  | succ d ih =>
      intro i
      have h := ih (i + 1)
      have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
      have h3 : i + (d + 1) = (i + 1) + d := by omega
      rw [h3]
      simp only [decAddrFrom]
      split <;> omega

/-- Divisibility: the in-place value of levels `≥ i` is a multiple of `2^i`. -/
theorem decAddrFrom_dvd (f : Nat → Bool) (d : Nat) : ∀ i,
    2 ^ i ∣ decAddrFrom f i d := by
  induction d with
  | zero => intro i; simp [decAddrFrom]
  | succ d ih =>
      intro i
      have h := ih (i + 1)
      have h2 : (2 : Nat) ^ i ∣ 2 ^ (i + 1) := pow_dvd_pow 2 (by omega)
      simp only [decAddrFrom]
      exact Nat.dvd_add (by split <;> simp) (h2.trans h)

/-- **Converse of `decAddr_eq`**: bit `ℓ` of the decoded value is the address
    wire at level `ℓ`. -/
theorem decAddrFrom_testBit (f : Nat → Bool) (d : Nat) : ∀ i ℓ, i ≤ ℓ → ℓ < i + d →
    (decAddrFrom f i d).testBit ℓ = f (ulookup_address_idx ℓ) := by
  induction d with
  | zero => intro i ℓ h1 h2; omega
  | succ d ih =>
      intro i ℓ h1 h2
      obtain ⟨r', hr'⟩ := decAddrFrom_dvd f d (i + 1)
      have hub := decAddrFrom_le f d (i + 1)
      simp only [decAddrFrom]
      rcases Nat.eq_or_lt_of_le h1 with hℓi | hℓi
      · -- ℓ = i: the head bit.
        subst hℓi
        rw [Nat.testBit_eq_decide_div_mod_eq, hr']
        have h2i : 2 ^ (i + 1) = 2 ^ i * 2 := pow_succ 2 i
        cases hf : f (ulookup_address_idx i)
        · rw [if_neg Bool.false_ne_true, Nat.zero_add, h2i,
              show 2 ^ i * 2 * r' = 2 ^ i * (2 * r') from by ring,
              Nat.mul_div_cancel_left _ (Nat.two_pow_pos i)]
          simp [Nat.mul_mod_right]
        · rw [if_pos rfl, h2i,
              show 2 ^ i + 2 ^ i * 2 * r' = 2 ^ i * (1 + 2 * r') from by ring,
              Nat.mul_div_cancel_left _ (Nat.two_pow_pos i)]
          have hm : (1 + 2 * r') % 2 = 1 := by omega
          simp [hm]
      · -- ℓ > i: the head term is invisible above bit i.
        have hih := ih (i + 1) ℓ (by omega) (by omega)
        set r : Nat := decAddrFrom f (i + 1) d with hr
        set c : Nat := if f (ulookup_address_idx i) then 2 ^ i else 0 with hc
        have hcle : c ≤ 2 ^ i := by rw [hc]; split <;> simp
        have hpowle : (2 : Nat) ^ (i + 1) ≤ 2 ^ ℓ :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have hdvdpow : (2 : Nat) ^ (i + 1) ∣ 2 ^ ℓ := pow_dvd_pow 2 (by omega)
        -- (c + r) / 2^ℓ = r / 2^ℓ: no carry into bit ℓ.
        have hipos : 0 < 2 ^ i := Nat.two_pow_pos i
        have h2i : 2 ^ (i + 1) = 2 ^ i * 2 := pow_succ 2 i
        have hmod : r % 2 ^ ℓ + c % 2 ^ ℓ < 2 ^ ℓ := by
          have hrmod : 2 ^ (i + 1) ∣ r % 2 ^ ℓ :=
            (Nat.dvd_mod_iff hdvdpow).mpr ⟨r', hr'⟩
          have hrlt : r % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt _ (Nat.two_pow_pos ℓ)
          have hcmod : c % 2 ^ ℓ = c := Nat.mod_eq_of_lt (by omega)
          -- the gap from r % 2^ℓ up to 2^ℓ is a positive multiple of 2^(i+1)
          have hgap : 2 ^ (i + 1) ≤ 2 ^ ℓ - r % 2 ^ ℓ :=
            Nat.le_of_dvd (by omega) (Nat.dvd_sub hdvdpow hrmod)
          omega
        have hdiv : (c + r) / 2 ^ ℓ = r / 2 ^ ℓ := by
          rw [Nat.add_div (Nat.two_pow_pos ℓ),
              Nat.div_eq_of_lt (show c < 2 ^ ℓ by
                have := Nat.mod_lt r (Nat.two_pow_pos ℓ); omega),
              if_neg (by omega)]
          omega
        rw [Nat.testBit_eq_decide_div_mod_eq, hdiv,
            ← Nat.testBit_eq_decide_div_mod_eq, hih]

/-- The full decoded address is in range. -/
theorem decAddr_lt (w : Nat) (f : Nat → Bool) : decAddr w f < 2 ^ w := by
  have h := decAddrFrom_le f w 0
  rw [Nat.zero_add, pow_zero] at h
  show decAddrFrom f 0 w < 2 ^ w
  omega

/-- Bits of the decoded address are the address wires. -/
theorem decAddr_testBit (w : Nat) (f : Nat → Bool) (ℓ : Nat) (hℓ : ℓ < w) :
    (decAddr w f).testBit ℓ = f (ulookup_address_idx ℓ) :=
  decAddrFrom_testBit f w 0 ℓ (by omega) (by omega)

/-- The lo half: the value held by address levels `0..w2−1`. -/
def decLo (w2 : Nat) (f : Nat → Bool) : Nat := decAddrFrom f 0 w2

/-- The hi half: the value held by address levels `w2..w1+w2−1`,
    shifted down — bit `k` of `decHi` is address wire `w2 + k`. -/
def decHi (w1 w2 : Nat) (f : Nat → Bool) : Nat := decAddr (w1 + w2) f / 2 ^ w2

/-- The lo half is in range. -/
theorem decLo_lt (w2 : Nat) (f : Nat → Bool) : decLo w2 f < 2 ^ w2 := by
  have h := decAddrFrom_le f w2 0
  rw [Nat.zero_add, pow_zero] at h
  show decAddrFrom f 0 w2 < 2 ^ w2
  omega

/-- **The hi‖lo split**: the in-place hi value is `2^w2 · decHi`, the hi half
    is in range, and `decAddr = decHi·2^w2 + decLo`. -/
theorem decHi_facts (w1 w2 : Nat) (f : Nat → Bool) :
    decAddrFrom f w2 w1 = 2 ^ w2 * decHi w1 w2 f
      ∧ decHi w1 w2 f < 2 ^ w1
      ∧ decAddr (w1 + w2) f = decHi w1 w2 f * 2 ^ w2 + decLo w2 f := by
  have hsplit : decAddr (w1 + w2) f
      = decAddrFrom f 0 w2 + decAddrFrom f w2 w1 := by
    rw [decAddr, show w1 + w2 = w2 + w1 from by omega,
        decAddrFrom_split f w2 w1 0, Nat.zero_add]
  obtain ⟨hiV, hhiV⟩ := decAddrFrom_dvd f w1 w2
  have hlo : decAddrFrom f 0 w2 < 2 ^ w2 := decLo_lt w2 f
  have hdiv : decHi w1 w2 f = hiV := by
    rw [decHi, hsplit, hhiV,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos w2),
        Nat.div_eq_of_lt hlo, Nat.zero_add]
  have hhi_lt : hiV < 2 ^ w1 := by
    by_contra hcon
    have h1 : 2 ^ w2 * 2 ^ w1 ≤ 2 ^ w2 * hiV :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 := decAddrFrom_le f w1 w2
    have hpow : (2 : Nat) ^ (w2 + w1) = 2 ^ w2 * 2 ^ w1 := pow_add 2 w2 w1
    have hp2 : 0 < 2 ^ w2 := Nat.two_pow_pos w2
    omega
  refine ⟨by rw [hhiV, hdiv], by rw [hdiv]; exact hhi_lt, ?_⟩
  rw [hsplit, hhiV, hdiv, decLo]; ring

/-! ## §1. Well-typedness of the Gray walk (§7 missing lemma #1).

Needed to push stages 1/3 through `uc_eval_toUCom_acts_on_basis`. -/

/-- The CX fan-out layer is well-typed when the control and all targets are
    in range and distinct from the control. -/
theorem cxGates_wellTyped (dim c : Nat) (xs : List Nat)
    (hdim : 0 < dim) (hc : c < dim)
    (hxs : ∀ t ∈ xs, t < dim ∧ c ≠ t) :
    Gate.WellTyped dim (cx_gates_from_indices c xs) := by
  induction xs with
  | nil => exact hdim
  | cons t rest ih =>
      obtain ⟨ht, hct⟩ := hxs t (List.mem_cons_self ..)
      exact ⟨ih (fun u hu => hxs u (List.mem_cons_of_mem t hu)), hc, ht, hct⟩

/-- **The Gray walk is well-typed** on any dimension covering its
    ctrl/address/ladder block and word positions. -/
theorem grayWalk_wellTyped (dim : Nat) (pos : Nat → Nat) (W : Nat)
    (T : Nat → Nat) (d : Nat) :
    ∀ (i parent vPrefix : Nat),
      parent ≤ 2 * i →
      2 * (i + d) < dim →
      (∀ j, j < W → pos j < dim ∧ 2 * (i + d) < pos j) →
      Gate.WellTyped dim (grayWalk pos W T d i parent vPrefix) := by
  induction d with
  | zero =>
      intro i parent vPrefix hpar hdim hpos
      show Gate.WellTyped dim
        (cx_gates_from_indices parent (wordCnotsAt pos W (T vPrefix)))
      refine cxGates_wellTyped dim parent _ (by omega) (by omega)
        (fun t ht => ?_)
      obtain ⟨j, hj, _, htj⟩ := (mem_wordCnotsAt pos W (T vPrefix) t).mp ht
      obtain ⟨h1, h2⟩ := hpos j hj
      subst htj
      exact ⟨h1, by omega⟩
  | succ d ih =>
      intro i parent vPrefix hpar hdim hpos
      have hA : ulookup_address_idx i = 1 + 2 * i := rfl
      have hC : ulookup_and_idx i = 1 + 2 * i + 1 := rfl
      have hpos' : ∀ j, j < W → pos j < dim ∧ 2 * ((i + 1) + d) < pos j :=
        fun j hj => by have := hpos j hj; omega
      have hsub : ∀ vP, Gate.WellTyped dim
          (grayWalk pos W T d (i + 1) (ulookup_and_idx i) vP) :=
        fun vP => ih (i + 1) (ulookup_and_idx i) vP (by omega) (by omega) hpos'
      show Gate.WellTyped dim (Gate.seq _ _)
      refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hsub _⟩, ?_⟩, hsub _⟩, ?_⟩
      · show ulookup_address_idx i < dim; omega
      · show parent < dim ∧ ulookup_address_idx i < dim ∧
          ulookup_and_idx i < dim ∧ parent ≠ ulookup_address_idx i ∧
          parent ≠ ulookup_and_idx i ∧
          ulookup_address_idx i ≠ ulookup_and_idx i
        omega
      · show ulookup_address_idx i < dim; omega
      · show parent < dim ∧ ulookup_and_idx i < dim ∧ parent ≠ ulookup_and_idx i
        omega
      · show parent < dim ∧ ulookup_address_idx i < dim ∧
          ulookup_and_idx i < dim ∧ parent ≠ ulookup_address_idx i ∧
          parent ≠ ulookup_and_idx i ∧
          ulookup_address_idx i ≠ ulookup_and_idx i
        omega

/-! ## §2. Stage 1/3: the ONE-HOT read over the HI address levels.

LITERALLY the proven Gray-code read with the one-hot table
`oneHotTable w2 x = 2^(x / 2^w2)`: the walk over levels `w2..w−1` selects the
leaf at in-place value `hi·2^w2`, whose word `2^hi` has bit `h` equal to
`[h = hi]` — so `grayWalk_selects_word` IS the one-hot contract. -/

/-- One-hot table: row at in-place hi-value `x = hi·2^w2` carries word `2^hi`. -/
def oneHotTable (w2 : Nat) : Nat → Nat := fun x => 2 ^ (x / 2 ^ w2)

/-- **Stage 1/3 circuit**: the Gray-code walk over the HI address levels
    `w2..w1+w2−1`, rooted at ctrl, writing the one-hot row marker into the
    `2^w1` wires `base + h`. -/
def oneHotRead (w1 w2 base : Nat) : Gate :=
  grayWalk (fun h => base + h) (2 ^ w1) (oneHotTable w2) w1 w2 ulookup_ctrl_idx 0

/-- The one-hot read is well-typed. -/
theorem oneHotRead_wellTyped (dim w1 w2 base : Nat)
    (hbase : 2 * (w1 + w2) < base) (hdim : base + 2 ^ w1 ≤ dim) :
    Gate.WellTyped dim (oneHotRead w1 w2 base) := by
  have hpow : 0 < 2 ^ w1 := Nat.two_pow_pos w1
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  exact grayWalk_wellTyped dim _ _ _ w1 w2 ulookup_ctrl_idx 0 (by omega)
    (by omega)
    (fun j hj => ⟨show base + j < dim by omega,
                  show 2 * (w2 + w1) < base + j by omega⟩)

/-- **Stage-1 word action**: on any state whose HI ladder wires are clean and
    one-hot wire `h` arbitrary, the read XORs `ctrl ∧ [addr_hi = h]` into wire
    `base + h` — with the hi half read off the state itself via `decHi`. -/
theorem oneHotRead_word (w1 w2 base : Nat) (f : Nat → Bool) (h : Nat)
    (hbase : 2 * (w1 + w2) < base) (hh : h < 2 ^ w1)
    (hand : ∀ ℓ, w2 ≤ ℓ → ℓ < w1 + w2 → f (ulookup_and_idx ℓ) = false) :
    Gate.applyNat (oneHotRead w1 w2 base) f (base + h)
      = xor (f (base + h))
            (f ulookup_ctrl_idx && decide (decHi w1 w2 f = h)) := by
  obtain ⟨hhiV, hhi, hvsplit⟩ := decHi_facts w1 w2 f
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  have hsel := grayWalk_selects_word (fun h => base + h) (2 ^ w1)
    (oneHotTable w2) (decAddr (w1 + w2) f)
    (fun j k hj hk hjk => by
      have hjk' : base + j = base + k := hjk; omega)
    h hh w1 w2 ulookup_ctrl_idx 0 f (by omega)
    (fun ℓ h1 h2 => (decAddr_testBit (w1 + w2) f ℓ (by omega)).symm)
    (fun ℓ h1 h2 => hand ℓ h1 (by omega))
    (fun k hk => show 2 * (w2 + w1) < base + k by omega)
  have hsel' : Gate.applyNat (oneHotRead w1 w2 base) f (base + h)
      = xor (f (base + h))
            (f ulookup_ctrl_idx
              && (oneHotTable w2
                    (0 + grayMidBits (decAddr (w1 + w2) f) w2 w1)).testBit h) :=
    hsel
  rw [hsel', Nat.zero_add]
  -- the selected leaf's in-place value is `2^w2·decHi`; its word is `2^decHi`.
  have hgm : grayMidBits (decAddr (w1 + w2) f) w2 w1
      = 2 ^ w2 * decHi w1 w2 f := by
    rw [← decAddrFrom_eq_grayMidBits f (decAddr (w1 + w2) f) w1 w2
          (fun ℓ h1 h2 => (decAddr_testBit (w1 + w2) f ℓ (by omega)).symm)]
    exact hhiV
  rw [hgm, oneHotTable, Nat.mul_div_cancel_left _ (Nat.two_pow_pos w2),
      Nat.testBit_two_pow]

/-- **Stage-1 frame**: every wire outside the one-hot block is untouched
    (ctrl, address, ladder, word register — all restored). -/
theorem oneHotRead_frame (w1 w2 base : Nat) (f : Nat → Bool) (p : Nat)
    (hbase : 2 * (w1 + w2) < base)
    (hp : ∀ h, h < 2 ^ w1 → p ≠ base + h) :
    Gate.applyNat (oneHotRead w1 w2 base) f p = f p := by
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  exact grayWalk_frame (fun h => base + h) (2 ^ w1) (oneHotTable w2) w1 w2
    ulookup_ctrl_idx 0 f p (by omega)
    (fun k hk => show 2 * (w2 + w1) < base + k by omega)
    (fun k hk => hp k hk)

/-! ## §3. Stage 2 leaf: the table-driven CZ row.

The leaf for lo-row `ℓ` applies `CZ parent (base + h)` for every `h < nH` with
`G h := F (h·2^w2 + ℓ)` set.  Its diagonal phase is the parity
`⊕_{h < nH} (G h ∧ f (base+h))`, gated by the parent (`czRow_diagonal`).
All CZs are Clifford — the row is T-free. -/

/-- The CZ fan-out over the one-hot block: `CZ parent (base+h)` for each
    `h < m` with `G h` set. -/
def czRow (dim parent base : Nat) (G : Nat → Bool) : Nat → BaseUCom dim
  | 0 => BaseUCom.ID 0
  | m + 1 =>
      UCom.seq (czRow dim parent base G m)
        (if G m then BaseUCom.CZ parent (base + m) else BaseUCom.ID 0)

/-- The row parity `⊕_{h < m} (G h ∧ f (base+h))` — the Boolean phase the CZ
    row acquires (before gating by the parent). -/
def hotParity (base : Nat) (G : Nat → Bool) (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | m + 1 => xor (hotParity base G f m) (G m && f (base + m))

/-- `hotParity` only reads the one-hot wires. -/
theorem hotParity_congr (base : Nat) (G : Nat → Bool) (f g : Nat → Bool)
    (m : Nat) (h : ∀ h', h' < m → f (base + h') = g (base + h')) :
    hotParity base G f m = hotParity base G g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [hotParity]
      rw [ih (fun h' hh' => h h' (by omega)), h m (by omega)]

/-- **One-hot collapse**: on a state whose one-hot wires hold the one-hot
    pattern `c ∧ [h₀ = ·]`, the row parity collapses to the single addressed
    table bit `c ∧ G h₀` (provided `h₀` is in range). -/
theorem hotParity_single (base : Nat) (G : Nat → Bool) (f : Nat → Bool)
    (c : Bool) (h0 : Nat) (m : Nat)
    (hf : ∀ h', h' < m → f (base + h') = (c && decide (h0 = h'))) :
    hotParity base G f m = (c && (decide (h0 < m) && G h0)) := by
  induction m with
  | zero => simp [hotParity]
  | succ m ih =>
      simp only [hotParity]
      rw [ih (fun h' hh' => hf h' (by omega)), hf m (by omega)]
      rcases Nat.lt_trichotomy h0 m with hlt | heq | hgt
      · have e1 : decide (h0 < m) = true := decide_eq_true hlt
        have e2 : decide (h0 < m + 1) = true := decide_eq_true (by omega)
        have e3 : decide (h0 = m) = false := decide_eq_false (by omega)
        rw [e1, e2, e3]
        cases c <;> cases G h0 <;> simp
      · subst heq
        have e1 : decide (h0 < h0) = false := decide_eq_false (by omega)
        have e2 : decide (h0 < h0 + 1) = true := decide_eq_true (by omega)
        rw [e1, e2, decide_eq_true (rfl : h0 = h0)]
        cases c <;> cases G h0 <;> simp
      · have e1 : decide (h0 < m) = false := decide_eq_false (by omega)
        have e2 : decide (h0 < m + 1) = false := decide_eq_false (by omega)
        have e3 : decide (h0 = m) = false := decide_eq_false (by omega)
        rw [e1, e2, e3]
        simp

/-- **The CZ row is diagonal** on every basis state, with phase
    `(−1)^(parent ∧ hotParity)` — `f_to_vec_CZ` iterated over the row. -/
theorem czRow_diagonal (dim parent base : Nat) (G : Nat → Bool)
    (hpb : parent < base) (f : Nat → Bool) :
    ∀ m, base + m ≤ dim →
      uc_eval (czRow dim parent base G m) * f_to_vec dim f
        = (if f parent && hotParity base G f m then (-1 : ℂ) else 1)
            • f_to_vec dim f := by
  intro m
  induction m with
  | zero =>
      intro hdim
      simp only [czRow, hotParity, Bool.and_false, Bool.false_eq_true, if_false,
        uc_eval_ID_eq_one (show 0 < dim by omega), Matrix.one_mul, one_smul]
  | succ m ih =>
      intro hdim
      simp only [czRow, hotParity, uc_eval_seq_mul]
      rw [ih (by omega), Matrix.mul_smul]
      rcases Bool.eq_false_or_eq_true (G m) with hG | hG
      · -- G m = true: the CZ fires.
        simp only [hG, if_true, Bool.true_and]
        rw [f_to_vec_CZ dim parent (base + m) (by omega) (by omega) (by omega) f,
            smul_smul]
        rcases Bool.eq_false_or_eq_true (f parent) with hp | hp <;>
          rcases Bool.eq_false_or_eq_true (hotParity base G f m) with hq | hq <;>
            rcases Bool.eq_false_or_eq_true (f (base + m)) with hr | hr <;>
              simp [hp, hq, hr]
      · -- G m = false: the slot is an identity.
        simp [hG, uc_eval_ID_eq_one (show 0 < dim by omega)]

/-! ## §4. Stage 2: the CZ-leaf phase walk over the LO address levels
(§7 missing lemma #2).

Same ENTER / SWITCH / EXIT recursion as `phaseWalk` (the classical segments
are the Gate-level `enterSeg`/`CX`/`CCX`, embedded via `Gate.toUCom`), with
the leaf for lo-prefix `ℓ` emitting the CZ row for the column
`G h := F (h·2^w2 + ℓ)`. -/

/-- **The CZ-leaf phase walk** — `czPhaseWalk dim F w2 base nH d i parent
    vPrefix` is the subtree at ladder level `i` with `d` levels remaining. -/
def czPhaseWalk (dim : Nat) (F : Nat → Bool) (w2 base nH : Nat) :
    Nat → Nat → Nat → Nat → BaseUCom dim
  | 0, _, parent, vPrefix =>
      czRow dim parent base (fun h => F (h * 2 ^ w2 + vPrefix)) nH
  | d + 1, i, parent, vPrefix =>
      UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (Gate.toUCom dim (enterSeg i parent))
        (czPhaseWalk dim F w2 base nH d (i + 1) (ulookup_and_idx i) vPrefix))
        (Gate.toUCom dim (Gate.CX parent (ulookup_and_idx i))))
        (czPhaseWalk dim F w2 base nH d (i + 1) (ulookup_and_idx i)
          (vPrefix + 2 ^ i)))
        (Gate.toUCom dim
          (Gate.CCX parent (ulookup_address_idx i) (ulookup_and_idx i)))

/-- **Diagonal action of the CZ-leaf walk** (mirror of `phaseWalk_diagonal`):
    on any basis state whose LO ladder wires are clean, the walk is diagonal
    with phase `(−1)^(parent ∧ hotParity(column at the decoded lo-value))` —
    the one-hot wires are read off `f` as-is, no constraint on them yet. -/
theorem czPhaseWalk_diagonal (dim : Nat) (F : Nat → Bool) (w2 base nH : Nat)
    (d : Nat) :
    ∀ (i parent vPrefix : Nat) (f : Nat → Bool),
      parent ≤ 2 * i →
      2 * (i + d) < base →
      base + nH ≤ dim →
      (∀ ℓ, i ≤ ℓ → ℓ < i + d → f (ulookup_and_idx ℓ) = false) →
      uc_eval (czPhaseWalk dim F w2 base nH d i parent vPrefix) * f_to_vec dim f
        = (if f parent
              && hotParity base
                   (fun h => F (h * 2 ^ w2 + (vPrefix + decAddrFrom f i d)))
                   f nH
           then (-1 : ℂ) else 1) • f_to_vec dim f := by
  induction d with
  | zero =>
      intro i parent vPrefix f hpar hbase hdim _
      simp only [czPhaseWalk, decAddrFrom, Nat.add_zero]
      exact czRow_diagonal dim parent base _ (by omega) f nH hdim
  | succ d ih =>
      intro i parent vPrefix f hpar hbase hdim hand
      have hA : ulookup_address_idx i = 1 + 2 * i := rfl
      have hC : ulookup_and_idx i = 1 + 2 * i + 1 := rfl
      have hfc : f (ulookup_and_idx i) = false := hand i (Nat.le_refl i) (by omega)
      have hPC : parent ≠ ulookup_and_idx i := by omega
      have hAC : ulookup_address_idx i ≠ ulookup_and_idx i := by omega
      have hdim' : 2 * (i + (d + 1)) < dim := by omega
      -- well-typedness of the three classical segments
      have hwtE : Gate.WellTyped dim (enterSeg i parent) := by
        simp only [enterSeg, Gate.WellTyped]; omega
      have hwtS : Gate.WellTyped dim (Gate.CX parent (ulookup_and_idx i)) := by
        simp only [Gate.WellTyped]; omega
      have hwtX : Gate.WellTyped dim
          (Gate.CCX parent (ulookup_address_idx i) (ulookup_and_idx i)) := by
        simp only [Gate.WellTyped]; omega
      -- the two intermediate ladder states
      set g3 : Nat → Bool :=
        update f (ulookup_and_idx i)
          (f parent && !f (ulookup_address_idx i)) with hg3
      set g5 : Nat → Bool :=
        update f (ulookup_and_idx i)
          (f parent && f (ulookup_address_idx i)) with hg5
      have hg3_C : g3 (ulookup_and_idx i)
          = (f parent && !f (ulookup_address_idx i)) := update_eq _ _ _
      have hg3_par : g3 parent = f parent := update_neq _ _ _ _ hPC
      have hg5_C : g5 (ulookup_and_idx i)
          = (f parent && f (ulookup_address_idx i)) := update_eq _ _ _
      have hg5_par : g5 parent = f parent := update_neq _ _ _ _ hPC
      have hg5_A : g5 (ulookup_address_idx i) = f (ulookup_address_idx i) := by
        rw [hg5, update_neq _ _ _ _ hAC]
      have hand3 : ∀ ℓ, i + 1 ≤ ℓ → ℓ < (i + 1) + d →
          g3 (ulookup_and_idx ℓ) = false := by
        intro ℓ h1 h2
        have e1 : ulookup_and_idx ℓ = 1 + 2 * ℓ + 1 := rfl
        rw [hg3, update_neq _ _ _ _ (by omega)]
        exact hand ℓ (by omega) (by omega)
      have hand5 : ∀ ℓ, i + 1 ≤ ℓ → ℓ < (i + 1) + d →
          g5 (ulookup_and_idx ℓ) = false := by
        intro ℓ h1 h2
        have e1 : ulookup_and_idx ℓ = 1 + 2 * ℓ + 1 := rfl
        rw [hg5, update_neq _ _ _ _ (by omega)]
        exact hand ℓ (by omega) (by omega)
      -- the decoder never reads the ladder wires
      have hdec3 : decAddrFrom g3 (i + 1) d = decAddrFrom f (i + 1) d := by
        refine decAddrFrom_congr _ _ d (i + 1) (fun ℓ h1 h2 => ?_)
        have e1 : ulookup_address_idx ℓ = 1 + 2 * ℓ := rfl
        rw [hg3, update_neq _ _ _ _ (by omega)]
      have hdec5 : decAddrFrom g5 (i + 1) d = decAddrFrom f (i + 1) d := by
        refine decAddrFrom_congr _ _ d (i + 1) (fun ℓ h1 h2 => ?_)
        have e1 : ulookup_address_idx ℓ = 1 + 2 * ℓ := rfl
        rw [hg5, update_neq _ _ _ _ (by omega)]
      -- the row parity never reads the ladder wires
      have hhot3 : ∀ G : Nat → Bool,
          hotParity base G g3 nH = hotParity base G f nH := fun G =>
        hotParity_congr base G g3 f nH (fun h' hh' => by
          rw [hg3, update_neq _ _ _ _ (by omega)])
      have hhot5 : ∀ G : Nat → Bool,
          hotParity base G g5 nH = hotParity base G f nH := fun G =>
        hotParity_congr base G g5 f nH (fun h' hh' => by
          rw [hg5, update_neq _ _ _ _ (by omega)])
      -- EXIT clears the ladder wire back to `f`
      have hclear : update g5 (ulookup_and_idx i) false = f := by
        rw [hg5, update_idem, ← hfc, update_self]
      -- the five-stage pipeline
      simp only [czPhaseWalk, uc_eval_seq_mul]
      -- ENTER
      rw [uc_eval_toUCom_acts_on_basis dim _ hwtE f,
          enterSeg_applyNat i parent hpar f, hfc, Bool.false_xor, ← hg3]
      -- 0-subtree (IH at parent' = the ladder wire, prefix unchanged)
      rw [ih (i + 1) (ulookup_and_idx i) vPrefix g3 (by omega) (by omega)
            hdim hand3]
      simp only [hg3_C, hdec3, hhot3, Matrix.mul_smul]
      -- SWITCH (the sawtooth CX)
      rw [uc_eval_toUCom_acts_on_basis dim _ hwtS g3, Gate.applyNat_CX,
          hg3_C, hg3_par, phase_switch, hg3, update_idem, ← hg5]
      -- 1-subtree (IH at prefix + 2^i)
      rw [ih (i + 1) (ulookup_and_idx i) (vPrefix + 2 ^ i) g5 (by omega)
            (by omega) hdim hand5]
      simp only [hg5_C, hdec5, hhot5, Matrix.mul_smul]
      -- EXIT
      rw [uc_eval_toUCom_acts_on_basis dim _ hwtX g5, Gate.applyNat_CCX,
          hg5_C, hg5_par, hg5_A, Bool.xor_self, hclear]
      -- combine the two ±1 phases: exactly one subtree was selected
      simp only [decAddrFrom]
      rcases Bool.eq_false_or_eq_true (f (ulookup_address_idx i)) with hbv | hbv <;>
        simp [hbv, Nat.add_assoc]

/-! ## §5. The three-stage composition (§7 missing lemma #3).

Stage 1 is a basis-state permutation (`uc_eval_toUCom_acts_on_basis` +
`grayWalk_selects_word`/`grayWalk_frame`), stage 2 is diagonal
(`czPhaseWalk_diagonal`), stage 3 inverts stage 1
(`oneHotRead_involution_at` — the leaf word-CNOTs are self-inverse XORs), so
the composite is diagonal with the stage-2 phase evaluated on the
one-hot-computed state — which collapses to `(−1)^(ctrl ∧ F(addr))`
(`hotParity_single`). -/

/-- Stage 1/3 is an involution: running the one-hot read twice restores every
    wire (needs only the HI ladder clean — the read's own operating frame). -/
theorem oneHotRead_involution_at (w1 w2 base : Nat) (f : Nat → Bool)
    (hbase : 2 * (w1 + w2) < base)
    (hand : ∀ ℓ, w2 ≤ ℓ → ℓ < w1 + w2 → f (ulookup_and_idx ℓ) = false)
    (p : Nat) :
    Gate.applyNat (oneHotRead w1 w2 base)
        (Gate.applyNat (oneHotRead w1 w2 base) f) p = f p := by
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  by_cases hp : ∀ h, h < 2 ^ w1 → p ≠ base + h
  · rw [oneHotRead_frame w1 w2 base _ p hbase hp,
        oneHotRead_frame w1 w2 base f p hbase hp]
  · -- p is a one-hot wire: the second read XORs the same selection bit again.
    push Not at hp
    obtain ⟨h, hh, hpeq⟩ := hp
    subst hpeq
    have hgframe : ∀ q, (∀ k, k < 2 ^ w1 → q ≠ base + k) →
        Gate.applyNat (oneHotRead w1 w2 base) f q = f q := fun q hq =>
      oneHotRead_frame w1 w2 base f q hbase hq
    have hand_g : ∀ ℓ, w2 ≤ ℓ → ℓ < w1 + w2 →
        Gate.applyNat (oneHotRead w1 w2 base) f (ulookup_and_idx ℓ) = false := by
      intro ℓ h1 h2
      rw [hgframe _ (fun k hk => by
        have e1 : ulookup_and_idx ℓ = 1 + 2 * ℓ + 1 := rfl
        omega)]
      exact hand ℓ h1 h2
    have hctrl : Gate.applyNat (oneHotRead w1 w2 base) f ulookup_ctrl_idx
        = f ulookup_ctrl_idx :=
      hgframe _ (fun k hk => by omega)
    have hdec : decHi w1 w2 (Gate.applyNat (oneHotRead w1 w2 base) f)
        = decHi w1 w2 f := by
      rw [decHi, decHi]
      congr 1
      exact decAddrFrom_congr _ _ (w1 + w2) 0 (fun ℓ h1 h2 =>
        hgframe _ (fun k hk => by
          have e1 : ulookup_address_idx ℓ = 1 + 2 * ℓ := rfl
          omega))
    rw [oneHotRead_word w1 w2 base _ h hbase hh hand_g, hctrl, hdec,
        oneHotRead_word w1 w2 base f h hbase hh hand]
    simp

/-- **Stage 2 packaged**: the CZ-leaf walk over the LO levels, full depth,
    rooted at ctrl. -/
def czPhaseLoLookup (dim : Nat) (F : Nat → Bool) (w1 w2 base : Nat) :
    BaseUCom dim :=
  czPhaseWalk dim F w2 base (2 ^ w1) w2 0 ulookup_ctrl_idx 0

/-- **THE SPLIT PHASE LOOKUP**: one-hot the hi half, CZ-leaf walk the lo half,
    un-one-hot the hi half. -/
def splitPhaseLookup (dim : Nat) (F : Nat → Bool) (w1 w2 base : Nat) :
    BaseUCom dim :=
  UCom.seq (UCom.seq
    (Gate.toUCom dim (oneHotRead w1 w2 base))
    (czPhaseLoLookup dim F w1 w2 base))
    (Gate.toUCom dim (oneHotRead w1 w2 base))

/-- **HEADLINE (diagonal action, decoder form)** — same statement shape as the
    unsplit `phaseLookup_diagonal`: on EVERY basis state whose AND-ladder and
    one-hot ancillas are clean (ctrl and address arbitrary), the split
    lookup is diagonal with phase `(−1)^(ctrl ∧ F(decAddr f))`. -/
theorem splitPhaseLookup_diagonal (dim w1 w2 base : Nat) (F : Nat → Bool)
    (f : Nat → Bool)
    (hbase : 2 * (w1 + w2) < base) (hdim : base + 2 ^ w1 ≤ dim)
    (hand : ∀ i, i < w1 + w2 → f (ulookup_and_idx i) = false)
    (hhot : ∀ h, h < 2 ^ w1 → f (base + h) = false) :
    uc_eval (splitPhaseLookup dim F w1 w2 base) * f_to_vec dim f
      = (if f ulookup_ctrl_idx && F (decAddr (w1 + w2) f) then (-1 : ℂ) else 1)
          • f_to_vec dim f := by
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  have hwt : Gate.WellTyped dim (oneHotRead w1 w2 base) :=
    oneHotRead_wellTyped dim w1 w2 base hbase hdim
  have hand_hi : ∀ ℓ, w2 ≤ ℓ → ℓ < w1 + w2 → f (ulookup_and_idx ℓ) = false :=
    fun ℓ _ h2 => hand ℓ h2
  obtain ⟨hhiV, hhi_lt, hsplit⟩ := decHi_facts w1 w2 f
  -- the pipeline
  simp only [splitPhaseLookup, uc_eval_seq_mul]
  -- stage 1: a basis-state permutation
  rw [uc_eval_toUCom_acts_on_basis dim _ hwt f]
  set g : Nat → Bool := Gate.applyNat (oneHotRead w1 w2 base) f with hg
  -- frame facts about the one-hot-computed state
  have hgframe : ∀ q, (∀ k, k < 2 ^ w1 → q ≠ base + k) → g q = f q :=
    fun q hq => by rw [hg]; exact oneHotRead_frame w1 w2 base f q hbase hq
  have hctrl_g : g ulookup_ctrl_idx = f ulookup_ctrl_idx :=
    hgframe _ (fun k hk => by omega)
  have hdec_g : decAddrFrom g 0 w2 = decAddrFrom f 0 w2 :=
    decAddrFrom_congr g f w2 0 (fun ℓ h1 h2 =>
      hgframe _ (fun k hk => by
        have e1 : ulookup_address_idx ℓ = 1 + 2 * ℓ := rfl
        omega))
  have hone : ∀ h', h' < 2 ^ w1 →
      g (base + h') = (f ulookup_ctrl_idx && decide (decHi w1 w2 f = h')) := by
    intro h' hh'
    rw [hg, oneHotRead_word w1 w2 base f h' hbase hh' hand_hi,
        hhot h' hh', Bool.false_xor]
  -- stage 2: diagonal on g (the lo ladder of g is clean, by the frame)
  have hstage2 := czPhaseWalk_diagonal dim F w2 base (2 ^ w1) w2 0
    ulookup_ctrl_idx 0 g (by omega) (by omega) hdim
    (fun ℓ h1 h2 => by
      rw [hgframe _ (fun k hk => by
        have e1 : ulookup_and_idx ℓ = 1 + 2 * ℓ + 1 := rfl
        omega)]
      exact hand ℓ (by omega))
  rw [czPhaseLoLookup, hstage2]
  -- stage 3: inverts stage 1 (the phase factor rides along)
  have hinv : Gate.applyNat (oneHotRead w1 w2 base) g = f := by
    rw [hg]
    exact funext (oneHotRead_involution_at w1 w2 base f hbase hand_hi)
  rw [Matrix.mul_smul, uc_eval_toUCom_acts_on_basis dim _ hwt g, hinv]
  -- collapse the phase: the one-hot pattern selects the single hi row
  have hcollapse := hotParity_single base
    (fun h => F (h * 2 ^ w2 + (0 + decAddrFrom f 0 w2))) g
    (f ulookup_ctrl_idx) (decHi w1 w2 f) (2 ^ w1) hone
  simp only [hdec_g, hctrl_g, hcollapse, decide_eq_true hhi_lt]
  -- assemble: ctrl ∧ (ctrl ∧ F(hi·2^w2 + lo)) = ctrl ∧ F(addr)
  have haddr_eq : decHi w1 w2 f * 2 ^ w2 + decAddrFrom f 0 w2
      = decAddr (w1 + w2) f := hsplit.symm
  rcases Bool.eq_false_or_eq_true (f ulookup_ctrl_idx) with hc | hc <;>
    simp [hc, haddr_eq]

/-- **HEADLINE (diagonal action, address form)** — mirror of
    `phaseLookup_diagonal_addr`: ctrl set, address holding `v`, ladders and
    one-hot ancillas clean ⟹ the split lookup applies exactly `(−1)^(F v)`. -/
theorem splitPhaseLookup_diagonal_addr (dim w1 w2 base : Nat) (F : Nat → Bool)
    (v : Nat) (f : Nat → Bool)
    (hbase : 2 * (w1 + w2) < base) (hdim : base + 2 ^ w1 ≤ dim)
    (hv : v < 2 ^ (w1 + w2))
    (hctrl : f ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w1 + w2 → f (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w1 + w2 → f (ulookup_and_idx i) = false)
    (hhot : ∀ h, h < 2 ^ w1 → f (base + h) = false) :
    uc_eval (splitPhaseLookup dim F w1 w2 base) * f_to_vec dim f
      = (if F v then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [splitPhaseLookup_diagonal dim w1 w2 base F f hbase hdim hand hhot, hctrl,
      Bool.true_and, decAddr_eq (w1 + w2) f v hv haddr]

/-! ## §6. The guarded-`hP` discharge and the END-TO-END channel corollary.

Mirrors PhaseLookupFixup §6 with the split circuit: the `Good` set
additionally demands clean one-hot ancillas, and the channel's word
positions sit above the one-hot block — so word-bit updates preserve it,
and §5's `measWordUncompute_perfect_guarded` applies verbatim. -/

/-- The `Good` set for the split lookup: ctrl set, AND-ladder clean
    (`GoodState`), and the `2^w1` one-hot ancillas clean. -/
def SplitGoodState (w1 w2 base : Nat) (f : Nat → Bool) : Prop :=
  GoodState (w1 + w2) f ∧ ∀ h, h < 2 ^ w1 → f (base + h) = false

/-- `SplitGoodState` is closed under updates above the one-hot block (where
    the channel's word register lives). -/
theorem SplitGoodState_update_word (w1 w2 base : Nat) (f : Nat → Bool)
    (q : Nat) (hbase : 2 * (w1 + w2) < base) (hq : base + 2 ^ w1 ≤ q)
    (v : Bool) (hf : SplitGoodState w1 w2 base f) :
    SplitGoodState w1 w2 base (update f q v) := by
  have hp1 : 0 < 2 ^ w1 := Nat.two_pow_pos w1
  refine ⟨GoodState_update_word (w1 + w2) f q (by omega) v hf.1,
    fun h hh => ?_⟩
  rw [update_neq _ _ _ _ (show base + h ≠ q by omega)]
  exact hf.2 h hh

/-- **The `hP` discharge (split form)**: on every `SplitGoodState`, the
    per-bit split phase lookup has EXACTLY the diagonal action
    `measWordUncompute_qrom` postulates for `P j`, with the concrete decoder
    `decAddr` — the analogue of `phaseLookup_discharges_hP` at
    `O(2^(w/2))` Toffolis instead of `O(2^w)`. -/
theorem splitPhaseLookup_discharges_hP (dim w1 w2 base : Nat)
    (T : Nat → Nat) (j : Nat)
    (hbase : 2 * (w1 + w2) < base) (hdim : base + 2 ^ w1 ≤ dim)
    (f : Nat → Bool) (hf : SplitGoodState w1 w2 base f) :
    uc_eval (splitPhaseLookup dim (fun v => (T v).testBit j) w1 w2 base)
        * f_to_vec dim f
      = (if (T (decAddr (w1 + w2) f)).testBit j then (-1 : ℂ) else 1)
          • f_to_vec dim f := by
  rw [splitPhaseLookup_diagonal dim w1 w2 base _ f hbase hdim hf.1.2 hf.2,
      hf.1.1, Bool.true_and]

/-- **END-TO-END HEADLINE** (mirror of `measWordUncompute_phaseLookup`):
    Gidney's measurement-based lookup-uncompute with the CONCRETE per-bit
    SPLIT fixups `P j := splitPhaseLookup dim (fun v => (T v).testBit j)
    w1 w2 base` is the perfect uncompute on every lookup-computed family
    (ctrl set, ladders and one-hot ancillas clean, word bit `j` holding
    `T[addr].bit j` on the support): coefficients intact, all `W` word bits
    released as `|0…0⟩`, no second lookup — now at the Gidney–Ekerå
    `O(2^(w/2))` fixup cost. -/
theorem measWordUncompute_splitPhaseLookup {dim : Nat} {ι : Type*}
    (w1 w2 base W : Nat) (pos : Nat → Nat) (T : Nat → Nat)
    (hbase : 2 * (w1 + w2) < base)
    (hdim : base + 2 ^ w1 ≤ dim)
    (hpos : ∀ j, j < W → pos j < dim)
    (hpos_high : ∀ j, j < W → base + 2 ^ w1 ≤ pos j)
    (hinj : ∀ j, j < W → ∀ k, k < W → j ≠ k → pos j ≠ pos k)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hgood : ∀ i ∈ s, SplitGoodState w1 w2 base (g i))
    (hword : ∀ i ∈ s, ∀ j, j < W →
        g i (pos j) = (T (decAddr (w1 + w2) (g i))).testBit j) :
    c_eval (measWordUncompute dim pos
        (fun j => splitPhaseLookup dim (fun v => (T v).testBit j) w1 w2 base) W)
        ((∑ i ∈ s, α i • f_to_vec dim (g i))
          * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))
          * (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))ᴴ :=
  measWordUncompute_perfect_guarded W pos _
    (fun j f => (T (decAddr (w1 + w2) f)).testBit j)
    (SplitGoodState w1 w2 base)
    hpos hinj
    (fun j _ f hf =>
      splitPhaseLookup_discharges_hP dim w1 w2 base T j hbase hdim f hf)
    (fun j _ k hk f v => by
      show (T (decAddr (w1 + w2) (update f (pos k) v))).testBit j = _
      rw [decAddr_update_word (w1 + w2) f (pos k)
            (by have := hpos_high k hk; have := Nat.two_pow_pos w1; omega) v])
    (fun f hf k hk v => SplitGoodState_update_word w1 w2 base f (pos k) hbase
      (hpos_high k hk) v hf)
    s α g hgood hword

/-! ## §7. Cost — THE POINT OF THIS FILE.

Stages 1/3 are Gate-level (`tcount` counts them directly); stage 2's
classical skeleton is the unsplit file's `phaseWalkSkeleton w2` and its CZ
leaves are Clifford (T-free, exactly like the unsplit walk's `Z` leaves —
`BaseUCom` carries no T-counter, so the count lives on the literal Gate-level
twin, mirroring PhaseLookupFixup §4):

    T-content = 2 × (one-hot read = `14·(2^w1 − 1)`)
              + (lo-walk skeleton = `14·(2^w2 − 1)`)

⟹ `toffoliCount = 4·(2^w1 − 1) + 2·(2^w2 − 1) = 4·2^w1 + 2·2^w2 − 6`
— vs the unsplit `2·(2^w − 1)`: `O(2^(w/2))` at `w1 = w2 = w/2`. -/

/-- The Gate-level T-content twin of `splitPhaseLookup`: the two one-hot
    reads ARE its stages 1/3; the middle factor is the classical skeleton of
    the lo-walk (its CZ leaves are Clifford and contribute no T). -/
def splitPhaseLookupSkeleton (w1 w2 base : Nat) : Gate :=
  Gate.seq (Gate.seq (oneHotRead w1 w2 base)
                     (phaseWalkSkeleton w2 0 ulookup_ctrl_idx))
           (oneHotRead w1 w2 base)

/-- T-count of one one-hot read: a `w1`-deep Gray walk — `14·(2^w1 − 1)`. -/
theorem tcount_oneHotRead (w1 w2 base : Nat) :
    tcount (oneHotRead w1 w2 base) = 14 * (2 ^ w1 - 1) :=
  tcount_grayWalk _ _ _ w1 w2 ulookup_ctrl_idx 0

/-- **T-count of the split fixup skeleton**, structured form:
    two one-hot reads + one lo-walk skeleton. -/
theorem tcount_splitPhaseLookupSkeleton (w1 w2 base : Nat) :
    tcount (splitPhaseLookupSkeleton w1 w2 base)
      = 2 * (14 * (2 ^ w1 - 1)) + 14 * (2 ^ w2 - 1) := by
  simp only [splitPhaseLookupSkeleton, tcount, tcount_oneHotRead,
    tcount_phaseWalkSkeleton]
  omega

/-- **T-count of the split fixup skeleton**, closed form:
    `28·2^w1 + 14·2^w2 − 42`. -/
theorem tcount_splitPhaseLookupSkeleton_closed (w1 w2 base : Nat) :
    tcount (splitPhaseLookupSkeleton w1 w2 base)
      = 28 * 2 ^ w1 + 14 * 2 ^ w2 - 42 := by
  rw [tcount_splitPhaseLookupSkeleton]
  have ha := Nat.two_pow_pos w1
  have hb := Nat.two_pow_pos w2
  omega

/-- **Toffoli count of the split fixup skeleton**:
    `4·(2^w1 − 1) + 2·(2^w2 − 1)` — the §7 figure. -/
theorem toffoliCount_splitPhaseLookupSkeleton (w1 w2 base : Nat) :
    toffoliCount (splitPhaseLookupSkeleton w1 w2 base)
      = 4 * (2 ^ w1 - 1) + 2 * (2 ^ w2 - 1) := by
  have ha := Nat.two_pow_pos w1
  have hb := Nat.two_pow_pos w2
  rw [toffoliCount, tcount_splitPhaseLookupSkeleton,
      show 2 * (14 * (2 ^ w1 - 1)) + 14 * (2 ^ w2 - 1)
          = (4 * (2 ^ w1 - 1) + 2 * (2 ^ w2 - 1)) * 7 from by omega,
      Nat.mul_div_cancel _ (by norm_num)]

/-- Toffoli count, closed form: `4·2^w1 + 2·2^w2 − 6`. -/
theorem toffoliCount_splitPhaseLookupSkeleton_closed (w1 w2 base : Nat) :
    toffoliCount (splitPhaseLookupSkeleton w1 w2 base)
      = 4 * 2 ^ w1 + 2 * 2 ^ w2 - 6 := by
  rw [toffoliCount_splitPhaseLookupSkeleton]
  have ha := Nat.two_pow_pos w1
  have hb := Nat.two_pow_pos w2
  omega

/-- **Split ≤ unsplit** whenever the lo half is nonempty (`w2 ≥ 1`):
    `4·(2^w1 − 1) + 2·(2^w2 − 1) ≤ 2·(2^(w1+w2) − 1)`. -/
theorem toffoliCount_split_le_unsplit (w1 w2 base : Nat) (hw2 : 1 ≤ w2) :
    toffoliCount (splitPhaseLookupSkeleton w1 w2 base)
      ≤ toffoliCount (phaseLookupSkeleton (w1 + w2)) := by
  rw [toffoliCount_splitPhaseLookupSkeleton, toffoliCount_phaseLookupSkeleton]
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ w1 = c + 1 :=
    ⟨2 ^ w1 - 1, by have := Nat.two_pow_pos w1; omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ w2 = d + 2 :=
    ⟨2 ^ w2 - 2, by
      have h2 : (2 : Nat) ^ 1 ≤ 2 ^ w2 := Nat.pow_le_pow_right (by norm_num) hw2
      have h2' : (2 : Nat) ^ 1 = 2 := by norm_num
      omega⟩
  have hpow : (2 : Nat) ^ (w1 + w2) = 2 ^ w1 * 2 ^ w2 := pow_add 2 w1 w2
  have hexp : 2 ^ w1 * 2 ^ w2 = c * d + 2 * c + d + 2 := by rw [hc, hd]; ring
  omega

/-- **Split < unsplit, strictly**, once both halves are real
    (`w1 ≥ 1`, `w2 ≥ 2`). -/
theorem toffoliCount_split_lt_unsplit (w1 w2 base : Nat)
    (hw1 : 1 ≤ w1) (hw2 : 2 ≤ w2) :
    toffoliCount (splitPhaseLookupSkeleton w1 w2 base)
      < toffoliCount (phaseLookupSkeleton (w1 + w2)) := by
  rw [toffoliCount_splitPhaseLookupSkeleton, toffoliCount_phaseLookupSkeleton]
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ w1 = c + 2 :=
    ⟨2 ^ w1 - 2, by
      have h2 : (2 : Nat) ^ 1 ≤ 2 ^ w1 := Nat.pow_le_pow_right (by norm_num) hw1
      have h2' : (2 : Nat) ^ 1 = 2 := by norm_num
      omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ w2 = d + 4 :=
    ⟨2 ^ w2 - 4, by
      have h2 : (2 : Nat) ^ 2 ≤ 2 ^ w2 := Nat.pow_le_pow_right (by norm_num) hw2
      have h2' : (2 : Nat) ^ 2 = 4 := by norm_num
      omega⟩
  have hpow : (2 : Nat) ^ (w1 + w2) = 2 ^ w1 * 2 ^ w2 := pow_add 2 w1 w2
  have hexp : 2 ^ w1 * 2 ^ w2 = c * d + 4 * c + 2 * d + 8 := by rw [hc, hd]; ring
  omega

/-- **The equal-halves headline**: at `w1 = w2 = w/2` (any `w = 2k ≥ 4`),
    the split fixup is STRICTLY cheaper than the unsplit one. -/
theorem toffoliCount_split_halves_lt_unsplit (k base : Nat) (hk : 2 ≤ k) :
    toffoliCount (splitPhaseLookupSkeleton k k base)
      < toffoliCount (phaseLookupSkeleton (k + k)) :=
  toffoliCount_split_lt_unsplit k k base (by omega) hk

/-! ## §8. Smoke checks (w1 = w2 = 1, base = 5, dim = 7: ctrl at 0,
lo address at 1, lo ladder at 2, hi address at 3, hi ladder at 4,
one-hot wires at 5–6). -/

/-- Phase ON: address holds `v = 2` (lo = 0, hi = 1), table `F = [· = 2]`
    ⟹ phase `−1`. -/
example :
    uc_eval (splitPhaseLookup 7 (fun v => v == 2) 1 1 5)
        * f_to_vec 7 (fun p => p == 0 || p == 3)
      = (-1 : ℂ) • f_to_vec 7 (fun p => p == 0 || p == 3) := by
  have h := splitPhaseLookup_diagonal_addr 7 1 1 5 (fun v => v == 2) 2
    (fun p => p == 0 || p == 3) (by norm_num) (by norm_num) (by norm_num) rfl
    (fun i hi => by interval_cases i <;> decide)
    (fun i hi => by interval_cases i <;> decide)
    (fun h hh => by interval_cases h <;> decide)
  simpa using h

/-- Phase OFF: address holds `v = 1` (lo = 1, hi = 0), table `F = [· = 2]`
    ⟹ identity. -/
example :
    uc_eval (splitPhaseLookup 7 (fun v => v == 2) 1 1 5)
        * f_to_vec 7 (fun p => p == 0 || p == 1)
      = f_to_vec 7 (fun p => p == 0 || p == 1) := by
  have h := splitPhaseLookup_diagonal_addr 7 1 1 5 (fun v => v == 2) 1
    (fun p => p == 0 || p == 1) (by norm_num) (by norm_num) (by norm_num) rfl
    (fun i hi => by interval_cases i <;> decide)
    (fun i hi => by interval_cases i <;> decide)
    (fun h hh => by interval_cases h <;> decide)
  simpa using h

/-- Count smoke (w = 4 split as 2+2): split = 4·3 + 2·3 = 18 Toffolis,
    unsplit = 2·15 = 30. -/
example : toffoliCount (splitPhaseLookupSkeleton 2 2 9) = 18 := by
  rw [toffoliCount_splitPhaseLookupSkeleton]; norm_num
example : toffoliCount (phaseLookupSkeleton 4) = 30 := by
  rw [toffoliCount_phaseLookupSkeleton]; norm_num
example : toffoliCount (splitPhaseLookupSkeleton 2 2 9)
    < toffoliCount (phaseLookupSkeleton 4) :=
  toffoliCount_split_halves_lt_unsplit 2 9 (by norm_num)

end -- noncomputable section

end FormalRV.Shor.SplitPhaseFixup
