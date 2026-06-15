/-
  FormalRV.Shor.PhaseLookupFixup — the CONCRETE phase-lookup fixup circuit for
  Gidney's measurement-based LOOKUP-uncompute, discharging the abstract `hP`
  hypothesis of `FormalRV.Shor.MeasuredLookupUncompute.measWordUncompute_qrom`.

  ## What this file builds

  `MeasuredLookupUncompute` proved the channel theorem with an ABSTRACT per-bit
  phase fixup `P j : BaseUCom dim` assumed diagonal:

      `uc_eval (P j) * |f⟩ = (-1)^((T (decAddr f)).testBit j) • |f⟩`.

  This file constructs the circuit family realizing it: `phaseLookup dim w F`,
  a BaseUCom-level PHASE walk that mirrors the Gate-level Gray-code/sawtooth
  QROM read (`UnaryLookupGrayCode.grayWalk`) — same ENTER-CCX / switch-CX /
  EXIT-CCX skeleton on the same wires (`ulookup_ctrl_idx`,
  `ulookup_address_idx i`, `ulookup_and_idx i`) — but where the leaf for table
  row `v` emits `Z ladderTop` exactly when the phase bit `F v` is set, instead
  of the read's word-CNOTs.  Since the ladder-top wire at row `v`'s leaf holds
  `ctrl ∧ [address = v]`, the product over all leaves is the single phase
  `(-1)^(ctrl ∧ F(address))` and the state is restored — `phaseWalk_diagonal`.

  ## The `hP` mismatch, and the guarded adapter (NO change to the channel file)

  `measWordUncompute_qrom`'s `hP` demands the diagonal action on ALL basis
  states `f` — including states whose AND-ladder ancillas are dirty.  No
  address-driven circuit on this wire layout can satisfy that for a general
  table: on a ladder-dirty state the walk's leaves fire on a COMPLEMENTED
  selection pattern, so the acquired phase is an XOR of SEVERAL table rows,
  not `T[addr]`.  (The abstract hypothesis is simply stronger than any real
  ancilla-using circuit can be.)  We therefore prove, in THIS file:

    * `phaseLookup_diagonal` — the diagonal action for every `f` whose ladder
      ancillas are clean (ctrl and address arbitrary; the acquired phase is
      `ctrl ∧ F(decAddr f)`), and
    * `measWordUncompute_perfect_guarded` — the channel headline re-derived
      with `hP` GUARDED by a predicate `Good` that holds on the input family
      and is preserved by word-bit updates (the only states the channel ever
      feeds to `P j`).  The proof reuses the PUBLIC building blocks of the
      channel file (`measBitUncompute_pure_step`, `measAND_branch0`,
      `clearWord_apply_ne`, `phase_clearWord`) and replays the two short
      branch-1 lemmas with the guard threaded through.
    * `measWordUncompute_phaseLookup` — the END-TO-END corollary: the channel
      with `P j := phaseLookup dim w (fun v => (T v).testBit j)` perfectly
      uncomputes the QROM word register on every lookup-computed family whose
      ctrl is set and ladder is clean.

  ## Cost (honest)

  The classical skeleton of the UNSPLIT phase walk is the gray walk's:
  `14·(2^w − 1)` T-gates (`tcount_phaseLookupSkeleton`; one ENTER + one EXIT
  Toffoli per internal node).  The inserted leaf `Z`s are Clifford (T-free).
  So the unsplit fixup costs ~one full table read — the measurement-based
  uncompute by itself only removes the EXIT-half of the SECOND read.  The
  `O(2^(w/2))` fixup that Gidney–Ekerå actually charge requires the SPLIT
  (one-hot hi-half + CZ-leaf lo-walk) construction — designed at the bottom
  of this file (§7) and deliberately NOT claimed here.
-/
import FormalRV.Shor.MeasuredLookupUncompute
import FormalRV.Arithmetic.UnaryLookup.UnaryLookupGrayCode

namespace FormalRV.Shor.PhaseLookupFixup

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Framework.BaseCom
open FormalRV.Framework.BaseUCom (proj)
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.MeasuredANDUncompute
open FormalRV.Shor.MeasuredLookupUncompute
open Matrix

noncomputable section

/-! ## §0. Boolean helper (the sawtooth switch, re-derived: the gray-file
    original is `private`). -/

/-- SWITCH-line algebra: with the ladder ancilla holding `P ∧ ¬b`, XOR-ing the
    parent `P` in (the sawtooth CX) leaves `P ∧ b`. -/
theorem phase_switch (P b : Bool) : xor (P && !b) P = (P && b) := by
  cases P <;> cases b <;> rfl

/-! ## §1. The address decoder `decAddr`: the number held in the address wires.

`decAddrFrom f i d` reads address wires `i, …, i+d−1` in place (bit `ℓ`
contributes `2^ℓ`), mirroring `grayMidBits` with `f (ulookup_address_idx ℓ)`
in place of `v.testBit ℓ`. -/

/-- The in-place value of address wires `i, …, i+d−1` of the state `f`. -/
def decAddrFrom (f : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | i, d + 1 =>
      (if f (ulookup_address_idx i) then 2 ^ i else 0) + decAddrFrom f (i + 1) d

/-- The full `w`-bit address held by the state `f` — the decoder the channel's
    `decAddr` parameter instantiates to. -/
def decAddr (w : Nat) (f : Nat → Bool) : Nat := decAddrFrom f 0 w

/-- `decAddrFrom` only reads the address wires at levels `i, …, i+d−1`. -/
theorem decAddrFrom_congr (f g : Nat → Bool) (d : Nat) :
    ∀ i, (∀ ℓ, i ≤ ℓ → ℓ < i + d →
            f (ulookup_address_idx ℓ) = g (ulookup_address_idx ℓ)) →
      decAddrFrom f i d = decAddrFrom g i d := by
  induction d with
  | zero => intro i _; rfl
  | succ d ih =>
      intro i h
      simp only [decAddrFrom]
      rw [h i (Nat.le_refl i) (by omega),
          ih (i + 1) (fun ℓ h1 h2 => h ℓ (by omega) (by omega))]

/-- On a state whose address wires hold the bits of `v`, the decoder reads the
    mid-bits of `v`. -/
theorem decAddrFrom_eq_grayMidBits (f : Nat → Bool) (v : Nat) (d : Nat) :
    ∀ i, (∀ ℓ, i ≤ ℓ → ℓ < i + d → f (ulookup_address_idx ℓ) = v.testBit ℓ) →
      decAddrFrom f i d = grayMidBits v i d := by
  induction d with
  | zero => intro i _; rfl
  | succ d ih =>
      intro i h
      simp only [decAddrFrom, grayMidBits]
      rw [h i (Nat.le_refl i) (by omega),
          ih (i + 1) (fun ℓ h1 h2 => h ℓ (by omega) (by omega))]

/-- On a state whose address wires hold the bits of `v < 2^w`, `decAddr` reads
    exactly `v`. -/
theorem decAddr_eq (w : Nat) (f : Nat → Bool) (v : Nat) (hv : v < 2 ^ w)
    (haddr : ∀ i, i < w → f (ulookup_address_idx i) = v.testBit i) :
    decAddr w f = v := by
  rw [decAddr, decAddrFrom_eq_grayMidBits f v w 0 (fun ℓ _ h2 => haddr ℓ (by omega)),
      grayMidBits_eq_self v w hv]

/-- `decAddr` is untouched by updates away from the address wires. -/
theorem decAddr_update_ne (w : Nat) (f : Nat → Bool) (q : Nat) (v : Bool)
    (hq : ∀ i, i < w → q ≠ ulookup_address_idx i) :
    decAddr w (update f q v) = decAddr w f :=
  decAddrFrom_congr _ _ w 0 (fun ℓ _ h2 =>
    update_neq _ _ _ _ (Ne.symm (hq ℓ (by omega))))

/-- `decAddr` is word-independent: any wire above the ctrl/address/ladder block
    (`2*w < q`, where the channel's word positions live) leaves it unchanged. -/
theorem decAddr_update_word (w : Nat) (f : Nat → Bool) (q : Nat)
    (hq : 2 * w < q) (v : Bool) :
    decAddr w (update f q v) = decAddr w f :=
  decAddr_update_ne w f q v (fun i hi => by
    have hA : ulookup_address_idx i = 1 + 2 * i := rfl
    omega)

/-! ## §2. The circuit: the BaseUCom-level phase walk.

Mirror of the Gate-level `grayWalk` (same ENTER / SWITCH / EXIT segments on the
same wires), with the leaf action `Z ladderTop` when the row's phase bit is set
(instead of the read's word-CNOT layer). -/

/-- The ENTER segment of one internal node at level `i` (Gate-level, identical
    to the gray walk's): `X a_i ; CCX parent a_i and_i ; X a_i` — XORs
    `parent ∧ ¬a_i` into the ladder wire `and_i`. -/
def enterSeg (i parent : Nat) : Gate :=
  Gate.seq (Gate.seq
    (Gate.X (ulookup_address_idx i))
    (Gate.CCX parent (ulookup_address_idx i) (ulookup_and_idx i)))
    (Gate.X (ulookup_address_idx i))

/-- The ENTER segment collapsed to a single ladder-wire update (the X-pair
    conjugation restores the address wire; mirror of the gray file's private
    `grayEnter_state`). -/
theorem enterSeg_applyNat (i parent : Nat) (hpar : parent ≤ 2 * i) (f : Nat → Bool) :
    Gate.applyNat (enterSeg i parent) f
      = update f (ulookup_and_idx i)
          (xor (f (ulookup_and_idx i))
               (f parent && !f (ulookup_address_idx i))) := by
  have hA : ulookup_address_idx i = 1 + 2 * i := rfl
  have hC : ulookup_and_idx i = 1 + 2 * i + 1 := rfl
  have hCA : ulookup_and_idx i ≠ ulookup_address_idx i := by omega
  have hAC : ulookup_address_idx i ≠ ulookup_and_idx i := by omega
  have hPA : parent ≠ ulookup_address_idx i := by omega
  funext q
  simp only [enterSeg, Gate.applyNat_seq, Gate.applyNat_X, Gate.applyNat_CCX]
  rw [update_neq _ _ _ _ hCA,                     -- (update f A _) C   = f C
      update_neq _ _ _ _ hPA,                     -- (update f A _) par = f parent
      update_eq]                                  -- (update f A _) A   = !f A
  by_cases hqA : q = ulookup_address_idx i
  · subst hqA
    rw [update_neq _ _ _ _ hAC, update_eq, update_eq, update_neq _ _ _ _ hAC,
        Bool.not_not]
  · rw [update_neq _ _ _ _ hAC, update_eq, update_neq _ _ _ _ hqA]
    by_cases hqC : q = ulookup_and_idx i
    · subst hqC
      rw [update_eq, update_eq]
    · rw [update_neq _ _ _ _ hqC, update_neq _ _ _ _ hqA, update_neq _ _ _ _ hqC]

/-- **The phase walk** (BaseUCom level).  `phaseWalk dim F d i parent vPrefix`
    is the subtree at ladder level `i` with `d` levels remaining, parent wire
    `parent`, and path-accumulated row prefix `vPrefix` — exactly the gray
    walk's recursion, with the leaf emitting `Z parent` when `F vPrefix` is set
    (and nothing otherwise).  The three classical segments are the Gate-level
    pieces, embedded via `Gate.toUCom`. -/
def phaseWalk (dim : Nat) (F : Nat → Bool) :
    Nat → Nat → Nat → Nat → BaseUCom dim
  | 0, _, parent, vPrefix =>
      if F vPrefix then BaseUCom.Z parent else BaseUCom.ID 0
  | d + 1, i, parent, vPrefix =>
      UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (Gate.toUCom dim (enterSeg i parent))
        (phaseWalk dim F d (i + 1) (ulookup_and_idx i) vPrefix))
        (Gate.toUCom dim (Gate.CX parent (ulookup_and_idx i))))
        (phaseWalk dim F d (i + 1) (ulookup_and_idx i) (vPrefix + 2 ^ i)))
        (Gate.toUCom dim
          (Gate.CCX parent (ulookup_address_idx i) (ulookup_and_idx i)))

/-- **The phase lookup**: the full-depth phase walk rooted at the ctrl wire —
    the per-bit fixup `P j` of the measured lookup-uncompute, with phase table
    `F := fun v => (T v).testBit j`. -/
def phaseLookup (dim w : Nat) (F : Nat → Bool) : BaseUCom dim :=
  phaseWalk dim F w 0 ulookup_ctrl_idx 0

/-! ## §3. Diagonal action.

**The subtree invariant** (`phaseWalk_diagonal`): on ANY basis state `f` whose
ladder wires at the remaining levels are clean, the subtree is DIAGONAL with
phase `(-1)^(f parent ∧ F(vPrefix + ⟨address wires i..i+d−1⟩))` — no
constraint on ctrl or the address wires (the selected leaf is read off `f`
itself, via `decAddrFrom`).  Induction on the remaining depth `d`: the
classical segments act phase-free on basis states (`uc_eval_toUCom_acts_on_basis`),
the ENTER/SWITCH bookkeeping puts `P ∧ ¬a_i` / `P ∧ a_i` on the ladder wire for
the two subtrees, and the EXIT Toffoli restores it. -/

theorem phaseWalk_diagonal (dim : Nat) (F : Nat → Bool) (d : Nat) :
    ∀ (i parent vPrefix : Nat) (f : Nat → Bool),
      parent ≤ 2 * i →
      2 * (i + d) < dim →
      (∀ ℓ, i ≤ ℓ → ℓ < i + d → f (ulookup_and_idx ℓ) = false) →
      uc_eval (phaseWalk dim F d i parent vPrefix) * f_to_vec dim f
        = (if f parent && F (vPrefix + decAddrFrom f i d) then (-1 : ℂ) else 1)
            • f_to_vec dim f := by
  induction d with
  | zero =>
      intro i parent vPrefix f hpar hdim _
      simp only [phaseWalk, decAddrFrom, Nat.add_zero]
      by_cases hF : F vPrefix = true
      · rw [if_pos hF]
        simp only [hF, Bool.and_true]
        exact f_to_vec_Z_uc_eval dim parent (by omega) f
      · rw [if_neg hF]
        rw [Bool.not_eq_true] at hF
        simp only [hF, Bool.and_false, Bool.false_eq_true, if_false,
            uc_eval_ID_eq_one (show 0 < dim by omega), Matrix.one_mul, one_smul]
  | succ d ih =>
      intro i parent vPrefix f hpar hdim hand
      have hA : ulookup_address_idx i = 1 + 2 * i := rfl
      have hC : ulookup_and_idx i = 1 + 2 * i + 1 := rfl
      have hfc : f (ulookup_and_idx i) = false := hand i (Nat.le_refl i) (by omega)
      have hPC : parent ≠ ulookup_and_idx i := by omega
      have hAC : ulookup_address_idx i ≠ ulookup_and_idx i := by omega
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
      -- the decoder never reads the (even-numbered) ladder wires
      have hdec3 : decAddrFrom g3 (i + 1) d = decAddrFrom f (i + 1) d := by
        refine decAddrFrom_congr _ _ d (i + 1) (fun ℓ h1 h2 => ?_)
        have e1 : ulookup_address_idx ℓ = 1 + 2 * ℓ := rfl
        rw [hg3, update_neq _ _ _ _ (by omega)]
      have hdec5 : decAddrFrom g5 (i + 1) d = decAddrFrom f (i + 1) d := by
        refine decAddrFrom_congr _ _ d (i + 1) (fun ℓ h1 h2 => ?_)
        have e1 : ulookup_address_idx ℓ = 1 + 2 * ℓ := rfl
        rw [hg5, update_neq _ _ _ _ (by omega)]
      -- EXIT clears the ladder wire back to `f`
      have hclear : update g5 (ulookup_and_idx i) false = f := by
        rw [hg5, update_idem, ← hfc, update_self]
      -- the five-stage pipeline
      simp only [phaseWalk, uc_eval_seq_mul]
      -- ENTER
      rw [uc_eval_toUCom_acts_on_basis dim _ hwtE f,
          enterSeg_applyNat i parent hpar f, hfc, Bool.false_xor, ← hg3]
      -- 0-subtree (IH at parent' = the ladder wire, prefix unchanged)
      rw [ih (i + 1) (ulookup_and_idx i) vPrefix g3 (by omega) (by omega) hand3,
          hg3_C, hdec3]
      simp only [Matrix.mul_smul]
      -- SWITCH (the sawtooth CX)
      rw [uc_eval_toUCom_acts_on_basis dim _ hwtS g3, Gate.applyNat_CX,
          hg3_C, hg3_par, phase_switch, hg3, update_idem, ← hg5]
      -- 1-subtree (IH at prefix + 2^i)
      rw [ih (i + 1) (ulookup_and_idx i) (vPrefix + 2 ^ i) g5 (by omega) (by omega)
            hand5, hg5_C, hdec5]
      simp only [Matrix.mul_smul]
      -- EXIT
      rw [uc_eval_toUCom_acts_on_basis dim _ hwtX g5, Gate.applyNat_CCX,
          hg5_C, hg5_par, hg5_A, Bool.xor_self, hclear]
      -- combine the two ±1 phases: exactly one subtree was selected
      simp only [decAddrFrom]
      rcases Bool.eq_false_or_eq_true (f (ulookup_address_idx i)) with hbv | hbv <;>
        simp [hbv, Nat.add_assoc]

/-- **HEADLINE (diagonal action, decoder form)**: on EVERY basis state `f`
    whose AND-ladder ancillas are clean, the phase lookup is diagonal with
    phase `(-1)^(ctrl ∧ F(decAddr f))` — ctrl and address arbitrary, word
    register never touched (it isn't even wired in). -/
theorem phaseLookup_diagonal (dim w : Nat) (F : Nat → Bool) (f : Nat → Bool)
    (hdim : 2 * w < dim)
    (hand : ∀ i, i < w → f (ulookup_and_idx i) = false) :
    uc_eval (phaseLookup dim w F) * f_to_vec dim f
      = (if f ulookup_ctrl_idx && F (decAddr w f) then (-1 : ℂ) else 1)
          • f_to_vec dim f := by
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  have h := phaseWalk_diagonal dim F w 0 ulookup_ctrl_idx 0 f
    (by omega) (by omega) (fun ℓ _ h2 => hand ℓ (by omega))
  rw [phaseLookup, h, Nat.zero_add, decAddr]

/-- **HEADLINE (diagonal action, address form)** — the shape the prompt-level
    contract asks for: ctrl set, address holding `v < 2^w`, ladder clean ⟹
    the phase lookup applies exactly `(-1)^(F v)`. -/
theorem phaseLookup_diagonal_addr (dim w : Nat) (F : Nat → Bool) (v : Nat)
    (f : Nat → Bool)
    (hdim : 2 * w < dim) (hv : v < 2 ^ w)
    (hctrl : f ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w → f (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w → f (ulookup_and_idx i) = false) :
    uc_eval (phaseLookup dim w F) * f_to_vec dim f
      = (if F v then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [phaseLookup_diagonal dim w F f hdim hand, hctrl, Bool.true_and,
      decAddr_eq w f v hv haddr]

/-! ## §4. Cost: the Gate-level skeleton twin.

`phaseWalk` is the gray walk's classical skeleton with `Z`s (Clifford, T-free)
inserted at the leaves; `BaseUCom` carries no T-counter, so we state the count
on the literal Gate-level twin (same ENTER/SWITCH/EXIT segments, `I` leaves):
`14·(2^w − 1)` T = `2·(2^w − 1)` Toffolis — ~one full Gray-code table read
(`tcount_grayLookupReadAt`).  The honest reading: the UNSPLIT fixup does NOT
yet realize Gidney's `O(2^(w/2))`; that needs the split construction (§7). -/

/-- The Gate-level classical skeleton of `phaseWalk` (leaves = `I`; the leaf
    `Z`s of the real walk are Clifford and contribute no T). -/
def phaseWalkSkeleton : Nat → Nat → Nat → Gate
  | 0, _, _ => Gate.I
  | d + 1, i, parent =>
      Gate.seq (Gate.seq (Gate.seq (Gate.seq
        (enterSeg i parent)
        (phaseWalkSkeleton d (i + 1) (ulookup_and_idx i)))
        (Gate.CX parent (ulookup_and_idx i)))
        (phaseWalkSkeleton d (i + 1) (ulookup_and_idx i)))
        (Gate.CCX parent (ulookup_address_idx i) (ulookup_and_idx i))

/-- The full-depth skeleton, rooted at the ctrl wire (twin of `phaseLookup`). -/
def phaseLookupSkeleton (w : Nat) : Gate := phaseWalkSkeleton w 0 ulookup_ctrl_idx

/-- T-count of the skeleton subtree: one ENTER + one EXIT Toffoli (`14` T) per
    internal node, `2^d − 1` internal nodes. -/
theorem tcount_phaseWalkSkeleton (d : Nat) : ∀ (i parent : Nat),
    tcount (phaseWalkSkeleton d i parent) = 14 * (2 ^ d - 1) := by
  induction d with
  | zero => intro i parent; rfl
  | succ d ih =>
      intro i parent
      have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
      have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
      simp only [phaseWalkSkeleton, enterSeg, tcount, ih]
      omega

/-- **T-count of the (unsplit) phase-lookup fixup skeleton**: `14·(2^w − 1)` —
    the same as a full Gray-code table read. -/
theorem tcount_phaseLookupSkeleton (w : Nat) :
    tcount (phaseLookupSkeleton w) = 14 * (2 ^ w - 1) :=
  tcount_phaseWalkSkeleton w 0 ulookup_ctrl_idx

/-- **Toffoli count of the (unsplit) phase-lookup fixup skeleton**:
    `2·(2^w − 1)`. -/
theorem toffoliCount_phaseLookupSkeleton (w : Nat) :
    toffoliCount (phaseLookupSkeleton w) = 2 * (2 ^ w - 1) := by
  rw [toffoliCount, tcount_phaseLookupSkeleton,
      show 14 * (2 ^ w - 1) = 2 * (2 ^ w - 1) * 7 from by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- The unsplit fixup skeleton costs exactly one Gray-code table read. -/
theorem tcount_phaseLookupSkeleton_eq_grayRead
    (w W : Nat) (pos : Nat → Nat) (T : Nat → Nat) :
    tcount (phaseLookupSkeleton w) = tcount (grayLookupReadAt w pos W T) := by
  rw [tcount_phaseLookupSkeleton, tcount_grayLookupReadAt]

/-! ## §5. The guarded channel adapter.

`measWordUncompute_qrom`'s `hP` quantifies over ALL `f` — stronger than any
ancilla-using circuit satisfies (see the module docstring).  The channel proof
only ever invokes `hP` at states of the form
`update (clearWord pos j (g i)) (pos j) true` — word-bit updates of the input
family.  So we re-derive the headline with `hP` guarded by ANY predicate
`Good` that (a) holds on the family and (b) is preserved by word-bit updates,
replaying the two short branch-1 lemmas of `MeasuredLookupUncompute` with the
guard threaded through, and reusing its public machinery for everything else
(`measAND_branch0`, `measBitUncompute_pure_step`, `clearWord_apply_ne`,
`phase_clearWord`).  `MeasuredLookupUncompute` itself is NOT modified. -/

/-- Guarded mirror of `measBit_branch1_basis`: the diagonal action of `P` is
    only required at the single state it is invoked at, `update f q true`. -/
theorem measBit_branch1_basis_guarded {dim : Nat} (q : Nat) (hq : q < dim)
    (P : BaseUCom dim) (φj : (Nat → Bool) → Bool) (f : Nat → Bool)
    (hP1 : uc_eval P * f_to_vec dim (update f q true)
            = (if φj (update f q true) then (-1 : ℂ) else 1)
                • f_to_vec dim (update f q true))
    (hφ : ∀ v, φj (update f q v) = φj f)
    (hf : f q = φj f) :
    uc_eval (BaseUCom.X q : BaseUCom dim)
        * (uc_eval P
          * (proj q dim true * (uc_eval (BaseUCom.H q : BaseUCom dim) * f_to_vec dim f)))
      = (Real.sqrt 2 / 2 : ℂ) • f_to_vec dim (update f q false) := by
  rw [f_to_vec_H_uc_eval dim q hq f, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      proj_true_on_f_to_vec dim q hq, proj_true_on_f_to_vec dim q hq]
  simp only [update_eq, Bool.false_eq_true, if_true, if_false, smul_zero, zero_add]
  rw [Matrix.mul_smul, hP1, hφ true]
  rw [Matrix.mul_smul, Matrix.mul_smul, f_to_vec_X_uc_eval dim q hq (update f q true)]
  simp only [update_idem, update_eq, Bool.not_true]
  rw [hf, smul_smul]
  cases h : φj f <;> simp

/-- Guarded mirror of `measBit_branch1` (superposition form): `Good` need only
    hold at the bit-`q`-set states of the family. -/
theorem measBit_branch1_guarded {dim : Nat} {ι : Type*} (q : Nat) (hq : q < dim)
    (P : BaseUCom dim) (φj : (Nat → Bool) → Bool) (Good : (Nat → Bool) → Prop)
    (hP : ∀ f, Good f → uc_eval P * f_to_vec dim f
            = (if φj f then (-1 : ℂ) else 1) • f_to_vec dim f)
    (hφ : ∀ f v, φj (update f q v) = φj f)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hbit : ∀ i ∈ s, g i q = φj (g i))
    (hgood : ∀ i ∈ s, Good (update (g i) q true)) :
    uc_eval (BaseUCom.X q : BaseUCom dim)
        * (uc_eval P
          * (proj q dim true * (uc_eval (BaseUCom.H q : BaseUCom dim)
            * ∑ i ∈ s, α i • f_to_vec dim (g i))))
      = (Real.sqrt 2 / 2 : ℂ) • ∑ i ∈ s, α i • f_to_vec dim (update (g i) q false) := by
  rw [Matrix.mul_sum, Matrix.mul_sum, Matrix.mul_sum, Matrix.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      measBit_branch1_basis_guarded q hq P φj (g i)
        (hP _ (hgood i hi)) (fun v => hφ (g i) v) (hbit i hi)]
  exact smul_comm _ _ _

/-- Guarded mirror of `measBitUncompute_perfect`: one `H + meas + fixup + X`
    step clears word bit `q`, with `P`'s diagonal action only assumed on
    `Good` states. -/
theorem measBitUncompute_perfect_guarded {dim : Nat} {ι : Type*} (q : Nat)
    (hq : q < dim)
    (P : BaseUCom dim) (φj : (Nat → Bool) → Bool) (Good : (Nat → Bool) → Prop)
    (hP : ∀ f, Good f → uc_eval P * f_to_vec dim f
            = (if φj f then (-1 : ℂ) else 1) • f_to_vec dim f)
    (hφ : ∀ f v, φj (update f q v) = φj f)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hbit : ∀ i ∈ s, g i q = φj (g i))
    (hgood : ∀ i ∈ s, Good (update (g i) q true)) :
    c_eval (measBitUncompute dim q P)
        ((∑ i ∈ s, α i • f_to_vec dim (g i))
          * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (update (g i) q false))
          * (∑ i ∈ s, α i • f_to_vec dim (update (g i) q false))ᴴ :=
  measBitUncompute_pure_step q P _ _
    (measAND_branch0 q hq s α g)
    (measBit_branch1_guarded q hq P φj Good hP hφ s α g hbit hgood)

/-- A word-update-closed predicate holds on the word-cleared family. -/
theorem clearWord_good {Good : (Nat → Bool) → Prop} (pos : Nat → Nat) (W : Nat)
    (hupd : ∀ f, Good f → ∀ k, k < W → ∀ v, Good (update f (pos k) v))
    (f : Nat → Bool) (hf : Good f) : Good (clearWord pos W f) := by
  induction W with
  | zero => exact hf
  | succ W ih =>
      exact hupd _
        (ih (fun f hf k hk v => hupd f hf k (Nat.lt_succ_of_lt hk) v))
        W (Nat.lt_succ_self W) false

/-- **Guarded channel headline** — `measWordUncompute_perfect` with the
    per-bit fixup's diagonal action (`hP`) required only on a word-update-
    closed `Good` set containing the input family.  Same conclusion: the
    channel is the PERFECT uncompute on the lookup-computed family. -/
theorem measWordUncompute_perfect_guarded {dim : Nat} {ι : Type*} (W : Nat)
    (pos : Nat → Nat) (P : Nat → BaseUCom dim) (φ : Nat → (Nat → Bool) → Bool)
    (Good : (Nat → Bool) → Prop)
    (hpos : ∀ j, j < W → pos j < dim)
    (hinj : ∀ j, j < W → ∀ k, k < W → j ≠ k → pos j ≠ pos k)
    (hP : ∀ j, j < W → ∀ f, Good f → uc_eval (P j) * f_to_vec dim f
            = (if φ j f then (-1 : ℂ) else 1) • f_to_vec dim f)
    (hφ : ∀ j, j < W → ∀ k, k < W → ∀ f v, φ j (update f (pos k) v) = φ j f)
    (hGoodUpd : ∀ f, Good f → ∀ k, k < W → ∀ v, Good (update f (pos k) v))
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hgood : ∀ i ∈ s, Good (g i))
    (hword : ∀ i ∈ s, ∀ j, j < W → g i (pos j) = φ j (g i)) :
    c_eval (measWordUncompute dim pos P W)
        ((∑ i ∈ s, α i • f_to_vec dim (g i))
          * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))
          * (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))ᴴ := by
  induction W with
  | zero => simp only [measWordUncompute, clearWord, c_eval_skip]
  | succ W ih =>
      -- IH: the first W bits are cleared.
      have hψW := ih (fun j hj => hpos j (Nat.lt_succ_of_lt hj))
        (fun j hj k hk => hinj j (Nat.lt_succ_of_lt hj) k (Nat.lt_succ_of_lt hk))
        (fun j hj => hP j (Nat.lt_succ_of_lt hj))
        (fun j hj k hk => hφ j (Nat.lt_succ_of_lt hj) k (Nat.lt_succ_of_lt hk))
        (fun f hf k hk => hGoodUpd f hf k (Nat.lt_succ_of_lt hk))
        (fun i hi j hj => hword i hi j (Nat.lt_succ_of_lt hj))
      simp only [measWordUncompute, c_eval_useq]
      rw [hψW]
      -- Per-qubit step on the partially-cleared family.
      have hstep := measBitUncompute_perfect_guarded (pos W)
        (hpos W (Nat.lt_succ_self W)) (P W) (φ W) Good
        (hP W (Nat.lt_succ_self W))
        (fun f v => hφ W (Nat.lt_succ_self W) W (Nat.lt_succ_self W) f v)
        s α (fun i => clearWord pos W (g i))
        (fun i hi => by
          -- The partially-cleared family still satisfies bit W's hypothesis.
          show clearWord pos W (g i) (pos W) = φ W (clearWord pos W (g i))
          rw [clearWord_apply_ne pos W (g i) (pos W)
                (fun k hk => hinj W (Nat.lt_succ_self W) k (Nat.lt_succ_of_lt hk)
                  (Nat.ne_of_lt hk).symm),
              phase_clearWord pos W (φ W)
                (fun k hk f v =>
                  hφ W (Nat.lt_succ_self W) k (Nat.lt_succ_of_lt hk) f v)
                (g i)]
          exact hword i hi W (Nat.lt_succ_self W))
        (fun i hi => by
          -- The clearing keeps the family in the Good set; so does setting bit W.
          have h1 : Good (clearWord pos W (g i)) :=
            clearWord_good pos W
              (fun f hf k hk v => hGoodUpd f hf k (Nat.lt_succ_of_lt hk) v)
              (g i) (hgood i hi)
          exact hGoodUpd _ h1 W (Nat.lt_succ_self W) true)
      simpa only [clearWord] using hstep

/-! ## §6. END-TO-END: the channel with the CONCRETE phase-lookup fixups. -/

/-- The `Good` set for the phase lookup: ctrl wire set, AND-ladder clean.
    (Exactly the lookup's own operating conditions: the family the windowed
    pipeline feeds the uncompute satisfies it, and the channel's word-bit
    updates — at positions above `2*w` — never leave it.) -/
def GoodState (w : Nat) (f : Nat → Bool) : Prop :=
  f ulookup_ctrl_idx = true ∧ ∀ i, i < w → f (ulookup_and_idx i) = false

/-- `GoodState` is closed under updates above the ctrl/address/ladder block. -/
theorem GoodState_update_word (w : Nat) (f : Nat → Bool) (q : Nat)
    (hq : 2 * w < q) (v : Bool) (hf : GoodState w f) :
    GoodState w (update f q v) := by
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  refine ⟨?_, fun i hi => ?_⟩
  · rw [update_neq _ _ _ _ (show ulookup_ctrl_idx ≠ q by omega)]
    exact hf.1
  · have hC : ulookup_and_idx i = 1 + 2 * i + 1 := rfl
    rw [update_neq _ _ _ _ (show ulookup_and_idx i ≠ q by omega)]
    exact hf.2 i hi

/-- **The `hP` discharge**: on every `GoodState`, the per-bit phase lookup
    `phaseLookup dim w (fun v => (T v).testBit j)` has EXACTLY the diagonal
    action `measWordUncompute_qrom` postulates for `P j`, with the concrete
    decoder `decAddr`. -/
theorem phaseLookup_discharges_hP (dim w : Nat) (T : Nat → Nat) (j : Nat)
    (hdim : 2 * w < dim) (f : Nat → Bool) (hf : GoodState w f) :
    uc_eval (phaseLookup dim w (fun v => (T v).testBit j)) * f_to_vec dim f
      = (if (T (decAddr w f)).testBit j then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [phaseLookup_diagonal dim w _ f hdim hf.2, hf.1, Bool.true_and]

/-- **END-TO-END HEADLINE**: Gidney's measurement-based lookup-uncompute with
    the CONCRETE per-bit phase-lookup fixups
    `P j := phaseLookup dim w (fun v => (T v).testBit j)` is the perfect
    uncompute on every lookup-computed family (ctrl set, ladder clean, word
    bit `j` holding `T[addr].bit j` on the support): coefficients intact, all
    `W` word bits released as `|0…0⟩`, no second lookup.  This closes the
    abstract-`hP` gap of `measWordUncompute_qrom` with an actual circuit. -/
theorem measWordUncompute_phaseLookup {dim : Nat} {ι : Type*} (w W : Nat)
    (pos : Nat → Nat) (T : Nat → Nat)
    (hdim : 2 * w < dim)
    (hpos : ∀ j, j < W → pos j < dim)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (hinj : ∀ j, j < W → ∀ k, k < W → j ≠ k → pos j ≠ pos k)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hgood : ∀ i ∈ s, GoodState w (g i))
    (hword : ∀ i ∈ s, ∀ j, j < W →
        g i (pos j) = (T (decAddr w (g i))).testBit j) :
    c_eval (measWordUncompute dim pos
        (fun j => phaseLookup dim w (fun v => (T v).testBit j)) W)
        ((∑ i ∈ s, α i • f_to_vec dim (g i))
          * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))
          * (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))ᴴ :=
  measWordUncompute_perfect_guarded W pos _
    (fun j f => (T (decAddr w f)).testBit j) (GoodState w)
    hpos hinj
    (fun j _ f hf => phaseLookup_discharges_hP dim w T j hdim f hf)
    (fun j _ k hk f v => by
      show (T (decAddr w (update f (pos k) v))).testBit j = _
      rw [decAddr_update_word w f (pos k) (hpos_high k hk) v])
    (fun f hf k hk v => GoodState_update_word w f (pos k) (hpos_high k hk) v hf)
    s α g hgood hword

/-! ### Smoke checks (w = 1, dim = 3: ctrl at 0, address at 1, ladder at 2). -/

/-- Phase ON: address holds `v = 1`, table `F = [· = 1]` ⟹ phase `−1`. -/
example :
    uc_eval (phaseLookup 3 1 (fun v => v == 1))
        * f_to_vec 3 (fun p => p == 0 || p == 1)
      = (-1 : ℂ) • f_to_vec 3 (fun p => p == 0 || p == 1) := by
  have h := phaseLookup_diagonal_addr 3 1 (fun v => v == 1) 1
    (fun p => p == 0 || p == 1) (by norm_num) (by norm_num) rfl
    (fun i hi => by interval_cases i; decide)
    (fun i hi => by interval_cases i; decide)
  simpa using h

/-- Phase OFF: address holds `v = 0`, table `F = [· = 1]` ⟹ identity. -/
example :
    uc_eval (phaseLookup 3 1 (fun v => v == 1)) * f_to_vec 3 (fun p => p == 0)
      = f_to_vec 3 (fun p => p == 0) := by
  have h := phaseLookup_diagonal_addr 3 1 (fun v => v == 1) 0
    (fun p => p == 0) (by norm_num) (by norm_num) rfl
    (fun i hi => by interval_cases i; decide)
    (fun i hi => by interval_cases i; decide)
  simpa using h

/-! ## §7. The SPLIT fixup (Gidney's `O(2^(w/2))`) — design, deliberately not
    built here.

Split the address `v = hi‖lo` with `lo` the low `w2` bits (address levels
`0..w2−1`) and `hi` the high `w1` bits (levels `w2..w−1`), `w = w1 + w2`.
Allocate `2^w1` fresh one-hot wires `oneHot h` above the word block.

**Circuit** (three stages):

1. ONE-HOT (classical): compute `oneHot h := ctrl ∧ [addr_hi = h]` for all
   `h < 2^w1`.  This is LITERALLY the existing Gate-level gray walk over the
   hi levels with the one-hot table:
   `grayWalk pos (2^w1) (fun x => 2^(x / 2^w2)) w1 w2 ulookup_ctrl_idx 0`
   (word positions `pos h := oneHot h`) — row `hi`'s word is `2^hi`, whose
   bit `h` is `[h = hi]`, so `grayWalk_selects_word` already proves the
   one-hot contract and `grayWalk_frame` the restoration.
   Cost: `2·(2^w1 − 1)` Toffolis.

2. LO PHASE WALK with CZ leaves (the only new circuit): a `phaseWalk`-shaped
   walk over the LO levels (`d = w2, i = 0`, rooted at ctrl) whose leaf for
   lo-row `ℓ` applies `CZ ladderTop (oneHot h)` for EACH `h < 2^w1` with
   `F (h·2^w2 + ℓ) = true`.  CZ's diagonal action (`f_to_vec_CZ`,
   `MeasuredANDUncompute`) gives leaf phase
   `(−1)^(ladderTop ∧ oneHot h) = (−1)^([addr_lo = ℓ]·ctrl·[addr_hi = h]·F(h‖ℓ))`,
   and the product over all leaves and all `h` telescopes to
   `(−1)^(ctrl ∧ F(addr))` — exactly one `(ℓ, h)` pair fires.
   Cost: `2·(2^w2 − 1)` Toffolis; ALL CZs are Clifford (T-free).

3. UN-ONE-HOT: stage 1 reversed (the same walk again — the leaf CXs are
   self-inverse XORs). Cost: `2·(2^w1 − 1)` Toffolis.

**Exact count this construction yields**:
`2·(2^w1 − 1) + 2·(2^w2 − 1) + 2·(2^w1 − 1) = 4·2^w1 + 2·2^w2 − 6` Toffolis,
i.e. `O(2^(w/2))` at `w1 = w2 = w/2` — vs the unsplit `2·(2^w − 1)`.
(Gidney–Ekerå's further-optimized constant `2^w1 + 2^w2` additionally
measurement-uncomputes the one-hot register; that leg lives at the channel
layer, like this file's §5.)

**Lemmas it needs** (beyond this file):
  * `Gate.WellTyped dim (grayWalk …)` + a WellTyped lemma for
    `cx_gates_from_indices` (to push stages 1/3 through
    `uc_eval_toUCom_acts_on_basis`);
  * a `czPhaseWalk_diagonal` mirroring `phaseWalk_diagonal`, with leaf case an
    induction over the CZ list using `f_to_vec_CZ`, stated on states whose
    one-hot wires are arbitrary (phase `ctrl ∧ ⊕_h (oneHot h ∧ F(h‖lo))`);
  * the three-stage composition: stage 1 is a basis-state permutation
    (`grayWalk_selects_word`/`grayWalk_frame` describe its `Gate.applyNat`),
    stage 2 is diagonal, stage 3 inverts stage 1, so the composite is diagonal
    with the stage-2 phase evaluated on the one-hot-computed state — which
    collapses to `(−1)^(ctrl ∧ F(addr))`;
  * the guarded-`hP` discharge then reuses §5 verbatim (only
    `phaseLookup_discharges_hP` changes its circuit). -/

end -- noncomputable section

end FormalRV.Shor.PhaseLookupFixup
