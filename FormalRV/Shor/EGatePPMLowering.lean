/-
  FormalRV.Shor.EGatePPMLowering
  ──────────────────────────────
  **LOWERING THE MEASUREMENT-AUGMENTED IR `EGate` TO A PPM PROGRAM.**

  `EGate` (`FormalRV.Shor.MeasUncompute`) is the reversible Gate IR plus a
  measurement-reset node:

      EGate = base (g : Gate) | mz (q : Nat) | seq

  with Boolean (value) semantics `mz q ↦ Function.update f q false` (measure
  qubit `q` and reset it to |0⟩ — the computational effect of Gidney/Berry
  measurement-based uncomputation).

  The existing rotation pipeline lowers the *reversible* fragment
  (`gateRots`, `lowerFlat`, `lowerGate_denote`).  This file adds the one new
  node: a measurement-reset lowers to **a Pauli-Z measurement followed by a
  classically-controlled X reset** —

      mz q  ↦  c = Measure Z[q] ;  if c == 1 then X[q]

  i.e. exactly a Pauli-product measurement plus a frame correction, the PPM
  primitives.  On a basis state this selects the consistent measurement
  branch (`outcome = bit q`) and clears qubit `q`, reproducing
  `EGate.applyNat (mz q)` ON THE NOSE (`lowerMz_denote_basis`).

  §1  the lowering `lowerEGate` (+ `lowerMz`, ancilla/slot bookkeeping);
  §2  resource preservation — `countMagicT (lowerEGate g) = EGate.tcount g`
      (the measured T-count survives lowering exactly; `mz` is magic-free);
  §3  the measurement node's semantic core on basis states.
-/
import FormalRV.PauliRotation.Compiler.ToPPM.GadgetLowering
import FormalRV.Shor.MeasUncompute

namespace FormalRV.PauliRotation.EGateLowering

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.Framework (Gate)
open FormalRV.Shor.MeasUncompute (EGate mzList)
open FormalRV.BQCode
open Matrix

/-! ## §1. The lowering. -/

/-- Fresh ancilla wires a sub-circuit consumes (one per π/4 and π/8 rotation
in its base parts; a measurement consumes none). -/
def eAnc : EGate → Nat
  | .base g  => ((gateRots g).map rotAnc).sum
  | .mz _    => 0
  | .seq a b => eAnc a + eAnc b

/-- Classical outcome slots a sub-circuit binds (two per π/4 and π/8
rotation; one per measurement-reset). -/
def eSlots : EGate → Nat
  | .base g  => ((gateRots g).map rotSlots).sum
  | .mz _    => 1
  | .seq a b => eSlots a + eSlots b

/-- **The measurement-reset block.**  `mz q` lowers to a Pauli-`Z`
measurement at slot `c` followed by the `X[q]` reset fired on outcome `1`. -/
def lowerMz (c q : Nat) : PPMProg :=
  [PPMStmt.measure c [⟨q, PKind.z⟩],
   PPMStmt.correct [c] [⟨q, PKind.x⟩] []]

/-- **`EGate → PPMProg`**, threading the fresh-ancilla counter `a` and the
next-outcome-slot counter `c`. -/
def lowerEGate (a c : Nat) : EGate → PPMProg
  | .base g  => lowerFlat a c (gateRots g)
  | .mz q    => lowerMz c q
  | .seq x y => lowerEGate a c x ++ lowerEGate (a + eAnc x) (c + eSlots x) y

/-! ## §2. Resource preservation. -/

theorem lowerMz_magicT (c q : Nat) : countMagicT (lowerMz c q) = 0 := rfl

theorem lowerMz_cwidth (c q : Nat) : PPMProg.cwidth (lowerMz c q) = 1 := rfl

/-- **THE COST-FAITHFUL KEYSTONE**: the lowered PPM program consumes exactly
`EGate.tcount g` magic-T states — the measured T-count survives the lowering
on the nose, and the measurement nodes are magic-free. -/
theorem lowerEGate_magicT (g : EGate) :
    ∀ (a c : Nat), countMagicT (lowerEGate a c g) = EGate.tcount g := by
  induction g with
  | base gg =>
      intro a c
      show countMagicT (lowerFlat a c (gateRots gg)) = EGate.tcount (.base gg)
      rw [lowerFlat_magicT]
      exact gateRots_countPi8 gg
  | mz q => intro a c; rfl
  | seq x y ihx ihy =>
      intro a c
      show countMagicT (lowerEGate a c x ++ lowerEGate (a + eAnc x) (c + eSlots x) y)
        = EGate.tcount (.seq x y)
      rw [countMagicT_append, ihx, ihy]
      rfl

/-- No CCZ magic states are consumed by this rotation-by-rotation route. -/
theorem lowerEGate_magicCCZ (g : EGate) :
    ∀ (a c : Nat), countMagicCCZ (lowerEGate a c g) = 0 := by
  induction g with
  | base gg =>
      intro a c
      show countMagicCCZ (lowerFlat a c (gateRots gg)) = 0
      exact lowerFlat_magicCCZ (gateRots gg) a c
  | mz q => intro a c; rfl
  | seq x y ihx ihy =>
      intro a c
      show countMagicCCZ (lowerEGate a c x ++ lowerEGate _ _ y) = 0
      rw [countMagicCCZ_append, ihx, ihy]

/-- The lowered program binds exactly `eSlots g` classical outcome slots. -/
theorem lowerEGate_cwidth (g : EGate) :
    ∀ (a c : Nat), PPMProg.cwidth (lowerEGate a c g) = eSlots g := by
  induction g with
  | base gg =>
      intro a c
      show PPMProg.cwidth (lowerFlat a c (gateRots gg)) = eSlots (.base gg)
      rw [lowerFlat_cwidth]; rfl
  | mz q => intro a c; rfl
  | seq x y ihx ihy =>
      intro a c
      show PPMProg.cwidth (lowerEGate a c x ++ lowerEGate _ _ y) = eSlots (.seq x y)
      rw [PPMProg.cwidth_append, ihx, ihy]; rfl

/-! ## §3. The measurement node, semantically (on basis states). -/

/-- Clearing bit `q` of a width-`m` basis index — the measurement-reset's
action on a computational basis state. -/
def clearBitFin (m q : Nat) (hq : q < m) (x : Fin (2 ^ m)) : Fin (2 ^ m) :=
  ⟨if (x : Nat).testBit q then (x : Nat) ^^^ 2 ^ q else (x : Nat), by
    split
    · exact Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right (by norm_num) hq)
    · exact x.isLt⟩

/-- The cleared index's bits ARE `EGate.applyNat (mz q)` of the original. -/
theorem clearBitFin_testBit (m q : Nat) (hq : q < m) (x : Fin (2 ^ m)) (b : Nat) :
    ((clearBitFin m q hq x : Fin (2 ^ m)) : Nat).testBit b
      = EGate.applyNat (.mz q) (fun k => (x : Nat).testBit k) b := by
  show (if (x : Nat).testBit q then (x : Nat) ^^^ 2 ^ q else (x : Nat)).testBit b
      = Function.update (fun k => (x : Nat).testBit k) q false b
  by_cases h : (x : Nat).testBit q
  · rw [if_pos h, Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases hb : b = q
    · subst hb; simp [h]
    · rw [Function.update_of_ne hb, decide_eq_false (fun hh => hb hh.symm)]
      simp
  · rw [if_neg h]
    by_cases hb : b = q
    · subst hb; rw [Function.update_self]; simpa using h
    · rw [Function.update_of_ne hb]

/-- `M · |x⟩ = column `x` of `M` (acting on a computational basis vector). -/
theorem mulVec_single_one {N : Nat} (M : Matrix (Fin N) (Fin N) ℂ) (x : Fin N) :
    M.mulVec (Pi.single x (1 : ℂ)) = fun i => M i x := by
  funext i
  show (M i) ⬝ᵥ (Pi.single x (1 : ℂ)) = M i x
  rw [dotProduct_single, mul_one]

/-- The empty Pauli product is the identity matrix. -/
theorem axisMat_nil (n : Nat) : axisMat n ([] : PauliProduct) = 1 := by
  show opsMat n (kindFn []) = 1
  have h : kindFn ([] : PauliProduct) = (fun _ => Pauli.I) := by funext i; rfl
  rw [h]; exact opsMat_one n

/-- `Z_q · |x⟩ = (−1)^{x_q} |x⟩`. -/
theorem axisZ_mulVec_single (m q : Nat) (hq : q < m) (x : Fin (2 ^ m)) :
    (axisMat m [⟨q, PKind.z⟩]).mulVec (Pi.single x (1 : ℂ))
      = (if (x : Nat).testBit q then (-1 : ℂ) else 1)
          • (Pi.single x (1 : ℂ) : Fin (2 ^ m) → ℂ) := by
  rw [mulVec_single_one]
  funext i
  rw [axisMat_single_z_apply m q hq i x, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hix : i = x
  · rw [hix]; simp
  · rw [if_neg (fun h => hix (Fin.ext h)), if_neg hix, mul_zero]

/-- `X_q · |x⟩ = |x ⊕ 2^q⟩`. -/
theorem axisX_mulVec_single (m q : Nat) (hq : q < m) (x : Fin (2 ^ m)) :
    (axisMat m [⟨q, PKind.x⟩]).mulVec (Pi.single x (1 : ℂ))
      = Pi.single (⟨(x : Nat) ^^^ 2 ^ q,
          Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right (by norm_num) hq)⟩ :
          Fin (2 ^ m)) (1 : ℂ) := by
  rw [mulVec_single_one]
  funext i
  rw [axisMat_single_x_apply m q hq i x, Pi.single_apply]
  by_cases hix : (i : Nat) = (x : Nat) ^^^ 2 ^ q
  · rw [if_pos hix, if_pos (Fin.ext hix)]
  · rw [if_neg hix, if_neg (fun h => hix (by rw [h]))]

/-- Reading slot `outs.length` from the trace extended by `ω`. -/
theorem getD_extend_self (ω : Nat → Bool) (outs : List Bool) :
    (outs ++ [ω outs.length]).getD outs.length false = ω outs.length := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self]
  rfl

/-- **The measurement-reset block as a matrix** (per outcome branch): the
parity-`Z` projector followed by the conditional `X` reset. -/
theorem lowerMz_progDenote (m q : Nat) (ω : Nat → Bool) (outs : List Bool) :
    progDenote m ω outs (lowerMz outs.length q)
      = (if ω outs.length then axisMat m [⟨q, PKind.x⟩] else axisMat m ([] : PauliProduct))
          * projHalf (axisMat m [⟨q, PKind.z⟩]) (ω outs.length) := by
  show progDenote m ω outs
      ([PPMStmt.measure outs.length [⟨q, PKind.z⟩]]
        ++ [PPMStmt.correct [outs.length] [⟨q, PKind.x⟩] []]) = _
  rw [progDenote_append' m ω _ _ outs]
  have hcw : PPMProg.cwidth [PPMStmt.measure outs.length [⟨q, PKind.z⟩]] = 1 := rfl
  rw [hcw]
  have hext : extendTrace ω outs 1 = outs ++ [ω outs.length] := rfl
  have hmeas : progDenote m ω outs [PPMStmt.measure outs.length [⟨q, PKind.z⟩]]
      = projHalf (axisMat m [⟨q, PKind.z⟩]) (ω outs.length) := by
    show progDenote m ω (outs ++ List.replicate 1 (ω outs.length)) []
        * stmtDenote m outs (ω outs.length)
            (PPMStmt.measure outs.length [⟨q, PKind.z⟩]) = _
    rw [show progDenote m ω (outs ++ List.replicate 1 (ω outs.length)) []
          = (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) from rfl, Matrix.one_mul]
    rfl
  have hcorr : progDenote m ω (outs ++ [ω outs.length])
        [PPMStmt.correct [outs.length] [⟨q, PKind.x⟩] []]
      = (if ω outs.length then axisMat m [⟨q, PKind.x⟩]
          else axisMat m ([] : PauliProduct)) := by
    show progDenote m ω ((outs ++ [ω outs.length]) ++ List.replicate 0 _) []
        * stmtDenote m (outs ++ [ω outs.length])
            (ω (outs ++ [ω outs.length]).length)
            (PPMStmt.correct [outs.length] [⟨q, PKind.x⟩] []) = _
    rw [show progDenote m ω ((outs ++ [ω outs.length]) ++ List.replicate 0 _) []
          = (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) from rfl, Matrix.one_mul]
    show (if xorParity (outs ++ [ω outs.length]) [outs.length]
            then axisMat m [⟨q, PKind.x⟩] else axisMat m ([] : PauliProduct)) = _
    rw [show xorParity (outs ++ [ω outs.length]) [outs.length] = ω outs.length from by
          simp only [xorParity, List.foldl_cons, List.foldl_nil, Bool.false_xor]
          exact getD_extend_self ω outs]
  rw [hext, hcorr, hmeas]

private theorem fold_proj {N : Nat} (c1 c2 : ℂ) (v : Fin N → ℂ) :
    (2⁻¹ : ℂ) • (v + c1 • (c2 • v)) = (2⁻¹ * (1 + c1 * c2)) • v := by
  rw [smul_smul,
      show v + (c1 * c2) • v = (1 + c1 * c2) • v from by rw [add_smul, one_smul],
      smul_smul]

/-- **THE MEASUREMENT NODE IS A FAITHFUL PAULI MEASUREMENT.**  On a
computational basis state `|x⟩`, the lowered `mz q` block (`c = Measure Z[q];
if c then X[q]`) keeps ONLY the consistent branch `outcome = x_q` and there
returns `|x⟩` with qubit `q` cleared — exactly `EGate.applyNat (mz q)` on the
basis. -/
theorem lowerMz_denote_basis (m q : Nat) (hq : q < m) (ω : Nat → Bool)
    (outs : List Bool) (x : Fin (2 ^ m)) :
    (progDenote m ω outs (lowerMz outs.length q)).mulVec (Pi.single x (1 : ℂ))
      = (if ω outs.length = (x : Nat).testBit q then (1 : ℂ) else 0)
          • (Pi.single (clearBitFin m q hq x) (1 : ℂ) : Fin (2 ^ m) → ℂ) := by
  rw [lowerMz_progDenote m q ω outs, ← Matrix.mulVec_mulVec, projHalf_mulVec,
      axisZ_mulVec_single m q hq x, fold_proj, Matrix.mulVec_smul]
  cases hb : ω outs.length <;> cases hxq : (x : Nat).testBit q <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  -- ω = false, x_q = false : keep, identity reset
  · rw [axisMat_nil, Matrix.one_mulVec]
    rw [show (2⁻¹ * (1 + (1 : ℂ) * 1)) = 1 from by ring]
    congr 2
    exact Fin.ext (by simp [clearBitFin, hxq])
  -- ω = false, x_q = true : kill
  · rw [axisMat_nil, Matrix.one_mulVec,
        show (2⁻¹ * (1 + (1 : ℂ) * -1)) = 0 from by ring, zero_smul, zero_smul]
  -- ω = true, x_q = false : kill
  · rw [axisX_mulVec_single m q hq x,
        show (2⁻¹ * (1 + (-1 : ℂ) * 1)) = 0 from by ring, zero_smul, zero_smul]
  -- ω = true, x_q = true : keep, X reset
  · rw [axisX_mulVec_single m q hq x,
        show (2⁻¹ * (1 + (-1 : ℂ) * -1)) = 1 from by ring]
    congr 2
    exact Fin.ext (by simp [clearBitFin, hxq])

/-! ## §4. Composing measure-clears: the measured-uncompute primitive. -/

theorem eAnc_mzList (L : List Nat) : eAnc (mzList L) = 0 := by
  induction L with
  | nil => rfl
  | cons q qs ih => show eAnc (mzList qs) + eAnc (.mz q) = 0; rw [ih]; rfl

theorem eSlots_mzList (L : List Nat) : eSlots (mzList L) = L.length := by
  induction L with
  | nil => rfl
  | cons q qs ih =>
      show eSlots (mzList qs) + eSlots (.mz q) = (q :: qs).length
      rw [ih]; rfl

/-- **THE MEASURE-CLEAR REGISTER LOWERS TO A FAITHFUL PAULI-MEASUREMENT
SEQUENCE.**  `mzList L` (measure-and-reset every qubit of `L` — Gidney/Berry
measurement-based uncomputation of a temp register) lowers to a sequence of
Pauli-`Z` measurements with `X` resets; on a computational basis state `|x⟩`
its denotation, on each branch, is a scalar times the basis state whose bits
are EXACTLY `EGate.applyNat (mzList L)` of the input (every cleared qubit set
to 0).  No T magic states are consumed (`mzList` is reversible-free). -/
theorem lowerMzList_denote_basis (m : Nat) :
    ∀ (L : List Nat), (∀ q ∈ L, q < m) →
      ∀ (ω : Nat → Bool) (outs : List Bool) (x : Fin (2 ^ m)),
        ∃ (sc : ℂ) (y : Fin (2 ^ m)),
          (progDenote m ω outs (lowerEGate m outs.length (mzList L))).mulVec
              (Pi.single x (1 : ℂ))
            = sc • (Pi.single y (1 : ℂ) : Fin (2 ^ m) → ℂ)
          ∧ ∀ b, (y : Nat).testBit b
              = EGate.applyNat (mzList L) (fun k => (x : Nat).testBit k) b := by
  intro L
  induction L with
  | nil =>
      intro _ ω outs x
      refine ⟨1, x, ?_, fun b => rfl⟩
      show (progDenote m ω outs (lowerFlat m outs.length (gateRots Gate.I))).mulVec _ = _
      rw [show gateRots Gate.I = [] from rfl]
      show (progDenote m ω outs ([] : PPMProg)).mulVec (Pi.single x (1 : ℂ)) = _
      rw [show progDenote m ω outs ([] : PPMProg)
            = (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) from rfl,
          Matrix.one_mulVec, one_smul]
  | cons q qs ih =>
      intro hL ω outs x
      have hq : q < m := hL q (List.mem_cons_self ..)
      have hqs : ∀ q' ∈ qs, q' < m := fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')
      obtain ⟨sc1, y1, hy1eq, hy1bits⟩ := ih hqs ω outs x
      have hsplit : lowerEGate m outs.length (mzList (q :: qs))
          = lowerEGate m outs.length (mzList qs)
              ++ lowerMz (outs.length + qs.length) q := by
        show lowerEGate m outs.length (mzList qs)
            ++ lowerEGate (m + eAnc (mzList qs))
                (outs.length + eSlots (mzList qs)) (EGate.mz q) = _
        rw [eAnc_mzList, eSlots_mzList]
        rfl
      refine ⟨sc1 * (if ω (extendTrace ω outs qs.length).length
            = (y1 : Nat).testBit q then (1 : ℂ) else 0),
          clearBitFin m q hq y1, ?_, ?_⟩
      · rw [hsplit, progDenote_append',
            show PPMProg.cwidth (lowerEGate m outs.length (mzList qs)) = qs.length from by
              rw [lowerEGate_cwidth]; exact eSlots_mzList qs,
            ← Matrix.mulVec_mulVec, hy1eq, Matrix.mulVec_smul,
            show outs.length + qs.length = (extendTrace ω outs qs.length).length from
              (extendTrace_length ω qs.length outs).symm,
            lowerMz_denote_basis m q hq ω (extendTrace ω outs qs.length) y1, smul_smul]
      · intro b
        rw [clearBitFin_testBit m q hq y1 b]
        show Function.update (fun k => (y1 : Nat).testBit k) q false b
          = Function.update (EGate.applyNat (mzList qs) (fun k => (x : Nat).testBit k)) q false b
        rw [show (fun k => (y1 : Nat).testBit k)
              = EGate.applyNat (mzList qs) (fun k => (x : Nat).testBit k) from funext hy1bits]

end FormalRV.PauliRotation.EGateLowering
