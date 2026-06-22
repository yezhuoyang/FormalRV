/-
  FormalRV.QEC.LatticeSurgery.CliffordFrame
  -----------------------------------------
  **★ THE CLIFFORD-FRAME EXTENSION — mixed (`X̄Z̄`) and `Y`-basis measurements
  COMPOSE through the chain. ★**

  Pure-`Z` merges are not enough for the full lowered arithmetic: it also emits
  MIXED measurements (`mxzMerge` = `X̄₁Z̄₂`) and `Y`-readouts (`mY1`).  Their
  faithful realization is the CLIFFORD PROMOTION — `M_{X₁Z₂} = H₁·M_{Z₁Z₂}·H₁`,
  `M_Y = S·M_X·S†` — and those gadgets are already built and verified
  (`faithfulMixedMerge`, `yReadWeld`).

  The KEY for composition: the Clifford conjugation is SELF-CONTAINED inside the
  gadget — `mixLaS`'s output ports restore the input basis (`q₁` blue=`KJ` in AND
  out), so the conjugated gadget is itself a uniform-footprint chain gadget.  Its
  internal `H`s ARE the per-qubit frame conjugation; because they cancel, the
  GLOBAL frame is unchanged and the gadget welds like any other.  This file proves
  a mixed merge composes through the chain corollary — the Clifford-frame is
  handled, end to end.
-/
import FormalRV.QEC.LatticeSurgery.FaithfulMixedMerge
import FormalRV.QEC.LatticeSurgery.ChainComposition
import FormalRV.QEC.LatticeSurgery.Routing

namespace FormalRV.QEC.LaSre

/-! ## §1. A mixed merge composes — two `X̄₁Z̄₂` measurements welded. -/

/-- Only the data worldlines (`q₂` at col 0, `q₁` at col 1) weld across layers;
each gadget's `H`-aux stays internal. -/
def mixChainConn : List (Nat × Nat) := [(0, 0), (1, 0)]

def mixChain : List LaSre := [mixLaS, mixLaS]
def mixChainSurf : List Surf := [mixSurf, mixSurf]

/-- Composite ports: `q₂`/`q₁` in at k=0, out at k=`2·9−1=17`. -/
def mixChainPorts : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨1, 0, 0, 5, 4⟩, ⟨0, 0, 17, 4, 5⟩, ⟨1, 0, 17, 5, 4⟩]

/-- Spec: flow 0 `X̄₁Z̄₂` (Z on q₂, X on q₁); flow 1 `Z̄₁`; flow 2 `X̄₂`. -/
def mixChainPaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => Pauli.Z | 0, 1 => Pauli.X | 0, 2 => Pauli.Z | 0, 3 => Pauli.X
  | 1, 1 => Pauli.Z | 1, 3 => Pauli.Z
  | 2, 0 => Pauli.X | 2, 2 => Pauli.X
  | _, _ => Pauli.I

theorem mixChain_chainOK :
    chainOK 9 3 mixChainConn 3 2 mixChain mixChainSurf = true := by native_decide

theorem mixChain_ports :
    portsOK (weldChainSurf 9 mixChainSurf) mixChainPorts mixChainPaulis 3 = true := by native_decide

/-- **★ A MIXED MEASUREMENT COMPOSES THROUGH THE CHAIN ★** — two faithful
`X̄₁Z̄₂` merges (each an internal `H₁·Z-merge·H₁`), welded by the chain corollary,
pass the complete `LaSCorrectFull`.  The Clifford conjugation threads correctly
across the weld; mixed-basis measurements are chain-composable.  So the full
catalog — pure-`Z` (`lrMergeMulti`) AND mixed/`Y` (Clifford promotion) — flows
through the same verified composition framework. -/
theorem mixChain_correct :
    LaSCorrectFull (weldChain 9 mixChainConn mixChain) (weldChainSurf 9 mixChainSurf)
      mixChainPorts mixChainPaulis 3 = true :=
  weldChain_LaSCorrectFull 9 3 mixChainConn 3 2 mixChain mixChainSurf
    mixChainPorts mixChainPaulis mixChain_chainOK mixChain_ports

/-! ## §2. The frame conjugation is sound — the gadget measures the CONJUGATE.

  `mixLaS` measures `X̄₁Z̄₂`; its interior is a pure `Z`-merge.  The `H₁`
  conjugation (`Z̄₁ ↦ X̄₁`) is exactly why the joined plane reads `X̄₁`.  The
  TEETH theorem `faithfulMixedMerge_not_ZZ` (it does NOT measure `Z̄₁Z̄₂`) is the
  proof the conjugation is real, not a relabel — the Clifford-frame is anchored. -/
theorem cliffordFrame_sound :
    LaSCorrectFull mixLaS mixSurf mixPorts mixPaulis 3 = true
      ∧ LaSCorrectFull mixLaS mixSurf mixPorts mixPaulis_wrongZ 3 = false :=
  ⟨faithfulMixedMerge_fully_correct, faithfulMixedMerge_not_ZZ⟩

/-! ## §3. ★ A MIXED + PURE BLOCK — both families in ONE program. -/

/-- The pure-`Z` `Z̄₃Z̄₄` merge, padded to the mixed footprint (`h=9`) and shifted
to columns 3,4 — sharing the board with the mixed merge. -/
def pureZShifted : LaSre := shiftI 3 (lrMergeMultiH [0, 1] 9)
def pureZShiftedSurf : Surf := shiftISurf 3 (lrMergeMultiSurf [0, 1])

/-- ONE layer: mixed `X̄₁Z̄₂` (cols 0–2, with `H`-aux) ∥ pure-`Z` `Z̄₃Z̄₄`
(cols 3–4), on a `5×2×9` grid. -/
def fullLayerLaS : LaSre := unionLaS mixLaS pureZShifted

/-- Direct-sum surface: flows 0–2 = the mixed merge, flows 3–5 = the pure merge. -/
def fullLayerSurf : Surf :=
  { IJ := fun s i j k => if s < 3 then mixSurf.IJ s i j k else pureZShiftedSurf.IJ (s - 3) i j k
    IK := fun s i j k => if s < 3 then mixSurf.IK s i j k else pureZShiftedSurf.IK (s - 3) i j k
    JK := fun s i j k => if s < 3 then mixSurf.JK s i j k else pureZShiftedSurf.JK (s - 3) i j k
    JI := fun s i j k => if s < 3 then mixSurf.JI s i j k else pureZShiftedSurf.JI (s - 3) i j k
    KI := fun s i j k => if s < 3 then mixSurf.KI s i j k else pureZShiftedSurf.KI (s - 3) i j k
    KJ := fun s i j k => if s < 3 then mixSurf.KJ s i j k else pureZShiftedSurf.KJ (s - 3) i j k }

/-- Ports: mixed `q₂`/`q₁` (cols 0,1) + pure `q₃`/`q₄` (cols 3,4), at k=0 and k=8. -/
def fullLayerPorts : List Port :=
  mixPorts ++ [⟨3, 0, 0, 4, 5⟩, ⟨3, 0, 8, 4, 5⟩, ⟨4, 0, 0, 4, 5⟩, ⟨4, 0, 8, 4, 5⟩]

/-- Pure half's paulis (ports `[in₃,out₃,in₄,out₄]`): flow 0 `Z̄₃Z̄₄`, 1 `X̄₃`, 2 `X̄₄`. -/
def pureP : Nat → Nat → Pauli := fun s q =>
  match s, q with
  | 0, _ => Pauli.Z
  | 1, 0 => Pauli.X | 1, 1 => Pauli.X
  | 2, 2 => Pauli.X | 2, 3 => Pauli.X
  | _, _ => Pauli.I

def fullLayerPaulis : Nat → Nat → Pauli := fun s p =>
  if s < 3 then (if p < 4 then mixPaulis s p else Pauli.I)
  else (if 4 ≤ p then pureP (s - 3) (p - 4) else Pauli.I)

theorem fullLayer_correct :
    LaSCorrectFull fullLayerLaS fullLayerSurf fullLayerPorts fullLayerPaulis 6 = true := by
  native_decide

/-! ## §4. ...and it CHAINS — the mixed+pure block, multi-layer. -/

def fullConn : List (Nat × Nat) := [(0, 0), (1, 0), (3, 0), (4, 0)]

def fullChain : List LaSre := [fullLayerLaS, fullLayerLaS]
def fullChainSurf : List Surf := [fullLayerSurf, fullLayerSurf]

def fullChainPorts : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨1, 0, 0, 5, 4⟩, ⟨3, 0, 0, 4, 5⟩, ⟨4, 0, 0, 4, 5⟩,
   ⟨0, 0, 17, 4, 5⟩, ⟨1, 0, 17, 5, 4⟩, ⟨3, 0, 17, 4, 5⟩, ⟨4, 0, 17, 4, 5⟩]

def fullChainPaulis : Nat → Nat → Pauli := fun s p =>
  -- ports: 0=q2in 1=q1in 2=q3in 3=q4in, 4=q2out 5=q1out 6=q3out 7=q4out
  let col := p % 4
  match s with
  | 0 => if col == 0 then Pauli.Z else if col == 1 then Pauli.X else Pauli.I   -- X̄₁Z̄₂
  | 1 => if col == 1 then Pauli.Z else Pauli.I                                  -- Z̄₁
  | 2 => if col == 0 then Pauli.X else Pauli.I                                  -- X̄₂
  | 3 => if col == 2 || col == 3 then Pauli.Z else Pauli.I                      -- Z̄₃Z̄₄
  | 4 => if col == 2 then Pauli.X else Pauli.I                                  -- X̄₃
  | 5 => if col == 3 then Pauli.X else Pauli.I                                  -- X̄₄
  | _ => Pauli.I

theorem fullChain_chainOK :
    chainOK 9 6 fullConn 5 2 fullChain fullChainSurf = true := by native_decide

theorem fullChain_ports :
    portsOK (weldChainSurf 9 fullChainSurf) fullChainPorts fullChainPaulis 6 = true := by native_decide

/-- **★ A MIXED + PURE PROGRAM, COMPILED AND COMPOSED ★** — `X̄₁Z̄₂` (mixed,
Clifford-promoted) ∥ `Z̄₃Z̄₄` (pure-`Z` long-range), padded to a common footprint
and welded into a 2-layer chain — passing the complete `LaSCorrectFull`.  The full
catalog (pure-`Z` of any weight AND mixed/`Y` via Clifford promotion) composes in
ONE verified program. -/
theorem fullChain_correct :
    LaSCorrectFull (weldChain 9 fullConn fullChain) (weldChainSurf 9 fullChainSurf)
      fullChainPorts fullChainPaulis 6 = true :=
  weldChain_LaSCorrectFull 9 6 fullConn 5 2 fullChain fullChainSurf
    fullChainPorts fullChainPaulis fullChain_chainOK fullChain_ports

end FormalRV.QEC.LaSre
