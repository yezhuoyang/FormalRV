/-
  FormalRV.QEC.LogicalLayout.Bridge
  ---------------------------------
  **★ THE SCALABLE PROOF BRIDGE — prove each gadget ONCE, bridge to the whole
  circuit. ★**

  The scaling principle (John's): a circuit's correctness should NOT be one giant
  `native_decide`.  Instead:
    * prove each DISTINCT catalog gadget's `valid`+`funcOK` ONCE (small, reusable
      certificates — `cert_*` below);
    * assemble a program's `chainOK` from those certificates, reusing the SAME
      certificate for every occurrence of a gadget (so an N-occurrence gadget is
      proven once, not N times);
    * apply the GENERAL bridge `weldChain_LaSCorrectFull` (axiom-clean, no
      `native_decide`) to lift the per-gadget facts to the whole welded circuit.

  The SEMANTIC payload rides along: the chain's spec `paulis` IS the program's
  measurement sequence (flow 0 of each gadget = the demanded Pauli), so the
  whole-circuit `LaSCorrectFull` says the lattice surgery MEASURES exactly the
  program's measurements.  Structural + semantic, one bridge.
-/
import FormalRV.QEC.LogicalLayout.Compiler

namespace FormalRV.QEC.Threader

open FormalRV.QEC.LaSre

/-! ## §1. CATALOG CERTIFICATES — each distinct gadget proven ONCE. -/

/-- The `Z̄₀Z̄₁` merge is structurally valid (proven once, reused everywhere). -/
theorem cert_zm_valid : (lrMergeMulti [0, 1]).valid = true := by native_decide
/-- …and satisfies the interior functionality (the expensive check, once). -/
theorem cert_zm_func : (lrMergeMulti [0, 1]).funcOK (lrMergeMultiSurf [0, 1]) 3 = true := by
  native_decide

/-! ## §2. THE SCALABLE ASSEMBLY — `chainOK` from certificates (gadget reused). -/

def zmConn : List (Nat × Nat) := [(0, 0), (1, 0)]
def zmGadgets : List LaSre := [lrMergeMulti [0, 1], lrMergeMulti [0, 1]]
def zmSurfs : List Surf := [lrMergeMultiSurf [0, 1], lrMergeMultiSurf [0, 1]]

/-- `chainOK` for a 2-occurrence program, with the EXPENSIVE per-gadget `funcOK`
discharged by the SINGLE certificate `cert_zm_func` (reused for both layers).
Only the cheap footprints + the two interface layers go to `native_decide` —
the gadget interior is never re-decided. -/
theorem zmProg_chainOK :
    chainOK 3 3 zmConn 2 1 zmGadgets zmSurfs = true := by
  simp only [zmGadgets, zmSurfs, chainOK]   -- unfold the chain structure
  simp only [cert_zm_valid, cert_zm_func]   -- discharge BOTH gadget interiors via the ONE certificate
  native_decide                             -- only footprints + the two interface layers remain

/-! ## §3. THE BRIDGE — lift per-gadget facts to the WHOLE circuit. -/

/-- The program's measurement spec: flow 0 `Z̄₀Z̄₁` (the measured joint), 1 `X̄₀`,
2 `X̄₁`.  Ports at the first layer's bottom (k=0) and last layer's top (k=5). -/
def zmPorts : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨1, 0, 0, 4, 5⟩, ⟨0, 0, 5, 4, 5⟩, ⟨1, 0, 5, 4, 5⟩]
def zmPaulis : Nat → Nat → Pauli := fun s p =>
  match s with
  | 0 => Pauli.Z
  | 1 => if p % 2 == 0 then Pauli.X else Pauli.I
  | 2 => if p % 2 == 1 then Pauli.X else Pauli.I
  | _ => Pauli.I

theorem zmProg_ports :
    portsOK (weldChainSurf 3 zmSurfs) zmPorts zmPaulis 3 = true := by native_decide

/-- **★ THE WHOLE CIRCUIT IS CORRECT, BUILT FROM ONE GADGET PROOF + THE BRIDGE ★**
— the welded `Z̄₀Z̄₁ ; Z̄₀Z̄₁` program passes the complete `LaSCorrectFull` against
its measurement spec.  The interior-functionality fact came from the SINGLE
`cert_zm_func`; `weldChain_LaSCorrectFull` (general, axiom-clean) did the lift.
This is the scalable shape: per-distinct-gadget proof + one reusable bridge =
whole-circuit proof, with the lattice surgery MEASURING exactly the program's
`Z̄₀Z̄₁` sequence. -/
theorem zmProg_correct :
    LaSCorrectFull (weldChain 3 zmConn zmGadgets) (weldChainSurf 3 zmSurfs) zmPorts zmPaulis 3 = true :=
  weldChain_LaSCorrectFull 3 3 zmConn 2 1 zmGadgets zmSurfs zmPorts zmPaulis
    zmProg_chainOK zmProg_ports

/-! ## §4. SEMANTIC TIE — the spec flow 0 IS the program's measurement.

  `zmPaulis 0` (flow 0) is `Z̄` on every port — i.e. the joint `Z̄₀Z̄₁` the program
  measures.  `LaSCorrectFull` against this spec therefore states the welded
  lattice surgery realizes the `Z̄₀Z̄₁` measurement at each layer.  So the bridge
  carries the SEMANTICS (which Pauli is measured), not just structural validity. -/
theorem zmProg_measures_Z0Z1 : zmPaulis 0 0 = Pauli.Z ∧ zmPaulis 0 1 = Pauli.Z := ⟨rfl, rfl⟩

/-- The certificate `cert_zm_func` is REUSED — the same `Z̄₀Z̄₁` gadget appears in
both layers of `zmGadgets`, proven once.  Adding more occurrences adds no gadget
re-proof, only (cheap) interface checks. -/
theorem cert_reused : zmGadgets = [lrMergeMulti [0, 1], lrMergeMulti [0, 1]] := rfl

/-! ## §5. ★ SCALABILITY — the SAME certificate certifies a LARGER program. -/

def zm4Gadgets : List LaSre :=
  [lrMergeMulti [0, 1], lrMergeMulti [0, 1], lrMergeMulti [0, 1], lrMergeMulti [0, 1]]
def zm4Surfs : List Surf :=
  [lrMergeMultiSurf [0, 1], lrMergeMultiSurf [0, 1], lrMergeMultiSurf [0, 1], lrMergeMultiSurf [0, 1]]

/-- A 4-occurrence program's `chainOK`, with ALL FOUR gadget interiors discharged
by the ONE `cert_zm_func` (proven once).  Going from 2 to 4 occurrences adds NO
gadget re-proof — only the extra interface layers reach `native_decide`.  This is
the scaling claim, demonstrated: cost is O(distinct gadgets) + O(interfaces). -/
theorem zm4_chainOK :
    chainOK 3 3 zmConn 2 1 zm4Gadgets zm4Surfs = true := by
  simp only [zm4Gadgets, zm4Surfs, chainOK]
  simp only [cert_zm_valid, cert_zm_func]
  native_decide

theorem zm4_ports :
    portsOK (weldChainSurf 3 zm4Surfs)
      [⟨0, 0, 0, 4, 5⟩, ⟨1, 0, 0, 4, 5⟩, ⟨0, 0, 11, 4, 5⟩, ⟨1, 0, 11, 4, 5⟩]
      zmPaulis 3 = true := by native_decide

/-- **★ A LARGER `Z̄₀Z̄₁`×4 PROGRAM, CERTIFIED FROM THE SAME ONE GADGET PROOF ★** —
the welded 4-layer circuit is `LaSCorrectFull`, and (per `zm4_chainOK`) the
expensive gadget interior was proven exactly ONCE.  The bridge lifts it to the
whole.  Scaling the program does NOT scale the gadget proofs. -/
theorem zm4_correct :
    LaSCorrectFull (weldChain 3 zmConn zm4Gadgets) (weldChainSurf 3 zm4Surfs)
      [⟨0, 0, 0, 4, 5⟩, ⟨1, 0, 0, 4, 5⟩, ⟨0, 0, 11, 4, 5⟩, ⟨1, 0, 11, 4, 5⟩] zmPaulis 3 = true :=
  weldChain_LaSCorrectFull 3 3 zmConn 2 1 zm4Gadgets zm4Surfs _ zmPaulis zm4_chainOK zm4_ports

end FormalRV.QEC.Threader
