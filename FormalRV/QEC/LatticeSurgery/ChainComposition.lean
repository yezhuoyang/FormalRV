/-
  FormalRV.QEC.LatticeSurgery.ChainComposition
  --------------------------------------------
  **★ THE weldChain INDUCTION COROLLARY — certify an N-gadget program in
  PER-GADGET work, by induction on the chain. ★**

  `weldK_LaSCorrectFull` (WeldComposition) is the single-step rule.  Here it is
  lifted to a whole chain `weldChain h conn [g₀, g₁, …]`:

    * `chainOK` — a recursive Bool checker bundling, for each gadget, its own
      `valid`+`funcOK` (small, ONE gadget) and, for each weld, the two interface
      layers — NEVER the whole grid;
    * `chainOK_sound` — `chainOK = true → (weldChain …)` is `valid`+`funcOK`,
      by induction, each step discharged by `weldK_valid`/`weldK_funcOK`;
    * `weldChain_LaSCorrectFull` — add the composite ports ⇒ the whole chain is
      `LaSCorrectFull`.

  The win: each DISTINCT gadget's `funcOK` is certified ONCE (the catalog is
  already all `LaSCorrectFull`); a program's marginal cost is just its interface
  checks.  `weldChainSurf` with direct flow-maps is DEFINITIONALLY `stitchSurf`,
  so the single-step rule applies verbatim at every link.
-/
import FormalRV.QEC.LatticeSurgery.ProgramAssembly
import FormalRV.QEC.LatticeSurgery.WeldComposition

namespace FormalRV.QEC.LaSre

/-! ## §1. The recursive per-gadget + per-interface checker. -/

/-- All small checks for a chain: each gadget's footprint+`valid`+`funcOK`, and
each weld's two interface layers.  No check ever touches the whole welded grid. -/
def chainOK (h n : Nat) (conn : List (Nat × Nat)) (w wj : Nat) :
    List LaSre → List Surf → Bool
  | [g], [s] =>
      g.maxI == w && g.maxJ == wj && g.maxK == h && g.valid && g.funcOK s n
  | (g :: g2 :: rest), (s :: srest) =>
      g.maxI == w && g.maxJ == wj && g.maxK == h && g.valid && g.funcOK s n
        && weldInterfaceValidOK2 h g (weldChain h conn (g2 :: rest)) conn w wj
        && weldInterfaceOK2 h g (weldChain h conn (g2 :: rest)) s (weldChainSurf h srest) conn n w wj
        && chainOK h n conn w wj (g2 :: rest) srest
  | _, _ => false

/-! ## §2. SOUNDNESS — `chainOK` ⇒ the whole chain is valid + funcOK. -/

theorem chainOK_sound (h n : Nat) (conn : List (Nat × Nat)) (w wj : Nat) :
    ∀ (gs : List LaSre) (ss : List Surf), chainOK h n conn w wj gs ss = true →
      (weldChain h conn gs).valid = true
        ∧ (weldChain h conn gs).funcOK (weldChainSurf h ss) n = true
        ∧ (weldChain h conn gs).maxI = w ∧ (weldChain h conn gs).maxJ = wj := by
  intro gs
  induction gs with
  | nil => intro ss hc; simp [chainOK] at hc
  | cons g rest ih =>
    cases rest with
    | nil =>
      intro ss hc
      cases ss with
      | nil => simp [chainOK] at hc
      | cons s srest =>
        cases srest with
        | cons => simp [chainOK] at hc
        | nil =>
          simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨⟨⟨⟨hmi, hmj⟩, hmk⟩, hv⟩, hf⟩ := hc
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [weldChain] using hv
          · simpa [weldChain, weldChainSurf] using hf
          · simpa [weldChain] using hmi
          · simpa [weldChain] using hmj
    | cons g2 rest' =>
      intro ss hc
      cases ss with
      | nil => simp [chainOK] at hc
      | cons s srest =>
        cases srest with
        | nil => simp [chainOK] at hc
        | cons s2 srest' =>
          simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨⟨⟨⟨⟨⟨⟨hmi, hmj⟩, hmk⟩, hv⟩, hf⟩, hiv⟩, hif⟩, hrec⟩ := hc
          obtain ⟨Bv, Bf, Bi, Bj⟩ := ih (s2 :: srest') hrec
          -- weldChain (g :: g2 :: rest') = weldK h g (weldChain (g2 :: rest')) conn
          have hII : g.maxI = (weldChain h conn (g2 :: rest')).maxI := by rw [hmi, Bi]
          have hJJ : g.maxJ = (weldChain h conn (g2 :: rest')).maxJ := by rw [hmj, Bj]
          -- the welded footprint is exactly the chain's known constant width `w × wj`,
          -- so the O(N) interface check's bound covers every welded cube.
          have hWI : (weldK h g (weldChain h conn (g2 :: rest')) conn).maxI = w := by
            simp only [weldK]; rw [hmi, Bi, Nat.max_self]
          have hWJ : (weldK h g (weldChain h conn (g2 :: rest')) conn).maxJ = wj := by
            simp only [weldK]; rw [hmj, Bj, Nat.max_self]
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact weldK_valid h g (weldChain h conn (g2 :: rest')) conn hII hJJ hmk hv Bv
              (weldInterfaceValidOK_of_2 h g (weldChain h conn (g2 :: rest')) conn w wj
                hWI.le hWJ.le hiv)
          · exact weldK_funcOK h g (weldChain h conn (g2 :: rest')) s (weldChainSurf h (s2 :: srest'))
              conn n hII hJJ hmk hf Bf
              (weldInterfaceOK_of_2 h g (weldChain h conn (g2 :: rest')) s
                (weldChainSurf h (s2 :: srest')) conn n w wj hWI.le hWJ.le hif)
          · simp only [weldChain, weldK]; rw [hmi, Bi, Nat.max_self]
          · simp only [weldChain, weldK]; rw [hmj, Bj, Nat.max_self]

/-! ## §3. THE CHAIN CERTIFICATE — add the composite ports. -/

/-- **★ AN N-GADGET PROGRAM IS `LaSCorrectFull` FROM PER-GADGET CHECKS ★** —
`chainOK` (per-gadget + per-interface, each small) plus the composite ports ⇒ the
whole welded chain passes the complete checker.  Linear in the chain, never the
whole grid. -/
theorem weldChain_LaSCorrectFull (h n : Nat) (conn : List (Nat × Nat)) (w wj : Nat)
    (gs : List LaSre) (ss : List Surf) (ports : List Port) (paulis : Nat → Nat → Pauli)
    (hc : chainOK h n conn w wj gs ss = true)
    (hPorts : portsOK (weldChainSurf h ss) ports paulis n = true) :
    LaSCorrectFull (weldChain h conn gs) (weldChainSurf h ss) ports paulis n = true := by
  obtain ⟨hv, hf, _, _⟩ := chainOK_sound h n conn w wj gs ss hc
  simp only [LaSre.LaSCorrectFull, hv, hf, hPorts, Bool.and_self, Bool.and_true]

/-! ## §4. A REAL multi-gadget Shor block, DRIVEN THROUGH the chain corollary.

  The PPM primitive — a sequence of joint-Pauli measurements with idling — as a
  `weldChain`: `M_{Z̄₁Z̄₂} ; idle ; M_{Z̄₁Z̄₂}` on two qubits.  Each gadget's
  surface is pre-combined so the joint `Z̄₁Z̄₂` flow threads directly (the idle
  carries it as `Z̄₁⊕Z̄₂`).  Certified via `weldChain_LaSCorrectFull` — `chainOK`
  is each gadget's own check plus the two interfaces, never the whole 9-step grid. -/

open FormalRV.QEC.Gidney21 (mergeZLaS mergeZSurf)

/-- The block's gadgets: Z-merge, 2-patch idle, Z-merge. -/
def shorBlockGadgets : List LaSre := [mergeZLaS, parIdle, mergeZLaS]

/-- Pre-combined surfaces: the idle carries the joint `Z̄₁Z̄₂` as a product flow. -/
def shorBlockSurfs : List Surf := [mergeZSurf, surfCombine parIdleSurf fmIdleZZ, mergeZSurf]

/-- Each per-gadget + per-interface check passes (each SMALL). -/
theorem shorBlock_chainOK :
    chainOK 3 3 measConn 2 1 shorBlockGadgets shorBlockSurfs = true := by native_decide

/-- The composite ports match the `X̄₁`/`X̄₂`/`Z̄₁Z̄₂` spec. -/
theorem shorBlock_ports :
    portsOK (weldChainSurf 3 shorBlockSurfs) measProgramPorts measProgramPaulis 3 = true := by
  native_decide

/-- **★ A REAL 3-GADGET MEASUREMENT PROGRAM, CERTIFIED VIA THE CHAIN COROLLARY ★**
— the whole `M_{Z̄₁Z̄₂} ; idle ; M_{Z̄₁Z̄₂}` weld passes the complete
`LaSCorrectFull`, obtained from per-gadget + per-interface checks (`chainOK`) and
the ports — NOT from a `native_decide` on the whole welded diagram. -/
theorem shorBlock_correct :
    LaSCorrectFull (weldChain 3 measConn shorBlockGadgets) (weldChainSurf 3 shorBlockSurfs)
      measProgramPorts measProgramPaulis 3 = true :=
  weldChain_LaSCorrectFull 3 3 measConn 2 1 shorBlockGadgets shorBlockSurfs
    measProgramPorts measProgramPaulis shorBlock_chainOK shorBlock_ports

end FormalRV.QEC.LaSre
