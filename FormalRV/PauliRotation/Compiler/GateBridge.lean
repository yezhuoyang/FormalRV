/-
  FormalRV.PauliRotation.Compiler.GateBridge
  ─────────────────────────────────
  THE ARITHMETIC ENTRY POINT: compile the reversible Gate IR
  (`FormalRV.Framework.Gate` — I/X/CX/CCX/seq, the language of EVERY
  arithmetic gadget: Cuccaro, Gidney, ModularAdder, ModMult, ModExp,
  Windowed, …) into the Pauli-rotation IR.  Toffoli-class circuits are
  EXACTLY Clifford+T, so this compilation is exact — no approximation.

      X q       ↦  X_q^{π/2}                                (1 rotation)
      CX c t    ↦  the signed-π/4 triple (`cnotGate`)        (3 rotations)
      CCX a b t ↦  H_t ; CCZ(sort₃ a b t) ; H_t              (13 rotations,
                   7 of them π/8 — CCZ is symmetric, so operands sort)

  Generic theorems — EVERY Gate-IR gadget inherits them by composition with
  its existing `tcount`/`countToffoli` theorems:

    • `gateRots_countPi8`   : rotation T-count = `Gate.tcount` ON THE NOSE
    • `gateRots_length`     : #rotations = countX + 3·countCNOT + 13·countToffoli
    • `gateRots_bounded`    : every emitted axis canonical, within
                              `Resource.width g` (needs distinct operands)
    • `gateRotSchedule_denote` : the ASAP-parallelized program denotes
                              exactly the naive sequence
    • `gateRotSchedule_countPi8` : … and scheduling keeps the T-count.

  HONESTY: the correctness theorem is semantic preservation of the
  compile+schedule pipeline against `seqDenote (gateRots g)`; the dictionary
  leg (`seqDenote (gateRots g)` = the Gate's unitary, up to global phase) is
  the known open item (`README.md`).
-/
import FormalRV.PauliRotation.Compiler.Scheduler
import FormalRV.Resource.GateCount

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Framework (Gate)
open FormalRV.Resource

/-! ## §1. The compiler. -/

/-- Ascending ordering of three indices (CCZ is symmetric in its qubits). -/
def sort3 (a b c : Nat) : Nat × Nat × Nat :=
  if a ≤ b then
    if b ≤ c then (a, b, c)
    else if a ≤ c then (a, c, b) else (c, a, b)
  else
    if a ≤ c then (b, a, c)
    else if b ≤ c then (b, c, a) else (c, b, a)

/-- **Gate-IR → rotation sequence** (naive, gate by gate; exact). -/
def gateRots : Gate → List Rot
  | .I          => []
  | .X q        => [⟨false, .piHalf, [⟨q, .x⟩]⟩]
  | .CX c t     => (cnotGate c t).flatten
  | .CCX a b t  =>
      (hGate t).flatten
        ++ (cczGate (sort3 a b t).1 (sort3 a b t).2.1 (sort3 a b t).2.2).flatten
        ++ (hGate t).flatten
  | .seq g h    => gateRots g ++ gateRots h

/-- **The compiled-and-parallelized gadget.** -/
def gateRotSchedule (g : Gate) : RotProg := scheduleList (gateRots g)

/-- Distinct operands (the Gate-IR well-formedness this compilation needs). -/
def opsOK : Gate → Bool
  | .I          => true
  | .X _        => true
  | .CX c t     => decide (c ≠ t)
  | .CCX a b t  => decide (a ≠ b) && decide (a ≠ t) && decide (b ≠ t)
  | .seq g h    => opsOK g && opsOK h

/-! ## §2. Resource counts (generic, exact). -/

/-- **Rotation-level T-count = `Gate.tcount`, on the nose** — every gadget's
existing T-count theorem becomes its rotation T-count theorem for free. -/
theorem gateRots_countPi8 (g : Gate) :
    (gateRots g).countP (fun r => r.angle == RAngle.piEighth) = Gate.tcount g := by
  induction g with
  | I => rfl
  | X q => rfl
  | CX c t => rfl
  | CCX a b t => rfl
  | seq g h ihg ihh =>
      show ((gateRots g) ++ (gateRots h)).countP _ = Gate.tcount g + Gate.tcount h
      rw [List.countP_append, ihg, ihh]

/-- Total rotation count, in terms of the INDEPENDENT `Resource/` walkers. -/
theorem gateRots_length (g : Gate) :
    (gateRots g).length
      = countX g + 3 * countCNOT g + 13 * countToffoli g := by
  induction g with
  | I => rfl
  | X q => rfl
  | CX c t => rfl
  | CCX a b t => rfl
  | seq g h ihg ihh =>
      show ((gateRots g) ++ (gateRots h)).length = _
      rw [List.length_append, ihg, ihh]
      show _ = countX g + countX h + 3 * (countCNOT g + countCNOT h)
          + 13 * (countToffoli g + countToffoli h)
      omega

/-! ## §3. Boundedness (the side condition of the semantic theorem). -/

private theorem hGate_bounded (q : Nat) :
    ∀ r ∈ (hGate q).flatten,
      sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ q + 1 := by
  intro r hr
  simp only [hGate, rot1, List.append_assoc, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    exact ⟨rfl, by simp [PauliProduct.width]⟩

private theorem cnotGate_bounded (c t : Nat) (h : c ≠ t) :
    ∀ r ∈ (cnotGate c t).flatten,
      sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ max (c + 1) (t + 1) := by
  intro r hr
  simp only [cnotGate, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨?_, ?_⟩ <;> unfold mk2 <;> by_cases hct : c < t <;>
      simp [hct, sortedStrict, PauliProduct.width] <;> omega
  · exact ⟨rfl, by simp [PauliProduct.width]⟩
  · exact ⟨rfl, by simp [PauliProduct.width]⟩

private theorem cczGate_bounded (x y z : Nat) (hxy : x < y) (hyz : y < z) :
    ∀ r ∈ (cczGate x y z).flatten,
      sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ z + 1 := by
  intro r hr
  simp only [cczGate, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_⟩ <;> simp [sortedStrict, PauliProduct.width] <;> omega

theorem sort3_spec (a b t : Nat) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) :
    (sort3 a b t).1 < (sort3 a b t).2.1
      ∧ (sort3 a b t).2.1 < (sort3 a b t).2.2
      ∧ (sort3 a b t).2.2 + 1 ≤ max (max (a + 1) (b + 1)) (t + 1) := by
  unfold sort3
  split_ifs <;> simp <;> omega

/-- Every emitted rotation has a canonical axis within the gate's width. -/
theorem gateRots_bounded (g : Gate) (hops : opsOK g = true) :
    ∀ r ∈ gateRots g,
      sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ width g := by
  induction g with
  | I => intro r hr; cases hr
  | X q =>
      intro r hr
      simp only [gateRots, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨rfl, by simp [PauliProduct.width, width]⟩
  | CX c t =>
      simp only [opsOK, decide_eq_true_eq] at hops
      exact fun r hr => cnotGate_bounded c t hops r hr
  | CCX a b t =>
      intro r hr
      simp only [opsOK, Bool.and_eq_true, decide_eq_true_eq] at hops
      obtain ⟨s1, s2, s3⟩ := sort3_spec a b t hops.1.1 hops.1.2 hops.2
      simp only [gateRots, List.mem_append] at hr
      rcases hr with (hr | hr) | hr
      · obtain ⟨h1, h2⟩ := hGate_bounded t r hr
        exact ⟨h1, by simp only [width]; omega⟩
      · obtain ⟨h1, h2⟩ := cczGate_bounded _ _ _ s1 s2 r hr
        exact ⟨h1, by simp only [width]; omega⟩
      · obtain ⟨h1, h2⟩ := hGate_bounded t r hr
        exact ⟨h1, by simp only [width]; omega⟩
  | seq g h ihg ihh =>
      intro r hr
      simp only [opsOK, Bool.and_eq_true] at hops
      simp only [gateRots, List.mem_append] at hr
      rcases hr with hr | hr
      · obtain ⟨h1, h2⟩ := ihg hops.1 r hr
        exact ⟨h1, by simp only [width]; omega⟩
      · obtain ⟨h1, h2⟩ := ihh hops.2 r hr
        exact ⟨h1, by simp only [width]; omega⟩

/-! ## §4. The end-to-end theorems every gadget inherits. -/

/-- **GADGET CORRECTNESS (optimizer leg)**: for any well-operand Gate-IR
gadget within width `n`, the ASAP-parallelized rotation program denotes
EXACTLY the naive gate-by-gate rotation sequence. -/
theorem gateRotSchedule_denote (n : Nat) (g : Gate)
    (hops : opsOK g = true) (hw : width g ≤ n) :
    RotProg.denote n (gateRotSchedule g) = seqDenote n (gateRots g) :=
  scheduleList_denote n (gateRots g) (fun r hr =>
    ⟨(gateRots_bounded g hops r hr).1,
     le_trans (gateRots_bounded g hops r hr).2 hw⟩)

/-- **GADGET T-COUNT**: the parallelized program's π/8 count IS the gadget's
`Gate.tcount` — compose with any existing per-gadget `tcount` theorem. -/
theorem gateRotSchedule_countPi8 (g : Gate) :
    countPi8 (gateRotSchedule g) = Gate.tcount g := by
  rw [gateRotSchedule, scheduleList_countPi8, gateRots_countPi8]

/-- Scheduling also preserves the total rotation budget. -/
theorem gateRotSchedule_depth_le (g : Gate) :
    rotDepth (gateRotSchedule g) ≤ (gateRots g).length :=
  scheduleList_depth_le (gateRots g)

/-! ## §5. Smoke (kernel-checked on a real little circuit). -/

example :  -- a MAJ-style fragment: CX;CX;CCX = 3+3+13 rotations, 7 of them T
    (gateRots (.seq (.CX 2 1) (.seq (.CX 2 0) (.CCX 0 1 2)))).length = 19 := by
  decide
example :
    countPi8 (gateRotSchedule (.seq (.CX 2 1) (.seq (.CX 2 0) (.CCX 0 1 2)))) = 7 := by
  decide
example :  -- operands distinct, fits in 3 qubits: the semantic theorem applies
    opsOK (.seq (.CX 2 1) (.seq (.CX 2 0) (.CCX 0 1 2))) = true
      ∧ width (.seq (.CX 2 1) (.seq (.CX 2 0) (.CCX 0 1 2))) ≤ 3 := by decide
example :  -- CCX with operands in ANY order compiles (CCZ symmetric, sort₃)
    countPi8 (gateRotSchedule (.CCX 5 2 4)) = 7 := by decide

end FormalRV.PauliRotation
