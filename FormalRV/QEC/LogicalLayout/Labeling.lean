/-
  FormalRV.QEC.LogicalLayout.Labeling
  ───────────────────────────────────
  **HONEST LABELING of PPM programs over declared code blocks.**

  Under the consecutive numbering (`GlobalIndex`), labeling a PPM program
  CHANGES NOTHING: the program's wires already are the global logical
  indices, so every existing PPM theorem (semantics, counts, lowering)
  applies verbatim.  This file supplies the VIEW and its obligations:

    • `PPMStmt.qubits` / `PPMProg.qubits` — the wires a program touches,
      with `qubits ⊆ [0, width)`;
    • `supports blocks p` — the decidable fitting check
      `width p ≤ capacity` (every touched wire has a label);
    • **`labeled_exactly_one`** — under `supports`, every touched wire is
      EXACTLY ONE logical qubit of exactly one block (valid, round-trips,
      injective across wires);
    • the labeled views the QEC lowering will consume: `labeledProduct`
      (per-factor addresses), `slotsInBlock` (a joint operator's footprint
      inside one block), `blocksTouched` (which blocks a joint measurement
      spans — the surgery planning datum);
    • a renderer: `Measure X[C422₀.1]·Z[BB₁.0]`.
-/
import FormalRV.QEC.LogicalLayout.GlobalIndex
import FormalRV.PPM.Syntax.Program

namespace FormalRV.QEC.LogicalLayout

open FormalRV.QEC
open FormalRV.PPM.Prog

/-! ## §1. The wires a PPM program touches. -/

/-- The qubits of a Pauli product. -/
def productQubits (P : PauliProduct) : List Nat := P.map (·.qubit)

/-- The qubits one statement touches. -/
def stmtQubits : PPMStmt → List Nat
  | .measure _ P => productQubits P
  | .measureSel _ _ Pt Pe => productQubits Pt ++ productQubits Pe
  | .measureSel2 _ _ _ P00 P01 P10 P11 =>
      productQubits P00 ++ productQubits P01
        ++ productQubits P10 ++ productQubits P11
  | .frame P => productQubits P
  | .correct _ thn els => productQubits thn ++ productQubits els
  | .correctQ _ thn els => productQubits thn ++ productQubits els
  | .useT q => [q]
  | .useCCZ a b c => [a, b, c]

/-- The qubits a program touches. -/
def progQubits : PPMProg → List Nat
  | [] => []
  | st :: p => stmtQubits st ++ progQubits p

private theorem productQubits_lt_width (P : PauliProduct) :
    ∀ q ∈ productQubits P, q < PauliProduct.width P := by
  induction P with
  | nil => intro q hq; cases hq
  | cons f t ih =>
      intro q hq
      simp only [productQubits, List.map_cons, List.mem_cons] at hq
      show q < max (f.qubit + 1) (PauliProduct.width t)
      rcases hq with rfl | hq
      · omega
      · have := ih q hq
        omega

/-- Every touched wire is below the statement's width. -/
theorem stmtQubits_lt_width (st : PPMStmt) :
    ∀ q ∈ stmtQubits st, q < st.width := by
  intro q hq
  cases st <;>
    simp only [stmtQubits, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hq <;>
    simp only [PPMStmt.width]
  case measure dst P => exact productQubits_lt_width P q hq
  case measureSel sel dst Pt Pe =>
      rcases hq with hq | hq
      · have := productQubits_lt_width Pt q hq; omega
      · have := productQubits_lt_width Pe q hq; omega
  case measureSel2 s1 s2 dst P00 P01 P10 P11 =>
      rcases hq with ((hq | hq) | hq) | hq
      all_goals first
        | (have := productQubits_lt_width P00 q hq; omega)
        | (have := productQubits_lt_width P01 q hq; omega)
        | (have := productQubits_lt_width P10 q hq; omega)
        | (have := productQubits_lt_width P11 q hq; omega)
  case frame P => exact productQubits_lt_width P q hq
  case correct par thn els =>
      rcases hq with hq | hq
      · have := productQubits_lt_width thn q hq; omega
      · have := productQubits_lt_width els q hq; omega
  case correctQ mons thn els =>
      rcases hq with hq | hq
      · have := productQubits_lt_width thn q hq; omega
      · have := productQubits_lt_width els q hq; omega
  case useT q' => omega
  case useCCZ a b c =>
      rcases hq with rfl | rfl | rfl <;> omega

/-- Every touched wire is below the program's width. -/
theorem progQubits_lt_width (p : PPMProg) :
    ∀ q ∈ progQubits p, q < PPMProg.width p := by
  induction p with
  | nil => intro q hq; cases hq
  | cons st t ih =>
      intro q hq
      simp only [progQubits, List.mem_append] at hq
      show q < max st.width (PPMProg.width t)
      rcases hq with hq | hq
      · have := stmtQubits_lt_width st q hq; omega
      · have := ih q hq; omega

/-! ## §2. The fitting check and THE LABELING THEOREM. -/

/-- **The decidable fitting check**: every wire of the program has a
logical-qubit label (the program fits in the declared blocks). -/
def supports (blocks : List CodeBlock) (p : PPMProg) : Bool :=
  decide (PPMProg.width p ≤ capacityOf blocks)

/-- **THE LABELING THEOREM**: under `supports`, every wire the program
touches is EXACTLY ONE logical qubit of exactly one code block — its label
is valid, round-trips to the wire, and is the unique such address. -/
theorem labeled_exactly_one (blocks : List CodeBlock) (p : PPMProg)
    (hsup : supports blocks p = true)
    (q : Nat) (hq : q ∈ progQubits p) :
    validAddr blocks (addrOf blocks q) = true
      ∧ globalIndex blocks (addrOf blocks q) = q
      ∧ ∀ a, validAddr blocks a = true → globalIndex blocks a = q →
          a = addrOf blocks q := by
  unfold supports at hsup
  simp only [decide_eq_true_eq] at hsup
  have hcap : q < capacityOf blocks :=
    Nat.lt_of_lt_of_le (progQubits_lt_width p q hq) hsup
  exact ⟨validAddr_addrOf blocks q hcap,
         globalIndex_addrOf blocks q hcap,
         fun a ha hga => addrOf_unique blocks q a ha hga⟩

/-- **Distinct wires are distinct logical qubits** (no aliasing). -/
theorem labeling_inj (blocks : List CodeBlock) (p : PPMProg)
    (hsup : supports blocks p = true)
    (q q' : Nat) (hq : q ∈ progQubits p) (hq' : q' ∈ progQubits p)
    (h : addrOf blocks q = addrOf blocks q') : q = q' := by
  unfold supports at hsup
  simp only [decide_eq_true_eq] at hsup
  exact addrOf_inj blocks q q'
    (Nat.lt_of_lt_of_le (progQubits_lt_width p q hq) hsup)
    (Nat.lt_of_lt_of_le (progQubits_lt_width p q' hq') hsup) h

/-! ## §3. The labeled views the QEC lowering consumes. -/

/-- A joint Pauli operator with every factor labeled. -/
def labeledProduct (blocks : List CodeBlock) (P : PauliProduct) :
    List (LogicalAddr × PKind) :=
  P.map (fun f => (addrOf blocks f.qubit, f.kind))

/-- The footprint of a joint operator INSIDE block `b`: the in-block slots
it acts on, with kinds — the datum a per-block surgery lowering reads. -/
def slotsInBlock (blocks : List CodeBlock) (P : PauliProduct) (b : Nat) :
    List (Nat × PKind) :=
  (labeledProduct blocks P).filterMap
    (fun (a, k) => if a.block = b then some (a.idx, k) else none)

/-- The blocks a joint operator spans — the surgery-planning datum (a
joint measurement touching ≥ 2 blocks is an inter-block surgery). -/
def blocksTouched (blocks : List CodeBlock) (P : PauliProduct) : List Nat :=
  ((labeledProduct blocks P).map (fun (a, _) => a.block)).dedup

/-- Every labeled factor is the label of its wire (the view is honest). -/
theorem labeledProduct_spec (blocks : List CodeBlock) (P : PauliProduct)
    (f : PFactor) (hf : f ∈ P) :
    (addrOf blocks f.qubit, f.kind) ∈ labeledProduct blocks P :=
  List.mem_map.mpr ⟨f, hf, rfl⟩

/-! ## §4. Rendering (`X[C422₀.1]·Z[BB₁.0]`). -/

/-- Render one labeled address as `name_b.slot`. -/
def renderAddr (blocks : List CodeBlock) (a : LogicalAddr) : String :=
  (match blocks[a.block]? with
   | some blk => blk.name
   | none => "?") ++ "_" ++ toString a.block ++ "." ++ toString a.idx

private def renderKind : PKind → String
  | .x => "X" | .y => "Y" | .z => "Z"

/-- Render a joint product in labeled form. -/
def renderProduct (blocks : List CodeBlock) (P : PauliProduct) : String :=
  String.intercalate "·" (P.map (fun f =>
    renderKind f.kind ++ "[" ++ renderAddr blocks (addrOf blocks f.qubit) ++ "]"))

/-- Render one PPM statement with all wires labeled. -/
def renderStmt (blocks : List CodeBlock) : PPMStmt → String
  | .measure dst P =>
      s!"c{dst} = Measure {renderProduct blocks P}"
  | .measureSel _ dst Pt Pe =>
      s!"c{dst} = MeasureIf … then {renderProduct blocks Pt} else {renderProduct blocks Pe}"
  | .measureSel2 _ _ dst P00 P01 P10 P11 =>
      s!"c{dst} = MeasureSel2 {renderProduct blocks P00} {renderProduct blocks P01} "
        ++ s!"{renderProduct blocks P10} {renderProduct blocks P11}"
  | .frame P => s!"frame {renderProduct blocks P}"
  | .correct _ thn _ => s!"if … then {renderProduct blocks thn}"
  | .correctQ _ thn _ => s!"if …·… then {renderProduct blocks thn}"
  | .useT q => s!"useT[{renderAddr blocks (addrOf blocks q)}]"
  | .useCCZ a b c =>
      s!"useCCZ[{renderAddr blocks (addrOf blocks a)},"
        ++ s!"{renderAddr blocks (addrOf blocks b)},"
        ++ s!"{renderAddr blocks (addrOf blocks c)}]"

/-- Render a whole program in labeled form. -/
def renderProg (blocks : List CodeBlock) (p : PPMProg) : String :=
  String.intercalate ";\n" (p.map (renderStmt blocks))

end FormalRV.QEC.LogicalLayout
