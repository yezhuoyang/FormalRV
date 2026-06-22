/-
  FormalRV.QEC.BlockAddressing — the QEC ↔ PPM logical-qubit BINDING layer.

  ## Charter (John, 2026-06-10)

  The PPM layer speaks in flat VIRTUAL logical indices (`c2 = Measure X[2]Z[3]`).
  The first interface problem is the explicit, user-visible mapping of each
  virtual logical index to a LOGICAL QUBIT OF A NAMED CODE BLOCK:

      Measure X[2]Z[3]   ⟼   Measure X[B0(1)] Z[B1(1)]

  Division of labour: the USER supplies (i) the named code blocks with their
  code type and their declared logical operators (`LogicalBasis` — each
  in-block logical qubit thereby has a unique index), and (ii) the index map
  virtual → (block, in-block index).  OUR duty: once code + mapping are
  fixed, decidably VERIFY the lowered QEC-level object — the map is
  well-formed and injective, every block's basis is valid, and the joint
  Pauli the PPM measures is a genuine joint logical operator of the
  composite (direct-sum) code.

  Everything REUSES the legacy stack: `LogicalBasis` (Logical.lean) for the
  per-block operators, `PauliSem.PauliString.mul/commutes` for the joint
  operator, `CSSCode.directSum` (CodeBuilders.lean) for the composite code,
  `toStabilizers` for the commutation obligation, and `MeasBasis`/`toPauli`
  from the circuit IR.  Downstream, the composite-code logical feeds
  `canonicalXSurgery` / `extraction_measures_readout` — the verified
  measurement implementation of the resolved PPM.

  Residues (tracked): genuineness here = commutation with all composite
  stabilizers (the `valid` legs of each basis cover in/out-of-rowspace per
  block); same-block X·Z mixing in ONE PPM term list multiplies via
  `PauliString.mul` (phases tracked) but the worked example keeps bases on
  distinct blocks, the standard surgery case.

  No Mathlib.  No `sorry`; no project axioms (kernel `decide` throughout).
-/

import FormalRV.QEC.Logical
import FormalRV.QEC.LogicalFinder
import FormalRV.QEC.CodeBuilders
import FormalRV.QEC.Circuit.CircuitSemantics

set_option maxRecDepth 16384

namespace FormalRV.QEC

open FormalRV.Framework.PauliSem
open FormalRV.Framework.LDPC
open FormalRV.QEC.Circuit

/-! ## Named code blocks and the user-supplied index map -/

/-- A NAMED code block: the code, its logical-qubit count, and the
    USER-DECLARED logical operators giving each in-block logical qubit a
    unique index `0 .. k−1`. -/
structure CodeBlock where
  name  : String
  code  : CSSCode
  k     : Nat
  basis : LogicalBasis code k

/-- A block-local logical address `B_block(idx)`. -/
structure LogicalAddr where
  block : Nat
  idx   : Nat
  deriving DecidableEq, Repr

/-- The layout: the named blocks plus the USER-SUPPLIED map from virtual
    logical index `i` to `map[i] : LogicalAddr`. -/
structure BlockLayout where
  blocks : List CodeBlock
  map    : List LogicalAddr

namespace BlockLayout

/-- Total data-qubit count (blocks placed consecutively on virtual qubits). -/
def totalN (L : BlockLayout) : Nat :=
  (L.blocks.map (fun b => b.code.n)).foldl (· + ·) 0

/-- Total logical-qubit count (e.g. 2 × LP[144,12,12] ⇒ 24). -/
def totalLogical (L : BlockLayout) : Nat :=
  (L.blocks.map (fun b => b.k)).foldl (· + ·) 0

/-- One address is in range: names an existing block and an existing
    in-block logical index. -/
def wfAddr (L : BlockLayout) (a : LogicalAddr) : Bool :=
  match L.blocks[a.block]? with
  | some b => decide (a.idx < b.k)
  | none   => false

/-- The STRUCTURAL half of the layout obligation: every mapped address in
    range and the map INJECTIVE — cheap to decide at any scale. -/
def wfStructural (L : BlockLayout) : Bool :=
  L.map.all L.wfAddr && decide L.map.Nodup

/-- **The decidable layout obligation** (our side, once the user fixes code
    and mapping): the structural half plus every block's declared basis
    valid (`LogicalBasis.valid`: commutation with the block's stabilizers +
    symplectic δ-pairing).  At paper scale the basis-validity conjunct is
    supplied as an explicit hypothesis (imported-basis certificates are
    long off-path runs) — see `wf_of`. -/
def wf (L : BlockLayout) : Bool :=
  L.wfStructural && L.blocks.all (fun b => b.basis.valid)

/-- Assemble `wf` from the cheap structural check plus per-block basis
    validity (the hypothesis-passing form for paper-scale imported bases). -/
theorem wf_of (L : BlockLayout) (hs : L.wfStructural = true)
    (hb : L.blocks.all (fun b => b.basis.valid) = true) : L.wf = true := by
  rw [wf, hs, hb]
  rfl

/-! ## The explicit syntax: virtual PPMs and their block-resolved form -/

/-- A PPM term list over VIRTUAL logical indices:
    `Measure X[2]Z[3]` = `[(2, .x), (3, .z)]`. -/
abbrev VirtualPPM := List (Nat × MeasBasis)

/-- The block-resolved form: `Measure X[B0(1)] Z[B1(1)]`. -/
abbrev ResolvedPPM := List (LogicalAddr × MeasBasis)

/-- Apply the user map (out-of-range virtual indices resolve to the sentinel
    `B0(0)`; `wf` + `inRange` below rule that out for verified layouts). -/
def resolve (L : BlockLayout) (p : VirtualPPM) : ResolvedPPM :=
  p.map (fun t => (L.map.getD t.1 ⟨0, 0⟩, t.2))

/-- Every virtual index of the PPM is covered by the map. -/
def inRange (L : BlockLayout) (p : VirtualPPM) : Bool :=
  p.all (fun t => decide (t.1 < L.map.length))

/-- Render the resolved PPM in the explicit `X[B0(1)]` labeling. -/
def render (L : BlockLayout) (p : VirtualPPM) : String :=
  "Measure " ++ String.join ((L.resolve p).map (fun (a, b) =>
    (match b with | .x => "X[" | .z => "Z[")
      ++ (match L.blocks[a.block]? with
          | some blk => blk.name
          | none => "?")
      ++ "(" ++ toString a.idx ++ ")] "))

/-! ## Lowering: the joint Pauli the resolved PPM measures -/

/-- The declared support of in-block logical `i` in basis `b` (zero outside
    the block's range). -/
def CodeBlock.logicalSupport (blk : CodeBlock) (b : MeasBasis) (i : Nat) : BoolVec :=
  if h : i < blk.k then
    match b with
    | .x => blk.basis.lx ⟨i, h⟩
    | .z => blk.basis.lz ⟨i, h⟩
  else zero_vec blk.code.n

/-- One resolved term as a GLOBAL Pauli string over the layout's
    `totalN` virtual data qubits (identity outside the addressed block). -/
def globalPauli (L : BlockLayout) (a : LogicalAddr) (b : MeasBasis) : PauliString :=
  ⟨Phase.plus,
   L.blocks.zipIdx.flatMap (fun bj =>
     if bj.2 = a.block then
       (CodeBlock.logicalSupport bj.1 b a.idx).map
         (fun bit => if bit then b.toPauli else Pauli.I)
     else List.replicate bj.1.code.n Pauli.I)⟩

/-- The JOINT Pauli of the whole PPM term list (legacy `PauliString.mul`,
    phases tracked). -/
def jointPauli (L : BlockLayout) (p : VirtualPPM) : PauliString :=
  (L.resolve p).foldl (fun acc t => acc.mul (globalPauli L t.1 t.2))
    (PauliString.identity L.totalN)

/-- The composite code of the layout: the direct sum of all blocks
    (REUSES `CSSCode.directSum`; validity preserved by
    `directSum_valid`). -/
def compositeCode (L : BlockLayout) : CSSCode :=
  L.blocks.foldl (fun acc blk => acc.directSum blk.code) ⟨0, [], []⟩

/-- **The PPM-level verification obligation**: the joint Pauli the resolved
    PPM measures commutes with EVERY stabilizer of the composite code — it
    is a joint logical operator of the layout (per-block genuineness is the
    `wf` bases' `valid` legs). -/
def ppmTargetsLogical (L : BlockLayout) (p : VirtualPPM) : Bool :=
  (L.compositeCode.toStabilizers).all (fun g => g.commutes (L.jointPauli p))

/-! ## Uniform allocation with the NAIVE sequential map

    For papers that give no concrete logical layout (the audit convention,
    John 2026-06-10): allocate identical code blocks and label virtual
    logical `i` as block `i / k`, in-block index `i % k`.  Structural
    well-formedness is proven PARAMETRICALLY — no `decide` — so the same
    theorem covers the lpTiny demo and an RSA-scale demand alike. -/

/-- Blocks allocated for a demand of `Q` logical qubits at `k` per block:
    `Q / k + 1` (always sufficient; may include one spare block when
    `k ∣ Q` — the demand layer tolerates a spare, and the `+1` form keeps
    every proof a one-liner). -/
def blocksFor (Q k : Nat) : Nat := Q / k + 1

/-- The naive sequential index map. -/
def naiveMap (Q k : Nat) : List LogicalAddr :=
  (List.range Q).map (fun i => ⟨i / k, i % k⟩)

/-- `Q` virtual logicals over identical copies of block `b`, naively
    sequentially indexed. -/
def uniformLayout (b : CodeBlock) (Q : Nat) : BlockLayout :=
  ⟨List.replicate (blocksFor Q b.k) b, naiveMap Q b.k⟩

/-- Core-only (no Mathlib): mapping an injective function over `range Q`
    yields a duplicate-free list. -/
private theorem nodup_map_range {α : Type} (f : Nat → α)
    (hf : ∀ a b, f a = f b → a = b) (Q : Nat) :
    ((List.range Q).map f).Nodup := by
  induction Q generalizing f with
  | zero => exact List.nodup_nil
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine List.nodup_cons.mpr ⟨?_, ih (f ∘ Nat.succ)
      (fun a b h => by have := hf _ _ h; omega)⟩
    intro hmem
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hmem
    have := hf _ _ hi
    omega

/-- The naive map is injective: `(i / k, i % k)` determines `i`. -/
private theorem naiveMap_nodup (Q k : Nat) :
    (naiveMap Q k).Nodup := by
  refine nodup_map_range _ ?_ Q
  intro a b h
  have hdiv : a / k = b / k := congrArg LogicalAddr.block h
  have hmod : a % k = b % k := congrArg LogicalAddr.idx h
  have ha := Nat.div_add_mod a k
  have hb := Nat.div_add_mod b k
  rw [hdiv, hmod] at ha
  omega

/-- **Parametric structural well-formedness** of the uniform naive layout:
    every address in range and the map injective, for EVERY block type and
    EVERY demand `Q` — the allocation scales without kernel evaluation. -/
theorem uniformLayout_wfStructural (b : CodeBlock) (Q : Nat) (hk : 0 < b.k) :
    (uniformLayout b Q).wfStructural = true := by
  rw [BlockLayout.wfStructural, Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro a ha
    simp only [uniformLayout, naiveMap, List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    have hblk : i / b.k < blocksFor Q b.k :=
      Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hi))
    simp only [BlockLayout.wfAddr, uniformLayout]
    rw [List.getElem?_replicate]
    simp [hblk, Nat.mod_lt i hk]
  · exact decide_eq_true (naiveMap_nodup Q b.k)

private theorem foldl_add_init' (l : List Nat) :
    ∀ (n : Nat), l.foldl (· + ·) n = n + l.foldl (· + ·) 0 := by
  induction l with
  | nil => intro n; simp
  | cons x rest ih =>
    intro n
    simp only [List.foldl_cons]
    rw [ih (n + x), ih (0 + x)]
    omega

/-- Total data-qubit demand of the uniform layout (the figure handed to the
    System layer): blocks × n. -/
theorem uniformLayout_totalN (b : CodeBlock) (Q : Nat) :
    (uniformLayout b Q).totalN = blocksFor Q b.k * b.code.n := by
  rw [BlockLayout.totalN, uniformLayout]
  induction blocksFor Q b.k with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.map_cons, List.foldl_cons, foldl_add_init',
        ih, Nat.succ_mul]
    omega

end BlockLayout

/-! ## Worked example — the user's story at kernel-checkable scale

    Two blocks `B0, B1` of the SAME code type (here `bbSmall` [[18,2,·]] with
    its certified `bbSmallLogicalBasis`; the LP[144,12,12]-style story is the
    same shape), 4 virtual logicals, user map `[B0(0), B1(0), B0(1), B1(1)]`.
    The PPM `Measure X[2]Z[3]` resolves to `Measure X[B0(1)] Z[B1(1)]` —
    cross-block, exactly the user's example — and its lowered joint Pauli is
    verified a joint logical of the composite [[36,·]] code. -/

open FormalRV.QEC.LogicalFinder in
def demoB0 : CodeBlock := ⟨"B0", bbSmall, 2, bbSmallLogicalBasis⟩

open FormalRV.QEC.LogicalFinder in
def demoB1 : CodeBlock := ⟨"B1", bbSmall, 2, bbSmallLogicalBasis⟩

def demoLayout : BlockLayout :=
  ⟨[demoB0, demoB1], [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]⟩

/-- 2 blocks × 2 logicals = 4 virtual logical qubits over 36 data qubits. -/
theorem demoLayout_totals :
    demoLayout.totalLogical = 4 ∧ demoLayout.totalN = 36 := by decide

/-- The layout obligation: in-range, injective, bases valid. -/
theorem demoLayout_wf : demoLayout.wf = true := by decide

/-- The user's PPM `Measure X[2]Z[3]`. -/
def demoPPM : BlockLayout.VirtualPPM := [(2, .x), (3, .z)]

theorem demoPPM_inRange : demoLayout.inRange demoPPM = true := by decide

/-- Explicit resolution: virtual 2 ↦ B0's logical 1 (X), virtual 3 ↦ B1's
    logical 1 (Z). -/
theorem demoPPM_resolves :
    demoLayout.resolve demoPPM = [(⟨0, 1⟩, .x), (⟨1, 1⟩, .z)] := by decide

theorem demoPPM_renders :
    demoLayout.render demoPPM = "Measure X[B0(1)] Z[B1(1)] " := by decide

/-- **Verified**: the joint Pauli of `Measure X[B0(1)] Z[B1(1)]` is a joint
    logical operator of the composite [[36,·]] code (commutes with all 18
    composite stabilizers). -/
theorem demoPPM_targets_logical :
    demoLayout.ppmTargetsLogical demoPPM = true := by decide

end FormalRV.QEC
