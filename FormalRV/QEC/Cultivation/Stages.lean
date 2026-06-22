/-
  FormalRV.QEC.Cultivation.Stages
  -------------------------------
  **Structural infrastructure for magic-state cultivation** (Gidney–Shutty–Jones,
  arXiv:2409.17595).  This file organizes the construction into its three stages
  and the cultivation `check → grow → stabilize` cycle, and connects the
  CODE-LEVEL realizability of the controlled-H check to the verified single-qubit
  and two-qubit semantic kernel in `Cultivation.TStateCheck`.

  SCOPE (honest): this is a SPECIFICATION / scaffolding layer.  The semantic
  correctness that is actually *proved* is the controlled-`H_XY` check kernel
  (`TStateCheck`) plus the self-duality of the `d=3` color code that makes a
  TRANSVERSAL `H` implement a LOGICAL `H` (so the kernel applies at the code
  level).  We do NOT prove circuit-level fault distance or the escape stage's
  grafting (out of scope, per the brief).  The reference circuits live in
  `Library/2409.17595/code/.../src/cultiv/_construction/`:
  `_injection_stage.py`, `_cultivation_stage.py` (the `cat-check` gadget),
  `_color_code.py`, `_escape_stage.py`.
-/
import FormalRV.QEC.Cultivation.TStateCheck
import FormalRV.QEC.Logical

namespace FormalRV.QEC.Cultivation

open FormalRV.QEC

/-! ## §1. The `d=3` color code is the Steane code, and it is SELF-DUAL.

The cultivation stage stores the `|T⟩` in a triangular color code.  At `d=3` the
triangular color code IS the `[[7,1,3]]` Steane code.  Its defining feature for
cultivation is **self-duality** (`hx = hz`): the X- and Z-stabilizer supports
coincide, so a TRANSVERSAL Hadamard maps every X-stabilizer to the (already
present) Z-stabilizer and vice versa — preserving the stabilizer group — while
swapping the logical `X̄ ↔ Z̄`.  That is exactly "transversal `H` = logical `H`",
which is what lets the controlled-transversal-`H` check verify the logical value. -/

/-- The `d=3` triangular color code = the `[[7,1,3]]` Steane code. -/
def colorCodeD3 : CSSCode := steaneCSS

/-- **The `d=3` color code is self-dual** (`hx = hz`). -/
theorem colorCodeD3_selfDual : colorCodeD3.hx = colorCodeD3.hz := by decide

/-- **Transversal `H` implements logical `H` (symplectic content).**  Because the
code is self-dual, transversal `H` permutes the stabilizer generators among
themselves (X-checks ↔ Z-checks, which have identical supports), and it carries
the logical `X̄` support to the logical `Z̄` support (they are equal).  So a
transversal `H` is a logical `H`. -/
theorem transversalH_is_logicalH :
    colorCodeD3.hx = colorCodeD3.hz ∧
      steaneLogical.lx = steaneLogical.lz := by
  refine ⟨colorCodeD3_selfDual, ?_⟩
  decide

/-! ## §2. The three stages and the cultivation cycle. -/

/-- The stages/steps of a magic-state cultivation (paper §Construction). -/
inductive Step
  | inject       -- create the encoded `|T⟩` in a `d=3` color code (fault distance 1)
  | check        -- the double-cat controlled-`H_XY` check (raises fault distance)
  | grow         -- enlarge the color code via Bell-pair preparation
  | stabilize    -- superdense color-code cycles (×3) to settle new stabilizers
  | escape       -- graft into a large matchable surface code
  deriving DecidableEq, Repr

/-- The `check → grow → stabilize` cultivation cycle (one fault-distance step). -/
def cultivationCycle : List Step := [.check, .grow, .stabilize]

/-- **The full cultivation pipeline** to target fault distance `d` (odd): inject,
then run the cultivation cycle while the code grows from `3` up to `d` in steps of
`2`, then escape.  (Each cycle raises the fault distance and grows the code.) -/
def cultivationPipeline (d : Nat) : List Step :=
  [Step.inject] ++ (List.range ((d - 3) / 2 + 1)).flatMap (fun _ => cultivationCycle)
    ++ [Step.escape]

/-- The `d=3` pipeline runs exactly one cultivation cycle (`cat-check-d3`) then
escapes — matching `make_inject_and_cultivate_chunks_d3` in the reference code. -/
theorem cultivationPipeline_d3 :
    cultivationPipeline 3 = [.inject, .check, .grow, .stabilize, .escape] := by
  decide

/-- The `d=5` pipeline runs two cultivation cycles (`cat-check-d3`, then grow to
`d=5` and `cat-check-d5`) — matching `make_inject_and_cultivate_chunks_d5`. -/
theorem cultivationPipeline_d5 :
    cultivationPipeline 5 =
      [.inject, .check, .grow, .stabilize, .check, .grow, .stabilize, .escape] := by
  decide

/-! ## §3. The check step's semantic spec — discharged by `TStateCheck`.

The cultivation `check` step's job is to verify the encoded logical value is the
magic state `|T⟩`, by a controlled-(transversal-)`H_XY`.  §1 reduces this to a
controlled-`H_XY` on the logical qubit (transversal `H` = logical `H`), and
`TStateCheck` proves that controlled-`H_XY` check is correct: it passes (no
detection) on `|T⟩` and FIRES on the orthogonal magic state. -/

/-- **The check step is semantically correct (logical level).**  Packaged from
the verified kernel: the controlled-`H_XY` check leaves `|+⟩⊗|T⟩` fixed (passes)
and sends `|+⟩⊗T|−⟩` to `|−⟩⊗T|−⟩` (detects) — and `|T⟩` is exactly the `+1`
eigenstate of the check observable `H_XY = (X+Y)/√2`. -/
theorem check_step_correct :
    ctrlHXY * plusT = plusT
      ∧ ctrlHXY * plusTm = minusTm
      ∧ hXY * magicT = magicT := by
  exact ⟨ctrlHXY_check_passes, ctrlHXY_check_detects, hXY_stabilizes_magicT⟩

/-! ## §4. Reference resource counts (paper, `d=3`), as documented data.

These are the paper's reported sizes for the `d=3` "double cat check" (15 qubits,
6 layers per check) and the `cultivation` postselection regime — recorded here as
plain data, NOT derived. -/

/-- Qubits spanned by the `d=3` cat-check (paper §Cultivation Stage). -/
def d3CatCheckQubits : Nat := 15
/-- Layers spanned by the `d=3` cat-check (paper §Cultivation Stage). -/
def d3CatCheckLayers : Nat := 6
/-- Superdense stabilize cycles per stabilize step (paper's chosen value). -/
def stabilizeCycles : Nat := 3

end FormalRV.QEC.Cultivation
