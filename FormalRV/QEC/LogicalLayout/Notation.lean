/-
  FormalRV.QEC.LogicalLayout.Notation
  ───────────────────────────────────
  **The one-file layout declaration** (paper-thin macro, never
  load-bearing — the `ppm_program` discipline):

      logical_layout machine {
        blocks 1024 of scBlock;   -- a FARM: 1024 identical surface patches
        block lpBlock;            -- one LP block
        block bbBlock             -- one BB block
      }

  elaborates to

      def machine : BlockLayout :=
        consecutive (List.replicate 1024 scBlock ++ [lpBlock] ++ [bbBlock])
      theorem machine_wfStructural : machine.wfStructural = true

  MACHINE-READABLE replication: a farm elaborates to the literal
  `List.replicate n blk`, so the closed-form indexing theorems
  (`addrOf_replicate`: wire `g` ↦ patch `g / k`, slot `g % k`;
  `capacityOf_replicate`; the `addrOf_append_*` segment laws) fire on the
  declared data directly — no 1024-step list walks, for the kernel or for
  an auditor.

  The block terms are ordinary `CodeBlock` values — the user supplies the
  code (CSSCode), the logical count `k`, and CRUCIALLY the `LogicalBasis`:
  the indexed logical-Z̄/X̄ operators that GROUND what "slot i of this
  block" means.  Wires are labeled consecutively in declaration order.
-/
import FormalRV.QEC.LogicalLayout.GlobalIndex

namespace FormalRV.QEC.LogicalLayout

open Lean

/-- One layout entry: a single block or a replicated farm. -/
declare_syntax_cat layoutEntry

/-- `block b` — one code block. -/
syntax "block " term : layoutEntry

/-- `blocks n of b` — a FARM of `n` identical code blocks. -/
syntax "blocks " num " of " term : layoutEntry

/-- `logical_layout name { entries }` — declare a layout from ordered
blocks and farms, with its structural well-formedness theorem generated
for free. -/
syntax "logical_layout " ident " {" sepBy(layoutEntry, ";") "}" : command

/-- Each entry as a block-list segment. -/
private def entrySegment : TSyntax `layoutEntry → MacroM (TSyntax `term)
  | `(layoutEntry| block $b:term) => `(([$b] : List FormalRV.QEC.CodeBlock))
  | `(layoutEntry| blocks $n:num of $b:term) =>
      `((List.replicate $n $b : List FormalRV.QEC.CodeBlock))
  | _ => Macro.throwError "unsupported layout entry"

macro_rules
  | `(logical_layout $name:ident { $[$entries:layoutEntry];* }) => do
      let segs ← entries.mapM entrySegment
      let blockList ← segs.foldrM (fun seg acc => `($seg ++ $acc))
        (← `(([] : List FormalRV.QEC.CodeBlock)))
      let wfName := mkIdent (name.getId.appendAfter "_wfStructural")
      `(def $name : FormalRV.QEC.BlockLayout :=
          FormalRV.QEC.LogicalLayout.consecutive $blockList
        theorem $wfName : ($name).wfStructural = true :=
          FormalRV.QEC.LogicalLayout.consecutive_wfStructural _)

end FormalRV.QEC.LogicalLayout
