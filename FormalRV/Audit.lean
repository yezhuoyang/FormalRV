/-
  FormalRV.Audit — one reader-facing audit file per paper.

  Each `FormalRV/Audit/<Paper>.lean` REDEFINES NOTHING: it imports the real
  definitions/theorems from `Corpus/` (and the shared `Framework/` · `Shor/`
  folders) and exposes them with `#check` / `#print axioms`, framed by a docstring
  that states the paper's headline claim, the SETTINGS a reader should check against
  the paper, OUR APPROACH, the GAP we determined, and what is STILL UNSOLVED.

  A reader verifies any single paper with, e.g.,
      lake build FormalRV.Audit.Gidney2025
  Compilation confirms every cited theorem type-checks; the `#print axioms` lines
  reveal the exact trust base.  See FormalRV/Audit/README.md for the index table.
-/
import FormalRV.Audit.Common            -- shared infrastructure (used by several paper audits)
import FormalRV.Audit.Peng2022          -- the cross-cutting order-finding success bound
import FormalRV.Audit.Gidney2025
import FormalRV.Audit.GidneyEkera2021
import FormalRV.Audit.CainXu2026
import FormalRV.Audit.Webster2026
import FormalRV.Audit.Babbush2026
import FormalRV.Audit.Xu2024
