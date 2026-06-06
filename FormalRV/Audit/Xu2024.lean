/-
================================================================================
  AUDIT — Qian Xu et al. 2024, "Constant-overhead fault-tolerant quantum
          computation with reconfigurable atom arrays"   (arXiv:2308.08648)
================================================================================
HEADLINE CLAIM:  constant-overhead FTQC on neutral atoms; ~24 ms QEC cycle.

STATUS (⬜ recorded/assumed + ➗ a cross-check):  parameter-binding tuple, plus an
  arithmetic cross-check of the 24 ms cycle as the corpus's 24,000× hardware-clock
  OUTLIER (vs the 1 µs baseline shared by GE2021 / Gidney2025 / Babbush).  This is
  the architecture that the neutral-atom lattice-surgery DEMO (Example/neutral_atom)
  realizes physically.

SETTINGS A READER SHOULD CHECK MATCH THE PAPER:
  • q_A = 8 (window) ;  lifted-product code  [[544, 80, 12]]
  • physical error 1e-3 ;  cycle time = 24 ms  (= 240000 tenths-of-µs)
  • the 24,000× ratio:  240000 = 24000 · 10  (10 tenths = the 1 µs baseline)

OUR APPROACH:  bind (L1 algorithm, L4 LP code, hardware) as Lean data; smoke-check
  fields by reflexivity (q_A, (n,k,d), cycle); encode the 24 ms cycle as a Nat so the
  24,000× outlier is decidable, surfacing hardware-clock sensitivity ACROSS the corpus.

THE GAP WE DETERMINED:  records + cross-checks the parametric tuple and the cycle-time
  outlier; does NOT semantically verify the code distance/logical-error properties
  from the parity matrices (stubbed `[]`), the physical→logical error curve, or
  end-to-end Shor integration.

STILL UNSOLVED:  code-distance verification from parity matrices; the subthreshold
  logical-error ansatz; end-to-end circuit-depth / FT integration; the neutral-atom
  syndrome-extraction physical model (engineering cross-check, out of formal scope).

This file REDEFINES NOTHING.  Build:  `lake build FormalRV.Audit.Xu2024`.
-/
import FormalRV.Corpus.Xu2024

/-! ## Recorded settings (⬜) — reader checks these against the paper -/
#check @FormalRV.Corpus.Xu2024.xu2024_shor       -- q_A = 8
#check @FormalRV.Corpus.Xu2024.xu2024_code       -- LP [[544, 80, 12]]
#check @FormalRV.Corpus.Xu2024.xu2024_hw         -- 1e-3, 24 ms cycle
#check @FormalRV.Corpus.Xu2024.xu2024_instance

/-! ## The 24,000× cycle-time outlier, re-checked here (➗) -/
-- 24 ms cycle = 240000 tenths-of-µs = 24000 × the 1 µs (10-tenths) baseline:
example : FormalRV.Corpus.Xu2024.xu2024_hw.cycle_time_us_tenths = 24000 * 10 := by decide
