/-
  FormalRV.Shor.GidneyTCount — the Gidney-2018 temporary-AND T-count model, and the
  PAPER-EXACT `4L − 4` T-count of the Babbush unary-iteration QROM read.

  ## What this closes

  The audited windowed-Shor lookup is Babbush et al.'s unary-iteration QROM
  (arXiv:1805.03662, §III.A "Unary Iteration" + §III.C "QROM").  The repo's
  `MeasUncomputeAt.unaryQROMAt` already realises it as the merged-AND tree with
  EXACTLY `L − 1 = 2^d − 1` AND gates (`toffoli_unaryQROMAt`) — the paper's AND count.
  But every `CCX` is costed at the textbook 7 T (`Core.Gate.tcount`), so the read's
  `EGate.tcount` is `7·(2^d − 1)`, whereas the paper reports `4L − 4`.

  The gap is the AND *realisation*: the paper (fig. "temporary-and-notation", citing
  Gidney 2018, arXiv:1709.06648) realises each AND as a **temporary AND** — computed
  into a CLEAN ancilla with 4 T, uncomputed by MEASUREMENT (0 T).  The repo already
  has the measurement-uncompute half (`EGate.mz`); the missing half is accounting the
  COMPUTE at 4 T instead of 7.

  `Core.Gate.tcount`'s own docstring mandates the discipline: such optimisations are a
  SEPARATE cost model, "NOT by mutating tcount".  This file supplies that model
  (`gidneyTCount`, with the "4" sourced from the paper-claim constant
  `gidney_2018_logical_AND_compute_tcount`) and proves the read hits `4·(2^d − 1) =
  4L − 4` on the SAME verified syntactic object — honestly, because every `CCX` of the
  QROM tree writes a fresh `mz`-cleared AND-ancilla (a genuine temporary AND).

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasUncomputeAt
import FormalRV.Framework.PaperClaims
import FormalRV.Core.GidneyAND
import FormalRV.Core.GateQASM

namespace FormalRV.Shor.GidneyTCount

open FormalRV.Framework
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasUncomputeAt

/-- **The Gidney-2018 temporary-AND T-count.**  Under Gidney's measurement-based
    logical-AND (arXiv:1709.06648; reproduced in arXiv:1805.03662 fig.
    "temporary-and-notation"), an AND into a clean ancilla costs `4` T to compute and
    `0` T to uncompute (by measurement).  For a circuit `e` whose every Toffoli is such
    a temporary AND — i.e. targets a `|0⟩` ancilla that is later `mz`-cleared, which the
    merged-AND QROM tree satisfies by construction — the honest T-count is

      `gidneyTCount e = (4 T per AND) · (number of ANDs) = 4 · EGate.toffoli e`.

    This is a SEPARATE cost model: it does NOT mutate `EGate.tcount` (which keeps the
    textbook 7-T Toffoli, per the `Core.Gate.tcount` docstring).  The factor `4` is the
    paper-claim constant `gidney_2018_logical_AND_compute_tcount`, so the model is
    traceable to the source, not a magic number. -/
def gidneyTCount (e : EGate) : Nat :=
  PaperClaims.gidney_2018_logical_AND_compute_tcount * EGate.toffoli e

/-- The model is exactly the textbook T-count rescaled by the AND ratio `4 : 7`
    (compute-only temporary AND vs the 7-T Toffoli): `7 · gidneyTCount = 4 · tcount`.
    For the QROM tree (whose only T-source is its ANDs) `gidneyTCount` is therefore the
    genuine T-count under the temporary-AND realisation. -/
theorem gidneyTCount_seven (e : EGate) :
    7 * gidneyTCount e = 4 * (EGate.toffoli e * 7) := by
  unfold gidneyTCount
  show 7 * (4 * EGate.toffoli e) = 4 * (EGate.toffoli e * 7)
  ring

/-- **★ The Babbush–Gidney QROM read hits the paper's exact `4·(2^d − 1) = 4L − 4`
    T-count.**  The merged-AND unary-iteration read of an `L = 2^d`-entry table has
    `L − 1 = 2^d − 1` temporary ANDs (`toffoli_unaryQROMAt`); at 4 T per AND the Gidney
    T-count is `4·(2^d − 1)` — exactly arXiv:1805.03662 §III.A ("a T-count of 4L − 4")
    and §III.C (fig. QROM: "T-count of 4L − 4, due entirely to the unary iteration").
    Holds for ANY address-tree position (`addrBase`, `ancBase`, `ctrl`, `base`) and any
    word map `pos`/width `W`/table `T` — the count is layout-independent. -/
theorem gidneyTCount_unaryQROMAt (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase d ctrl base : Nat) :
    gidneyTCount (unaryQROMAt pos W T addrBase ancBase d ctrl base) = 4 * (2 ^ d - 1) := by
  unfold gidneyTCount
  rw [toffoli_unaryQROMAt]
  rfl

/-- The same headline in the literal `4L − 4` form (`L = 2^d`). -/
theorem gidneyTCount_unaryQROMAt_eq_4L_minus_4 (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase d ctrl base : Nat) :
    gidneyTCount (unaryQROMAt pos W T addrBase ancBase d ctrl base) = 4 * 2 ^ d - 4 := by
  rw [gidneyTCount_unaryQROMAt]
  have h : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  omega

/-- The temporary-AND realisation is strictly cheaper than the textbook one whenever the
    read is non-trivial (`d ≥ 1`): `gidneyTCount = 4·(2^d−1) < 7·(2^d−1) = tcount`. -/
theorem gidneyTCount_unaryQROMAt_lt_tcount (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase d ctrl base : Nat) (hd : 0 < d) :
    gidneyTCount (unaryQROMAt pos W T addrBase ancBase d ctrl base)
      < EGate.tcount (unaryQROMAt pos W T addrBase ancBase d ctrl base) := by
  rw [gidneyTCount_unaryQROMAt, tcount_unaryQROMAt]
  have h : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  omega

/-! ## §2. Abandoning `tcount / 7` — the count is a LITERAL AND-count, and the per-AND
    `4` is a PROVEN real circuit, not a model constant. -/

/-- The LITERAL number of measurement-uncomputed AND gates (`Gate.CCX` nodes) in a measured
    circuit — counted directly, with NO `tcount / 7`. -/
def EGate.numCCX : EGate → Nat
  | .base g => Gate.numCCX g
  | .mz _ => 0
  | .seq a b => EGate.numCCX a + EGate.numCCX b

theorem EGate.tcount_eq_seven_numCCX (e : EGate) :
    EGate.tcount e = 7 * EGate.numCCX e := by
  induction e with
  | base g => exact Gate.tcount_eq_seven_numCCX g
  | mz q => rfl
  | seq a b iha ihb => simp only [EGate.tcount, EGate.numCCX, iha, ihb]; ring

/-- **`tcount / 7` is NOT a heuristic — it provably equals the literal AND-count.**  So the
    `EGate.toffoli := tcount / 7` definition and the honest direct count `EGate.numCCX`
    coincide on the nose; nothing numerical rests on the division. -/
theorem EGate.toffoli_eq_numCCX (e : EGate) : EGate.toffoli e = EGate.numCCX e := by
  unfold EGate.toffoli
  rw [EGate.tcount_eq_seven_numCCX, Nat.mul_div_cancel_left _ (by norm_num)]

/-- The Gidney T-count is `4 × (literal AND-count)` — the per-AND cost times the genuine
    number of ANDs, with no `tcount / 7` in sight. -/
theorem gidneyTCount_eq_four_numCCX (e : EGate) :
    gidneyTCount e = 4 * EGate.numCCX e := by
  unfold gidneyTCount
  rw [EGate.toffoli_eq_numCCX]; rfl

/-- **★ The per-AND `4` is a PROVEN real circuit, not a paper constant. ★**  The factor
    `gidney_2018_logical_AND_compute_tcount` (= 4) used by `gidneyTCount` is EXACTLY the
    literal T-gate count of the verified Clifford+T `Framework.gidneyAND` — the real
    measurement-based AND that `Framework.gidneyAND_correct` proves computes `|a,b,0⟩ ↦
    |a,b,a∧b⟩`.  So `gidneyTCount e = (T-gates in the real Gidney AND) × (number of ANDs)`. -/
theorem gidney_per_AND_is_real_circuit (dim a b c : Nat) :
    PaperClaims.gidney_2018_logical_AND_compute_tcount
      = Framework.tGateCount (Framework.gidneyAND a b c : Framework.BaseUCom dim) := by
  rw [Framework.tGateCount_gidneyAND]
  rfl

/-- **The Babbush read's `4L − 4`, grounded in the real circuit.**  Realising each of the read's
    `2^d − 1` literal ANDs as the verified 4-T `Framework.gidneyAND`, the genuine T-count is
    `tGateCount(gidneyAND) · numCCX(read) = 4·(2^d − 1) = 4L − 4` — paper-exact, on real circuits,
    no `tcount / 7`. -/
theorem realTCount_unaryQROMAt (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase d ctrl base : Nat) (dimA a b cc : Nat) :
    Framework.tGateCount (Framework.gidneyAND a b cc : Framework.BaseUCom dimA)
        * EGate.numCCX (unaryQROMAt pos W T addrBase ancBase d ctrl base)
      = 4 * (2 ^ d - 1) := by
  rw [Framework.tGateCount_gidneyAND, ← EGate.toffoli_eq_numCCX, toffoli_unaryQROMAt]

end FormalRV.Shor.GidneyTCount
