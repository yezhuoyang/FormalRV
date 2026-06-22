/-
  FormalRV.Audit.GidneyEkera2021.PhysicalSyndrome
  ───────────────────────────────────────────────
  **THE PHYSICAL SYNDROME-EXTRACTION FOOTPRINT of the GE2021 surface-code
  patch — every syndrome ancilla counted, by theorem.**

  Gidney–Ekerå store each logical qubit in a distance-`d` surface patch and
  run one syndrome-extraction round per surface-code cycle.  The repo's
  PhysCircuit IR builds that round with EXPLICIT measure/ancilla qubits
  (`extractionBlocks`: data `0‥n−1`, one X-syndrome ancilla per `hx` row,
  one Z-syndrome ancilla per `hz` row), and the proven width counter gives

      widthC (extraction round)  =  n  +  |hx|  +  |hz|
                                    data  X-synd   Z-synd

  This file pins the syndrome-ancilla counts of the GE2021 distance-`d`
  code PARAMETRICALLY (HGP row arithmetic), instantiates at `d = 27`, and
  reconciles the result to the paper's per-patch footprint
  `2(d+1)² = 1568` — surfacing, honestly, that the repo's VERIFIED code is
  the UNROTATED surface code (more data qubits than the paper's rotated
  patch; the rotated [[d²,1,d]] choice is documented as the remaining
  fidelity step).

  Distillation (T / CCZ factories) is the paper's OWN black box — GE2021
  cites gidney2018magic/gidney2019autoccz for the AutoCCZ factory rather
  than deriving it — so it is modeled at the factory level elsewhere
  (`PPM/QECBridge/FactoryHierarchy`), not as a verified circuit here.
-/
import FormalRV.QEC.Codes.Surface.SurfaceFamily
import FormalRV.QEC.Codes.Surface.RotatedSurface
import FormalRV.QEC.Circuit.ExtractionCount

namespace FormalRV.Audit.GidneyEkera2021

open FormalRV.QEC
open FormalRV.QEC.Circuit
open FormalRV.QEC.Algebraic
open FormalRV.QEC.Codes
open FormalRV.Framework.LDPC
open FormalRV.Resource

/-! ## §1. HGP row arithmetic: how many syndrome ancillas. -/

/-- A Kronecker block has `|A|·|B|` rows. -/
theorem kron_length (A B : BoolMat) :
    (kron A B).length = A.length * B.length := by
  unfold kron
  rw [List.length_flatMap]
  rw [show (A.map (fun arow => (B.map (fun brow =>
        arow.flatMap (fun a => brow.map (fun b => a && b)))).length))
      = A.map (fun _ => B.length) from by
    apply List.map_congr_left
    intro arow _
    rw [List.length_map]]
  rw [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]

/-- `identMat n` has `n` rows. -/
theorem identMat_length (n : Nat) : (identMat n).length = n := by
  unfold identMat
  rw [List.length_map, List.length_range]

/-- `repCode d` has `d − 1` rows. -/
theorem repCode_length (d : Nat) : (repCode d).length = d - 1 := by
  unfold repCode
  rw [List.length_map, List.length_range]

/-- `transpose h n` has `n` rows (one per original column). -/
theorem transpose_length (h : BoolMat) (n : Nat) :
    (transpose h n).length = n := by
  unfold transpose
  rw [List.length_map, List.length_range]

/-- `hcat` (row-wise concatenation) has `min` of the heights. -/
theorem hcat_length (L R : BoolMat) :
    (hcat L R).length = min L.length R.length := by
  unfold hcat
  rw [List.length_zipWith]

/-- **The X-syndrome ancilla count**: `(surfaceHGP d).hx` has `(d−1)·d`
rows — one X-check ancilla each. -/
theorem surfaceHGP_hx_length (d : Nat) :
    (surfaceHGP d).hx.length = (d - 1) * d := by
  show (hcat (kron (repCode d) (identMat d))
        (kron (identMat (d - 1)) (transpose (repCode d) d))).length = _
  rw [hcat_length, kron_length, kron_length, repCode_length, identMat_length,
      identMat_length, transpose_length, Nat.min_self]

/-- **The Z-syndrome ancilla count**: `(surfaceHGP d).hz` has `(d−1)·d`
rows. -/
theorem surfaceHGP_hz_length (d : Nat) :
    (surfaceHGP d).hz.length = (d - 1) * d := by
  show (hcat (kron (identMat d) (repCode d))
        (kron (transpose (repCode d) d) (identMat (d - 1)))).length = _
  rw [hcat_length, kron_length, kron_length, identMat_length, repCode_length,
      transpose_length, identMat_length]
  rw [Nat.mul_comm d (d - 1), Nat.min_self]

/-- **Total syndrome ancillas** of the distance-`d` patch: `2(d−1)d`. -/
def syndromeAncillas (d : Nat) : Nat := 2 * (d - 1) * d

theorem syndromeAncillas_eq (d : Nat) :
    (surfaceHGP d).hx.length + (surfaceHGP d).hz.length = syndromeAncillas d := by
  rw [surfaceHGP_hx_length, surfaceHGP_hz_length]
  unfold syndromeAncillas
  rw [Nat.two_mul, Nat.add_mul]

/-! ## §2. The physical extraction footprint, by theorem. -/

/-- Total physical qubits of one syndrome-extraction round of the
distance-`d` patch: data `+` X-syndrome `+` Z-syndrome. -/
def extractionPhysicalQubits (d : Nat) : Nat :=
  (surfaceHGP d).n + syndromeAncillas d

/-- Every row of `surfaceHGP d` (both `hx` and `hz`) is within the data
register `n` — the side condition for the width theorem. -/
private theorem surfaceHGP_rows_le (d : Nat)
    (hws : (surfaceHGP d).well_shaped = true) :
    (∀ row ∈ (surfaceHGP d).hx, row.length ≤ (surfaceHGP d).n)
      ∧ (∀ row ∈ (surfaceHGP d).hz, row.length ≤ (surfaceHGP d).n) := by
  unfold CSSCode.well_shaped FormalRV.Framework.LDPC.matrix_has_n_cols at hws
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hws
  exact ⟨fun row hrow => Nat.le_of_eq (hws.1 row hrow),
         fun row hrow => Nat.le_of_eq (hws.2 row hrow)⟩

/-- **THE PHYSICAL SYNDROME-EXTRACTION THEOREM**: the width counter on the
compiled extraction round of the distance-`d` patch returns EXACTLY
`data + syndrome ancillas` — the syndrome overhead is in the syntax tree
and counted, for every well-shaped `d`. -/
theorem widthC_ge2021_extraction (d : Nat)
    (hws : (surfaceHGP d).well_shaped = true)
    (hnz : (surfaceHGP d).hz ≠ []) :
    widthC (Round.ops (CSSCode.extractionRound (surfaceHGP d)))
      = extractionPhysicalQubits d := by
  obtain ⟨hxr, hzr⟩ := surfaceHGP_rows_le d hws
  show widthC (Round.ops (extractionBlocks (surfaceHGP d).n
      (surfaceHGP d).hx (surfaceHGP d).hz)) = _
  rw [widthC_extractionBlocks _ _ _ hxr hzr hnz]
  unfold extractionPhysicalQubits
  rw [← syndromeAncillas_eq]
  omega

/-! ## §3. The GE2021 distance-27 instantiation. -/

/-- The GE2021 level-2 (data) code distance. -/
def ge2021Distance : Nat := 27

/-- The GE2021 data code, distance 27 — the repo's verified construction
`[[1405, 1, 27]]` (UNROTATED surface code). -/
abbrev ge2021DataCode : CSSCode := surfaceHGP ge2021Distance

/-- 1405 data qubits (`27² + 26²`). -/
theorem ge2021_data_qubits : ge2021DataCode.n = 1405 := rfl

/-- 702 X-syndrome ancillas (`26·27`). -/
theorem ge2021_x_syndrome : ge2021DataCode.hx.length = 702 := by
  rw [surfaceHGP_hx_length]; rfl

/-- 702 Z-syndrome ancillas. -/
theorem ge2021_z_syndrome : ge2021DataCode.hz.length = 702 := by
  rw [surfaceHGP_hz_length]; rfl

/-- **1404 total syndrome ancillas** for the GE2021 patch (`= n − k`). -/
theorem ge2021_syndrome_ancillas : syndromeAncillas ge2021Distance = 1404 := by
  unfold syndromeAncillas ge2021Distance
  norm_num

/-- **2809 physical qubits** in one GE2021 syndrome-extraction round
(1405 data + 1404 syndrome). -/
theorem ge2021_extraction_physical : extractionPhysicalQubits ge2021Distance = 2809 := by
  unfold extractionPhysicalQubits
  rw [ge2021_syndrome_ancillas]
  rfl

/-! ## §4. Reconciliation to the paper's per-patch footprint. -/

/-- The paper's per-patch physical footprint: `2(d+1)²` (rotated surface
code, data + measure qubits + inter-patch spacing). -/
def paperPatchFootprint (d : Nat) : Nat := 2 * (d + 1) * (d + 1)

/-- **1568 physical qubits per patch at `d = 27`** — the paper's figure
(§"Physical qubit count": each logical qubit covers `2(d+1)²`). -/
theorem paper_patch_1568 : paperPatchFootprint ge2021Distance = 1568 := by
  unfold paperPatchFootprint ge2021Distance
  norm_num

/-- The rotated surface code the paper actually uses would have `d²` data
and `d² − 1` measure qubits = `2d² − 1` physical, plus inter-patch
spacing up to `2(d+1)²`.  At `d = 27`: `729` data, `728` measure, `1457`
physical, padded to `1568`. -/
theorem rotated_patch_accounting :
    27 * 27 = 729                          -- rotated data qubits
      ∧ 27 * 27 - 1 = 728                   -- rotated measure (syndrome) qubits
      ∧ 27 * 27 + (27 * 27 - 1) = 1457      -- rotated data + measure
      ∧ paperPatchFootprint 27 = 1568       -- + spacing (the paper's figure)
      ∧ 1568 - 1457 = 111 := by
  refine ⟨rfl, rfl, rfl, paper_patch_1568, rfl⟩

/-- **THE FOOTPRINT-EXACT GE2021 PATCH (now verified)**: the rotated
`[[729, 1, 27]]` surface code — the ACTUAL code the paper uses — is a
verified valid CSS code (`RotatedSurface.rotatedSurface27_valid`) with
729 data + 728 syndrome = 1457 physical qubits per extraction round, and
the paper's per-patch figure `2(d+1)² = 1568` is exactly that plus the
111-qubit routing border.  The unrotated `[[1405,1,27]]` HGP construction
(used elsewhere in the audit) is the heavier stand-in. -/
theorem ge2021_footprint_exact :
    (FormalRV.QEC.Codes.Surface.rotatedSurface 27).valid = true   -- verified rotated patch
      ∧ FormalRV.QEC.Codes.Surface.rotatedPhysicalQubits 27 = 1457  -- data + syndrome
      ∧ paperPatchFootprint ge2021Distance = 1568                  -- paper (+ spacing)
      ∧ 1568 - 1457 = 111 := by                                    -- routing border
  exact ⟨FormalRV.QEC.Codes.Surface.rotatedSurface27_valid,
         FormalRV.QEC.Codes.Surface.rotated27_physical,
         paper_patch_1568, by decide⟩

/-! ## §5. Syndrome extraction IS correct (the semantic anchor).

The compiled extraction round of any well-shaped CSS code measures EXACTLY
the code's stabilizers (`extractionRound_measures_code`, CircuitSemantics);
for the surface family this is `family_extraction_measures`.  So the GE2021
syndrome circuit is not merely sized correctly — it measures the right
operators (per-block segmentation caveat noted upstream). -/

set_option maxRecDepth 8192 in
/-- The GE2021 syndrome-extraction round measures the data code's
stabilizers (instantiating the surface-family semantics theorem). -/
theorem ge2021_extraction_measures_code
    (hws : ge2021DataCode.well_shaped = true) :
    Round.measuredDataObs
        (ge2021DataCode.n + ge2021DataCode.hx.length + ge2021DataCode.hz.length)
        ge2021DataCode.n (Surface.extractionRound ge2021Distance)
      = ge2021DataCode.toStabilizers :=
  Surface.family_extraction_measures ge2021Distance hws

end FormalRV.Audit.GidneyEkera2021
