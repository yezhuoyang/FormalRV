/-
  FormalRV.LatticeSurgery.LaSsynthImport — SAT-synthesized lattice surgeries (Tan, Niu &
  Gidney, "A SAT Scalpel for Lattice Surgery", ISCA 2024) imported into our ZX/PPM
  IR by `PyCircuits/lasre_to_ppm.py`.

  Each design's `.lasre.json` (the *optimized*, minimum-spacetime-volume LaS that
  LaSsynth's SAT solver produces) is parsed into a `ZXDiagram`: every Z/X
  cube-spider becomes a Pauli-product MEASUREMENT (`mkSpider`).  This is the user's
  thesis — "all lattice surgery, even optimized, goes through PPM" — applied to
  REAL optimizer output: the synthesized design is, in our framework, a PPM program.

  Correctness is certified externally by stimzx (`verify_stabilizers_stimzx = True`,
  see `PyCircuits/lasre_verify.py`), whose algorithm interprets every spider as a
  postselected parity measurement — identical to our `zxToPPM`.  `factory121` is a
  PURE measurement fragment (0 H domain-walls), so its import is fully faithful;
  `majority_gate` additionally has 6 H domain-walls (basis changes), recorded
  separately for the faithful replay.

  GENERATED — do not edit by hand.  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Rules.ZXStabilizer

namespace FormalRV.LatticeSurgery.LaSsynthImport

open FormalRV.Framework.ZX

/-- ZXDiagram of the SAT-synthesized `factory121` lattice surgery (LaSsynth), imported by `PyCircuits/lasre_to_ppm.py`.
    97 Z/X measurement spiders over 132 edge-qubits. -/
def factory121_zx : ZXDiagram :=
  [
    mkSpider ZXColor.X [4, 16] 132,
    mkSpider ZXColor.X [5, 17] 132,
    mkSpider ZXColor.X [6, 18] 132,
    mkSpider ZXColor.X [7, 19] 132,
    mkSpider ZXColor.X [8, 20] 132,
    mkSpider ZXColor.X [9, 21] 132,
    mkSpider ZXColor.X [10, 22] 132,
    mkSpider ZXColor.X [11, 23] 132,
    mkSpider ZXColor.X [12, 24] 132,
    mkSpider ZXColor.X [13, 25] 132,
    mkSpider ZXColor.X [14, 26] 132,
    mkSpider ZXColor.X [16, 27, 28] 132,
    mkSpider ZXColor.X [17, 29] 132,
    mkSpider ZXColor.X [18, 30] 132,
    mkSpider ZXColor.X [19, 31] 132,
    mkSpider ZXColor.X [20, 32] 132,
    mkSpider ZXColor.X [21, 33] 132,
    mkSpider ZXColor.X [22, 34] 132,
    mkSpider ZXColor.X [23, 35] 132,
    mkSpider ZXColor.X [24, 36] 132,
    mkSpider ZXColor.X [25, 37] 132,
    mkSpider ZXColor.X [26, 38] 132,
    mkSpider ZXColor.X [27, 39] 132,
    mkSpider ZXColor.Z [39] 132,
    mkSpider ZXColor.Z [0, 40, 41] 132,
    mkSpider ZXColor.Z [40, 42, 43] 132,
    mkSpider ZXColor.Z [42, 44, 45] 132,
    mkSpider ZXColor.X [44, 46] 132,
    mkSpider ZXColor.Z [46, 47, 48] 132,
    mkSpider ZXColor.X [47, 49] 132,
    mkSpider ZXColor.X [49, 50] 132,
    mkSpider ZXColor.Z [50, 51, 52] 132,
    mkSpider ZXColor.X [51, 53] 132,
    mkSpider ZXColor.Z [53, 54, 55] 132,
    mkSpider ZXColor.X [54, 56] 132,
    mkSpider ZXColor.X [28, 41, 57, 58] 132,
    mkSpider ZXColor.X [29, 43, 59, 60] 132,
    mkSpider ZXColor.X [30, 45, 61] 132,
    mkSpider ZXColor.X [31, 62, 63] 132,
    mkSpider ZXColor.X [32, 48, 64, 65] 132,
    mkSpider ZXColor.X [33, 66] 132,
    mkSpider ZXColor.X [34, 67, 68] 132,
    mkSpider ZXColor.X [35, 52, 69] 132,
    mkSpider ZXColor.X [36, 70, 71] 132,
    mkSpider ZXColor.X [37, 55, 72] 132,
    mkSpider ZXColor.X [38, 56, 73, 74] 132,
    mkSpider ZXColor.Z [1, 57, 75] 132,
    mkSpider ZXColor.Z [59, 75, 76] 132,
    mkSpider ZXColor.X [76, 77] 132,
    mkSpider ZXColor.Z [62, 77, 78] 132,
    mkSpider ZXColor.Z [64, 78, 79] 132,
    mkSpider ZXColor.X [79, 80] 132,
    mkSpider ZXColor.Z [67, 80, 81] 132,
    mkSpider ZXColor.X [81, 82] 132,
    mkSpider ZXColor.Z [70, 82, 83] 132,
    mkSpider ZXColor.X [83, 84] 132,
    mkSpider ZXColor.X [73, 84] 132,
    mkSpider ZXColor.Z [2, 85, 86] 132,
    mkSpider ZXColor.X [85, 87] 132,
    mkSpider ZXColor.Z [87, 88, 89] 132,
    mkSpider ZXColor.Z [88, 90, 91] 132,
    mkSpider ZXColor.Z [90, 92, 93] 132,
    mkSpider ZXColor.Z [92, 94, 95] 132,
    mkSpider ZXColor.X [94, 96] 132,
    mkSpider ZXColor.X [96, 97] 132,
    mkSpider ZXColor.Z [97, 98, 99] 132,
    mkSpider ZXColor.X [98, 100] 132,
    mkSpider ZXColor.X [58, 86, 101] 132,
    mkSpider ZXColor.X [60, 102] 132,
    mkSpider ZXColor.X [61, 89, 103] 132,
    mkSpider ZXColor.X [63, 91, 104] 132,
    mkSpider ZXColor.X [65, 93, 105, 106] 132,
    mkSpider ZXColor.X [66, 95, 107, 108] 132,
    mkSpider ZXColor.X [68, 109, 110] 132,
    mkSpider ZXColor.X [69, 111, 112] 132,
    mkSpider ZXColor.X [71, 99, 113] 132,
    mkSpider ZXColor.X [72, 100, 114] 132,
    mkSpider ZXColor.X [74, 115] 132,
    mkSpider ZXColor.X [3, 116] 132,
    mkSpider ZXColor.Z [102, 116, 117] 132,
    mkSpider ZXColor.Z [103, 117, 118] 132,
    mkSpider ZXColor.Z [104, 118, 119] 132,
    mkSpider ZXColor.Z [105, 119, 120] 132,
    mkSpider ZXColor.Z [107, 120, 121] 132,
    mkSpider ZXColor.Z [109, 121, 122] 132,
    mkSpider ZXColor.X [111, 122] 132,
    mkSpider ZXColor.X [101, 123] 132,
    mkSpider ZXColor.X [123, 124] 132,
    mkSpider ZXColor.X [124, 125] 132,
    mkSpider ZXColor.Z [125] 132,
    mkSpider ZXColor.X [106, 126] 132,
    mkSpider ZXColor.Z [108, 126, 127] 132,
    mkSpider ZXColor.Z [110, 127, 128] 132,
    mkSpider ZXColor.Z [112, 128, 129] 132,
    mkSpider ZXColor.Z [113, 129, 130] 132,
    mkSpider ZXColor.Z [114, 130, 131] 132,
    mkSpider ZXColor.Z [15, 115, 131] 132
  ]

/-- The optimized `factory121` imported as 97 Pauli-product measurements (every spider is a PPM), and the ZX→PPM translation
    yields exactly one measurement per spider. -/
example : factory121_zx.length = 97 := rfl
example : (zxToPPM factory121_zx).length = factory121_zx.length := by simp [zxToPPM]

/-- ZXDiagram of the SAT-synthesized `majority_gate` lattice surgery (LaSsynth), imported by `PyCircuits/lasre_to_ppm.py`.
    43 Z/X measurement spiders over 58 edge-qubits. -/
def majority_gate_zx : ZXDiagram :=
  [
    mkSpider ZXColor.Z [1, 9, 10] 58,
    mkSpider ZXColor.X [4, 11] 58,
    mkSpider ZXColor.Z [11, 12, 13] 58,
    mkSpider ZXColor.X [12, 14] 58,
    mkSpider ZXColor.X [9, 15, 16] 58,
    mkSpider ZXColor.X [15, 17] 58,
    mkSpider ZXColor.X [13, 18] 58,
    mkSpider ZXColor.X [14, 19] 58,
    mkSpider ZXColor.X [16, 20] 58,
    mkSpider ZXColor.X [20, 21] 58,
    mkSpider ZXColor.X [7, 22] 58,
    mkSpider ZXColor.X [5, 19] 58,
    mkSpider ZXColor.X [2, 23] 58,
    mkSpider ZXColor.X [10, 24] 58,
    mkSpider ZXColor.X [8, 25] 58,
    mkSpider ZXColor.X [26, 27] 58,
    mkSpider ZXColor.X [26, 28] 58,
    mkSpider ZXColor.X [29, 30] 58,
    mkSpider ZXColor.X [24, 31] 58,
    mkSpider ZXColor.X [17, 25, 32] 58,
    mkSpider ZXColor.X [18, 27, 33] 58,
    mkSpider ZXColor.X [34, 35] 58,
    mkSpider ZXColor.X [36, 37] 58,
    mkSpider ZXColor.X [31, 38] 58,
    mkSpider ZXColor.Z [0, 32, 39] 58,
    mkSpider ZXColor.X [39, 40] 58,
    mkSpider ZXColor.X [34, 41] 58,
    mkSpider ZXColor.X [23, 36] 58,
    mkSpider ZXColor.X [3, 42] 58,
    mkSpider ZXColor.X [6, 43] 58,
    mkSpider ZXColor.X [43, 44] 58,
    mkSpider ZXColor.X [45, 46, 47] 58,
    mkSpider ZXColor.X [29, 45] 58,
    mkSpider ZXColor.X [42, 48] 58,
    mkSpider ZXColor.X [48, 49] 58,
    mkSpider ZXColor.X [33, 49] 58,
    mkSpider ZXColor.Z [35, 46, 50] 58,
    mkSpider ZXColor.X [37, 51] 58,
    mkSpider ZXColor.X [38, 52] 58,
    mkSpider ZXColor.X [52, 53] 58,
    mkSpider ZXColor.X [53, 54] 58,
    mkSpider ZXColor.X [50, 55, 56] 58,
    mkSpider ZXColor.X [51, 57] 58
  ]

/-- `majority_gate` H domain-walls (basis-change nodes), each over its incident edge-qubits. -/
def majority_gate_hwalls : List (List Nat) :=
  [
    [21, 22],
    [28, 30],
    [40, 41],
    [44, 47],
    [54, 55],
    [56, 57]
  ]

/-- The optimized `majority_gate` imported as 43 Pauli-product measurements (every spider is a PPM), and the ZX→PPM translation
    yields exactly one measurement per spider. -/
example : majority_gate_zx.length = 43 := rfl
example : (zxToPPM majority_gate_zx).length = majority_gate_zx.length := by simp [zxToPPM]

end FormalRV.LatticeSurgery.LaSsynthImport
