/-
  FormalRV.PauliRotation.Compiler.GateDictionary
  ──────────────────────────────
  The STANDARD gate dictionary into the Pauli-rotation IR (Litinski Table 1,
  full-angle convention `P_θ = e^{-iθP}`, each up to an explicit global
  phase):

      T  = Z_{π/8}          T† = Z_{−π/8}
      S  = Z_{π/4}          S† = Z_{−π/4}
      Z  = Z_{π/2}    X = X_{π/2}    Y = Y_{π/2}     (phase −i each)
      H  = Z_{π/4} · X_{π/4} · Z_{π/4}               (phase e^{−iπ/4})
      CNOT(c,t) = (Z_c X_t)_{π/4} · (Z_c)_{−π/4} · (X_t)_{−π/4}
                                                      (phase e^{iπ/4})
      CCZ(a,b,c) = the SEVEN π/8 rotations of the phase polynomial
                   4·xyz = x+y+z − x⊕y − x⊕z − y⊕z + x⊕y⊕z :
                   +π/8 on each single Z, −π/8 on each pair ZZ,
                   +π/8 on the triple ZZZ — `countPi8 = 7` (seven T's,
                   cf. `PPM/Rules/EightTToCCZScheme.lean`).

  These are concrete syntax trees: well-formedness and the resource counts
  below close by `decide`, and a skeptic can `#eval` the counters directly.

  HONESTY BOUNDARY: this file defines the dictionary and proves its
  STRUCTURAL properties (wf, counts, depth).  The matrix-correctness leg
  (each program's `RotProg.denote` equals the gate matrix up to the stated
  global phase) is the designated next step over `Semantics.lean`
  (`rotOf_pi_div_two` already gives the Pauli rows); the CCZ sign
  orientation will additionally be discharged against the proven net-phase
  data in `PPM/Rules/EightTToCCZScheme.lean`.  Until that leg lands, do NOT
  cite this dictionary as verified semantics.
-/
import FormalRV.PauliRotation.Syntax
import FormalRV.Resource.RotationCount

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog

/-! ## §1. Single-qubit gates. -/

/-- One single-axis rotation as a one-layer program. -/
def rot1 (neg : Bool) (a : RAngle) (k : PKind) (q : Nat) : RotProg :=
  [[⟨neg, a, [⟨q, k⟩]⟩]]

def tGate (q : Nat) : RotProg := rot1 false .piEighth .z q
def tDag  (q : Nat) : RotProg := rot1 true  .piEighth .z q
def sGate (q : Nat) : RotProg := rot1 false .piQuarter .z q
def sDag  (q : Nat) : RotProg := rot1 true  .piQuarter .z q
def zGate (q : Nat) : RotProg := rot1 false .piHalf .z q
def xGate (q : Nat) : RotProg := rot1 false .piHalf .x q
def yGate (q : Nat) : RotProg := rot1 false .piHalf .y q

/-- `H = Z_{π/4} · X_{π/4} · Z_{π/4}` (up to the global phase `e^{−iπ/4}`). -/
def hGate (q : Nat) : RotProg :=
  rot1 false .piQuarter .z q ++ rot1 false .piQuarter .x q
    ++ rot1 false .piQuarter .z q

/-! ## §2. Two-qubit axes and CNOT. -/

/-- The sorted two-qubit product with kind `kc` on `c` and `kt` on `t`
(canonical whatever the index order; `c ≠ t` expected). -/
def mk2 (c : Nat) (kc : PKind) (t : Nat) (kt : PKind) : PauliProduct :=
  if c < t then [⟨c, kc⟩, ⟨t, kt⟩] else [⟨t, kt⟩, ⟨c, kc⟩]

/-- `CNOT(c,t) = (Z_c X_t)_{π/4} · (Z_c)_{−π/4} · (X_t)_{−π/4}` (up to the
global phase `e^{iπ/4}`).  Note the NEGATIVE quarter rotations — this is why
the IR carries signs. -/
def cnotGate (c t : Nat) : RotProg :=
  [[⟨false, .piQuarter, mk2 c .z t .x⟩],
   [⟨true,  .piQuarter, [⟨c, .z⟩]⟩],
   [⟨true,  .piQuarter, [⟨t, .x⟩]⟩]]

/-! ## §3. CCZ: the seven π/8 rotations (T-count 7, no ancilla). -/

/-- `CCZ(a,b,c)` for `a < b < c`: `+π/8` on the three single `Z`s, `−π/8` on
the three pairs, `+π/8` on the triple.  Seven non-Clifford rotations and
NOTHING else — the rotation IR shows the Toffoli-class T-count directly. -/
def cczGate (a b c : Nat) : RotProg :=
  [[⟨false, .piEighth, [⟨a, .z⟩]⟩],
   [⟨false, .piEighth, [⟨b, .z⟩]⟩],
   [⟨false, .piEighth, [⟨c, .z⟩]⟩],
   [⟨true,  .piEighth, [⟨a, .z⟩, ⟨b, .z⟩]⟩],
   [⟨true,  .piEighth, [⟨a, .z⟩, ⟨c, .z⟩]⟩],
   [⟨true,  .piEighth, [⟨b, .z⟩, ⟨c, .z⟩]⟩],
   [⟨false, .piEighth, [⟨a, .z⟩, ⟨b, .z⟩, ⟨c, .z⟩]⟩]]

/-- All seven CCZ axes are Z-type, hence pairwise commuting: the WHOLE CCZ
phase polynomial is ONE parallel layer.  This is the parallelism the layer
structure exists to express. -/
def cczLayer (a b c : Nat) : RotProg :=
  [[⟨false, .piEighth, [⟨a, .z⟩]⟩,
    ⟨false, .piEighth, [⟨b, .z⟩]⟩,
    ⟨false, .piEighth, [⟨c, .z⟩]⟩,
    ⟨true,  .piEighth, [⟨a, .z⟩, ⟨b, .z⟩]⟩,
    ⟨true,  .piEighth, [⟨a, .z⟩, ⟨c, .z⟩]⟩,
    ⟨true,  .piEighth, [⟨b, .z⟩, ⟨c, .z⟩]⟩,
    ⟨false, .piEighth, [⟨a, .z⟩, ⟨b, .z⟩, ⟨c, .z⟩]⟩]]

/-! ## §4. Structural anchors (`decide` on the concrete trees). -/

example : RotProg.wf (tGate 3) = true := by decide
example : RotProg.wf (hGate 0) = true := by decide
example : RotProg.wf (cnotGate 0 1) = true := by decide
example : RotProg.wf (cnotGate 5 2) = true := by decide  -- works either order
example : RotProg.wf (cczGate 0 1 2) = true := by decide
example : RotProg.wf (cczLayer 0 1 2) = true := by decide  -- ONE commuting layer

open FormalRV.Resource in
example : countPi8 (tGate 0) = 1 := by decide          -- T IS one π/8
open FormalRV.Resource in
example : countPi8 (hGate 0) = 0 := by decide          -- H is Clifford-only
open FormalRV.Resource in
example : countPi8 (cnotGate 0 1) = 0 := by decide     -- CNOT is Clifford-only
open FormalRV.Resource in
example : countPi8 (cczGate 0 1 2) = 7 := by decide    -- the famous 7 T's
open FormalRV.Resource in
example : rotDepth (cczGate 0 1 2) = 7 := by decide       -- serialized: depth 7 …
open FormalRV.Resource in
example : rotDepth (cczLayer 0 1 2) = 1 := by decide      -- … grouped: depth 1
open FormalRV.Resource in
example : countPi8 (cczLayer 0 1 2) = 7 := by decide   -- same T-count

end FormalRV.PauliRotation
