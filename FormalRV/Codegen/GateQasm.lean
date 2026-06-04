/-
  FormalRV.Codegen.GateQasm — emit logical OpenQASM 2.0 from the `Gate` IR,
  with PROVED faithfulness theorems at BOTH the classical (native) and the
  quantum (Clifford+T) level.

  ## What is proved

  * NATIVE (`x`/`cx`/`ccx`):  `emitOps_applyNat` — the emitted native program,
    under its Boolean (qelib1) semantics, equals the verified `Gate.applyNat`.
  * CLIFFORD+T (`h`/`t`/`tdg`/`x`/`cx`):  `emitCliffT_acts_on_basis` — the
    emitted Clifford+T program's UNITARY (`progMat`, built from `BaseUCom`
    `uc_eval` matrices) acts on every basis state exactly as `Gate.applyNat`.
    The `CCX` lowering is aligned with `BaseUCom.CCX` (the 7-T decomposition
    the whole verified Shor stack rides on); its Toffoli action is the repo's
    proven `gate_ccx_acts_on_basis`, so nothing about the 7-T identity is
    re-derived or assumed.

  Both are kernel-clean; rendering (ops → text) is a syntactic serialization.
-/
import FormalRV.Arithmetic.Correctness
import FormalRV.Arithmetic.ModularAdder.Defs

namespace FormalRV.Codegen

open FormalRV.Framework
open FormalRV.BQAlgo

/-! ## §1. The classical-reversible OpenQASM subset, with Boolean semantics. -/

/-- OpenQASM register reference `q[i]`. -/
def qref (q : Nat) : String := "q[" ++ toString q ++ "]"

/-- The classical-reversible `qelib1` gates: bit-flip, CNOT, Toffoli. -/
inductive QasmOp where
  | x   : Nat → QasmOp
  | cx  : Nat → Nat → QasmOp
  | ccx : Nat → Nat → Nat → QasmOp
  deriving Repr, DecidableEq

/-- Boolean (basis-state) semantics, matching `qelib1` and `Gate.applyNat`. -/
def QasmOp.applyNat : QasmOp → (Nat → Bool) → (Nat → Bool)
  | QasmOp.x q,       f => update f q (!f q)
  | QasmOp.cx c t,    f => update f t (xor (f t) (f c))
  | QasmOp.ccx a b c, f => update f c (xor (f c) (f a && f b))

/-- Run a native program left-to-right. -/
def applyProg (prog : List QasmOp) (f : Nat → Bool) : Nat → Bool :=
  prog.foldl (fun s op => op.applyNat s) f

/-- OpenQASM 2.0 text for one native op. -/
def QasmOp.render : QasmOp → String
  | QasmOp.x q       => "x " ++ qref q ++ ";"
  | QasmOp.cx c t    => "cx " ++ qref c ++ "," ++ qref t ++ ";"
  | QasmOp.ccx a b c => "ccx " ++ qref a ++ "," ++ qref b ++ "," ++ qref c ++ ";"

theorem applyProg_append (p q : List QasmOp) (f : Nat → Bool) :
    applyProg (p ++ q) f = applyProg q (applyProg p f) := by
  simp only [applyProg, List.foldl_append]

/-- **Native emitter (structured).** -/
def emitOps : Gate → List QasmOp
  | Gate.I         => []
  | Gate.X q       => [QasmOp.x q]
  | Gate.CX c t    => [QasmOp.cx c t]
  | Gate.CCX a b c => [QasmOp.ccx a b c]
  | Gate.seq g₁ g₂ => emitOps g₁ ++ emitOps g₂

/-- **★ Native faithfulness ★** — the emitted native program equals the
    verified Boolean semantics `Gate.applyNat`, for every gate. -/
theorem emitOps_applyNat (g : Gate) (f : Nat → Bool) :
    applyProg (emitOps g) f = Gate.applyNat g f := by
  induction g generalizing f with
  | I => rfl
  | X q => rfl
  | CX c t => rfl
  | CCX a b c => rfl
  | seq g₁ g₂ ih₁ ih₂ =>
    show applyProg (emitOps g₁ ++ emitOps g₂) f = Gate.applyNat g₂ (Gate.applyNat g₁ f)
    rw [applyProg_append, ih₁, ih₂]

/-! ## §2. Width and the verified-permutation cross-check (native). -/

def widthOf : Gate → Nat
  | Gate.I         => 0
  | Gate.X q       => q + 1
  | Gate.CX c t    => max (c + 1) (t + 1)
  | Gate.CCX a b c => max (max (a + 1) (b + 1)) (c + 1)
  | Gate.seq g₁ g₂ => max (widthOf g₁) (widthOf g₂)

def packBits (dim : Nat) (f : Nat → Bool) : Nat :=
  (List.range dim).foldl (fun acc q => acc + (if f q then 2 ^ q else 0)) 0

def permAt (dim : Nat) (g : Gate) (x : Nat) : Nat :=
  packBits dim (Gate.applyNat g (fun q => x.testBit q))

def permAtProg (dim : Nat) (prog : List QasmOp) (x : Nat) : Nat :=
  packBits dim (applyProg prog (fun q => x.testBit q))

theorem emitOps_permAt (dim : Nat) (g : Gate) (x : Nat) :
    permAtProg dim (emitOps g) x = permAt dim g x := by
  unfold permAtProg permAt; rw [emitOps_applyNat]

/-- Native OpenQASM text. -/
def emitNative (g : Gate) : List String := (emitOps g).map QasmOp.render

/-! ## §3. The Clifford+T op IR, its unitary, and the emitter.

The Clifford+T gates `h`/`t`/`tdg`/`x`/`cx` denote `BaseUCom` gates; the
emitted program's unitary is `progMat`.  The `CCX` lowering is the exact
sequence of `BaseUCom.CCX` (the repo's 7-T Toffoli, `QuantumGate.lean:189`). -/

/-- A Clifford+T OpenQASM op. -/
inductive CliffTOp where
  | h   : Nat → CliffTOp
  | t   : Nat → CliffTOp
  | tdg : Nat → CliffTOp
  | x   : Nat → CliffTOp
  | cx  : Nat → Nat → CliffTOp
  deriving Repr, DecidableEq

/-- OpenQASM 2.0 text for one Clifford+T op. -/
def CliffTOp.render : CliffTOp → String
  | CliffTOp.h n    => "h " ++ qref n ++ ";"
  | CliffTOp.t n    => "t " ++ qref n ++ ";"
  | CliffTOp.tdg n  => "tdg " ++ qref n ++ ";"
  | CliffTOp.x n     => "x " ++ qref n ++ ";"
  | CliffTOp.cx c tg => "cx " ++ qref c ++ "," ++ qref tg ++ ";"

/-- The `BaseUCom` unitary of one Clifford+T op at dimension `dim`. -/
noncomputable def CliffTOp.mat (dim : Nat) : CliffTOp → Square dim
  | CliffTOp.h n    => uc_eval (BaseUCom.H n)
  | CliffTOp.t n    => uc_eval (BaseUCom.T n)
  | CliffTOp.tdg n  => uc_eval (BaseUCom.TDAG n)
  | CliffTOp.x n     => uc_eval (BaseUCom.X n)
  | CliffTOp.cx c tg => uc_eval (BaseUCom.CNOT c tg)

/-- Unitary realised by a Clifford+T program: circuit order left-to-right =
    matrix product right-to-left, starting from the identity. -/
noncomputable def progMat (dim : Nat) : List CliffTOp → Square dim
  | []      => 1
  | op :: l => progMat dim l * op.mat dim

theorem progMat_append (dim : Nat) (l1 l2 : List CliffTOp) :
    progMat dim (l1 ++ l2) = progMat dim l2 * progMat dim l1 := by
  induction l1 with
  | nil => simp [progMat]
  | cons op l ih =>
    show progMat dim (op :: (l ++ l2)) = progMat dim l2 * progMat dim (op :: l)
    simp only [progMat, ih, Matrix.mul_assoc]

/-- **Clifford+T emitter (structured).**  `CCX` → the exact 7-T sequence of
    `BaseUCom.CCX` (controls `a`,`b`; target `c`). -/
def emitCliffTOps : Gate → List CliffTOp
  | Gate.I         => []
  | Gate.X q       => [CliffTOp.x q]
  | Gate.CX c t    => [CliffTOp.cx c t]
  | Gate.CCX a b c =>
      [CliffTOp.h c,   CliffTOp.cx b c, CliffTOp.tdg c, CliffTOp.cx a c,
       CliffTOp.t c,   CliffTOp.cx b c, CliffTOp.tdg c, CliffTOp.cx a c,
       CliffTOp.cx a b, CliffTOp.tdg b, CliffTOp.cx a b,
       CliffTOp.t a,   CliffTOp.t b,   CliffTOp.t c,    CliffTOp.h c]
  | Gate.seq g₁ g₂ => emitCliffTOps g₁ ++ emitCliffTOps g₂

/-- Clifford+T OpenQASM text = rendering of the verified ops. -/
def emitCliffT (g : Gate) : List String := (emitCliffTOps g).map CliffTOp.render

/-- The emitted 7-T sequence realises exactly the `BaseUCom.CCX` unitary
    (same 15 gate factors, re-associated). -/
theorem progMat_CCX (dim a b c : Nat) :
    progMat dim (emitCliffTOps (Gate.CCX a b c)) = uc_eval (BaseUCom.CCX a b c : BaseUCom dim) := by
  simp only [emitCliffTOps, progMat, CliffTOp.mat, BaseUCom.CCX, uc_eval_seq,
             Matrix.one_mul, Matrix.mul_assoc]

/-! ## §4. ★ Clifford+T faithfulness ★ -/

/-- **The emitted Clifford+T circuit's unitary acts on every basis state
    exactly as the verified Boolean semantics `Gate.applyNat`.**  The `CCX`
    case is the repo's proven `gate_ccx_acts_on_basis` (the 7-T Toffoli
    action); `X`/`CX` use `gate_x/cx_acts_on_basis`; `seq` composes via
    `progMat_append`.  Requires `Gate.WellTyped dim g` (the gate identities
    need each qubit `< dim` and the multi-qubit gates' qubits distinct). -/
theorem emitCliffT_acts_on_basis (dim : Nat) (g : Gate) :
    ∀ (f : Nat → Bool), Gate.WellTyped dim g →
      progMat dim (emitCliffTOps g) * f_to_vec dim f = f_to_vec dim (Gate.applyNat g f) := by
  induction g with
  | I =>
    intro f _
    simp only [emitCliffTOps, progMat, Gate.applyNat, Matrix.one_mul]
  | X q =>
    intro f hwt
    have hq : q < dim := hwt
    calc progMat dim (emitCliffTOps (Gate.X q)) * f_to_vec dim f
        = uc_eval (Gate.toUCom dim (Gate.X q)) * f_to_vec dim f := by
          simp [emitCliffTOps, progMat, CliffTOp.mat, Gate.toUCom_X]
      _ = f_to_vec dim (update f q (!f q)) := gate_x_acts_on_basis dim q hq f
      _ = f_to_vec dim (Gate.applyNat (Gate.X q) f) := rfl
  | CX c t =>
    intro f hwt
    have hwt' : c < dim ∧ t < dim ∧ c ≠ t := hwt
    obtain ⟨hc, ht, hct⟩ := hwt'
    calc progMat dim (emitCliffTOps (Gate.CX c t)) * f_to_vec dim f
        = uc_eval (Gate.toUCom dim (Gate.CX c t)) * f_to_vec dim f := by
          simp [emitCliffTOps, progMat, CliffTOp.mat, Gate.toUCom_CX]
      _ = f_to_vec dim (update f t (xor (f t) (f c))) := gate_cx_acts_on_basis dim c t hc ht hct f
      _ = f_to_vec dim (Gate.applyNat (Gate.CX c t) f) := rfl
  | CCX a b c =>
    intro f hwt
    have hwt' : a < dim ∧ b < dim ∧ c < dim ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := hwt
    obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := hwt'
    calc progMat dim (emitCliffTOps (Gate.CCX a b c)) * f_to_vec dim f
        = uc_eval (Gate.toUCom dim (Gate.CCX a b c)) * f_to_vec dim f := by
          rw [progMat_CCX, Gate.toUCom_CCX]
      _ = f_to_vec dim (update f c (xor (f c) (f a && f b))) :=
          gate_ccx_acts_on_basis dim a b c ha hb hc hab hac hbc f
      _ = f_to_vec dim (Gate.applyNat (Gate.CCX a b c) f) := rfl
  | seq g₁ g₂ ih₁ ih₂ =>
    intro f hwt
    obtain ⟨hwt₁, hwt₂⟩ := hwt
    show progMat dim (emitCliffTOps g₁ ++ emitCliffTOps g₂) * f_to_vec dim f
        = f_to_vec dim (Gate.applyNat g₂ (Gate.applyNat g₁ f))
    rw [progMat_append, Matrix.mul_assoc, ih₁ f hwt₁]
    exact ih₂ (Gate.applyNat g₁ f) hwt₂

/-! ## §5. OpenQASM text + smoke checks. -/

/-- Full OpenQASM 2.0 program.  `cliffT = true` ⇒ Clifford+T basis. -/
def toQasm (g : Gate) (cliffT : Bool := true) (dim : Nat := 0) : String :=
  let n := max dim (widthOf g)
  let body := if cliffT then emitCliffT g else emitNative g
  String.intercalate "\n"
    ([ "OPENQASM 2.0;", "include \"qelib1.inc\";", "qreg q[" ++ toString n ++ "];" ] ++ body)
    ++ "\n"

example : emitNative (Gate.X 0) = ["x q[0];"] := by decide
example : (emitCliffT (Gate.CCX 0 1 2)).length = 15 := by decide
example : permAtProg 2 (emitOps (qubit_swap 0 1)) 1 = 2 := by decide
example : permAt 3 (Gate.CCX 0 1 2) 3 = 7 := by decide

/-! ## §6. Demo export. -/

def demos : List (String × Gate) :=
  [ ("swap01",    qubit_swap 0 1),
    ("toffoli",   Gate.CCX 0 1 2),
    ("addconst3", addConstGate 3 5),
    ("modadd",    modAddConstGate 2 3 1),
    ("modmult",   modMultConstGate 2 3 2 2) ]

#eval show IO Unit from do
  let dir := "C:/tmp/qasm_demo/"
  for (name, g) in demos do
    let w := widthOf g
    IO.FS.writeFile (dir ++ name ++ ".qasm") (toQasm g true w)
    IO.FS.writeFile (dir ++ name ++ ".ccx.qasm") (toQasm g false w)
    if w ≤ 3 then
      let tt := (List.range (2 ^ w)).map (fun x => toString x ++ " " ++ toString (permAt w g x))
      IO.FS.writeFile (dir ++ name ++ ".tt")
        (toString w ++ "\n" ++ String.intercalate "\n" tt ++ "\n")
    IO.println s!"emitted {name}: width={w} gcount={Gate.gcount g} tcount={Gate.tcount g}"

end FormalRV.Codegen
