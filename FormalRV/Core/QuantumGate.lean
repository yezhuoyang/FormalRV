/-
  FormalRV.Framework.QuantumGate — quantum unitary circuit IR.

  Lean translation of SQIR/SQIR/SQIR.v, narrowed to the base gate set
  used in the SQIR formalization of Shor's algorithm. Targets
  Shor-correctness as the end goal.

  Hierarchy of IRs in this project:
    - `Framework.Gate` (already written): RCIR-level reversible classical
       circuits (I/X/CX/CCX/seq). Used for adders, modular multipliers,
       lookups. Bit-vector semantics in `Framework.Semantics`.
    - `Framework.QuantumGate` (this file): general unitary circuits with
       a parametric R(θ,ϕ,λ) rotation gate and CNOT. Matrix semantics in
       `Framework.UnitarySem`.
    - Future: density-matrix / measurement semantics (SQIR's NDSem.v,
       DensitySem.v) when we model the full Shor algorithm with classical
       post-processing.

  Refs:
    - SQIR/SQIR/SQIR.v (this file's source)
    - Peng et al. 2022 (arXiv:2204.07112) §2 — formal methods overview
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace FormalRV.Framework

/-! ## Base unitary gate set

    SQIR uses two "physical" gates: the universal R(θ,ϕ,λ) rotation
    (sufficient for any single-qubit unitary) and CNOT. All other gates
    (H, X, T, S, ...) are defined as syntactic shorthands for R with
    specific angle parameters. -/

/-- The arity-indexed unitary primitive set.
    `BaseUnitary 1` covers all single-qubit gates via R(θ,ϕ,λ).
    `BaseUnitary 2` is just CNOT. We don't need a 3-qubit primitive —
    Toffoli is built from H/T/CNOT (see `CCX` below). -/
inductive BaseUnitary : Nat → Type
  | R    : ℝ → ℝ → ℝ → BaseUnitary 1   -- general 1-qubit rotation
  | CNOT : BaseUnitary 2

/-! ## UCom: the unitary circuit AST

    Mirrors SQIR's `ucom U dim` — sequenced applications of unitaries
    parameterized over a gate set `U` and a system dimension `dim`. -/

/-- Unitary circuit over gate set `U`, acting on `dim` qubits.
    Constructors:
    - `seq`   : sequential composition
    - `app1 u n` : apply 1-qubit unitary `u` to qubit `n`
    - `app2 u m n` : apply 2-qubit unitary `u` to qubits `m`, `n`
    - `app3 u m n p` : apply 3-qubit unitary `u` to qubits `m`, `n`, `p`
                       (no 3-qubit gates in BaseUnitary; reserved for
                       future extensions like Toffoli decomposition study) -/
inductive UCom (U : Nat → Type) (dim : Nat) : Type
  | seq  : UCom U dim → UCom U dim → UCom U dim
  | app1 : U 1 → Nat → UCom U dim
  | app2 : U 2 → Nat → Nat → UCom U dim
  | app3 : U 3 → Nat → Nat → Nat → UCom U dim

/-- A `UCom` over the base unitary set. -/
abbrev BaseUCom (dim : Nat) := UCom BaseUnitary dim

namespace BaseUCom
open BaseUnitary

-- All gate definitions below depend on `Real.pi`, which is noncomputable
-- (π is an irrational real). The matrix semantics in `UnitarySem` is
-- correspondingly noncomputable, but proofs work fine.
noncomputable section

/-! ## Standard single-qubit shorthands (translation of SQIR.v lines 41-57)

    These mirror SQIR's definitions verbatim. Each is a `BaseUnitary 1`
    constructed as an `R` with specific angles. The semantic correctness
    (i.e., that `U_H` actually equals the Hadamard matrix) is proved in
    `Framework.UnitarySem`. -/

/-- Hadamard: R(π/2, 0, π). -/
def U_H : BaseUnitary 1 := R (Real.pi / 2) 0 Real.pi

/-- Pauli X: R(π, 0, π). -/
def U_X : BaseUnitary 1 := R Real.pi 0 Real.pi

/-- Pauli Y: R(π, π/2, π/2). -/
def U_Y : BaseUnitary 1 := R Real.pi (Real.pi / 2) (Real.pi / 2)

/-- Pauli Z: R(0, 0, π). -/
def U_Z : BaseUnitary 1 := R 0 0 Real.pi

/-- Identity: R(0, 0, 0). -/
def U_I : BaseUnitary 1 := R 0 0 0

/-- T gate (π/8 rotation): Rz(π/4) = R(0, 0, π/4). -/
def U_T : BaseUnitary 1 := R 0 0 (Real.pi / 4)

/-- T-dagger: Rz(-π/4). -/
def U_TDAG : BaseUnitary 1 := R 0 0 (-(Real.pi / 4))

/-- S gate (phase): Rz(π/2). -/
def U_S : BaseUnitary 1 := R 0 0 (Real.pi / 2)

/-- S-dagger: Rz(-π/2). -/
def U_SDAG : BaseUnitary 1 := R 0 0 (-(Real.pi / 2))

/-- General Z-axis rotation by angle `λ`: R(0, 0, λ). -/
def U_Rz (lam : ℝ) : BaseUnitary 1 := R 0 0 lam

/-- General X-axis rotation by angle `θ`: R(θ, -π/2, π/2). -/
def U_Rx (th : ℝ) : BaseUnitary 1 := R th (-(Real.pi / 2)) (Real.pi / 2)

/-- General Y-axis rotation by angle `θ`: R(θ, 0, 0). -/
def U_Ry (th : ℝ) : BaseUnitary 1 := R th 0 0

/-! ## Circuit-level shorthands

    Wrap each base unitary in `UCom.app1` / `app2` for the natural
    "apply this gate to qubit n" syntax. Mirrors SQIR.v's `H {dim} n`
    definitions. -/

/-- Apply Hadamard to qubit `n`. -/
def H {dim : Nat} (n : Nat) : BaseUCom dim := UCom.app1 U_H n

/-- Apply Pauli X to qubit `n`. -/
def X {dim : Nat} (n : Nat) : BaseUCom dim := UCom.app1 U_X n

/-- Apply Pauli Y to qubit `n`. -/
def Y {dim : Nat} (n : Nat) : BaseUCom dim := UCom.app1 U_Y n

/-- Apply Pauli Z to qubit `n`. -/
def Z {dim : Nat} (n : Nat) : BaseUCom dim := UCom.app1 U_Z n

/-- Identity on qubit `n`. -/
def ID {dim : Nat} (n : Nat) : BaseUCom dim := UCom.app1 U_I n

/-- A no-op (`SKIP` in SQIR). Identity on qubit 0; well-typed iff dim ≥ 1. -/
def SKIP {dim : Nat} : BaseUCom dim := ID 0

/-- T gate on qubit `n`. -/
def T {dim : Nat} (n : Nat) : BaseUCom dim := UCom.app1 U_T n

/-- T-dagger on qubit `n`. -/
def TDAG {dim : Nat} (n : Nat) : BaseUCom dim := UCom.app1 U_TDAG n

/-- S gate (= P, phase) on qubit `n`. -/
def S {dim : Nat} (n : Nat) : BaseUCom dim := UCom.app1 U_S n

/-- S-dagger on qubit `n`. -/
def SDAG {dim : Nat} (n : Nat) : BaseUCom dim := UCom.app1 U_SDAG n

/-- Rz(λ) on qubit `n`. -/
def Rz {dim : Nat} (lam : ℝ) (n : Nat) : BaseUCom dim := UCom.app1 (U_Rz lam) n

/-- Rx(θ) on qubit `n`. -/
def Rx {dim : Nat} (th : ℝ) (n : Nat) : BaseUCom dim := UCom.app1 (U_Rx th) n

/-- Ry(θ) on qubit `n`. -/
def Ry {dim : Nat} (th : ℝ) (n : Nat) : BaseUCom dim := UCom.app1 (U_Ry th) n

/-- CNOT with control `c`, target `t`. -/
def CNOT {dim : Nat} (c t : Nat) : BaseUCom dim := UCom.app2 BaseUnitary.CNOT c t

/-! ## Derived two- and three-qubit gates (SQIR.v lines 59-80)

    These are circuit-level definitions, NOT new BaseUnitary primitives.
    Their matrix semantics fall out of `uc_eval` automatically. -/

/-- Controlled-Z = H · CNOT · H on the target.
    Mirrors SQIR.v: `Definition CZ m n := H n ; CNOT m n ; H n`. -/
def CZ {dim : Nat} (m n : Nat) : BaseUCom dim :=
  UCom.seq (H n) (UCom.seq (CNOT m n) (H n))

/-- SWAP via three CNOTs.
    Mirrors SQIR.v: `Definition SWAP m n := CNOT m n; CNOT n m; CNOT m n`. -/
def SWAP {dim : Nat} (m n : Nat) : BaseUCom dim :=
  UCom.seq (CNOT m n) (UCom.seq (CNOT n m) (CNOT m n))

/-- Toffoli via the standard 7-T decomposition (SQIR.v line 67).
    This is the canonical Cliffords+T realization of CCX:

      H c ; CNOT b c ; T† c ; CNOT a c ;
      T c ; CNOT b c ; T† c ; CNOT a c ;
      CNOT a b ; T† b ; CNOT a b ;
      T a ; T b ; T c ; H c

    Counted as 7 T gates (T†, T appear 4 + 3 times; the textbook
    accounting that gives "7 T per Toffoli"). -/
def CCX {dim : Nat} (a b c : Nat) : BaseUCom dim :=
  let s₁ := UCom.seq (H c)        (UCom.seq (CNOT b c) (UCom.seq (TDAG c) (CNOT a c)))
  let s₂ := UCom.seq (T c)        (UCom.seq (CNOT b c) (UCom.seq (TDAG c) (CNOT a c)))
  let s₃ := UCom.seq (CNOT a b)   (UCom.seq (TDAG b)   (CNOT a b))
  let s₄ := UCom.seq (T a)        (UCom.seq (T b)      (UCom.seq (T c)    (H c)))
  UCom.seq s₁ (UCom.seq s₂ (UCom.seq s₃ s₄))

/-- CCZ = CCX without the framing Hadamards (SQIR.v line 75). -/
def CCZ {dim : Nat} (a b c : Nat) : BaseUCom dim :=
  let s₁ := UCom.seq (CNOT b c)   (UCom.seq (TDAG c)   (CNOT a c))
  let s₂ := UCom.seq (T c)        (UCom.seq (CNOT b c) (UCom.seq (TDAG c) (CNOT a c)))
  let s₃ := UCom.seq (CNOT a b)   (UCom.seq (TDAG b)   (CNOT a b))
  let s₄ := UCom.seq (T a)        (UCom.seq (T b)      (T c))
  UCom.seq s₁ (UCom.seq s₂ (UCom.seq s₃ s₄))

end -- noncomputable section
end BaseUCom

/-! ## Well-typedness

    Mirrors SQIR.v's `uc_well_typed`. A circuit is well-typed if every
    gate references qubit indices < dim, and 2- and 3-qubit gates have
    distinct qubits.

    SQIR proves the semantic relevance of well-typedness elsewhere
    (a non-well-typed circuit's matrix semantics is the zero matrix). -/

inductive UCom.WellTyped {U : Nat → Type} : (dim : Nat) → UCom U dim → Prop
  | seq  {dim c₁ c₂} :
      WellTyped dim c₁ → WellTyped dim c₂ → WellTyped dim (UCom.seq c₁ c₂)
  | app1 {dim u n} :
      n < dim → WellTyped dim (UCom.app1 u n)
  | app2 {dim u m n} :
      m < dim → n < dim → m ≠ n → WellTyped dim (UCom.app2 u m n)
  | app3 {dim u m n p} :
      m < dim → n < dim → p < dim → m ≠ n → n ≠ p → m ≠ p →
      WellTyped dim (UCom.app3 u m n p)

/-! ## General programs: `Com` (translation of SQIR.v lines 147-175)

    Beyond `UCom` (purely unitary), `Com` adds:
    - `cskip` — no-op
    - `useq` — sequential composition (renamed from `seq` to avoid clash)
    - `embedU` — embed a UCom as a Com
    - `meas` — measure qubit; on outcome 1 run c₁, on outcome 0 run c₂
-/

/-- General programs with measurement, parameterized over gate set `U`. -/
inductive Com (U : Nat → Type) (dim : Nat) : Type
  | cskip : Com U dim
  | useq  : Com U dim → Com U dim → Com U dim
  | embedU : UCom U dim → Com U dim
  | meas  : Nat → Com U dim → Com U dim → Com U dim

abbrev BaseCom (dim : Nat) := Com BaseUnitary dim

/-- Coerce any UCom to a Com (transparent). -/
instance {U : Nat → Type} {dim : Nat} : Coe (UCom U dim) (Com U dim) :=
  ⟨Com.embedU⟩

end FormalRV.Framework
