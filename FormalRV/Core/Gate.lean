/-
  FormalRV.Framework.Gate — quantum circuit IR + resource accounting.

  Mirrors SQIR's `bccom` (RCIR) and `ucom` (SQIR) deep embeddings, but
  Lean-native and minimal: just the gate set BQ-Algo needs to express
  Cuccaro / Gidney 2018 / windowed arithmetic / etc., plus tcount/gcount/depth.

  This is the SQIR analogue layer 1 (gate IR). Layer 2 (semantics) is
  `Framework.Semantics`. Layer 3 (full quantum / unitary matrices) is
  deferred until BQ-Algo gets to QPE — at the RCIR level (bit-vector
  semantics), arithmetic correctness can be proved without complex matrices.
-/

namespace FormalRV.Framework

/-- Reversible classical / Clifford+Toffoli circuit IR.

    Constructors:
    - `I`         — identity (no-op)
    - `X q`       — bit-flip on qubit `q`
    - `CX c t`    — controlled-NOT, control `c`, target `t`
    - `CCX a b t` — Toffoli, controls `a` `b`, target `t`
                    (the only gate with nonzero T-count in this base IR)
    - `seq g₁ g₂` — sequential composition (`g₁` first, then `g₂`)

    Future quantum-only gates (`H`, `T`, `Rz`, ...) will go in
    `Framework/QuantumGate.lean` when we need QPE-level reasoning. -/
inductive Gate where
  | I    : Gate
  | X    : Nat → Gate
  | CX   : Nat → Nat → Gate
  | CCX  : Nat → Nat → Nat → Gate
  | seq  : Gate → Gate → Gate
  deriving Repr, DecidableEq

namespace Gate

/-! ## Resource accounting

T-count, gate count, and depth functions. All `decide`-computable on
small instances; usable as the right-hand side of `paper_claim_*` proofs. -/

/-- T-gate count under the textbook 7-T Toffoli decomposition.
    Cliffords (X, CX) and identity are free. Optimizations like
    Gidney 2018's logical-AND (4-T per Toffoli) appear as separate
    Gate variants in `BQAlgo/Gidney2018.lean`, NOT by mutating tcount. -/
def tcount : Gate → Nat
  | I            => 0
  | X _          => 0
  | CX _ _       => 0
  | CCX _ _ _    => 7
  | seq g₁ g₂    => tcount g₁ + tcount g₂

/-- Total gate count (each primitive = 1, identity = 0). -/
def gcount : Gate → Nat
  | I            => 0
  | X _          => 1
  | CX _ _       => 1
  | CCX _ _ _    => 1
  | seq g₁ g₂    => gcount g₁ + gcount g₂

/-- Sequential depth (sum of primitive depths).
    True parallel depth would require a `par` constructor and a different
    cost — a Cuccaro adder is sequential, so this suffices for now. -/
def depth : Gate → Nat
  | I            => 0
  | X _          => 1
  | CX _ _       => 1
  | CCX _ _ _    => 1
  | seq g₁ g₂    => depth g₁ + depth g₂

/-! ## Smoke checks -/

example : tcount (CCX 0 1 2) = 7 := by decide
example : gcount (CCX 0 1 2) = 1 := by decide
example : depth  (CCX 0 1 2) = 1 := by decide

example : tcount (seq (X 0) (CCX 0 1 2)) = 7  := by decide
example : gcount (seq (X 0) (CCX 0 1 2)) = 2  := by decide
example : depth  (seq (X 0) (CCX 0 1 2)) = 2  := by decide

end Gate
end FormalRV.Framework
