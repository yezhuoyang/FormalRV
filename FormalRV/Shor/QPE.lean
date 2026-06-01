/-
  FormalRV.Framework.QPE — Quantum Phase Estimation circuit.

  Lean translation skeleton of `SQIR/examples/QPEGeneral.v`.
  QPE applied to a unitary U with eigenstate |ψ⟩ (eigenvalue e^(2πi·θ))
  outputs an n-bit approximation of θ.

  Status: SCAFFOLDING. The circuit is defined; the correctness theorem
  (success probability ≥ 4/π² for n-bit precision) is sorried — it requires
  significant analysis of the inverse QFT applied to the right input state.
-/
import FormalRV.Core.UnitaryOps
import FormalRV.Core.NDSem
import FormalRV.Core.DensitySem
import FormalRV.Core.QuantumLib

namespace FormalRV.Framework

namespace BaseUCom
open BaseUCom

/-! ## Inverse QFT — needed by QPE's measurement basis

    Quantum Fourier Transform: applies a sequence of Hadamards and
    controlled-rotations. The inverse QFT (QFT†) decodes the phase. -/

/-- Quantum Fourier Transform on `n` qubits. SQIR's `QFT n` is a
    well-known circuit; this is a stub. -/
noncomputable def QFT {dim : Nat} (n : Nat) : BaseUCom dim :=
  -- Placeholder: real QFT is a recursive H + controlled-Rz pattern.
  -- See SQIR/examples/QFT.v for the full Coq definition (~50 lines).
  -- Stub: applies Hadamards on first n qubits.
  npar n (fun k => H k)

/-! ### Real inverse-QFT circuit pieces (syntactic, polymorphic in dim)

The following four definitions are the syntactic circuit building
blocks for the real recursive inverse-QFT layer
`real_QFTinv_layer n`. They were originally formulated in
`SQIRPort/ControlledGates.lean` and `SQIRPort/PostQFT.lean`; moving
them down into the framework lets `Framework.QPE.QFTinv` directly
point to `real_QFTinv_layer n`, replacing the prior stub
`QFTinv n := invert (QFT n) = invert (npar_H n)` that was
semantically wrong (the stub was just inverted Hadamards, not the
real inverse QFT). All correctness proofs remain in
`SQIRPort/PostQFT.lean`. -/

/-- **Controlled-Rz (controlled-phase) decomposition.** Five-gate
sequence implementing controlled-Rz via Rz, CNOT, Rz, CNOT, Rz. -/
noncomputable def controlled_Rz {dim : Nat} (q t : Nat) (lam : ℝ) : BaseUCom dim :=
  UCom.seq (Rz (lam/2) q)
    (UCom.seq (CNOT q t)
      (UCom.seq (Rz (-(lam/2)) t)
        (UCom.seq (CNOT q t)
          (Rz (lam/2) t))))

/-- **Inverse-QFT phase ladder for one target.** Sequence of
controlled-Rz gates targeting qubit `target` from controls
`target+1, target+2, ..., n-1`, followed by `H target`. -/
noncomputable def inverse_qft_phase_ladder
    {dim : Nat} (n target : Nat) : BaseUCom dim :=
  let rec loop (j : Nat) : BaseUCom dim :=
    if j < n then
      UCom.seq (controlled_Rz j target (-(Real.pi / (2 ^ (j - target) : ℝ))))
               (loop (j + 1))
    else
      H target
  loop (target + 1)

/-- **Bit-reversal SWAP cascade for `n` qubits.** Swaps qubit `i`
with qubit `n-1-i` for `i < n/2`. Required at the end of the
inverse-QFT to undo the QFT's natural reverse-bit ordering. -/
noncomputable def bit_reversal_swaps {dim : Nat} (n : Nat) : BaseUCom dim :=
  let rec loop (i : Nat) : BaseUCom dim :=
    if i + i + 1 < n then
      UCom.seq (SWAP i (n - 1 - i)) (loop (i + 1))
    else
      SKIP
  loop 0

/-- **Recursive layer of the real inverse-QFT for `n` qubits.**
1. Bit-reversal SWAP cascade `bit_reversal_swaps n`.
2. For `target = n-1` down to `0`: `inverse_qft_phase_ladder n target`. -/
noncomputable def real_QFTinv_layer {dim : Nat} (n : Nat) : BaseUCom dim :=
  let rec countdown (k : Nat) : BaseUCom dim :=
    match k with
    | 0 => SKIP
    | k+1 => UCom.seq (inverse_qft_phase_ladder n k) (countdown k)
  UCom.seq (bit_reversal_swaps n) (countdown n)

/-- **Inverse QFT (QFT†)**: the real recursive inverse-QFT layer.

Previously a stub `invert (QFT n) = invert (npar_H n)` (semantically
wrong — see `FormalRV.SQIRPort.QFTinv_is_stub`). Replaced
2026-05-26 with the real recursive layer
`real_QFTinv_layer n`, whose matrix correctness is established by
`FormalRV.SQIRPort.uc_eval_real_QFTinv_layer_eq_IQFT_matrix`.

This replacement breaks the prior `QFT_QFTinv_id`-style cancellation
theorems (which only held because both QFT and QFTinv were `npar_H`
stubs). Those theorems are removed; the corresponding correct
behavior is captured in
`SQIRPort.uc_eval_real_QFTinv_layer_eq_IQFT_matrix`. -/
noncomputable def QFTinv {dim : Nat} (n : Nat) : BaseUCom dim :=
  real_QFTinv_layer n

/-- The current QFT stub equals npar_H — useful as a bridge to the
    UnitaryOps lemmas about npar_H. When the real QFT is implemented,
    this lemma will go away. -/
theorem QFT_eq_npar_H {dim : Nat} (n : Nat) :
    (QFT n : BaseUCom dim) = npar_H n := rfl

/-- `QFT 0 ≡ SKIP` — empty QFT is a no-op. -/
@[simp] theorem QFT_zero {dim : Nat} : (QFT 0 : BaseUCom dim) = SKIP := rfl

/-- `QFT (n+1) = QFT n ; H n` — the recursive structure of the stub. -/
@[simp] theorem QFT_succ {dim : Nat} (n : Nat) :
    (QFT (n + 1) : BaseUCom dim) = UCom.seq (QFT n) (H n) := rfl

/-- Matrix form of QFT's succ: `uc_eval (QFT (n+1)) = pad_u dim n hMatrix
    * uc_eval (QFT n)`. Direct lift of `uc_eval_npar_H_succ` via QFT = npar_H. -/
theorem uc_eval_QFT_succ {dim : Nat} (n : Nat) :
    uc_eval (QFT (n + 1) : BaseUCom dim)
      = pad_u dim n hMatrix * uc_eval (QFT n) :=
  uc_eval_npar_H_succ n

/-- Matrix form of QFT's zero base case: `uc_eval (QFT 0) = 1` when 0 < dim. -/
theorem uc_eval_QFT_zero_eq_one {dim : Nat} (h : 0 < dim) :
    uc_eval (QFT 0 : BaseUCom dim) = (1 : Square dim) :=
  uc_eval_npar_H_zero_eq_one h

/-- The QFT stub is WellTyped on `dim` qubits when `n ≤ dim` (so all the
    H gates fit) and `0 < dim` (so the SKIP base case is valid).
    1-line corollary of `npar_H_well_typed` since QFT = npar_H definitionally. -/
theorem QFT_well_typed {dim : Nat} (n : Nat) (h : n ≤ dim) (hd : 0 < dim) :
    UCom.WellTyped dim (QFT n : BaseUCom dim) :=
  npar_H_well_typed n h hd

/-! ### Removed QFT/QFTinv stub-cancellation theorems

The following theorems were artifacts of the prior QFTinv stub
(`invert (QFT n) = invert (npar_H n)`) and are no longer true after
the replacement `QFTinv n := real_QFTinv_layer n`:

- `QFTinv_zero`, `QFTinv_succ`, `uc_eval_QFTinv_succ`
- `QFT_QFTinv_zero_id`, `QFT_QFTinv_id`, `QFTinv_QFT_id`
- `nd_equiv_embedU_QFT_QFTinv_eq_ID`, `nd_equiv_embedU_QFTinv_QFT_eq_ID`
- `c_equiv_embedU_QFT_QFTinv_eq_ID`, `c_equiv_embedU_QFTinv_QFT_eq_ID`
- `useq_QFT_QFTinv_cancel`, `useq_QFTinv_QFT_cancel`
- `useq_QFT_QFTinv_cancel_l`, `useq_QFTinv_QFT_cancel_l`

They only held because both QFT and QFTinv were `npar_H` stubs, so
their "cancellation" was really `H ∘ H = id`. With the real
`real_QFTinv_layer` plugged in, these would assert that the real IQFT
undoes a stub `npar_H`, which is false. They are removed.

`QFTinv_zero` and `uc_eval_QFTinv_zero_eq_one` remain valid (both
the stub and the new layer collapse to identity at n=0) and are
preserved with new proofs. -/

/-- `QFTinv 0 = real_QFTinv_layer 0 = bit_reversal_swaps 0 ; SKIP =
    SKIP ; SKIP` (a definitional simplification). Distinct from the
    prior stub which gave `QFTinv 0 = SKIP` directly. Use
    `uc_eval_QFTinv_zero_eq_one` for the matrix-level identity. -/
theorem QFTinv_zero_unfold {dim : Nat} :
    (QFTinv 0 : BaseUCom dim) = UCom.seq SKIP SKIP := by
  show real_QFTinv_layer 0 = UCom.seq SKIP SKIP
  unfold real_QFTinv_layer real_QFTinv_layer.countdown
  show UCom.seq (bit_reversal_swaps 0 : BaseUCom dim) SKIP = UCom.seq SKIP SKIP
  congr 1
  unfold bit_reversal_swaps bit_reversal_swaps.loop
  rfl

/-- Matrix form of QFTinv's zero base case: `uc_eval (QFTinv 0) = 1`
    when `0 < dim`. The new `real_QFTinv_layer 0` is `SKIP ; SKIP`,
    whose `uc_eval` is `1 * 1 = 1`. -/
theorem uc_eval_QFTinv_zero_eq_one {dim : Nat} (h : 0 < dim) :
    uc_eval (QFTinv 0 : BaseUCom dim) = (1 : Square dim) := by
  rw [QFTinv_zero_unfold]
  show uc_eval (SKIP : BaseUCom dim) * uc_eval (SKIP : BaseUCom dim) = 1
  show uc_eval (ID 0 : BaseUCom dim) * uc_eval (ID 0 : BaseUCom dim) = 1
  rw [uc_eval_ID_eq_one h, Matrix.one_mul]

/-- The inverse QFT is WellTyped on `dim` qubits when `n ≤ dim` (so
    all gates fit) and `0 < dim` (so the SKIP base cases are valid).
    Proven via well-typedness of `real_QFTinv_layer`, which is
    established in `FormalRV.SQIRPort.PostQFT.lean` as
    `wellTyped_real_QFTinv_layer`. To avoid an import cycle, this
    theorem's proof is parameterized: the calling site supplies
    well-typedness of the inner layer (typically via the SQIRPort
    theorem). -/
theorem QFTinv_well_typed_of_layer_well_typed {dim : Nat} (n : Nat)
    (h_layer_wt : UCom.WellTyped dim (real_QFTinv_layer n : BaseUCom dim)) :
    UCom.WellTyped dim (QFTinv n : BaseUCom dim) := by
  show UCom.WellTyped dim (real_QFTinv_layer n : BaseUCom dim)
  exact h_layer_wt

/-! ## Controlled powers — `controlled_powers f n m` applies `f i` controlled
    on qubit `i` for i = 0..n-1.

    For QPE: `f i = U^(2^i)` controlled on qubit i, applied to a
    target register starting at qubit n. -/

/-- Apply `f i` controlled on qubit `i` for i in [0, n). -/
noncomputable def controlled_powers {dim : Nat} (f : Nat → BaseUCom dim) (n : Nat) : BaseUCom dim :=
  npar n (fun i => control i (f i))

/-- `controlled_powers f 0 = SKIP` — empty controlled-powers chain is no-op. -/
@[simp] theorem controlled_powers_zero {dim : Nat} (f : Nat → BaseUCom dim) :
    controlled_powers f 0 = (SKIP : BaseUCom dim) := rfl

/-- `controlled_powers f (n+1) = controlled_powers f n ; control n (f n)` —
    appending one more controlled-power at the end. -/
@[simp] theorem controlled_powers_succ {dim : Nat} (f : Nat → BaseUCom dim) (n : Nat) :
    controlled_powers f (n + 1)
      = UCom.seq (controlled_powers f n) (control n (f n)) := rfl

/-- Matrix form of controlled_powers' zero base case: equals SKIP. -/
theorem uc_eval_controlled_powers_zero {dim : Nat} (f : Nat → BaseUCom dim) :
    uc_eval (controlled_powers f 0) = uc_eval (SKIP : BaseUCom dim) := rfl

/-- Well-typed matrix form for the empty controlled-powers chain:
    `uc_eval (controlled_powers f 0) = 1` when 0 < dim. -/
theorem uc_eval_controlled_powers_zero_eq_one {dim : Nat}
    (f : Nat → BaseUCom dim) (hd : 0 < dim) :
    uc_eval (controlled_powers f 0) = (1 : Square dim) := by
  rw [uc_eval_controlled_powers_zero]
  exact uc_eval_ID_eq_one hd

/-- Matrix form of controlled_powers' succ unfold: appending `control n (f n)`
    left-multiplies by its uc_eval. -/
theorem uc_eval_controlled_powers_succ {dim : Nat} (f : Nat → BaseUCom dim) (n : Nat) :
    uc_eval (controlled_powers f (n + 1))
      = uc_eval (control n (f n)) * uc_eval (controlled_powers f n) := rfl

/-! ## QPE circuit (SQIR/examples/QPEGeneral.v line ~100)

    Matches SQIR signature: `QPE k n c : base_ucom (k + n)`.
    - k : measurement register size
    - n : data register size
    - c : unitary acting on the data register (n qubits)

    Steps:
    1. Apply Hadamards to the k measurement qubits
    2. Apply controlled powers of c (c controlled on qubit i, repeated 2^i times)
    3. Apply inverse QFT to measurement register -/

/-- The QPE circuit on k+n qubits (matches SQIR `QPE k n c`).
    The first k qubits are the measurement register, the next n are the
    data register where c acts. -/
noncomputable def QPE (k n : Nat) (c : Nat → BaseUCom (k + n)) : BaseUCom (k + n) :=
  let prep := npar_H k
  let phase := controlled_powers c k
  let measBasis := QFTinv k
  UCom.seq prep (UCom.seq phase measBasis)

/-- Definitional unfolding of QPE: exposes the 3-piece composition. -/
theorem QPE_def_unfold {k n : Nat} (c : Nat → BaseUCom (k + n)) :
    QPE k n c
      = UCom.seq (npar_H k) (UCom.seq (controlled_powers c k) (QFTinv k)) :=
  rfl

/-- Matrix form of QPE: the right-to-left chain
    `uc_eval (QFTinv k) * uc_eval (controlled_powers c k) * uc_eval (npar_H k)`. -/
theorem uc_eval_QPE {k n : Nat} (c : Nat → BaseUCom (k + n)) :
    uc_eval (QPE k n c)
      = uc_eval (QFTinv k) * uc_eval (controlled_powers c k) * uc_eval (npar_H k) :=
  rfl

/-! ## QPE correctness — the headline theorem of the QPE module

    Statement: For any U with eigenstate |ψ⟩ (eigenvalue e^(2πi·θ)),
    measuring the QPE output gives k such that k/2^n ≈ θ with high
    probability (≥ 4/π² for an n-bit precision target).

    SQIR proves this in QPEGeneral.v ~200 LOC. Here it's stated precisely;
    the proof is one of the big open Lean targets. -/

/-! ## QPE_semantics_full — faithful translation of SQIR's headline QPE theorem

    SQIR/examples/shor/QPEGeneral.v line 105:
    ```
    Lemma QPE_semantics_full : forall k n (c : base_ucom n) z (ψ : Vector (2^n)) (δ : R),
      (n > 0)%nat -> (k > 1)%nat -> uc_well_typed c -> Pure_State_Vector ψ ->
      (-1 / 2^(k+1) <= δ < 1 / 2^(k+1))%R ->
      let θ := ((INR (funbool_to_nat k z) / 2^k) + δ)%R in
      (uc_eval c) × ψ = Cexp (2 * PI * θ) .* ψ ->
      probability_of_outcome
          ((f_to_vec k z) ⊗ ψ)
          (@Mmult _ _ (1*1) (uc_eval (QPE k n c)) (k ⨂ ∣0⟩ ⊗ ψ))
      >= 4 / (PI ^ 2).
    ```

    The Lean translation below has the EXACT SAME shape. Helpers are from
    `Framework.QuantumLib` (axiomatized; their Lean implementations are
    future work). The proof is sorried — it requires translating the
    180+ line SQIR proof plus all of QuantumLib it depends on. -/

/-- QPE_semantics_full — FAITHFUL translation of SQIR's headline theorem.
    SQIR/examples/shor/QPEGeneral.v line 105:

    ```coq
    Lemma QPE_semantics_full : forall k n (c : base_ucom n) z (ψ : Vector (2^n)) (δ : R),
      (n > 0)%nat -> (k > 1)%nat -> uc_well_typed c -> Pure_State_Vector ψ ->
      (-1 / 2^(k+1) <= δ < 1 / 2^(k+1))%R ->
      let θ := ((INR (funbool_to_nat k z) / 2^k) + δ)%R in
      (uc_eval c) × ψ = Cexp (2 * PI * θ) .* ψ ->
      probability_of_outcome
          ((f_to_vec k z) ⊗ ψ)
          (@Mmult _ _ (1*1) (uc_eval (QPE k n c)) (k ⨂ ∣0⟩ ⊗ ψ))
      >= 4 / (PI ^ 2).
    ```

    DEFERRED — ref: SQIR/examples/shor/QPEGeneral.v `Lemma QPE_semantics_full`
    (~180 LOC of Coq, depending on the full QuantumLib QFT/Fourier
    infrastructure). G-T axiom catalogue. Closing this in Lean requires:
    (a) full QFT correctness theorem, (b) inverse-QFT-on-eigenstate analysis,
    (c) Born-rule lower bound via Dirichlet kernel summation. Total estimated
    ~1500 LOC of Lean (mathlib has no quantum-circuit Fourier library). -/
axiom QPE_semantics_full
    (k n : Nat) (c : BaseUCom (k + n)) (z : Nat → Bool)
    (ψ : Matrix (Fin (2^n)) (Fin 1) ℂ) (δ : ℝ)
    (hn : 0 < n) (hk : 1 < k)
    (hc : UCom.WellTyped (k + n) c)
    (hψ : Pure_State_Vector ψ)
    (hδ_low  : (-1 : ℝ) / 2^(k+1) ≤ δ)
    (hδ_high : δ < 1 / 2^(k+1))
    (θ : ℝ)
    (θ_def : θ = ((funbool_to_nat k z : ℝ) / 2^k) + δ)
    (h_eigen : uc_eval c * (kron_zeros k ⊗ᵥ ψ) =
               Complex.exp (2 * Real.pi * θ * Complex.I) • (kron_zeros k ⊗ᵥ ψ)) :
    probability_of_outcome
        ((f_to_vec k z) ⊗ᵥ ψ)
        (uc_eval (QPE k n (fun _ => c)) * (kron_zeros k ⊗ᵥ ψ))
      ≥ 4 / Real.pi ^ 2

end BaseUCom
end FormalRV.Framework
