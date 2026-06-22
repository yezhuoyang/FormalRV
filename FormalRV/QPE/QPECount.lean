/-
  FormalRV.QPE.QPECount
  ─────────────────────
  CLOSED-FORM, ANCHORED resource counts for the QPE circuit, with the oracle as
  a BLACK BOX: the independent `Resource` counters applied to THE actual
  `BaseUCom` syntax tree `QPE k n c`, proven equal to a closed form that is
  parametric in the oracle family's own counts.  QPE adds NOTHING hidden on top
  of its oracle calls: the count theorem exhibits exactly

      CNOTs(QPE k n c) = Σᵢ (2·1q(cᵢ) + 6·CNOT(cᵢ))   [the controlled oracle calls]
                         + 3·⌊k/2⌋ + k·(k−1)            [the inverse-QFT basis]

  (a controlled 1-qubit gate costs 2 CNOTs + 4 one-qubit gates; a controlled
  CNOT is a Toffoli = 6 CNOTs + 9 one-qubit gates — `Resource.UComCombinators`).
  The modular-exponentiation instantiation's cost is the INSTANTIATION's
  business; it enters only through `oneQCountU (f i)` / `cnotCountU (f i)`.

  Headlines:
    • `cnotCountU_QPE` / `oneQCountU_QPE`     — the framework `QPE k n c`
    • `cnotCountU_QPE_var_lsb`                — the Shor-facing wrapper (counts
      invariant under the `map_qubits` lift and the LSB index reversal)
    • `widthU_QPE_decomp` + `widthU_QFTinv`   — the space decomposition
    • `qpe_verified_with_resources`           — THE TRIPLE: black-box semantic
      correctness AND the CNOT count, about the SAME syntactic object.
-/
import FormalRV.Resource.UComCombinators
import FormalRV.QFT.IQFTCount
import FormalRV.QPE.QPECorrectness

namespace FormalRV.Resource

open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ## §1. Counts are invariant under qubit relabeling (`map_qubits`). -/

theorem oneQCountU_map_qubits {dim dim' : Nat} (g : Nat → Nat) (c : BaseUCom dim) :
    oneQCountU (FormalRV.SQIRPort.map_qubits g c : BaseUCom dim') = oneQCountU c := by
  induction c with
  | seq a b iha ihb =>
      simp only [FormalRV.SQIRPort.map_qubits, oneQCountU_seq, iha, ihb]
  | app1 u t => rfl
  | app2 u m n => rfl
  | app3 u a b c => rfl

theorem cnotCountU_map_qubits {dim dim' : Nat} (g : Nat → Nat) (c : BaseUCom dim) :
    cnotCountU (FormalRV.SQIRPort.map_qubits g c : BaseUCom dim') = cnotCountU c := by
  induction c with
  | seq a b iha ihb =>
      simp only [FormalRV.SQIRPort.map_qubits, cnotCountU_seq, iha, ihb]
  | app1 u t => rfl
  | app2 u m n => rfl
  | app3 u a b c => rfl

/-! ## §2. The controlled-powers ladder over a black-box family. -/

/-- CNOTs of the controlled-powers ladder: each controlled oracle call costs
`2·(its one-qubit gates) + 6·(its CNOTs)`. -/
theorem cnotCountU_controlled_powers {dim : Nat} (c : Nat → BaseUCom dim) (k : Nat) :
    cnotCountU (controlled_powers c k)
      = ∑ i ∈ Finset.range k, (2 * oneQCountU (c i) + 6 * cnotCountU (c i)) := by
  have hcp : controlled_powers c k = npar k (fun i => control i (c i)) := rfl
  rw [hcp, cnotCountU_npar]
  exact Finset.sum_congr rfl (fun i _ => cnotCountU_control i (c i))

/-- One-qubit gates of the controlled-powers ladder (`+1` for the structural
`SKIP` at the base of `npar`). -/
theorem oneQCountU_controlled_powers {dim : Nat} (c : Nat → BaseUCom dim) (k : Nat) :
    oneQCountU (controlled_powers c k)
      = (∑ i ∈ Finset.range k, (4 * oneQCountU (c i) + 9 * cnotCountU (c i))) + 1 := by
  have hcp : controlled_powers c k = npar k (fun i => control i (c i)) := rfl
  rw [hcp, oneQCountU_npar]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => oneQCountU_control i (c i))

/-! ## §3. THE assembled QPE counts (black-box oracle). -/

/-- **QPE CNOT count (THE headline, time).**  Exactly the controlled-oracle
calls plus the inverse-QFT measurement basis — nothing hidden. -/
theorem cnotCountU_QPE {k n : Nat} (c : Nat → BaseUCom (k + n)) :
    cnotCountU (QPE k n c)
      = (∑ i ∈ Finset.range k, (2 * oneQCountU (c i) + 6 * cnotCountU (c i)))
        + (3 * (k / 2) + k * (k - 1)) := by
  rw [QPE_def_unfold, cnotCountU_seq, cnotCountU_seq, cnotCountU_npar_H,
      cnotCountU_controlled_powers, cnotCountU_QFTinv]
  omega

/-- **QPE one-qubit-gate count (time).**  The `k` Hadamards, the controlled
oracle calls, the inverse-QFT rotations, and the structural `SKIP`s. -/
theorem oneQCountU_QPE {k n : Nat} (c : Nat → BaseUCom (k + n)) :
    oneQCountU (QPE k n c)
      = (∑ i ∈ Finset.range k, (4 * oneQCountU (c i) + 9 * cnotCountU (c i)))
        + (3 * (k * (k - 1) / 2) + 2 * k + 4) := by
  rw [QPE_def_unfold, oneQCountU_seq, oneQCountU_seq, oneQCountU_npar_H,
      oneQCountU_controlled_powers, oneQCountU_QFTinv]
  omega

/-- **QPE width decomposition (space).**  The register is the max of the three
stages' footprints — with the oracle's footprint left as the black box it is. -/
theorem widthU_QPE_decomp {k n : Nat} (c : Nat → BaseUCom (k + n)) :
    widthU (QPE k n c)
      = max (widthU (npar_H k : BaseUCom (k + n)))
          (max (widthU (controlled_powers c k)) (widthU (QFTinv k : BaseUCom (k + n)))) := by
  rw [QPE_def_unfold]
  rfl

/-! ## §4. The Shor-facing wrappers: `QPE_var` (lifted oracle) and
`QPE_var_lsb` (LSB index reversal).  Counts pass through both. -/

/-- CNOTs of `QPE_var`: the `map_qubits` lift does not change any count. -/
theorem cnotCountU_QPE_var (m anc : Nat) (f : Nat → BaseUCom anc) :
    cnotCountU (FormalRV.SQIRPort.QPE_var m anc f)
      = (∑ i ∈ Finset.range m, (2 * oneQCountU (f i) + 6 * cnotCountU (f i)))
        + (3 * (m / 2) + m * (m - 1)) := by
  have h : FormalRV.SQIRPort.QPE_var m anc f
      = QPE m anc (fun i => FormalRV.SQIRPort.map_qubits (fun q => m + q) (f i)) := rfl
  rw [h, cnotCountU_QPE]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by
    rw [oneQCountU_map_qubits, cnotCountU_map_qubits])

/-- CNOTs of `QPE_var_lsb`: the LSB index reversal is a permutation of the
oracle family, so the summed count is unchanged (`Finset.sum_range_reflect`). -/
theorem cnotCountU_QPE_var_lsb (m anc : Nat) (f : Nat → BaseUCom anc) :
    cnotCountU (FormalRV.SQIRPort.QPE_var_lsb m anc f)
      = (∑ i ∈ Finset.range m, (2 * oneQCountU (f i) + 6 * cnotCountU (f i)))
        + (3 * (m / 2) + m * (m - 1)) := by
  have h : FormalRV.SQIRPort.QPE_var_lsb m anc f
      = FormalRV.SQIRPort.QPE_var m anc (fun j => f (FormalRV.SQIRPort.revIndex m j)) := rfl
  rw [h, cnotCountU_QPE_var]
  congr 1
  simp only [FormalRV.SQIRPort.revIndex]
  exact Finset.sum_range_reflect (fun i => 2 * oneQCountU (f i) + 6 * cnotCountU (f i)) m

end FormalRV.Resource

namespace FormalRV.SQIRPort

open FormalRV.Framework
open FormalRV.Resource

/-! ## §5. THE TRIPLE — black-box QPE: semantics + count, one syntactic object. -/

/-- **QPE, verified with resources (black-box oracle).**  For ANY eigenstate-
bearing oracle family `f`, the single syntactic object `QPE_var_lsb m anc f` is
simultaneously:
  1. **semantically correct** — it maps `|0^m⟩ ⊗ ψ` to `qpe_phase_state m θ ⊗ ψ`;
  2. **time-counted** — the independent CNOT counter walks its tree to exactly
     the controlled-oracle calls plus the inverse-QFT basis
     `3·⌊m/2⌋ + m·(m−1)`, with the oracle's own counts left as the black box
     they are.
The counters live in `Resource/` and import only the IR — nothing here can
influence what they return. -/
theorem qpe_verified_with_resources
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (θ : ℝ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_lsb : ∀ i, i < m →
      FormalRV.Framework.uc_eval (f i) * ψ =
        Complex.exp (((2 * Real.pi * ((2^i : Nat) : ℝ) * θ : ℝ) : ℂ) * Complex.I) • ψ) :
    (FormalRV.Framework.uc_eval (QPE_var_lsb m anc f)
        * kron_vec (FormalRV.Framework.kron_zeros m) ψ
      = kron_vec (qpe_phase_state m θ) ψ)
    ∧ cnotCountU (QPE_var_lsb m anc f)
      = (∑ i ∈ Finset.range m,
          (2 * oneQCountU (f i) + 6 * cnotCountU (f i)))
        + (3 * (m / 2) + m * (m - 1)) :=
  ⟨qpe_on_eigenstate_correct hmanc hm f ψ θ h_wt_all h_eig_lsb,
   cnotCountU_QPE_var_lsb m anc f⟩

end FormalRV.SQIRPort
