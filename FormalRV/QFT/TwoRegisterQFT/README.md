# `FormalRV.QFT.TwoRegisterQFT` — a reusable two-register QFT measurement model

This folder formalises the **amplitude / Born-probability layer of a two-control-register quantum
Fourier transform with an entangled target register** — the measurement structure shared by

* **Ekerå–Håstad** short-DLP factoring (arXiv:1702.00249, §quantum-part), and
* **Ekerå** general-DLP (arXiv:1905.09084),

both of which run *two* control registers (sizes `2^a`, `2^b`), entangle a target register by a
function `f : (x,y) ↦ e` (the measured group element `[a−bd]g` / `[a−bd]g`), apply `QFT_{2^a}` to the
first control register and `QFT_{2^b}` to the second, and measure all three registers.

The single-register order-finding QPE already lives in `FormalRV.QPE` / `FormalRV.QFT` (inverse-QFT
circuit). This module is the **two-register generalisation at the amplitude level** — the object the
Ekerå–Håstad success analysis (`FormalRV.CFS.EkeraLemma7`) is *about*.

## Interface (`Basic.lean`)

QFT convention: `|x⟩ ↦ (1/√2^a) ∑_j e^{2πi·xj/2^a} |j⟩`.

| Name | Meaning |
|---|---|
| `qftKernel a x j` | the QFT phase `e^{2πi·x·j / 2^a}` |
| `qftAmp a c j` | single-register QFT output amplitude at `j` from input amplitudes `c : ℕ → ℂ` |
| `qft2Amp a b c j k` | two-register QFT output amplitude at `(j,k)` from `c : ℕ → ℕ → ℂ` |
| `qft2FiberAmp a b c f j k e` | amplitude of the joint outcome `|j,k,e⟩` (target fibre `f x y = e`) |
| `qft2MeasProb a b c f E j k` | **Born probability of control outcome `(j,k)`** = `∑_{e∈E} ‖fibre amp‖²` |

Key reusable theorems:

* **`qft2Amp_factor`** — the *structural* law: a two-register QFT is the **tensor product** of two
  single-register QFTs. When the input factors `c x y = c₁ x · c₂ y`,
  `qft2Amp a b c j k = qftAmp a c₁ j · qftAmp b c₂ k`.
* `qft2MeasProb_nonneg` — the Born probability is `≥ 0`.

All axiom-clean (`[propext, Classical.choice, Quot.sound]`), no `sorry`, no `native_decide`.

## Example 1 — the tensor-factorisation law

A product input state `|ψ₁⟩ ⊗ |ψ₂⟩` (amplitudes `c x y = c₁ x · c₂ y`) is sent by the two-register
QFT to the product of the two single-register QFT outputs:

```lean
open FormalRV.QFT.TwoRegisterQFT in
example (a b : ℕ) (c₁ c₂ : ℕ → ℂ) (j k : ℕ) :
    qft2Amp a b (fun x y => c₁ x * c₂ y) j k = qftAmp a c₁ j * qftAmp b c₂ k :=
  qft2Amp_factor a b c₁ c₂ j k
```

## Example 2 — instantiating the Ekerå–Håstad circuit

Take the normalised uniform input `c x y = 1/√2^{2ℓ+m}` and the EH target `f x y = x − y·d`; then
`qft2MeasProb (ℓ+m) ℓ c f E j k` is the EH circuit's probability of measuring control outcome
`(j,k)`. Its per-fibre amplitude is exactly the paper's
`(1/2^{2ℓ+m}) ∑_{(a,b): a−bd=e} e^{2πi(aj + 2^m bk)/2^{ℓ+m}}` (1702.00249 l.457), and after the
paper's steps 2–4 (factor the `e`-phase, centre `b`, reduce mod `2^{ℓ+m}`) it becomes the centered
balanced-residue sum that `FormalRV.CFS.EkeraLemma7.ekera_lemma7` lower-bounds by `2^{−(m+ℓ+2)}` for
good pairs. The instantiation + this identification live in
`FormalRV.Audit.Gidney2025.EkeraHastadCircuit`.

## The gate-level circuit (`Circuit.lean`)

`Basic.lean` is the amplitude *model*; `Circuit.lean` supplies the **actual gate circuit** it is about,
built from the project's fully-verified single-register inverse-QFT circuit `IQFT`.

| Name | Meaning |
|---|---|
| `twoRegQFT a b : BaseUCom (a+b)` | `IQFT a` on qubits `[0,a)` ; `IQFT b` on qubits `[a,a+b)` |
| `twoRegQFT_wellTyped` | it touches only qubits `< a+b` (pluggable into `BaseUCom`/`prob_partial_meas`) |
| `uc_eval_twoRegQFT_kron` | **unitary semantics**: `uc_eval (twoRegQFT a b) * (ψc ⊗ᵥ ψd) = (IQFT_matrix a · ψc) ⊗ᵥ (IQFT_matrix b · ψd)` — acts as `IQFT ⊗ IQFT` (via `iqft_correct` per register) |
| `twoRegQFT_out_apply` | **gate-level tensor law**: joint output amplitude at `(j,k)` = product of the two single-register inverse-QFT amplitudes (circuit counterpart of `qft2Amp_factor`) |
| `iqft_matrix_mulVec_apply` | explicit single-register readout `(IQFT_matrix a · ψ) j = (1/√2^a) ∑ₓ e^{-2πi·xj/2^a} ψₓ` |
| `uc_eval_map_qubits_shift_kron_vec` | reusable: a shift-lifted circuit on the data register factors through `kron_vec` for *any* control factor (data-register dual of `uc_eval_control_register_circuit_kron_vec`) |

All axiom-clean (`#verify_clean`). **Convention:** `twoRegQFT` realizes the *inverse* QFT (`e^{-2πi·xj}`,
the measurement transform QPE/Shor apply); `qft2Amp` uses the forward kernel. They are complex
conjugates, so every Born probability `‖·‖²` agrees.

> Layering: `Circuit.lean` uses the `map_qubits` kron-factorization lemmas in `FormalRV.QPE.PhaseKickback`
> (which imports `Shor.MainAlgorithm`), so it is kept OUT of the Shor-agnostic `FormalRV.QFT` umbrella
> and imported where the circuit is used (`FormalRV.Audit.Gidney2025.EkeraHastadCircuit`).

## Example 3 — the gate circuit acts as `IQFT ⊗ IQFT`

```lean
open FormalRV.QFT.TwoRegisterQFT FormalRV.SQIRPort FormalRV.Framework in
example (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (ψc : Matrix (Fin (2^a)) (Fin 1) ℂ) (ψd : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    uc_eval (twoRegQFT a b) * kron_vec ψc ψd
      = kron_vec (IQFT_matrix a * ψc) (IQFT_matrix b * ψd) :=
  uc_eval_twoRegQFT_kron a b ha hb ψc ψd
```

## The measured run — QFT + projection (`CircuitMeasurement.lean`)

`Circuit.lean` is the QFT gate; `CircuitMeasurement.lean` applies it to a post-oracle state and reads
off the control-register Born probability as a `prob_partial_meas` statement of the shape the Shor
pipeline consumes. **Gate-honest** in its QFT (`twoRegQFT`, real `uc_eval`) and its measurement
(`prob_partial_meas`); the **oracle is abstracted by its output state** (see below).

| Name | Meaning |
|---|---|
| `twoRegOracleState a b t c tgt` | post-oracle 3-register state `∑_{x,y} c x y · \|x⟩\|y⟩\|tgt x y⟩` |
| `twoRegQFTMeasState …` | `twoRegQFT ⊗ I_target` applied to it (via `uc_eval_control_register_circuit_kron_vec`) |
| `twoRegQFTMeasState_action` | the QFT⊗I action: each `\|x⟩\|y⟩` → `(IQFT_a\|x⟩)⊗(IQFT_b\|y⟩)`, target untouched |
| `twoRegQFTMeasState_regroup` | regroup by target value → `∑_i (fibre-i amp) ⊗ \|i⟩` (distinct ⇒ orthonormal) |
| **`prob_partial_meas_twoRegQFTMeasState`** | **headline**: `prob_partial_meas (\|j,k⟩) (measured state) = ∑_i ‖fibre-i control amp‖²` — the gate Born probability, in pipeline form |

> **Scope (honest).** `twoRegOracleState` is *posited* (arbitrary `c, tgt`, no `BaseUCom`/`uc_eval`/
> unitarity hypothesis) — the oracle is abstracted by its OUTPUT STATE. This is **weaker** than the
> single-register pipeline's `MultiplyCircuitProperty`, which pins the full `uc_eval` action of an
> actual `BaseUCom` oracle (the post-oracle state is then *derived*). Realizing `twoRegOracleState` as
> `entangling-oracle-gate ∘ input-prep` is the remaining **open seam**. So the QFT and the measurement
> are gate-honest; the oracle entanglement is an assumed state.

The Ekerå–Håstad instantiation lives in `FormalRV.Audit.Gidney2025.EkeraHastadCircuitMeasurement`:
with `tgt = ` (the shift-encoded `a−b·d` — the standard reversible `|x,y,0⟩↦|x,y,x−yd⟩` image, true
here by construction not by a discharged gate property), the target sum reindexes to `ehE`, the real
input makes the inverse-kernel fibre amplitude `conj(qft2FiberAmp)` (equal `normSq`), and so

* `prob_partial_meas_eq_ehCircuitMeasProb` — the Born probability of the measured state **equals**
  `ehCircuitMeasProb` (`= ehProb`), and
* **`ehGate_per_run_ge_eighth`** — Ekerå–Håstad per-run success `≥ 1/8` as a `prob_partial_meas` bound.

All axiom-clean (`#verify_clean`).

## How this closes the circuit-semantic boundary

`FormalRV.CFS.EkeraLemma7` proves the success bound on the *probability expression*
`ehProb`. This module supplies the missing half — the **circuit** whose Born probability *is* that
expression — so that the Ekerå–Håstad per-run success (`EkeraEndToEnd.ehShor_per_run_ge_eighth`,
`≥ 1/8`) and the deterministic factor recovery compose into end-to-end EH Shor correctness, with the
QFT amplitude derived (not assumed). The remaining gate-level step — that `qftAmp` is the `uc_eval`
of the concrete inverse-QFT *gate* circuit — is the same single-register QFT-circuit correctness the
`FormalRV.QFT` inverse-QFT folder establishes, lifted per register.
