/-
  FormalRV.QFT.TwoRegisterQFT.Basic — a REUSABLE two-register quantum Fourier transform
  measurement model, the amplitude/Born-probability layer of the Ekerå–Håstad short-DLP circuit
  (and Ekerå's general-DLP circuit — both use the same two-control-register + entangled-target shape).

  ## The model (1702.00249 §quantum-part l.408–451; 1905.09084 §general DLP)

  A run prepares a two-control-register input state with amplitudes `c x y` (`x` in register A of
  `2^a` states, `y` in register B of `2^b` states), an oracle entangles a target register via a
  function `f : x,y ↦ e` (the measured group element), the QFT of size `2^a` is applied to A and the
  QFT of size `2^b` to B, and all three registers are measured.

  Using the QFT convention `|x⟩ ↦ (1/√2^a) ∑_j e^{2πi xj/2^a} |j⟩`, the amplitude of measuring
  `(j, k, e)` is `(1/√(2^a·2^b)) ∑_{(x,y): f x y = e} c x y · e^{2πi xj/2^a} · e^{2πi yk/2^b}`
  (`qft2FiberAmp`), and the probability of the control outcome `(j,k)` — marginalising the target —
  is `∑_e ‖qft2FiberAmp …‖²` (`qft2MeasProb`).

  ## What is reusable here (clear interface)

  * `qftKernel a x j`           — the QFT phase `e^{2πi xj/2^a}`.
  * `qftAmp a c j`              — single-register QFT output amplitude from input amplitudes `c`.
  * `qft2Amp a b c j k`         — two-register QFT output amplitude.
  * `qft2Amp_factor`            — **the structural law**: the two-register QFT is the TENSOR product of
                                  two single-register QFTs (`qft2Amp = qftAmp · qftAmp` when `c` factors).
  * `qft2FiberAmp` / `qft2MeasProb` — the target-fibre amplitude and the Born probability of `(j,k)`.
  * `qft2MeasProb_nonneg`       — the probability is `≥ 0`.

  Instantiate with `c =` (normalised uniform) and `f = (x,y) ↦ x − y·d` to obtain the Ekerå–Håstad
  measurement probability; see `EkeraHastadCircuit` and `README.md`.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import Mathlib

namespace FormalRV.QFT.TwoRegisterQFT

open scoped BigOperators

/-- The QFT phase kernel `e^{2πi·x·j / 2^a}`. -/
noncomputable def qftKernel (a x j : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((x : ℂ) * (j : ℂ)) / (2 ^ a : ℂ))

/-- Single-register QFT output amplitude at outcome `j` from input amplitudes `c : ℕ → ℂ`
    (`|ψ⟩ = ∑_{x<2^a} c x |x⟩ ↦ ∑_j (qftAmp a c j) |j⟩`). -/
noncomputable def qftAmp (a : ℕ) (c : ℕ → ℂ) (j : ℕ) : ℂ :=
  (1 / (Real.sqrt (2 ^ a) : ℂ)) * ∑ x ∈ Finset.range (2 ^ a), c x * qftKernel a x j

/-- Two-register QFT output amplitude at `(j,k)` from input amplitudes `c : ℕ → ℕ → ℂ`. -/
noncomputable def qft2Amp (a b : ℕ) (c : ℕ → ℕ → ℂ) (j k : ℕ) : ℂ :=
  (1 / (Real.sqrt (2 ^ a * 2 ^ b) : ℂ))
    * ∑ x ∈ Finset.range (2 ^ a), ∑ y ∈ Finset.range (2 ^ b),
        c x y * qftKernel a x j * qftKernel b y k

/-- **★ The two-register QFT is the TENSOR of two single-register QFTs. ★**  If the input amplitudes
    factor as `c x y = c₁ x · c₂ y`, then `qft2Amp = qftAmp(c₁) · qftAmp(c₂)`.  This is the structural
    reusability law: a multi-register QFT factors over its registers. -/
theorem qft2Amp_factor (a b : ℕ) (c₁ c₂ : ℕ → ℂ) (j k : ℕ) :
    qft2Amp a b (fun x y => c₁ x * c₂ y) j k = qftAmp a c₁ j * qftAmp b c₂ k := by
  unfold qft2Amp qftAmp
  have hnorm : (1 / (Real.sqrt (2 ^ a * 2 ^ b) : ℂ))
      = (1 / (Real.sqrt (2 ^ a) : ℂ)) * (1 / (Real.sqrt (2 ^ b) : ℂ)) := by
    rw [Real.sqrt_mul (by positivity)]
    push_cast
    rw [one_div_mul_one_div]
  rw [hnorm]
  rw [mul_mul_mul_comm]
  congr 1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  ring

/-- The QFT amplitude of `(j,k)` restricted to the target fibre `f x y = e` (the amplitude of the
    joint outcome `|j,k,e⟩`). -/
noncomputable def qft2FiberAmp (a b : ℕ) (c : ℕ → ℕ → ℂ) (f : ℕ → ℕ → ℤ) (j k : ℕ) (e : ℤ) : ℂ :=
  (1 / (Real.sqrt (2 ^ a * 2 ^ b) : ℂ))
    * ∑ x ∈ Finset.range (2 ^ a), ∑ y ∈ (Finset.range (2 ^ b)).filter (fun y => f x y = e),
        c x y * qftKernel a x j * qftKernel b y k

/-- **Born probability of the control outcome `(j,k)`**, marginalising the target register over the
    value set `E` (`= ∑_e ‖amplitude of (j,k,e)‖²`). -/
noncomputable def qft2MeasProb (a b : ℕ) (c : ℕ → ℕ → ℂ) (f : ℕ → ℕ → ℤ) (E : Finset ℤ) (j k : ℕ) : ℝ :=
  ∑ e ∈ E, Complex.normSq (qft2FiberAmp a b c f j k e)

/-- The Born probability is non-negative. -/
theorem qft2MeasProb_nonneg (a b : ℕ) (c : ℕ → ℕ → ℂ) (f : ℕ → ℕ → ℤ) (E : Finset ℤ) (j k : ℕ) :
    0 ≤ qft2MeasProb a b c f E j k :=
  Finset.sum_nonneg (fun _e _ => Complex.normSq_nonneg _)

end FormalRV.QFT.TwoRegisterQFT
