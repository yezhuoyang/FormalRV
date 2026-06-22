/-
  FormalRV.Audit.Gidney2025.EkeraHastadCircuitMeasurement — wiring the two-register QFT measurement
  (`FormalRV.QFT.TwoRegisterQFT.CircuitMeasurement`) to the Ekerå–Håstad probability `ehProb`, giving a
  `prob_partial_meas` success bound on the gate-built state.  GATE-HONEST half: the QFT gate
  (`twoRegQFT`, genuine `uc_eval`) and the measurement (`prob_partial_meas`).  ABSTRACTED half: the
  oracle is posited as the output state `twoRegOracleState` (see `CircuitMeasurement`'s scope note),
  weaker than the single-register `MultiplyCircuitProperty`; realizing it as an entangling oracle gate
  is the remaining open seam.

  The target register encodes the integer value `e = a − b·d` as the natural number
  `ehEnc x y = (e + 2^(ℓ+m)).toNat` (an injection of `ehE = (-2^(ℓ+m), 2^(ℓ+m))` into `[0, 2^(ℓ+m+1))`).
  With this encoding the generic measurement headline `prob_partial_meas_twoRegQFTMeasState` reindexes
  to the value set `ehE`, and (the real EH input + inverse vs forward kernel being complex conjugates)
  the per-fibre amplitude is `conj (qft2FiberAmp …)`, so its `normSq` matches.  Hence

      prob_partial_meas (… control outcome (j,k) …) (ehMeasState …) = ehCircuitMeasProb ℓ m d j k
                                                                     = ehProb ℓ m d j k        (gap 1)

  and `ehCircuit_per_run_ge_eighth` lands as `prob_partial_meas ≥ 1/8` on the genuine gate-built state.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.QFT.TwoRegisterQFT.CircuitMeasurement
import FormalRV.Audit.Gidney2025.EkeraHastadCircuit
import FormalRV.Verifier.ProofGate

namespace FormalRV.Audit.Gidney2025.EkeraHastadCircuit

open scoped BigOperators
open FormalRV.QFT.TwoRegisterQFT
open FormalRV.SQIRPort (prob_partial_meas)
open FormalRV.Audit.Gidney2025.EkeraHastad (cresid)
open FormalRV.Audit.Gidney2025.EkeraEndToEnd (goodOutcomes kPair)

/-! ## §1. The target-register encoding and its arithmetic -/

/-- Inject the integer value `e` into the target register `[0, 2^(ℓ+m+1))` by shifting by `2^(ℓ+m)`. -/
noncomputable def ehEncZ (ℓ m : ℕ) (e : ℤ) : ℕ := (e + (2 : ℤ) ^ (ℓ + m)).toNat

/-- The oracle's target value at `(x,y)`: `ehTarget d x y = x − y·d`, encoded as a natural. -/
noncomputable def ehEnc (ℓ m d : ℕ) : ℕ → ℕ → ℕ := fun x y => ehEncZ ℓ m (ehTarget d x y)

/-- Membership in `ehE` unfolded. -/
theorem mem_ehE_iff (ℓ m : ℕ) (e : ℤ) :
    e ∈ FormalRV.CFS.EkeraLemma7.ehE ℓ m ↔ -(2 : ℤ) ^ (ℓ + m) < e ∧ e < (2 : ℤ) ^ (ℓ + m) := by
  unfold FormalRV.CFS.EkeraLemma7.ehE
  exact Finset.mem_Ioo

/-- The encoding lands in the target register `[0, 2^(ℓ+m+1))` for every value in `ehE`. -/
theorem ehEncZ_lt (ℓ m : ℕ) (e : ℤ) (he : e ∈ FormalRV.CFS.EkeraLemma7.ehE ℓ m) :
    ehEncZ ℓ m e < 2 ^ (ℓ + m + 1) := by
  rw [mem_ehE_iff] at he
  unfold ehEncZ
  have hpow : ((2 : ℤ) ^ (ℓ + m + 1)) = 2 ^ (ℓ + m) + 2 ^ (ℓ + m) := by ring
  rw [Int.toNat_lt (by linarith [he.1])]
  push_cast
  linarith [he.2]

/-- The encoding is injective on `ehE` (both shifted values are non-negative). -/
theorem ehEncZ_injOn (ℓ m : ℕ) {e e' : ℤ}
    (he : e ∈ FormalRV.CFS.EkeraLemma7.ehE ℓ m) (he' : e' ∈ FormalRV.CFS.EkeraLemma7.ehE ℓ m)
    (heq : ehEncZ ℓ m e = ehEncZ ℓ m e') : e = e' := by
  rw [mem_ehE_iff] at he he'
  unfold ehEncZ at heq
  have h1 : (0 : ℤ) ≤ e + 2 ^ (ℓ + m) := by linarith [he.1]
  have h2 : (0 : ℤ) ≤ e' + 2 ^ (ℓ + m) := by linarith [he'.1]
  have e1 : (((e + 2 ^ (ℓ + m)).toNat : ℕ) : ℤ) = e + 2 ^ (ℓ + m) := Int.toNat_of_nonneg h1
  have e2 : (((e' + 2 ^ (ℓ + m)).toNat : ℕ) : ℤ) = e' + 2 ^ (ℓ + m) := Int.toNat_of_nonneg h2
  rw [heq, e2] at e1
  linarith [e1]

/-- The oracle's integer value is always in `ehE` (the registers are sized so `a − b·d` does not
wrap). -/
theorem ehTarget_mem_ehE (ℓ m d x y : ℕ) (hx : x < 2 ^ (ℓ + m)) (hy : y < 2 ^ ℓ) (hd : d < 2 ^ m) :
    ehTarget d x y ∈ FormalRV.CFS.EkeraLemma7.ehE ℓ m := by
  rw [mem_ehE_iff]
  unfold ehTarget
  have hyd : y * d < 2 ^ (ℓ + m) := by
    calc y * d < 2 ^ ℓ * 2 ^ m := Nat.mul_lt_mul'' hy hd
      _ = 2 ^ (ℓ + m) := by rw [← pow_add]
  have hxZ : (x : ℤ) < 2 ^ (ℓ + m) := by exact_mod_cast hx
  have hydZ : (y : ℤ) * (d : ℤ) < 2 ^ (ℓ + m) := by exact_mod_cast hyd
  have hyd0 : (0 : ℤ) ≤ (y : ℤ) * (d : ℤ) := by positivity
  have hx0 : (0 : ℤ) ≤ (x : ℤ) := by positivity
  constructor
  · linarith
  · linarith

/-! ## §2. The inverse-QFT matrix entry is the conjugate forward kernel -/

/-- `conj` of the forward QFT kernel is the inverse kernel: `conj e^{+2πi·xj/2^a} = e^{-2πi·xj/2^a}`. -/
theorem conj_qftKernel (a x j : ℕ) :
    starRingEnd ℂ (qftKernel a x j)
      = Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) * (j : ℂ) / (2 ^ a : ℂ)) := by
  unfold qftKernel
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, map_natCast, map_pow]
  ring

/-- **The inverse-QFT matrix entry is the conjugate forward kernel scaled by `1/√2^a`.**
`(IQFT_matrix a · |x⟩) j = (1/√2^a) · conj(qftKernel a x j)`. -/
theorem iqft_entry (a x j : ℕ) (hx : x < 2 ^ a) (hj : j < 2 ^ a) :
    (FormalRV.SQIRPort.IQFT_matrix a * FormalRV.Framework.basis_vector (2 ^ a) x)
        (⟨j, hj⟩ : Fin (2 ^ a)) 0
      = (1 / (Real.sqrt (2 ^ a : ℝ) : ℂ)) * starRingEnd ℂ (qftKernel a x j) := by
  rw [FormalRV.Framework.mul_basis_vector_apply (FormalRV.SQIRPort.IQFT_matrix a) x hx
        (⟨j, hj⟩ : Fin (2 ^ a))]
  rw [conj_qftKernel]
  unfold FormalRV.SQIRPort.IQFT_matrix
  congr 2

/-! ## §3. The gate fibre amplitude is the conjugate of the forward `qft2FiberAmp` -/

/-- `ehInput` is real, so `conj` fixes it. -/
theorem conj_ehInput (ℓ m x y : ℕ) : starRingEnd ℂ (ehInput ℓ m x y) = ehInput ℓ m x y := by
  unfold ehInput
  rw [map_div₀, map_one, Complex.conj_ofReal]

/-- **★ The gate's fibre-`e` control amplitude is `conj (qft2FiberAmp …)`. ★**  Combining the
inverse-vs-forward kernel conjugation (`iqft_entry`/`conj_qftKernel`), the real EH input
(`conj_ehInput`), and the target-fibre identification (`ehEncZ_injOn`), the fibre amplitude the gate
produces is the complex conjugate of the analysed `qft2FiberAmp` — hence has the same `normSq`. -/
theorem ehFiberCtrl_eq_conj (ℓ m d : ℕ) (e : ℤ) (he : e ∈ FormalRV.CFS.EkeraLemma7.ehE ℓ m)
    (j k : ℕ) (hj : j < 2 ^ (ℓ + m)) (hk : k < 2 ^ ℓ) (hdlt : d < 2 ^ m) :
    fiberCtrl (ℓ + m) ℓ (ℓ + m + 1) (ehInput ℓ m) (ehEnc ℓ m d)
        ⟨ehEncZ ℓ m e, ehEncZ_lt ℓ m e he⟩
        (FormalRV.Framework.kron_vec_combine (⟨j, hj⟩ : Fin (2 ^ (ℓ + m))) (⟨k, hk⟩ : Fin (2 ^ ℓ))) 0
      = starRingEnd ℂ (qft2FiberAmp (ℓ + m) ℓ (ehInput ℓ m) (ehTarget d) j k e) := by
  rw [fiberCtrl_apply_combine (ℓ + m) ℓ (ℓ + m + 1) (ehInput ℓ m) (ehEnc ℓ m d)
        ⟨ehEncZ ℓ m e, ehEncZ_lt ℓ m e he⟩ j k hj hk]
  -- the common big sum (forward kernels conjugated)
  have hconst : (1 / (Real.sqrt (2 ^ (ℓ + m) : ℝ) : ℂ)) * (1 / (Real.sqrt (2 ^ ℓ : ℝ) : ℂ))
      = 1 / (Real.sqrt (2 ^ (ℓ + m) * 2 ^ ℓ : ℝ) : ℂ) := by
    rw [Real.sqrt_mul (by positivity)]
    push_cast
    rw [one_div_mul_one_div]
  -- LHS normal form
  have hLHS : (∑ x ∈ Finset.range (2 ^ (ℓ + m)),
        ∑ y ∈ (Finset.range (2 ^ ℓ)).filter
            (fun y => ehEnc ℓ m d x y = (⟨ehEncZ ℓ m e, ehEncZ_lt ℓ m e he⟩ : Fin (2 ^ (ℓ + m + 1))).val),
          ehInput ℓ m x y
            * (FormalRV.SQIRPort.IQFT_matrix (ℓ + m) * FormalRV.Framework.basis_vector (2 ^ (ℓ + m)) x)
                (⟨j, hj⟩ : Fin (2 ^ (ℓ + m))) 0
            * (FormalRV.SQIRPort.IQFT_matrix ℓ * FormalRV.Framework.basis_vector (2 ^ ℓ) y)
                (⟨k, hk⟩ : Fin (2 ^ ℓ)) 0)
      = (1 / (Real.sqrt (2 ^ (ℓ + m) : ℝ) : ℂ)) * (1 / (Real.sqrt (2 ^ ℓ : ℝ) : ℂ))
          * ∑ x ∈ Finset.range (2 ^ (ℓ + m)),
              ∑ y ∈ (Finset.range (2 ^ ℓ)).filter (fun y => ehTarget d x y = e),
                ehInput ℓ m x y * starRingEnd ℂ (qftKernel (ℓ + m) x j)
                  * starRingEnd ℂ (qftKernel ℓ y k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx' : x < 2 ^ (ℓ + m) := Finset.mem_range.mp hx
    have hfilter : (Finset.range (2 ^ ℓ)).filter
          (fun y => ehEnc ℓ m d x y = (⟨ehEncZ ℓ m e, ehEncZ_lt ℓ m e he⟩ : Fin (2 ^ (ℓ + m + 1))).val)
        = (Finset.range (2 ^ ℓ)).filter (fun y => ehTarget d x y = e) := by
      apply Finset.filter_congr
      intro y hy
      have hy' : y < 2 ^ ℓ := Finset.mem_range.mp hy
      show ehEnc ℓ m d x y = ehEncZ ℓ m e ↔ ehTarget d x y = e
      unfold ehEnc
      constructor
      · intro h; exact ehEncZ_injOn ℓ m (ehTarget_mem_ehE ℓ m d x y hx' hy' hdlt) he h
      · intro h; rw [h]
    rw [hfilter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have hy' : y < 2 ^ ℓ := Finset.mem_range.mp (Finset.mem_of_mem_filter y hy)
    rw [iqft_entry (ℓ + m) x j hx' hj, iqft_entry ℓ y k hy' hk]
    ring
  rw [hLHS]
  -- RHS normal form
  unfold qft2FiberAmp
  rw [map_mul, map_div₀, map_one, Complex.conj_ofReal, map_sum]
  rw [← hconst]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [map_mul, map_mul, conj_ehInput]

/-! ## §4. Reindex the target sum from `Fin (2^(ℓ+m+1))` to the value set `ehE` -/

/-- A total target-index map `ℤ → Fin (2^(ℓ+m+1))` (the genuine encoding on `ehE`, junk via `%`
elsewhere) — convenient for the `Finset.sum_image` reindex. -/
noncomputable def encTot (ℓ m : ℕ) (e : ℤ) : Fin (2 ^ (ℓ + m + 1)) :=
  ⟨ehEncZ ℓ m e % 2 ^ (ℓ + m + 1), Nat.mod_lt _ (Nat.two_pow_pos (ℓ + m + 1))⟩

/-- On `ehE`, `encTot` is the genuine encoding. -/
theorem encTot_eq (ℓ m : ℕ) (e : ℤ) (he : e ∈ FormalRV.CFS.EkeraLemma7.ehE ℓ m) :
    encTot ℓ m e = ⟨ehEncZ ℓ m e, ehEncZ_lt ℓ m e he⟩ := by
  apply Fin.ext
  show ehEncZ ℓ m e % 2 ^ (ℓ + m + 1) = ehEncZ ℓ m e
  exact Nat.mod_eq_of_lt (ehEncZ_lt ℓ m e he)

/-- `encTot` is injective on `ehE`. -/
theorem encTot_injOn (ℓ m : ℕ) {e e' : ℤ}
    (he : e ∈ FormalRV.CFS.EkeraLemma7.ehE ℓ m) (he' : e' ∈ FormalRV.CFS.EkeraLemma7.ehE ℓ m)
    (heq : encTot ℓ m e = encTot ℓ m e') : e = e' := by
  rw [encTot_eq ℓ m e he, encTot_eq ℓ m e' he'] at heq
  exact ehEncZ_injOn ℓ m he he' (Fin.mk.injEq .. ▸ heq)

/-- Off the image of `ehE` under `encTot`, the fibre control amplitude vanishes (no `(x,y)` writes
that target value). -/
theorem fiberCtrl_eq_zero_of_not_image (ℓ m d j k : ℕ) (hj : j < 2 ^ (ℓ + m)) (hk : k < 2 ^ ℓ)
    (hdlt : d < 2 ^ m) (i : Fin (2 ^ (ℓ + m + 1)))
    (hi : i ∉ (FormalRV.CFS.EkeraLemma7.ehE ℓ m).image (encTot ℓ m)) :
    fiberCtrl (ℓ + m) ℓ (ℓ + m + 1) (ehInput ℓ m) (ehEnc ℓ m d) i
        (FormalRV.Framework.kron_vec_combine (⟨j, hj⟩ : Fin (2 ^ (ℓ + m))) (⟨k, hk⟩ : Fin (2 ^ ℓ))) 0
      = 0 := by
  rw [fiberCtrl_apply_combine (ℓ + m) ℓ (ℓ + m + 1) (ehInput ℓ m) (ehEnc ℓ m d) i j k hj hk]
  apply Finset.sum_eq_zero
  intro x hx
  have hx' : x < 2 ^ (ℓ + m) := Finset.mem_range.mp hx
  apply Finset.sum_eq_zero
  intro y hy
  -- y is in the filter, so ehEnc d x y = i.val; derive i ∈ image, contradiction
  have hmem := Finset.mem_filter.mp hy
  have hy' : y < 2 ^ ℓ := Finset.mem_range.mp hmem.1
  have henc : ehEnc ℓ m d x y = i.val := hmem.2
  exfalso
  apply hi
  rw [Finset.mem_image]
  refine ⟨ehTarget d x y, ehTarget_mem_ehE ℓ m d x y hx' hy' hdlt, ?_⟩
  apply Fin.ext
  rw [encTot_eq ℓ m (ehTarget d x y) (ehTarget_mem_ehE ℓ m d x y hx' hy' hdlt)]
  show ehEncZ ℓ m (ehTarget d x y) = i.val
  rw [← henc]
  rfl

/-- **Reindex the target sum to the value set `ehE`.**  Off the encoded image the fibre is zero
(`fiberCtrl_eq_zero_of_not_image`); on the image `encTot` is the injective genuine encoding
(`encTot_injOn`/`encTot_eq`) and the fibre amplitude is `conj (qft2FiberAmp)` (`ehFiberCtrl_eq_conj`),
whose `normSq` matches. -/
theorem eh_fiber_sum_eq (ℓ m d j k : ℕ) (hj : j < 2 ^ (ℓ + m)) (hk : k < 2 ^ ℓ) (hdlt : d < 2 ^ m) :
    (∑ i : Fin (2 ^ (ℓ + m + 1)),
        Complex.normSq
          (fiberCtrl (ℓ + m) ℓ (ℓ + m + 1) (ehInput ℓ m) (ehEnc ℓ m d) i
            (FormalRV.Framework.kron_vec_combine (⟨j, hj⟩ : Fin (2 ^ (ℓ + m)))
              (⟨k, hk⟩ : Fin (2 ^ ℓ))) 0))
      = ∑ e ∈ FormalRV.CFS.EkeraLemma7.ehE ℓ m,
          Complex.normSq (qft2FiberAmp (ℓ + m) ℓ (ehInput ℓ m) (ehTarget d) j k e) := by
  rw [← Finset.sum_subset
        (Finset.subset_univ ((FormalRV.CFS.EkeraLemma7.ehE ℓ m).image (encTot ℓ m)))
        (fun i _ hi => by
          rw [fiberCtrl_eq_zero_of_not_image ℓ m d j k hj hk hdlt i hi, Complex.normSq_zero])]
  rw [Finset.sum_image (fun e he e' he' heq => encTot_injOn ℓ m he he' heq)]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [encTot_eq ℓ m e he, ehFiberCtrl_eq_conj ℓ m d e he j k hj hk hdlt, Complex.normSq_conj]

/-! ## §5. The bridge to `ehCircuitMeasProb` / `ehProb`, and the pipeline-form success bound -/

/-- **★ The gate-built measurement probability IS the analysed `ehCircuitMeasProb` (= `ehProb`). ★**
Combining the generic measurement headline, the target reindex, and the inverse-vs-forward kernel
conjugation: measuring the two control registers of the genuine gate-built state at `(j,k)` gives
exactly `ehCircuitMeasProb ℓ m d j k`. -/
theorem prob_partial_meas_eq_ehCircuitMeasProb (ℓ m d j k : ℕ) (hℓ : 1 ≤ ℓ)
    (hj : j < 2 ^ (ℓ + m)) (hk : k < 2 ^ ℓ) (hdlt : d < 2 ^ m) :
    prob_partial_meas
        (FormalRV.SQIRPort.basis_vector (2 ^ ((ℓ + m) + ℓ))
          (FormalRV.Framework.kron_vec_combine (⟨j, hj⟩ : Fin (2 ^ (ℓ + m)))
            (⟨k, hk⟩ : Fin (2 ^ ℓ))).val)
        (twoRegQFTMeasState (ℓ + m) ℓ (ℓ + m + 1) (ehInput ℓ m) (ehEnc ℓ m d))
      = ehCircuitMeasProb ℓ m d j k := by
  rw [prob_partial_meas_twoRegQFTMeasState (ℓ + m) ℓ (ℓ + m + 1) (by omega) (by omega)
        (ehInput ℓ m) (ehEnc ℓ m d) j k hj hk]
  rw [eh_fiber_sum_eq ℓ m d j k hj hk hdlt]
  rfl

/-- **★ Ekerå–Håstad per-run success `≥ 1/8` as a `prob_partial_meas` bound. ★**  The verified
two-register QFT gate, applied to the post-oracle state and measured in the control registers,
observes a good pair with probability `≥ 1/8` — the pipeline-form success bound.  GATE-HONEST in its
QFT + measurement; the oracle entanglement is the abstracted output state `twoRegOracleState` (the
documented open seam — realizing it as an entangling oracle gate would reach full parity with the
single-register pipeline). -/
theorem ehGate_per_run_ge_eighth (ℓ m d : ℕ) (hℓ : 1 ≤ ℓ) (hm : 2 ≤ m) (hd0 : 0 < d) (hdlt : d < 2 ^ m) :
    (1 / 8 : ℝ) ≤ ∑ j ∈ goodOutcomes ℓ m d,
      prob_partial_meas
        (FormalRV.SQIRPort.basis_vector (2 ^ ((ℓ + m) + ℓ)) (j * 2 ^ ℓ + kPair ℓ m d j))
        (twoRegQFTMeasState (ℓ + m) ℓ (ℓ + m + 1) (ehInput ℓ m) (ehEnc ℓ m d)) := by
  have key : ∀ j ∈ goodOutcomes ℓ m d,
      prob_partial_meas
          (FormalRV.SQIRPort.basis_vector (2 ^ ((ℓ + m) + ℓ)) (j * 2 ^ ℓ + kPair ℓ m d j))
          (twoRegQFTMeasState (ℓ + m) ℓ (ℓ + m + 1) (ehInput ℓ m) (ehEnc ℓ m d))
        = ehCircuitMeasProb ℓ m d j (kPair ℓ m d j) := by
    intro j hj_mem
    classical
    have hj : j < 2 ^ (ℓ + m) := Finset.mem_range.mp (Finset.mem_filter.mp hj_mem).1
    have hex := (Finset.mem_filter.mp hj_mem).2
    have hk : kPair ℓ m d j < 2 ^ ℓ := by
      unfold kPair; rw [dif_pos hex]; exact hex.choose_spec.1
    have hidx : j * 2 ^ ℓ + kPair ℓ m d j
        = (FormalRV.Framework.kron_vec_combine (⟨j, hj⟩ : Fin (2 ^ (ℓ + m)))
            (⟨kPair ℓ m d j, hk⟩ : Fin (2 ^ ℓ))).val := rfl
    rw [hidx]
    exact prob_partial_meas_eq_ehCircuitMeasProb ℓ m d j (kPair ℓ m d j) hℓ hj hk hdlt
  rw [Finset.sum_congr rfl key]
  exact ehCircuit_per_run_ge_eighth ℓ m d hℓ hm hd0 hdlt

end FormalRV.Audit.Gidney2025.EkeraHastadCircuit

/-! ## §6. Verifier gates -/
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadCircuit.ehEncZ_lt
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadCircuit.ehEncZ_injOn
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadCircuit.ehTarget_mem_ehE
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadCircuit.iqft_entry
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadCircuit.ehFiberCtrl_eq_conj
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadCircuit.eh_fiber_sum_eq
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadCircuit.prob_partial_meas_eq_ehCircuitMeasProb
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadCircuit.ehGate_per_run_ge_eighth
