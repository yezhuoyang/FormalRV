/-
  FormalRV.Audit.Gidney2025.EkeraHastadCircuit — instantiating the reusable two-register QFT model
  (`FormalRV.QFT.TwoRegisterQFT`) at the Ekerå–Håstad short-DLP circuit, and connecting its Born
  probability to the analysed expression `ehProb` (`EkeraEndToEnd`).

  The EH circuit (1702.00249 l.408–451): uniform superposition over `(a,b) ∈ [0,2^{ℓ+m})×[0,2^ℓ)`,
  oracle `↦ |a,b,[a−bd]g⟩`, `QFT_{2^{ℓ+m}} ⊗ QFT_{2^ℓ}` on the controls, measure.  Instantiating the
  reusable model with the normalised-uniform input and the target `f(a,b) = a − b·d` gives
  `ehCircuitMeasProb`, the probability of control outcome `(j,k)`.

  `ehCircuit_fiberAmp_eq` shows its per-fibre amplitude is EXACTLY the paper's raw amplitude
  `(1/2^{2ℓ+m}) ∑_{(a,b): a−bd=e} e^{2πi(aj + 2^m bk)/2^{ℓ+m}}` (l.457) — the circuit half of the
  boundary.  Composing with the paper's steps 2–4 (factor the `e`-phase, centre `b`, reduce mod
  `2^{ℓ+m}`; each a unit-modulus factor, invariant under `‖·‖²`) and the fibre reindexing
  `(x,y)↦y` (`x = e+bd`, the `ehBe` set) identifies `ehCircuitMeasProb` with `ehProb`, after which
  `EkeraEndToEnd.ehShor_per_run_ge_eighth` gives the `≥ 1/8` per-run success on the genuine circuit
  Born probability.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.QFT.TwoRegisterQFT.Basic
import FormalRV.QFT.TwoRegisterQFT.Circuit
import FormalRV.Audit.Gidney2025.EkeraEndToEnd
import FormalRV.Verifier.ProofGate

namespace FormalRV.Audit.Gidney2025.EkeraHastadCircuit

open scoped BigOperators
open FormalRV.QFT.TwoRegisterQFT
open FormalRV.Audit.Gidney2025.EkeraHastad (cresid)

/-- The EH circuit's normalised uniform input over the two control registers. -/
noncomputable def ehInput (ℓ m : ℕ) : ℕ → ℕ → ℂ := fun _ _ => (1 / (Real.sqrt (2 ^ (2 * ℓ + m)) : ℂ))

/-- The EH oracle target: the measured group element index `e = a − b·d`. -/
def ehTarget (d : ℕ) : ℕ → ℕ → ℤ := fun x y => (x : ℤ) - (y : ℤ) * (d : ℤ)

/-- **The Ekerå–Håstad circuit measurement probability** of control outcome `(j,k)`, via the reusable
    two-register QFT model. -/
noncomputable def ehCircuitMeasProb (ℓ m d j k : ℕ) : ℝ :=
  qft2MeasProb (ℓ + m) ℓ (ehInput ℓ m) (ehTarget d) (FormalRV.CFS.EkeraLemma7.ehE ℓ m) j k

theorem ehCircuitMeasProb_nonneg (ℓ m d j k : ℕ) : 0 ≤ ehCircuitMeasProb ℓ m d j k :=
  qft2MeasProb_nonneg _ _ _ _ _ _ _

/-- **The two QFT kernels combine into the paper's single phase.**
    `e^{2πi·xj/2^{ℓ+m}} · e^{2πi·yk/2^ℓ} = e^{2πi(xj + 2^m·yk)/2^{ℓ+m}}` (since `2^{ℓ+m} = 2^m·2^ℓ`). -/
theorem ehKernel_combine (ℓ m x j y k : ℕ) :
    qftKernel (ℓ + m) x j * qftKernel ℓ y k
      = Complex.exp (2 * Real.pi * Complex.I * ((x : ℂ) * j + 2 ^ m * ((y : ℂ) * k))
          / (2 ^ (ℓ + m) : ℂ)) := by
  unfold qftKernel
  rw [← Complex.exp_add]
  congr 1
  have hℓ : (2 : ℂ) ^ ℓ ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsplit : (2 : ℂ) ^ (ℓ + m) = 2 ^ m * 2 ^ ℓ := by rw [pow_add]; ring
  rw [hsplit]
  field_simp

/-- **★ The EH circuit's per-fibre amplitude is the paper's raw amplitude. ★**  (1702.00249 l.457.)
    Pulling out the uniform input and combining the two QFT kernels (`ehKernel_combine`), the amplitude
    of the joint outcome `|j,k,e⟩` is `(1/2^{2ℓ+m}) ∑_{(a,b): a−bd=e} e^{2πi(aj + 2^m bk)/2^{ℓ+m}}`. -/
theorem ehCircuit_fiberAmp_eq (ℓ m d j k : ℕ) (e : ℤ) :
    qft2FiberAmp (ℓ + m) ℓ (ehInput ℓ m) (ehTarget d) j k e
      = (1 / (2 ^ (2 * ℓ + m) : ℂ))
          * ∑ x ∈ Finset.range (2 ^ (ℓ + m)),
              ∑ y ∈ (Finset.range (2 ^ ℓ)).filter (fun y => ehTarget d x y = e),
                Complex.exp (2 * Real.pi * Complex.I * ((x : ℂ) * j + 2 ^ m * ((y : ℂ) * k))
                  / (2 ^ (ℓ + m) : ℂ)) := by
  unfold qft2FiberAmp ehInput
  have hpow : (2 : ℝ) ^ (ℓ + m) * 2 ^ ℓ = 2 ^ (2 * ℓ + m) := by rw [← pow_add]; congr 1; omega
  have hSnn : (0 : ℝ) ≤ 2 ^ (2 * ℓ + m) := by positivity
  have hpref : (1 / (Real.sqrt (2 ^ (ℓ + m) * 2 ^ ℓ) : ℂ)) * (1 / (Real.sqrt (2 ^ (2 * ℓ + m)) : ℂ))
      = 1 / (2 ^ (2 * ℓ + m) : ℂ) := by
    rw [hpow, div_mul_div_comm, one_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt hSnn]
    push_cast; ring
  rw [← hpref, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← ehKernel_combine]; ring

/-! ## §A. Closing the amplitude identity `ehCircuitMeasProb = ehProb`.

Two ingredients: (1) the fibre reindexing `(x,y) ↦ y` (`x = e+bd`, landing in `ehBe`), and
(2) the paper's steps 2–4 (factor the `e`-phase, centre `b`, reduce mod `2^{ℓ+m}`) — each a
`b`-independent unit-modulus factor, so invariant under `‖·‖²`. -/

/-- Singleton collapse: `∑_{x<N} [if (x:ℤ)=w then h x] = if (0≤w<N) then h w.toNat else 0`. -/
private theorem sum_range_int_ite {M : Type*} [AddCommMonoid M] (N : ℕ) (w : ℤ) (h : ℕ → M) :
    (∑ x ∈ Finset.range N, if (x : ℤ) = w then h x else 0)
      = if (0 ≤ w ∧ w < (N : ℤ)) then h w.toNat else 0 := by
  split_ifs with hw
  · obtain ⟨hw0, hwN⟩ := hw
    have hmem : w.toNat ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single w.toNat]
    · rw [if_pos (Int.toNat_of_nonneg hw0)]
    · intro x _ hx
      refine if_neg (fun hxw => hx ?_)
      omega
    · intro hcon; exact absurd hmem hcon
  · apply Finset.sum_eq_zero
    intro x hx
    refine if_neg (fun hxw => hw ?_)
    refine ⟨hxw ▸ Int.natCast_nonneg x, ?_⟩
    rw [← hxw]; exact_mod_cast Finset.mem_range.mp hx

/-- **The fibre reindexing.**  The EH target fibre `{(x,y) : x − yd = e}` is reindexed by `y ↦ b`
    (with `x = (e+bd).toNat`), landing in `ehBe ℓ m d e`. -/
theorem ehFiber_reindex {M : Type*} [AddCommMonoid M] (ℓ m d : ℕ) (e : ℤ) (g : ℕ → ℕ → M) :
    (∑ x ∈ Finset.range (2 ^ (ℓ + m)),
        ∑ y ∈ (Finset.range (2 ^ ℓ)).filter (fun y => ehTarget d x y = e), g x y)
      = ∑ b ∈ FormalRV.CFS.EkeraLemma7.ehBe ℓ m d e, g (e + (b : ℤ) * (d : ℤ)).toNat b := by
  simp only [ehTarget, Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold FormalRV.CFS.EkeraLemma7.ehBe
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hcond : ∀ x : ℕ, ((x : ℤ) - (y : ℤ) * (d : ℤ) = e) = ((x : ℤ) = e + (y : ℤ) * (d : ℤ)) := by
    intro x; apply propext; constructor <;> intro h <;> omega
  simp only [hcond]
  rw [sum_range_int_ite (2 ^ (ℓ + m)) (e + (y : ℤ) * (d : ℤ)) (fun x => g x y)]
  have hN : (((2 ^ (ℓ + m) : ℕ)) : ℤ) = (2 : ℤ) ^ (ℓ + m) := by push_cast; ring
  rw [hN]

#verify_clean sum_range_int_ite
#verify_clean ehFiber_reindex

/-- The circuit's per-fibre `‖·‖²` equals `(1/2^{2(2ℓ+m)})·‖∑_{b∈ehBe} e^{raw-phase}‖²` — the prefactor
    extracted and the fibre reindexed (no phase manipulation yet). -/
theorem ehFiberNormSq_raw (ℓ m d j k : ℕ) (e : ℤ) :
    Complex.normSq (qft2FiberAmp (ℓ + m) ℓ (ehInput ℓ m) (ehTarget d) j k e)
      = (1 / (2 : ℝ) ^ (2 * (2 * ℓ + m)))
          * Complex.normSq (∑ b ∈ FormalRV.CFS.EkeraLemma7.ehBe ℓ m d e,
              Complex.exp (2 * Real.pi * Complex.I
                * ((((e + (b : ℤ) * (d : ℤ)).toNat : ℕ) : ℂ) * j + 2 ^ m * ((b : ℂ) * k))
                  / (2 ^ (ℓ + m) : ℂ))) := by
  rw [ehCircuit_fiberAmp_eq,
      ehFiber_reindex ℓ m d e (fun x y => Complex.exp (2 * Real.pi * Complex.I
        * ((x : ℂ) * j + 2 ^ m * ((y : ℂ) * k)) / (2 ^ (ℓ + m) : ℂ))),
      Complex.normSq_mul]
  congr 1
  rw [map_div₀, map_one, map_pow]
  rw [show Complex.normSq 2 = (4 : ℝ) by simp [Complex.normSq]; norm_num]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]

/-- `e^{2πi·z} = 1` for integer `z`. -/
private theorem exp_two_pi_int (z : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ)) = 1 := by
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (z : ℂ)
        = (z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I z

/-- `‖e^{↑r·i}‖² = 1` for real `r`. -/
private theorem normSq_exp_ofReal_mul_I (r : ℝ) :
    Complex.normSq (Complex.exp ((r : ℂ) * Complex.I)) = 1 := by
  rw [Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      ← pow_two, ← pow_two]
  linarith [Real.sin_sq_add_cos_sq r]

/-- **★ (gap 1) The per-fibre phase invariance (steps 2–4). ★**  `‖∑_b e^{raw}‖² = ‖∑_b e^{iθ}‖²`:
    per-`b`, `e^{raw_b} = U · e^{iθ_b}` with `U = e^{2πi(ej + 2^{ℓ-1}c)/2^{ℓ+m}}` (`|U|=1`), using
    `(dj+2^m k) = c + 2^{ℓ+m}·s` (`c = {·}`, `s` from `Int.dvd_self_sub_bmod`) and `e^{2πi·bs}=1`. -/
theorem ehPhase_normSq (ℓ m d j k : ℕ) (e : ℤ) :
    Complex.normSq (∑ b ∈ FormalRV.CFS.EkeraLemma7.ehBe ℓ m d e,
        Complex.exp (2 * Real.pi * Complex.I
          * ((((e + (b : ℤ) * (d : ℤ)).toNat : ℕ) : ℂ) * j + 2 ^ m * ((b : ℂ) * k))
            / (2 ^ (ℓ + m) : ℂ)))
      = Complex.normSq (∑ b ∈ FormalRV.CFS.EkeraLemma7.ehBe ℓ m d e,
          Complex.exp (((2 * Real.pi / (2 : ℝ) ^ (ℓ + m)) * ((b : ℝ) - (2 : ℝ) ^ (ℓ - 1))
            * ((cresid ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m)) : ℤ) : ℝ) : ℝ) * Complex.I)) := by
  set c := cresid ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m)) with hc
  obtain ⟨s, hs⟩ := @Int.dvd_self_sub_bmod ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m))
  have hWcastC : (d : ℂ) * (j : ℂ) + (2 : ℂ) ^ m * (k : ℂ) = (c : ℂ) + (2 : ℂ) ^ (ℓ + m) * (s : ℂ) := by
    have hcb : Int.bmod ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m)) = c := rfl
    rw [hcb] at hs
    have hR : ((((d : ℤ) * j + 2 ^ m * k) - c : ℤ) : ℂ) = (((2 ^ (ℓ + m) : ℕ) : ℤ) : ℂ) * (s : ℂ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hs
    push_cast at hR
    linear_combination hR
  have hper : ∀ b ∈ FormalRV.CFS.EkeraLemma7.ehBe ℓ m d e,
      Complex.exp (2 * Real.pi * Complex.I
          * ((((e + (b : ℤ) * (d : ℤ)).toNat : ℕ) : ℂ) * j + 2 ^ m * ((b : ℂ) * k))
            / (2 ^ (ℓ + m) : ℂ))
        = Complex.exp ((2 * Real.pi * ((e : ℝ) * j + (2 : ℝ) ^ (ℓ - 1) * (c : ℝ)) / (2 : ℝ) ^ (ℓ + m) : ℝ)
              * Complex.I)
          * Complex.exp (((2 * Real.pi / (2 : ℝ) ^ (ℓ + m)) * ((b : ℝ) - (2 : ℝ) ^ (ℓ - 1))
              * ((c : ℤ) : ℝ) : ℝ) * Complex.I) := by
    intro b hb
    have hb0 : (0 : ℤ) ≤ e + (b : ℤ) * (d : ℤ) := (Finset.mem_filter.mp hb).2.1
    have htoNatC : (((e + (b : ℤ) * (d : ℤ)).toNat : ℕ) : ℂ) = (e : ℂ) + (b : ℂ) * (d : ℂ) := by
      have h1 : ((e + (b : ℤ) * (d : ℤ)).toNat : ℤ) = e + (b : ℤ) * (d : ℤ) := Int.toNat_of_nonneg hb0
      calc (((e + (b : ℤ) * (d : ℤ)).toNat : ℕ) : ℂ)
          = (((e + (b : ℤ) * (d : ℤ)).toNat : ℤ) : ℂ) := by push_cast; ring
        _ = ((e + (b : ℤ) * (d : ℤ) : ℤ) : ℂ) := by rw [h1]
        _ = (e : ℂ) + (b : ℂ) * (d : ℂ) := by push_cast; ring
    rw [← Complex.exp_add]
    have key : 2 * Real.pi * Complex.I
          * ((((e + (b : ℤ) * (d : ℤ)).toNat : ℕ) : ℂ) * j + 2 ^ m * ((b : ℂ) * k))
            / (2 ^ (ℓ + m) : ℂ)
        = ((2 * Real.pi * ((e : ℝ) * j + (2 : ℝ) ^ (ℓ - 1) * (c : ℝ)) / (2 : ℝ) ^ (ℓ + m) : ℝ) : ℂ)
              * Complex.I
            + ((2 * Real.pi / (2 : ℝ) ^ (ℓ + m)) * ((b : ℝ) - (2 : ℝ) ^ (ℓ - 1)) * ((c : ℤ) : ℝ) : ℝ)
              * Complex.I
          + 2 * Real.pi * Complex.I * (((b : ℤ) * s : ℤ) : ℂ) := by
      rw [htoNatC]
      rw [show ((e : ℂ) + (b : ℂ) * (d : ℂ)) * (j : ℂ) + (2 : ℂ) ^ m * ((b : ℂ) * (k : ℂ))
            = (e : ℂ) * j + (b : ℂ) * ((d : ℂ) * (j : ℂ) + (2 : ℂ) ^ m * (k : ℂ)) by ring]
      rw [hWcastC]
      have h2 : (2 : ℂ) ^ (ℓ + m) ≠ 0 := pow_ne_zero _ (by norm_num)
      have h2r : ((2 : ℝ) ^ (ℓ + m) : ℂ) ≠ 0 := by push_cast; exact pow_ne_zero _ (by norm_num)
      push_cast
      field_simp
      ring
    rw [key, Complex.exp_add, exp_two_pi_int, mul_one]
  rw [Finset.sum_congr rfl hper, ← Finset.mul_sum, Complex.normSq_mul,
      normSq_exp_ofReal_mul_I, one_mul]

/-- **★ (gap 1, headline) The EH circuit's measurement probability EQUALS the analysed `ehProb`. ★**
    Closing the amplitude boundary: combining `ehFiberNormSq_raw` (prefactor + reindex) with
    `ehPhase_normSq` (steps 2–4), the genuine EH circuit Born probability of `(j,k)` equals the
    expression `ehProb` that `EkeraEndToEnd.ehShor_per_run_ge_eighth` lower-bounds by `1/8`. -/
theorem ehCircuitMeasProb_eq_ehProb (ℓ m d j k : ℕ) :
    ehCircuitMeasProb ℓ m d j k = FormalRV.Audit.Gidney2025.EkeraEndToEnd.ehProb ℓ m d j k := by
  unfold ehCircuitMeasProb FormalRV.Audit.Gidney2025.EkeraEndToEnd.ehProb qft2MeasProb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [ehFiberNormSq_raw, ehPhase_normSq]

/-- **★ EH single-run success `≥ 1/8` on the GENUINE circuit Born probability. ★**  Combining
    `ehCircuitMeasProb_eq_ehProb` (circuit = analysed expression) with
    `EkeraEndToEnd.ehShor_per_run_ge_eighth` (the `≥ 1/8` bound on `ehProb`): the probability that one
    run of the verified two-register QFT circuit observes a good pair is `≥ 1/8`. -/
theorem ehCircuit_per_run_ge_eighth (ℓ m d : ℕ) (hℓ : 1 ≤ ℓ) (hm : 2 ≤ m) (hd0 : 0 < d) (hdlt : d < 2 ^ m) :
    (1 / 8 : ℝ) ≤ ∑ j ∈ FormalRV.Audit.Gidney2025.EkeraEndToEnd.goodOutcomes ℓ m d,
        ehCircuitMeasProb ℓ m d j (FormalRV.Audit.Gidney2025.EkeraEndToEnd.kPair ℓ m d j) := by
  rw [Finset.sum_congr rfl (fun j _ => ehCircuitMeasProb_eq_ehProb ℓ m d j
        (FormalRV.Audit.Gidney2025.EkeraEndToEnd.kPair ℓ m d j))]
  exact FormalRV.Audit.Gidney2025.EkeraEndToEnd.ehShor_per_run_ge_eighth ℓ m d hℓ hm hd0 hdlt

/-! ## The EH-circuit results pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean ehCircuitMeasProb_nonneg
#verify_clean ehKernel_combine
#verify_clean ehCircuit_fiberAmp_eq
#verify_clean ehFiberNormSq_raw
#verify_clean ehPhase_normSq
#verify_clean ehCircuitMeasProb_eq_ehProb
#verify_clean ehCircuit_per_run_ge_eighth

/-! ## Gate-level realization (`FormalRV.QFT.TwoRegisterQFT.Circuit`)

The probability `ehCircuitMeasProb`/`qft2MeasProb` analysed above is the Born probability of the
two-register QFT *amplitude model*.  Its concrete **gate circuit** now exists and is verified:

* `FormalRV.QFT.TwoRegisterQFT.twoRegQFT a b : BaseUCom (a+b)` — the actual gate circuit, `IQFT a`
  on the high control register `[0,a)` composed with `IQFT b` on the low register `[a,a+b)`;
* `uc_eval_twoRegQFT_kron` — its unitary semantics: `uc_eval (twoRegQFT a b) * kron_vec ψc ψd =
  kron_vec (IQFT_matrix a * ψc) (IQFT_matrix b * ψd)`, i.e. it acts as `IQFT ⊗ IQFT` (reusing
  `iqft_correct` per register);
* `twoRegQFT_out_apply` — the gate-level tensor law: the joint output amplitude at `(j,k)` factors as
  the product of the two single-register inverse-QFT amplitudes (the circuit counterpart of
  `qft2Amp_factor`);
* `twoRegQFT_wellTyped` — pluggable into the `BaseUCom` / `prob_partial_meas` pipeline.

**Convention.** `twoRegQFT` realizes the verified INVERSE-QFT matrix (`e^{-2πi·xj}`, the measurement
transform QPE/Shor actually apply), whereas the analysed `ehProb`/`qft2Amp` use the forward kernel
`e^{+2πi·xj}`.  Per fibre the EH input amplitudes are uniform-modulus, so the inverse fibre sum is the
complex conjugate of the forward one (`exp_two_pi_int`/`normSq_exp_ofReal_mul_I` above are exactly the
unit-modulus facts), hence **identical `Complex.normSq`** — every Born probability is convention-blind.

**Remaining seam (honest).** Tying the gate circuit's Born probability *literally* to `ehProb` still
needs the 3-register EH circuit model — the controlled oracle producing the entangled target
`|[a−bd]g⟩` and the measurement projection onto a target fibre `e` — so that `twoRegQFT ⊗ I_target`
applied to the post-oracle state yields, per fibre, the inverse-kernel `qft2FiberAmp` whose `normSq`
equals the forward one analysed here.  The QFT half (this circuit, its unitary semantics, and the
per-register/joint amplitude readout) and the probability half (gap 1, `ehCircuitMeasProb_eq_ehProb`)
are both closed; the oracle+projection plumbing is the documented connector. -/

end FormalRV.Audit.Gidney2025.EkeraHastadCircuit
