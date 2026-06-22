/-
  FormalRV.PauliRotation.Correctness.ShorEndToEnd
  ───────────────────────────────────
  THE COMPOSITION: all the proven gadget rows assemble into an end-to-end
  semantic statement for the Pauli-rotation compilation of the Shor/QPE
  circuit shape

      H-layer ; modexp oracle ; banded inverse QFT

  Every block reduces to its CLOSED operator form:
    • the H-layer to a product of generalized Hadamards (`hLayer_denote`,
      from `hGate_denote`),
    • the IQFT ladder to a product of Hadamards and controlled-S†
      diagonals (`ladderLow_denote`, from `csDag_rots_denote`),
    • the bit-reversal cascade to CX permutation products
      (`swapRots_denote`/`bitRev_denote`, from `cnot_rots_applyNat`),
    • the Gate-IR modexp oracle to its own Boolean semantics
      (`gateRots_denote_applyNat`),
  and `shorQPE_rots_denote` multiplies them out with ONE explicit global
  phase — composed end-to-end semantics for the whole compiled algorithm,
  with `shorQPE_schedule_denote` extending it through the verified
  parallelizer and `shor15_schedule_denote` instantiating it at the
  verified Shor-15 modexp oracle.

  HONEST SCOPE: the oracle enters as the QPE black box on the same wire
  pool (the repo's own QPE design — the controlled-powers wiring is the
  QPE-side contract); relating the closed operator form to
  `IQFT_matrix`/`uc_eval` is the BaseUCom bridge (unstarted); the banding ε
  is the existing derived budget in `QFT/AQFTCompile`.
-/
import FormalRV.PauliRotation.Correctness.Assembly
import FormalRV.PauliRotation.Correctness.QFTRows
import FormalRV.PauliRotation.Gadgets

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. The H-layer block. -/

/-- The UNNORMALIZED Hadamard at wire `q` (`Z_q + X_q`); the `√2/2` and the
`−i` live in the phases, keeping every block matrix scalar-free. -/
noncomputable def hadSum (n q : Nat) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  axisMat n [⟨q, .z⟩] + axisMat n [⟨q, .x⟩]

/-- The H-layer product `(Z+X)_{k−1} ⋯ (Z+X)_0`. -/
noncomputable def hLayerMat (n : Nat) : Nat → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => 1
  | k + 1 => hadSum n k * hLayerMat n k

theorem hLayer_denote (n : Nat) :
    ∀ k, k ≤ n →
      seqDenote n (hLayerRots k)
        = ((-Complex.I) * (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ)) ^ k
            • hLayerMat n k := by
  intro k
  induction k with
  | zero =>
      intro _
      show (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) = _
      rw [pow_zero, one_smul]
      rfl
  | succ k ih =>
      intro hk
      have hsplit : hLayerRots (k + 1) = hLayerRots k ++ (hGate k).flatten := by
        show (List.range (k + 1)).flatMap (fun q => (hGate q).flatten) = _
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons,
            List.flatMap_nil, List.append_nil]
        rfl
      rw [hsplit, seqDenote_append, hGate_denote n k (by omega), ih (by omega)]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1

/-! ## §2. The IQFT ladder block. -/

/-- The ladder product for targets `t−1 … 0`: each target contributes a
Hadamard then (reading right-to-left) its kept controlled-S† diagonal. -/
noncomputable def ladderMat (n : Nat) : Nat → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => 1
  | t + 1 => ladderMat n t * hadSum n t * csDagMat n t

theorem ladderLow_denote (n : Nat) :
    ∀ t, t < n →
      seqDenote n (aqftLadderLow t)
        = ((-Complex.I) * (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ)
            * phaseC (Real.pi / 8)) ^ t • ladderMat n t := by
  intro t
  induction t with
  | zero =>
      intro _
      show (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) = _
      rw [pow_zero, one_smul]
      rfl
  | succ t ih =>
      intro ht
      show seqDenote n (csDagRots t ++ ((hGate t).flatten ++ aqftLadderLow t)) = _
      rw [seqDenote_append, seqDenote_append, csDag_rots_denote n t (by omega),
          hGate_denote n t (by omega), ih (by omega)]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ring

/-! ## §3. The bit-reversal block. -/

/-- One SWAP, semantically: three CX permutations with phase `e^{i3π/4}`. -/
theorem swapRots_denote (n i j : Nat) (hij : i ≠ j) (hi : i < n) (hj : j < n) :
    seqDenote n (swapRots i j)
      = phaseC (Real.pi / 4) ^ 3
          • (applyMat n (.CX i j) * applyMat n (.CX j i)
              * applyMat n (.CX i j)) := by
  show seqDenote n ((cnotGate i j).flatten
      ++ ((cnotGate j i).flatten ++ (cnotGate i j).flatten)) = _
  rw [seqDenote_append, seqDenote_append]
  rw [show seqDenote n (cnotGate i j).flatten
        = phaseC (Real.pi / 4) • applyMat n (.CX i j) from
      cnot_rots_applyNat n i j hij hi hj,
      show seqDenote n (cnotGate j i).flatten
        = phaseC (Real.pi / 4) • applyMat n (.CX j i) from
      cnot_rots_applyNat n j i (fun h => hij h.symm) hj hi]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

/-- The bit-reversal product over the first `m` pairs of width `k`. -/
noncomputable def bitRevMat (n k : Nat) : Nat → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => 1
  | i + 1 => (applyMat n (.CX i (k - 1 - i)) * applyMat n (.CX (k - 1 - i) i)
      * applyMat n (.CX i (k - 1 - i))) * bitRevMat n k i

theorem bitRev_denote (n k : Nat) (hk : k ≤ n) :
    seqDenote n (bitRevRots k)
      = (phaseC (Real.pi / 4) ^ 3) ^ (k / 2) • bitRevMat n k (k / 2) := by
  suffices h : ∀ m, m ≤ k / 2 →
      seqDenote n ((List.range m).flatMap fun i => swapRots i (k - 1 - i))
        = (phaseC (Real.pi / 4) ^ 3) ^ m • bitRevMat n k m from
    h (k / 2) (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
      intro _
      show (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) = _
      rw [pow_zero, one_smul]
      rfl
  | succ m ih =>
      intro hm
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, seqDenote_append,
          swapRots_denote n m (k - 1 - m) (by omega) (by omega) (by omega),
          ih (by omega)]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1

/-! ## §4. The banded IQFT, assembled. -/

/-- The closed operator form of the banded inverse QFT on `k+1` wires. -/
noncomputable def iqftMat (n k : Nat) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  ladderMat n k * hadSum n k * bitRevMat n (k + 1) ((k + 1) / 2)

/-- The banded IQFT's global phase. -/
noncomputable def iqftPhase (k : Nat) : ℂ :=
  ((-Complex.I) * (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ) * phaseC (Real.pi / 8)) ^ k
    * ((-Complex.I) * (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ))
    * (phaseC (Real.pi / 4) ^ 3) ^ ((k + 1) / 2)

/-- **The banded IQFT block, semantically.** -/
theorem aqft2_denote (n k : Nat) (hk : k + 1 ≤ n) :
    seqDenote n (aqft2Rots (k + 1)) = iqftPhase k • iqftMat n k := by
  show seqDenote n (bitRevRots (k + 1)
      ++ ((hGate k).flatten ++ aqftLadderLow k)) = _
  rw [seqDenote_append, seqDenote_append, ladderLow_denote n k (by omega),
      hGate_denote n k (by omega), bitRev_denote n (k + 1) (by omega)]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  unfold iqftPhase
  ring

/-! ## §5. THE COMPOSED SHOR/QPE STATEMENT. -/

/-- **END-TO-END SEMANTICS OF THE COMPILED SHOR/QPE CIRCUIT SHAPE**: the
full rotation sequence — H-layer, then any Gate-IR modular-exponentiation
oracle, then the banded inverse QFT — denotes the product of the three
blocks' closed operator forms, with ONE explicit global phase. -/
theorem shorQPE_rots_denote (n k : Nat) (oracleG : FormalRV.Framework.Gate)
    (hops : opsOK oracleG = true) (hw : FormalRV.Resource.width oracleG ≤ n)
    (hk : k + 1 ≤ n) :
    seqDenote n (qpeRots (k + 1) (gateRots oracleG))
      = (iqftPhase k * gphase oracleG
            * ((-Complex.I) * (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ)) ^ (k + 1))
          • (iqftMat n k * applyMat n oracleG * hLayerMat n (k + 1)) := by
  show seqDenote n (hLayerRots (k + 1)
      ++ (gateRots oracleG ++ aqft2Rots (k + 1))) = _
  rw [seqDenote_append, seqDenote_append, aqft2_denote n k hk,
      gateRots_denote_applyNat n oracleG hops hw, hLayer_denote n (k + 1) hk]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

/-- **…and through the verified parallelizer**: the SCHEDULED program means
the same thing (side condition decidable per instance). -/
theorem shorQPE_schedule_denote (n k : Nat) (oracleG : FormalRV.Framework.Gate)
    (hops : opsOK oracleG = true) (hw : FormalRV.Resource.width oracleG ≤ n)
    (hk : k + 1 ≤ n)
    (hb : ∀ r ∈ qpeRots (k + 1) (gateRots oracleG),
        sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ n) :
    RotProg.denote n (qpeSchedule (k + 1) (gateRots oracleG))
      = (iqftPhase k * gphase oracleG
            * ((-Complex.I) * (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ)) ^ (k + 1))
          • (iqftMat n k * applyMat n oracleG * hLayerMat n (k + 1)) := by
  show RotProg.denote n (scheduleList (qpeRots (k + 1) (gateRots oracleG))) = _
  rw [scheduleList_denote n _ hb, shorQPE_rots_denote n k oracleG hops hw hk]

/-! ## §6. The Shor-15 instance (verified modexp oracle, 3 phase qubits). -/

open FormalRV.BQAlgo in
set_option maxRecDepth 10000 in
/-- **Shor-15, compiled and parallelized, end to end**: with the verified
in-place modexp oracle at `(N, a, ainv) = (15, 7, 13)` and three phase
qubits, the scheduled Pauli-rotation program of the whole QPE circuit
denotes the composed closed form — all side conditions kernel-checked. -/
theorem shor15_schedule_denote :
    RotProg.denote 7 (qpeSchedule 3 (gateRots (shorModExpVerified 1 15 7 13)))
      = (iqftPhase 2 * gphase (shorModExpVerified 1 15 7 13)
            * ((-Complex.I) * (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ)) ^ 3)
          • (iqftMat 7 2 * applyMat 7 (shorModExpVerified 1 15 7 13)
              * hLayerMat 7 3) :=
  shorQPE_schedule_denote 7 2 _ (by decide) (by decide) (by omega) (by decide)

end FormalRV.PauliRotation
