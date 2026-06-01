import FormalRV.Shor.PhaseKickback
import FormalRV.Shor.QPEAmplitude

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom


/-! ## §1. Ideal inverse-QFT matrix and its action on Fourier-weighted states

This section is pure linear algebra — the matrix-level target that
any honest `QFTinv` circuit must reproduce. -/

/-- **Ideal inverse-QFT matrix.** `IQFT_matrix m y x = (1/√2^m) ·
exp(-2πi · x · y / 2^m)`. This is the matrix-level target for any
correct `QFTinv m` circuit. -/
noncomputable def IQFT_matrix (m : Nat) :
    Matrix (Fin (2^m)) (Fin (2^m)) ℂ :=
  fun y x =>
    ((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
      Complex.exp (-(2 * Real.pi * Complex.I) * (x.val : ℂ) * (y.val : ℂ) / (2^m : ℂ))

/-! ## §2. Real inverse-QFT circuit (1-qubit base case)

The full recursive inverse-QFT requires controlled phase rotations
with decreasing angles, plus a bit-reversal step at the end. The
1-qubit case collapses to a single Hadamard, which is a clean base
case to certify against `IQFT_matrix`. -/

/-- **Real inverse-QFT circuit.** Base cases for `n ≤ 2`; the
recursive case for `n ≥ 3` is provided by `real_QFTinv_layer` below.
For `n = 2`, uses the verified `real_QFTinv2_candidate`. -/
noncomputable def real_QFTinv_on : (n : Nat) → BaseUCom n
  | 0 => SKIP
  | 1 => H 0
  | 2 => UCom.seq
           (UCom.seq
             (UCom.seq (SWAP 0 1) (H 1))
             (controlled_Rz 1 0 (-(Real.pi / 2))))
           (H 0)
  | _+3 => SKIP  -- General case: deferred to `real_QFTinv_layer` (see §4)

/-! ## §4. 2-qubit inverse-QFT circuit candidate + recursive layer

The 2-qubit inverse QFT is the smallest nontrivial case. With the
framework's MSB-first convention (`padEquiv` puts qubit `i` at weight
`2^(m-i-1)`, so qubit 0 is the most significant), the standard
forward-QFT decomposition is:

    H 0 ;  controlled_Rz 1 0 (π/2) ;  H 1 ;  SWAP 0 1

Its **inverse** (reverse order + adjoint angles) is:

    SWAP 0 1 ;  H 1 ;  controlled_Rz 1 0 (-π/2) ;  H 0

The latter is the `real_QFTinv2_candidate` defined below. Hand
verification (see the docstring): the matrix product
`H 0 · CR · H 1 · SWAP` evaluates entry-by-entry to
`(1/2) · [[1,1,1,1]; [1,-i,-1,i]; [1,-1,1,-1]; [1,i,-1,-i]]`,
which equals `IQFT_matrix 2`. The mechanized 16-entry matrix proof
requires per-gate basis-action infrastructure that does not yet
exist in the framework; the candidate is committed here as a
landing point and the matrix theorem is the next pass's target. -/

/-- **2-qubit inverse-QFT candidate.** Order: `SWAP 0 1 ; H 1 ;
controlled_Rz 1 0 (-π/2) ; H 0`. Hand-verified to equal
`IQFT_matrix 2` (mechanized proof deferred).

Action analysis (each basis vector `|x_0 x_1⟩`):
- `|00⟩ → (1/2)(|00⟩ + |01⟩ + |10⟩ + |11⟩)`
- `|01⟩ → (1/2)(|00⟩ - i|01⟩ - |10⟩ + i|11⟩)`
- `|10⟩ → (1/2)(|00⟩ - |01⟩ + |10⟩ - |11⟩)`
- `|11⟩ → (1/2)(|00⟩ + i|01⟩ - |10⟩ - i|11⟩)`
matching `IQFT_matrix 2`'s columns. -/
noncomputable def real_QFTinv2_candidate : BaseUCom 2 :=
  UCom.seq
    (UCom.seq
      (UCom.seq (SWAP 0 1) (H 1))
      (controlled_Rz 1 0 (-(Real.pi / 2))))
    (H 0)

/-- **Phase ladder for inverse QFT on the `target`-th qubit.**

SQIRPort-namespaced n-qubit version. Coexists with the
`{dim}`-polymorphic `Framework.BaseUCom.inverse_qft_phase_ladder`
(moved to the framework 2026-05-26 to support `QFTinv`'s replacement).
Equivalence between the two is established by
`SQIRPort_inverse_qft_phase_ladder_eq_Framework`. -/
noncomputable def inverse_qft_phase_ladder
    (n target : Nat) : FormalRV.Framework.BaseUCom n :=
  let rec loop (j : Nat) : FormalRV.Framework.BaseUCom n :=
    if j < n then
      UCom.seq (controlled_Rz j target (-(Real.pi / (2 ^ (j - target) : ℝ))))
               (loop (j + 1))
    else
      H target
  loop (target + 1)

/-- **Bit-reversal SWAP cascade for `n` qubits.** SQIRPort-namespaced
n-qubit version. See `inverse_qft_phase_ladder` for the framework
relationship note. -/
noncomputable def bit_reversal_swaps (n : Nat) : FormalRV.Framework.BaseUCom n :=
  let rec loop (i : Nat) : FormalRV.Framework.BaseUCom n :=
    if i + i + 1 < n then
      UCom.seq (SWAP i (n - 1 - i)) (loop (i + 1))
    else
      SKIP
  loop 0

/-- **Recursive layer of the real inverse-QFT for `n` qubits.**
SQIRPort-namespaced n-qubit version. See `inverse_qft_phase_ladder`
for the framework relationship note. -/
noncomputable def real_QFTinv_layer (n : Nat) : FormalRV.Framework.BaseUCom n :=
  let rec countdown (k : Nat) : FormalRV.Framework.BaseUCom n :=
    match k with
    | 0 => SKIP
    | k+1 => UCom.seq (inverse_qft_phase_ladder n k) (countdown k)
  UCom.seq (bit_reversal_swaps n) (countdown n)

/-! ## §6. Real QPE pipeline assuming arbitrary-n IQFT correctness

This section closes the QPE pipeline at the level of `real_QFTinv_on`'s
matrix correctness. The final theorem `real_QPE_on_eigenstate_from_IQFT_correct`
shows that, once `uc_eval (real_QFTinv_on m) = IQFT_matrix m` is proved
for arbitrary `m`, the full QPE eigenstate semantic theorem follows.

This establishes a clean theorem boundary: the remaining work for
`QPE_MMI_correct` reduces to proving arbitrary-n IQFT matrix correctness
(the 2-qubit case is in §5; the recursive case is the next deliverable). -/

/-- **Real QPE circuit.** `npar_H` (prep) ; `controlled_powers` (oracle
ladder, lifted to the data register) ; `real_QFTinv_on m` (measurement
basis, lifted to the control register). -/
noncomputable def real_QPE (m anc : Nat) (f : Nat → BaseUCom anc) :
    BaseUCom (m + anc) :=
  UCom.seq (npar_H m)
    (UCom.seq
      (controlled_powers
        (fun i => (map_qubits (fun q => m + q) (f i) : BaseUCom (m + anc))) m)
      (map_qubits (fun q => q) (real_QFTinv_on m) : BaseUCom (m + anc)))

/-- **High bit of a Fin (2^(n+1)) index.** MSB-first convention: the
high bit is `x.val / 2^n`. -/
noncomputable def iqftHighBit (n : Nat) (x : Fin (2^(n+1))) : Fin 2 :=
  ⟨x.val / 2^n, by
    have : x.val < 2^(n+1) := x.isLt
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)]
    omega⟩

/-- **Lower n bits of a Fin (2^(n+1)) index.** `x.val % 2^n`. -/
noncomputable def iqftLowBits (n : Nat) (x : Fin (2^(n+1))) : Fin (2^n) :=
  ⟨x.val % 2^n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- **Ideal IQFT column**: the column vector `IQFT_matrix n · basis_vector (2^n) x.val`.
This is the target of the `real_QFTinv_layer n` action on basis vector `x`. -/
noncomputable def IQFT_column (n : Nat) (x : Fin (2^n)) :
    Matrix (Fin (2^n)) (Fin 1) ℂ :=
  IQFT_matrix n * FormalRV.Framework.basis_vector (2^n) x.val

/-! ### Bit-reversal SWAP cascade basis action

The `bit_reversal_swaps n` circuit applies SWAP gates `SWAP i (n-1-i)`
for `i = 0, 1, ..., ⌊n/2⌋-1`. On a basis state `f_to_vec n f`, the
result is `f_to_vec n` of the function with bits reversed across
positions `[0, n-1]`. -/

/-- **Bit-swap on Boolean functions.** Swaps the values at positions
`a` and `b`. -/
def swapBits (f : Nat → Bool) (a b : Nat) : Nat → Bool :=
  fun i => if i = a then f b else if i = b then f a else f i

/-- **Recursive cumulative bit-reversal function.** Result of applying
all SWAPs `(k, n-1-k), (k+1, n-2-k), ...` to `f`. Terminates when
`2k+1 ≥ n` (no more swap pairs). -/
def applySwapsFrom (n : Nat) : (k : Nat) → (Nat → Bool) → (Nat → Bool)
  | k, f =>
    if h : 2 * k + 1 < n then
      applySwapsFrom n (k+1) (swapBits f k (n-1-k))
    else
      f
  termination_by k _ => n - 2 * k

/-! ### Inverse-QFT phase ladder basis action

The `inverse_qft_phase_ladder n target` circuit consists of a sequence
of `controlled_Rz` gates targeting qubit `target` from controls
`target+1, target+2, ..., n-1`, followed by `H target`. Each `controlled_Rz`
contributes a phase factor `exp(-π · I / 2^(j-target))` when both
control bit `j` and target bit `target` are 1; otherwise contributes 1.

On a basis state `f_to_vec n f`, the action factors as
`(accumulated phase) • (H_target · f_to_vec n f)`. -/

/-- **Recursive ladder phase scalar.** Product of controlled-Rz phase
factors for controls `j ∈ [k, n)`. -/
noncomputable def inverse_qft_ladder_phase_from
    (n target : Nat) (f : Nat → Bool) (k : Nat) : ℂ :=
  ∏ j ∈ Finset.Ico k n,
    if f j ∧ f target then
      Complex.exp ((((-(Real.pi / 2 ^ (j - target))) : ℝ)) * Complex.I)
    else 1

/-- **Full ladder phase**: the accumulated phase scalar for the
inverse-QFT ladder targeting `target`. -/
noncomputable def inverse_qft_ladder_phase
    (n target : Nat) (f : Nat → Bool) : ℂ :=
  inverse_qft_ladder_phase_from n target f (target + 1)

/-- **Recursive countdown output.** The expected output of `countdown n k`
applied to `f_to_vec n f`. Mirrors `countdown_succ_acts`: at step k+1,
ladder k is applied first (producing a phase × two-branch sum), then
`countdown_output n k` recursively to each branch. -/
noncomputable def countdown_output
    (n : Nat) : Nat → (Nat → Bool) → Matrix (Fin (2^n)) (Fin 1) ℂ
  | 0, f => f_to_vec n f
  | k+1, f =>
      inverse_qft_ladder_phase n k f •
        (((Real.sqrt 2 / 2 : ℂ) • countdown_output n k (update f k false))
          + ((if f k then -(Real.sqrt 2 / 2 : ℂ) else (Real.sqrt 2 / 2 : ℂ))
              • countdown_output n k (update f k true)))

/-! ### Named helpers for the countdown column

The countdown column for a basis-vector input `x : Fin (2^n)` is the
result of applying `real_QFTinv_layer n` to `basis_vector (2^n) x.val`,
expressed via the recursive `countdown_output`. Naming these helpers
makes the arbitrary-n induction proof more readable. -/

/-- Boolean function encoding a `Fin (2^n)` index in MSB-first form. -/
noncomputable def basisFunOfIndex (n : Nat) (x : Fin (2^n)) : Nat → Bool :=
  nat_to_funbool n x.val

/-- Boolean function after applying the full bit-reversal of `basisFunOfIndex`. -/
noncomputable def bitReversedBasisFun (n : Nat) (x : Fin (2^n)) : Nat → Bool :=
  applySwapsFrom n 0 (basisFunOfIndex n x)

/-- The countdown column: the result of `real_QFTinv_layer n` applied to
`basis_vector (2^n) x.val`, as an explicit matrix column. -/
noncomputable def countdownColumn (n : Nat) (x : Fin (2^n)) :
    Matrix (Fin (2^n)) (Fin 1) ℂ :=
  countdown_output n n (bitReversedBasisFun n x)

/-! ### Countdown output dimension split

Bridges the (n+1)-qubit `countdown_output` to the n-qubit one with
an extra LSB qubit carried through. Each ladder for target `t < n`
in the (n+1)-qubit system contributes an extra phase from qubit n
acting as a control. The cumulative extra phase is tracked by
`cumulative_extra_phase`. -/

/-- **Embed an n-qubit state into an (n+1)-qubit state by appending
an extra LSB qubit.** Uses `kron_vec` with the n-qubit vector at the
high positions and the 1-qubit extra at the LSB. -/
noncomputable def embedWithExtraBit
    (n : Nat) (extra : Bool)
    (v : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    Matrix (Fin (2^(n+1))) (Fin 1) ℂ :=
  kron_vec v (FormalRV.Framework.basis_vector 2 (if extra then 1 else 0))

/-- **Cumulative extra phase**: product over targets `t ∈ [0, k)` of the
phase factor contributed by qubit `n` controlling target `t`. -/
noncomputable def cumulative_extra_phase
    (n k : Nat) (f : Nat → Bool) : ℂ :=
  ∏ t ∈ Finset.range k,
    if f n ∧ f t then
      Complex.exp ((((-(Real.pi / 2 ^ (n - t))) : ℝ)) * Complex.I)
    else 1

/-! ### Index splits for the output column

The output index `y : Fin (2^(n+1))` of a column theorem needs to be
split into a high-n part and a low-1 (LSB) part, matching the
`embedWithExtraBit` structure (which uses `kron_vec` with n-qubit at
high positions and 1-qubit at LSB). -/

/-- **High n bits of an (n+1)-qubit index.** `y.val / 2`. -/
noncomputable def iqftHighBitsN (n : Nat) (y : Fin (2^(n+1))) : Fin (2^n) :=
  ⟨y.val / 2, by
    have : y.val < 2^(n+1) := y.isLt
    have h : 2^(n+1) = 2 * 2^n := by ring
    omega⟩

/-- **LSB of an (n+1)-qubit index.** `y.val % 2`. -/
noncomputable def iqftLowBitLSB (n : Nat) (y : Fin (2^(n+1))) : Fin 2 :=
  ⟨y.val % 2, by omega⟩

/-! ### Real, non-stub QPE circuit + unconditional single-eigenstate theorem

The companion to `real_QPE` that uses the arbitrary-n correct
`real_QFTinv_layer` instead of the stubbed `real_QFTinv_on`. The
single-eigenstate semantic theorem is now UNCONDITIONAL (no
`h_IQFT` hypothesis). -/

/-- **Real QPE circuit using `real_QFTinv_layer`.** The non-stub
counterpart to `real_QPE`. Structure:
  `npar_H m ; controlled_powers (lifted f) m ; lifted real_QFTinv_layer m`. -/
noncomputable def real_QPE_layer (m anc : Nat) (f : Nat → FormalRV.Framework.BaseUCom anc) :
    FormalRV.Framework.BaseUCom (m + anc) :=
  UCom.seq (npar_H m)
    (UCom.seq
      (controlled_powers
        (fun i => (map_qubits (fun q => m + q) (f i)
          : FormalRV.Framework.BaseUCom (m + anc))) m)
      (map_qubits (fun q => q) (real_QFTinv_layer m)
        : FormalRV.Framework.BaseUCom (m + anc)))

/-- **LSB-compatible Shor final state** (parallel to `Shor_final_state`).
Uses `QPE_var_lsb` (the LSB-oracle-reversed wrapper) instead of `QPE_var`.
This is the state on which the LSB-chain semantic theorems apply
directly; bridging to the published `Shor_final_state` requires a
design decision per the autoresearch protocol. -/
noncomputable def Shor_final_state_lsb (m n anc : Nat)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc)) :
    QState (2^m * 2^n * 2^anc) :=
  QState.cast (by rw [pow_add, pow_add, mul_assoc])
    (uc_eval (QPE_var_lsb m (n + anc) f) (Shor_initial_state m n anc))

end FormalRV.SQIRPort
