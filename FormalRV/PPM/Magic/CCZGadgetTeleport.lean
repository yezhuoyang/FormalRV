/-
  FormalRV.PPM.Magic.CCZGadgetTeleport — measurement-based gate teleportation
  for the CCZ gate, all-zeros (b=000) measurement branch, proved correct on
  state vectors. The 3-qubit analogue of MagicStateTeleport's
  `t_teleport_outcome_0` (the no-correction T branch).

  ## The protocol (one branch)

  To apply CCZ to a 3-qubit data register |ψ⟩ using one |CCZ⟩ = CCZ·|+++⟩
  magic state:
    1. prepare |ψ⟩ ⊗ |CCZ⟩  (3 data ⊗ 3 ancilla = 6 qubits, 64-dim space);
    2. apply the transversal CNOT chain (data qubit k controls ancilla k);
    3. measure all three ancillas in the Z basis;
       * outcome 000 ⇒ the data register is CCZ·|ψ⟩ (no correction) — PROVED HERE;
       * outcomes 001..111 ⇒ outcome-dependent CZ/Pauli correction — NOT formalised here.

  ## Honesty boundary  (see `honest_gaps`)

  * State-vector correctness of the 000 branch only; the 1/(2√2) factor is the
    Born amplitude (unnormalised post-measurement state), not a probability.
  * |CCZ⟩ is SUPPLIED (factory output); distillation correctness is out of scope.
    But `cczKet` is defined concretely (= cczMat·|+++⟩), NOT axiomatised, and is
    tied to the repo's 8T→CCZ `cczMat` by `cczKet_eq_cczMat_plus3` below.
  * The other 7 outcomes need a `czMatrix` primitive that the repo lacks
    (CZ exists only as a circuit `BaseUCom`).

  The single import `FormalRV.PPM.Magic.MagicStateTeleport` transitively provides
  `StateVec`, `kron_vec` (⊗ᵥ), `basisState`, `kron_vec_apply/high/low` (Core,
  via `NDSem`) and `cczMat` (`FormalRV.Framework.EightTToCCZ`).
-/
import FormalRV.PPM.Magic.MagicStateTeleport

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.EightTToCCZ
open Complex

namespace FormalRV.PPM.Magic.CCZGadgetTeleport

-- §1. Ingredients.  6-qubit register = 3 data (high 3 bits, i/8) ⊗ 3 ancilla
-- (low 3 bits, i%8), matching kron_vec's high=first-factor convention
-- (ψ ⊗ᵥ cczKet ⇒ ψ is the high register).

/-- The genuine |CCZ⟩ magic state = CCZ·|+++⟩ = (1/2√2)·∑_d (-1)^[d=7] |d⟩:
    uniform 1/(2√2) amplitude on every basis state except |111⟩ (index 7),
    which carries -1/(2√2). The only supplied (factory) object. -/
noncomputable def cczKet : StateVec 3 :=
  fun i _ => if i = 7 then (-1 / (2 * Real.sqrt 2) : ℂ) else (1 / (2 * Real.sqrt 2) : ℂ)

/-- The CCZ unitary action read entrywise on a 3-qubit data state:
    phase -1 on the |111⟩ component (index 7). -/
noncomputable def CCZdata (ψ : StateVec 3) : StateVec 3 :=
  fun i j => if i = 7 then -(ψ i j) else ψ i j

/-- The transversal 3-CNOT chain (data qubit k controls ancilla qubit k) as an
    index permutation: data*8 + anc ↦ data*8 + (anc XOR data). Encoded as a
    permutation matrix; avoids any 64×64 array literal. -/
def cnotChainPerm (n : Nat) : Nat := (n / 8) * 8 + ((n % 8) ^^^ (n / 8))

noncomputable def cnotChain : Matrix (Fin 64) (Fin 64) ℂ :=
  fun i j => if i.val = cnotChainPerm j.val then 1 else 0

/-- Z-measurement projector onto ancilla outcome |000⟩ (low 3 bits = 0). -/
noncomputable def projAnc000 : Matrix (Fin 64) (Fin 64) ℂ :=
  Matrix.diagonal (fun i => if i.val % 8 = 0 then 1 else 0)

/-- |+++⟩ on 3 qubits = uniform 1/(2√2). -/
noncomputable def plus3 : StateVec 3 := fun _ _ => (1 / (2 * Real.sqrt 2) : ℂ)

/-- The data action spelled as the repo's `cczMat` matrix-vector product. -/
noncomputable def cczMatData (ψ : StateVec 3) : StateVec 3 := cczMat * ψ

-- §2. Permutation helpers (all proved, no sorry).

theorem cnotChainPerm_lt (n : Nat) (h : n < 64) : cnotChainPerm n < 64 := by
  unfold cnotChainPerm
  have hx : (n % 8) ^^^ (n / 8) < 2^3 := Nat.xor_lt_two_pow (n := 3) (by omega) (by omega)
  omega

theorem cnotChainPerm_invol (n : Nat) (h : n < 64) :
    cnotChainPerm (cnotChainPerm n) = n := by
  have key : ∀ m : Fin 64, cnotChainPerm (cnotChainPerm m.val) = m.val := by decide
  exact key ⟨n, h⟩

/-- KEY LEMMA: the CNOT chain acts on a column vector by the index permutation,
    so `(cnotChain * v) i = v (perm i)`. This is what avoids a 64-term brute
    force (the fin_cases-on-Fin-64 / 4096-goal heartbeat timeout). -/
theorem cnotChain_mul_apply (v : Matrix (Fin 64) (Fin 1) ℂ) (i : Fin 64) (j : Fin 1) :
    (cnotChain * v) i j = v ⟨cnotChainPerm i.val, cnotChainPerm_lt i.val i.isLt⟩ j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single ⟨cnotChainPerm i.val, cnotChainPerm_lt i.val i.isLt⟩]
  · have hII : i.val = cnotChainPerm (cnotChainPerm i.val) :=
      (cnotChainPerm_invol i.val i.isLt).symm
    simp only [cnotChain]; rw [if_pos hII, one_mul]
  · intro k _ hk
    simp only [cnotChain]; rw [if_neg, zero_mul]
    intro hcontra; apply hk; apply Fin.ext
    have : cnotChainPerm i.val = cnotChainPerm (cnotChainPerm k.val) := by rw [hcontra]
    rw [cnotChainPerm_invol k.val k.isLt] at this; exact this.symm
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

-- §3. NON-VACUITY bridges (both proved): the magic state is genuinely
-- cczMat·|+++⟩, and the claimed output is genuinely the cczMat unitary action,
-- tied to the repo's 8T→CCZ `cczMat`.  These are the surface Design A omitted.

theorem cczKet_eq_cczMat_plus3 : cczMat * plus3 = cczKet := by
  funext i j
  rw [cczMat, Matrix.diagonal_mul]
  simp only [cczKet, plus3]
  split
  · simp_all; ring
  · simp_all

theorem CCZdata_eq_cczMat_mul (ψ : StateVec 3) : CCZdata ψ = cczMat * ψ := by
  funext i j
  rw [cczMat, Matrix.diagonal_mul]
  simp only [CCZdata]
  split <;> simp_all

-- §4. HEADLINE amplitude theorem (all-zeros / b=000 branch), proved no sorry.
--
-- After the transversal CNOT chain and projecting all three ancillas onto |0⟩,
-- the three data qubits carry CCZ·ψ (= CCZdata ψ), with the 1/(2√2) Born
-- amplitude, and the ancilla register left in |000⟩.  No Clifford correction
-- needed on THIS branch.  Proved for ARBITRARY input ψ via the permutation-
-- collapse lemma (NO fin_cases on Fin 64).
theorem ccz_teleport_outcome_000 (ψ : StateVec 3) :
    projAnc000 * (cnotChain * (ψ ⊗ᵥ cczKet))
      = (1 / (2 * Real.sqrt 2) : ℂ) • (CCZdata ψ ⊗ᵥ (basisState 0 : StateVec 3)) := by
  funext i j
  simp only [projAnc000, Matrix.diagonal_mul]
  rw [cnotChain_mul_apply]
  simp only [kron_vec_apply, Matrix.smul_apply, smul_eq_mul, kron_vec_high, kron_vec_low,
    basisState, CCZdata, cczKet]
  have hpd : cnotChainPerm i.val / 8 = i.val / 8 := by
    unfold cnotChainPerm
    have hx : (i.val % 8) ^^^ (i.val / 8) < 2^3 :=
      Nat.xor_lt_two_pow (n := 3) (by omega) (by omega)
    omega
  simp only [show (2:Nat)^3 = 8 from rfl, hpd, Fin.ext_iff, Fin.val_zero,
    show ((7 : Fin 8)).val = 7 from rfl]
  by_cases hi : i.val % 8 = 0
  · have hp8 : cnotChainPerm i.val % 8 = i.val / 8 := by
      unfold cnotChainPerm; rw [hi, Nat.zero_xor]; omega
    rw [if_pos hi, hp8]
    by_cases hd : i.val / 8 = 7
    · simp only [hd, if_true]; ring
    · simp only [if_neg hd]; ring
  · rw [if_neg hi]; simp

-- §5. HEADLINE restated with the genuine repo `cczMat` unitary, plus an
-- existential form. These make the non-vacuity explicit: the data register
-- provably receives `cczMat·ψ` (not an ad-hoc vector, not a compile:=cczMat
-- shortcut — the cczMat phase EMERGES from the CNOT+projection algebra).
theorem ccz_gadget_outcome_000_is_cczMat (ψ : StateVec 3) :
    projAnc000 * (cnotChain * (ψ ⊗ᵥ cczKet))
      = (1 / (2 * Real.sqrt 2) : ℂ) • (cczMatData ψ ⊗ᵥ (basisState 0 : StateVec 3)) := by
  rw [ccz_teleport_outcome_000]; congr 2; rw [CCZdata_eq_cczMat_mul]; rfl

theorem ccz_gadget_data_is_CCZ (ψ : StateVec 3) :
    ∃ c : ℂ, projAnc000 * (cnotChain * (ψ ⊗ᵥ cczKet))
      = c • (cczMatData ψ ⊗ᵥ (basisState 0 : StateVec 3)) :=
  ⟨(1 / (2 * Real.sqrt 2) : ℂ), ccz_gadget_outcome_000_is_cczMat ψ⟩

end FormalRV.PPM.Magic.CCZGadgetTeleport