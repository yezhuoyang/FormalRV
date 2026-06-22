/-
  FormalRV.Resource.UComCombinators
  ─────────────────────────────────
  Resource-count laws for the CORE `BaseUCom` circuit combinators: the derived
  gates (`CCX`, `controlled_R`) and the generic builders (`control`, `npar`,
  `npar_H`).  These are the compositional laws that let a gadget's count theorem
  reduce a structured circuit to the counts of its parts — e.g. QPE's count
  decomposes over a BLACK-BOX oracle family via `control`/`npar`.

  Same discipline as the rest of `Resource/`: the counters (`UComCount.lean`)
  never change; this file only PROVES what they return on the core combinators.
  Everything here is forced by the syntax tree — `SKIP` is honestly one `app1`
  gate (`ID 0 = R(0,0,0)` on qubit 0), `SWAP` is honestly 3 CNOTs, `CCX` is
  honestly its 15-gate decomposition.

  Imports: the IR-level counters + `Core.UnitaryOps` (where `control`/`npar`
  live).  Still NO gadget constructors, NO correctness proofs.
-/
import FormalRV.Resource.UComCount
import FormalRV.Core.UnitaryOps

namespace FormalRV.Resource

open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ## §1. Atoms and small derived gates. -/

@[simp] theorem oneQCountU_SKIP {dim : Nat} : oneQCountU (SKIP : BaseUCom dim) = 1 := rfl
@[simp] theorem cnotCountU_SKIP {dim : Nat} : cnotCountU (SKIP : BaseUCom dim) = 0 := rfl
@[simp] theorem widthU_SKIP {dim : Nat} : widthU (SKIP : BaseUCom dim) = 1 := rfl

/-- Width of `SWAP` (3 CNOTs): it touches exactly its two qubits. -/
theorem widthU_SWAP {dim : Nat} (m n : Nat) :
    widthU (SWAP m n : BaseUCom dim) = max (m + 1) (n + 1) := by
  simp only [SWAP, CNOT, widthU]
  omega

/-- `CCX` is honestly its 15-gate Clifford+T decomposition: 9 one-qubit gates. -/
@[simp] theorem oneQCountU_CCX {dim : Nat} (a b c : Nat) :
    oneQCountU (CCX a b c : BaseUCom dim) = 9 := rfl

/-- … and 6 CNOTs. -/
@[simp] theorem cnotCountU_CCX {dim : Nat} (a b c : Nat) :
    cnotCountU (CCX a b c : BaseUCom dim) = 6 := rfl

/-- `controlled_R` (the ABXBXC controlled-rotation) is 4 one-qubit gates… -/
@[simp] theorem oneQCountU_controlled_R {dim : Nat} (q t : Nat) (θ φ lam : ℝ) :
    oneQCountU (controlled_R q t θ φ lam : BaseUCom dim) = 4 := rfl

/-- … and 2 CNOTs. -/
@[simp] theorem cnotCountU_controlled_R {dim : Nat} (q t : Nat) (θ φ lam : ℝ) :
    cnotCountU (controlled_R q t θ φ lam : BaseUCom dim) = 2 := rfl

/-- Width of `controlled_R`: it touches exactly the control and the target. -/
theorem widthU_controlled_R {dim : Nat} (q t : Nat) (θ φ lam : ℝ) :
    widthU (controlled_R q t θ φ lam : BaseUCom dim) = max (q + 1) (t + 1) := by
  simp only [controlled_R, Rz, CNOT, widthU]
  omega

/-- Width of `CCX`: it touches exactly its three qubits. -/
theorem widthU_CCX {dim : Nat} (a b c : Nat) :
    widthU (CCX a b c : BaseUCom dim) = max (a + 1) (max (b + 1) (c + 1)) := by
  simp only [CCX, H, T, TDAG, CNOT, widthU]
  omega

/-! ## §2. `control` — the counts of a controlled circuit.

`control q c` replaces every 1-qubit gate by a `controlled_R` (4 one-qubit,
2 CNOT) and every CNOT by a `CCX` (9 one-qubit, 6 CNOT), so its counts are an
EXACT linear function of `c`'s counts.  (`app3` is vacuous: `BaseUnitary 3` is
empty.) -/

/-- One-qubit-gate count of a controlled circuit:
`4·(one-qubit gates of c) + 9·(CNOTs of c)`. -/
theorem oneQCountU_control {dim : Nat} (q : Nat) (c : BaseUCom dim) :
    oneQCountU (control q c) = 4 * oneQCountU c + 9 * cnotCountU c := by
  induction c with
  | seq a b iha ihb =>
      simp only [control_seq, oneQCountU_seq, cnotCountU_seq, iha, ihb]; ring
  | app1 u t => cases u with | R θ φ lam => rfl
  | app2 u m n => cases u with | CNOT => rfl
  | app3 u _ _ _ => cases u

/-- CNOT count of a controlled circuit:
`2·(one-qubit gates of c) + 6·(CNOTs of c)`. -/
theorem cnotCountU_control {dim : Nat} (q : Nat) (c : BaseUCom dim) :
    cnotCountU (control q c) = 2 * oneQCountU c + 6 * cnotCountU c := by
  induction c with
  | seq a b iha ihb =>
      simp only [control_seq, oneQCountU_seq, cnotCountU_seq, cnotCountU_seq, iha, ihb]; ring
  | app1 u t => cases u with | R θ φ lam => rfl
  | app2 u m n => cases u with | CNOT => rfl
  | app3 u _ _ _ => cases u

/-- Width of a controlled circuit: the control qubit joins the footprint. -/
theorem widthU_control {dim : Nat} (q : Nat) (c : BaseUCom dim) :
    widthU (control q c) = max (q + 1) (widthU c) := by
  induction c with
  | seq a b iha ihb =>
      simp only [control_seq, widthU, iha, ihb]; omega
  | app1 u t =>
      cases u with
      | R θ φ lam =>
          show widthU (controlled_R q t θ φ lam : BaseUCom dim) = max (q + 1) (t + 1)
          exact widthU_controlled_R q t θ φ lam
  | app2 u m n =>
      cases u with
      | CNOT =>
          show widthU (CCX q m n : BaseUCom dim) = max (q + 1) (max (m + 1) (n + 1))
          exact widthU_CCX q m n
  | app3 u _ _ _ => cases u

/-! ## §3. `npar` — sums over a parallel family. -/

/-- One-qubit-gate count of `npar n g`: the sum over the family, plus 1 for the
terminal `SKIP` (honestly an `app1` in the tree). -/
theorem oneQCountU_npar {dim : Nat} (n : Nat) (g : Nat → BaseUCom dim) :
    oneQCountU (npar n g) = (∑ i ∈ Finset.range n, oneQCountU (g i)) + 1 := by
  induction n with
  | zero => simp [npar]
  | succ k ih =>
      rw [npar_succ, oneQCountU_seq, ih, Finset.sum_range_succ]; ring

/-- CNOT count of `npar n g`: the sum over the family (the `SKIP` is CNOT-free). -/
theorem cnotCountU_npar {dim : Nat} (n : Nat) (g : Nat → BaseUCom dim) :
    cnotCountU (npar n g) = ∑ i ∈ Finset.range n, cnotCountU (g i) := by
  induction n with
  | zero => simp [npar]
  | succ k ih =>
      rw [npar_succ, cnotCountU_seq, ih, Finset.sum_range_succ]

/-- The Hadamard layer `npar_H k` has exactly `k + 1` one-qubit gates
(`k` Hadamards + the terminal `SKIP`)… -/
theorem oneQCountU_npar_H {dim : Nat} (k : Nat) :
    oneQCountU (npar_H k : BaseUCom dim) = k + 1 := by
  rw [npar_H, oneQCountU_npar]
  simp [H, oneQCountU]

/-- … and zero CNOTs. -/
theorem cnotCountU_npar_H {dim : Nat} (k : Nat) :
    cnotCountU (npar_H k : BaseUCom dim) = 0 := by
  rw [npar_H, cnotCountU_npar]
  simp [H, cnotCountU]

/-- Width of the Hadamard layer: exactly `k` qubits (for `k ≥ 1`). -/
theorem widthU_npar_H {dim : Nat} (k : Nat) (hk : 0 < k) :
    widthU (npar_H k : BaseUCom dim) = k := by
  induction k with
  | zero => omega
  | succ m ih =>
      rw [npar_H, npar_succ, ← npar_H]
      by_cases hm : 0 < m
      · simp only [widthU, ih hm, H]
        omega
      · have : m = 0 := by omega
        subst this
        simp [npar_H, npar, widthU, H, SKIP, ID]

end FormalRV.Resource
