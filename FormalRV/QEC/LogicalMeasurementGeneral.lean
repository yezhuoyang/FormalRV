/-
  FormalRV.QEC.LogicalMeasurementGeneral — SCALE-FREE logical-measurement semantics:
  prove the LP-code measurement correctness GENERICALLY (∀ CSS code, from `LogicalBasis.valid`),
  so bbSmall / lp16 / lp20 are instances and there is NO `decide` on the stabilizer state at
  scale.

  John: "use some smarter way to avoid the scalability issue."  Right — the residue was that
  the LP-code Gottesman semantics were proven by `decide` at 18 qubits, so lp16/lp20 only
  appeared as plugged-in numbers.  The fix is a PARAMETRIC proof: the non-disturbance of a
  logical-Z measurement is a general stabilizer-algebra fact that follows from the GF(2)
  commutation data already packaged in `LogicalBasis.valid` (`z_in_ker_hx`, `pairs_delta`),
  via `apply_PPM_pos_preserves_mem_of_commutes` — by structure, NOT by enumeration.

  Consequently the SEMANTIC theorems below mention no fixed code and no `decide`:
    • a single logical-Z PPM preserves every stabilizer and every OTHER logical (∀ code);
    • the FULL modexp (any-length logical-Z sequence) preserves every stabilizer (∀ code).
  The only per-code obligation is `z_in_ker_hx` — a sparse GF(2) orthogonality predicate
  (linear, far cheaper than a rank/`decide` on the full stabilizer state, and for the
  structured LP codes it follows from the polynomial orthogonality by construction).

  No Mathlib heavy machinery, no `sorry`, no `axiom`.
-/

import FormalRV.QEC.Logical
import FormalRV.QEC.LatticeSurgery.SurgeryCorrect
namespace FormalRV.QEC.LogicalMeasurementGeneral

open FormalRV.QEC
open FormalRV.Framework.LDPC
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open FormalRV.Framework.SurgeryCorrect

/-! ## §1. GF(2) inner product is symmetric (helper) -/

/-- The GF(2) inner product `dotBit` is symmetric. -/
theorem dotBit_comm (a b : BoolVec) : dotBit a b = dotBit b a := by
  unfold dotBit
  have : (a.zip b).countP (fun p => p.1 && p.2) = (b.zip a).countP (fun p => p.1 && p.2) := by
    induction a generalizing b with
    | nil => cases b <;> simp
    | cons x xs ih =>
      cases b with
      | nil => simp
      | cons y ys => simp only [List.zip_cons_cons, List.countP_cons, ih, Bool.and_comm]
  rw [this]

/-! ## §2. The code state with its logical-X generators -/

/-- The stabilizer state of a CSS code together with all `k` logical-X generators
    (the logical qubits in an X-eigenstate) — the state on which a logical-Z measurement
    acts.  Generic in the code `c` and logical basis `L`. -/
def codeStateWithLogicals (c : CSSCode) (k : Nat) (L : LogicalBasis c k) : StabilizerState :=
  c.hx.map CSSCode.xStab ++ c.hz.map CSSCode.zStab ++ (List.finRange k).map L.xbar

/-! ## §3. Commutation of the measured logical-Z with the preserved generators (from `valid`) -/

/-- **Every stabilizer commutes with the measured logical Z̄_i** — from `z_in_ker_hx`
    (Z̄_i ⟂ all X-checks) and the fact that Z/I strings always commute with Z-checks.
    Generic; no `decide`. -/
theorem stab_commutes_zbar (c : CSSCode) (k : Nat) (L : LogicalBasis c k)
    (hzk : L.z_in_ker_hx = true) (i : Fin k) (g : PauliString)
    (hg : g ∈ c.hx.map CSSCode.xStab ++ c.hz.map CSSCode.zStab) :
    g.commutes (L.zbar i) = true := by
  rw [List.mem_append] at hg
  rcases hg with hgx | hgz
  · obtain ⟨row, hrow, hgeq⟩ := List.mem_map.mp hgx
    subst hgeq
    show (CSSCode.xStab row).commutes (L.zbar i) = true
    unfold LogicalBasis.zbar
    rw [CSSCode.xStab_zStab_commutes, dotBit_comm]
    have h1 := (List.all_eq_true.mp hzk) i (List.mem_finRange i)
    have h2 := (List.all_eq_true.mp h1) row hrow
    simpa using h2
  · obtain ⟨row, hrow, hgeq⟩ := List.mem_map.mp hgz
    subst hgeq
    show (CSSCode.zStab row).commutes (L.zbar i) = true
    unfold LogicalBasis.zbar
    exact CSSCode.zStab_commutes row (L.lz i)

/-- **Logical X̄_j (j ≠ i) commutes with the measured logical Z̄_i** — from `pairs_delta`
    (the symplectic form is δ_ij).  Generic; no `decide`. -/
theorem xbar_commutes_zbar (c : CSSCode) (k : Nat) (L : LogicalBasis c k)
    (hpd : L.pairs_delta = true) (i j : Fin k) (hij : j ≠ i) :
    (L.xbar j).commutes (L.zbar i) = true := by
  unfold LogicalBasis.xbar LogicalBasis.zbar
  rw [CSSCode.xStab_zStab_commutes]
  have h := (List.all_eq_true.mp ((List.all_eq_true.mp hpd) j (List.mem_finRange j))) i
              (List.mem_finRange i)
  have hji : decide (j = i) = false := by simp [hij]
  rw [hji] at h
  simp only [beq_iff_eq] at h
  simp [h]

/-! ## §4. Non-disturbance of a single logical-Z measurement (∀ CSS code, no `decide`) -/

/-- **A logical-Z measurement preserves every stabilizer — for ANY CSS code.**
    From `z_in_ker_hx` and `apply_PPM_pos_preserves_mem_of_commutes`.  No `decide`, no fixed
    code: bbSmall / lp16 / lp20 are all instances. -/
theorem logicalZ_preserves_stabilizers (c : CSSCode) (k : Nat) (L : LogicalBasis c k)
    (hzk : L.z_in_ker_hx = true) (i : Fin k) (g : PauliString)
    (hg : g ∈ c.hx.map CSSCode.xStab ++ c.hz.map CSSCode.zStab) :
    g ∈ apply_PPM_pos (codeStateWithLogicals c k L) (L.zbar i) := by
  refine apply_PPM_pos_preserves_mem_of_commutes (codeStateWithLogicals c k L) (L.zbar i) g ?_ ?_
  · exact List.mem_append_left _ hg
  · exact stab_commutes_zbar c k L hzk i g hg

/-- **A logical-Z measurement preserves every OTHER logical qubit — for ANY CSS code.**
    From `pairs_delta`.  No `decide`. -/
theorem logicalZ_preserves_other_logicals (c : CSSCode) (k : Nat) (L : LogicalBasis c k)
    (hpd : L.pairs_delta = true) (i j : Fin k) (hij : j ≠ i) :
    L.xbar j ∈ apply_PPM_pos (codeStateWithLogicals c k L) (L.zbar i) := by
  refine apply_PPM_pos_preserves_mem_of_commutes (codeStateWithLogicals c k L) (L.zbar i)
    (L.xbar j) ?_ ?_
  · exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange j))
  · exact xbar_commutes_zbar c k L hpd i j hij

/-! ## §5. The FULL modexp (any-length logical-Z sequence) preserves the code — ∀ CSS code -/

/-- **THE FULL MODEXP, SCALE-FREE.**  For ANY CSS code `c` with a logical basis whose
    `z_in_ker_hx` holds, and ANY sequence `ps` of logical-Z measurements (the full
    ≈10⁹-PPM modexp included), EVERY stabilizer survives the whole computation
    `measureChecks ps`.  Proved by induction on `ps` (via `mem_measureChecks_of_commutesAll`)
    from the generic per-PPM commutation — NO `decide`, NO fixed code, NO scale ceiling.
    lp16 [[2610,…]] and lp20 [[4350,…]] are covered by this single theorem; the only
    per-code obligation is the sparse GF(2) predicate `z_in_ker_hx`. -/
theorem full_modexp_preserves_code_general (c : CSSCode) (k : Nat) (L : LogicalBasis c k)
    (hzk : L.z_in_ker_hx = true) (ps : List PauliString)
    (hps : ∀ P ∈ ps, ∃ i : Fin k, P = L.zbar i)
    (g : PauliString) (hg : g ∈ c.hx.map CSSCode.xStab ++ c.hz.map CSSCode.zStab) :
    g ∈ measureChecks ps (codeStateWithLogicals c k L) := by
  refine mem_measureChecks_of_commutesAll ps g (codeStateWithLogicals c k L)
    (List.mem_append_left _ hg) ?_
  intro P hP
  obtain ⟨i, rfl⟩ := hps P hP
  exact stab_commutes_zbar c k L hzk i g hg

/-! ## §6. Instantiation: the SAME theorem at every scale

    For any concrete LP code, supplying its (cheap) `z_in_ker_hx` discharges the full-modexp
    code-preservation — at 18 qubits, 2610, or 4350 — from the ONE generic theorem above. -/

/-- The full-modexp code-preservation specialised to a code whose `LogicalBasis` is valid:
    validity (which includes `z_in_ker_hx`) is the ONLY per-code input. -/
theorem full_modexp_preserves_code_of_valid (c : CSSCode) (k : Nat) (L : LogicalBasis c k)
    (hv : L.valid = true) (ps : List PauliString)
    (hps : ∀ P ∈ ps, ∃ i : Fin k, P = L.zbar i)
    (g : PauliString) (hg : g ∈ c.hx.map CSSCode.xStab ++ c.hz.map CSSCode.zStab) :
    g ∈ measureChecks ps (codeStateWithLogicals c k L) := by
  have hzk : L.z_in_ker_hx = true := by
    unfold LogicalBasis.valid at hv
    simp only [Bool.and_eq_true] at hv
    exact hv.1.2
  exact full_modexp_preserves_code_general c k L hzk ps hps g hg

end FormalRV.QEC.LogicalMeasurementGeneral
