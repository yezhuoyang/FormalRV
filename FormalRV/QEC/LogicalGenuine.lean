/-
  FormalRV.QEC.LogicalGenuine — a VALID logical basis is GENUINE (its operators are real
  logical operators, not stabilizers), proven PARAMETRICALLY with NO rank / NO `decide` at
  scale — using only the GF(2)-linearity cornerstone.

  This dissolves the "homological-dimension wall" for COMPILATION CORRECTNESS.  The
  strengthened verifier (`ShorLPContract`) demands the logical qubits be genuine; the obvious
  route was `k = n − rank H_X − rank H_Z` (a rank at 4350 columns, forbidden by the no-native
  acceptance).  But genuineness does NOT need the rank: if a basis is `valid`
  (`x_in_ker_hz ∧ z_in_ker_hx ∧ pairs_delta`), the symplectic δ-pairing ALONE forces each
  logical to lie OUTSIDE the stabilizer rowspace — proven here via `dotBit_row_combination`
  (orthogonality to a set of rows propagates to their whole GF(2) span, by linearity).

  Consequence: a `valid` basis of `k` operators is `k` genuine, independent logical qubits,
  with NO claim about (and no computation of) the total logical dimension.  A correct
  compilation runs on exactly those `k` qubits.

  No Mathlib heavy machinery, no `sorry`, no `axiom`.
-/

import FormalRV.QEC.GF2Linearity
import FormalRV.QEC.LogicalMeasurementGeneral
import FormalRV.LatticeSurgery.SurgeryReadout

namespace FormalRV.QEC.LogicalGenuine

open FormalRV.Framework.LDPC
open FormalRV.QEC
open FormalRV.QEC.LogicalMeasurementGeneral
open FormalRV.Framework.SurgeryReadout

/-! ## §1. Orthogonality propagates to the GF(2) span (from linearity) -/

/-- **A vector orthogonal to every row of a matrix is orthogonal to every GF(2) combination
    of those rows** (the rowspace).  By induction on the selection, using the linearity
    cornerstone `dotBit_vec_xor`.  No `decide` at scale. -/
theorem dotBit_row_combination (n : Nat) (sel : BoolVec) (mat : BoolMat) (v : BoolVec)
    (hn : v.length = n) (hmat : ∀ r ∈ mat, r.length = n)
    (hrows : ∀ r ∈ mat, dotBit r v = false) :
    dotBit (row_combination sel mat) v = false := by
  induction sel generalizing mat with
  | nil => simp [row_combination, dotBit_nil_left]
  | cons s ts ih =>
    cases mat with
    | nil => simp [row_combination, dotBit_nil_left]
    | cons row tm =>
      have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
      have hdtm : ∀ r ∈ tm, dotBit r v = false := fun r hr => hrows r (List.mem_cons_of_mem _ hr)
      have hrow0 : dotBit row v = false := hrows row List.mem_cons_self
      have hrowlen : row.length = n := hmat row List.mem_cons_self
      cases s with
      | false => simp only [row_combination]; exact ih tm htm hdtm
      | true =>
          simp only [row_combination]
          cases hrc : row_combination ts tm with
          | nil => exact hrow0
          | cons aa as =>
              have hacc_len : (row_combination ts tm).length = n :=
                (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
              rw [hrc] at hacc_len
              have hih : dotBit (row_combination ts tm) v = false := ih tm htm hdtm
              rw [hrc] at hih
              rw [dotBit_vec_xor row (aa :: as) v (by rw [hrowlen, ← hacc_len]) (by rw [hrowlen, hn]),
                  hrow0, hih]
              rfl

/-! ## §2. Genuineness of a valid logical basis (NO rank) -/

/-- **No Z-logical of a valid basis is a Z-stabilizer.**  If `L.lz j` were a GF(2)
    combination of Z-checks, then (by `dotBit_row_combination` and `x_in_ker_hz`) it would be
    orthogonal to `L.lx j`, contradicting the symplectic `pairs_delta` (`dotBit(X̄ⱼ,Z̄ⱼ)=1`).
    Parametric; no rank, no `decide` at scale. -/
theorem valid_logical_not_Zstabilizer (c : CSSCode) (k : Nat) (L : LogicalBasis c k)
    (hv : L.valid = true) (hlx : ∀ i : Fin k, (L.lx i).length = c.n)
    (hhz : ∀ r ∈ c.hz, r.length = c.n) (j : Fin k) (w : BoolVec) :
    L.lz j ≠ row_combination w c.hz := by
  unfold LogicalBasis.valid at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨hxk, _hzk⟩, hpd⟩ := hv
  have hdelta : dotBit (L.lx j) (L.lz j) = true := by
    have := (List.all_eq_true.mp ((List.all_eq_true.mp hpd) j (List.mem_finRange j))) j
              (List.mem_finRange j)
    simpa using this
  have hxrow : ∀ r ∈ c.hz, dotBit r (L.lx j) = false := by
    intro r hr
    have := (List.all_eq_true.mp ((List.all_eq_true.mp hxk) j (List.mem_finRange j))) r hr
    have h0 : dotBit (L.lx j) r = false := by simpa using this
    rw [dotBit_comm]; exact h0
  intro heq
  have hcontra : dotBit (L.lx j) (L.lz j) = false := by
    rw [heq, dotBit_comm]
    exact dotBit_row_combination c.n w c.hz (L.lx j) (hlx j) hhz hxrow
  rw [hcontra] at hdelta; exact absurd hdelta (by decide)

/-- **No X-logical of a valid basis is an X-stabilizer** (the exact dual, via `z_in_ker_hx`). -/
theorem valid_logical_not_Xstabilizer (c : CSSCode) (k : Nat) (L : LogicalBasis c k)
    (hv : L.valid = true) (hlz : ∀ i : Fin k, (L.lz i).length = c.n)
    (hhx : ∀ r ∈ c.hx, r.length = c.n) (j : Fin k) (w : BoolVec) :
    L.lx j ≠ row_combination w c.hx := by
  unfold LogicalBasis.valid at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨_hxk, hzk⟩, hpd⟩ := hv
  have hdelta : dotBit (L.lx j) (L.lz j) = true := by
    have := (List.all_eq_true.mp ((List.all_eq_true.mp hpd) j (List.mem_finRange j))) j
              (List.mem_finRange j)
    simpa using this
  have hzrow : ∀ r ∈ c.hx, dotBit r (L.lz j) = false := by
    intro r hr
    have := (List.all_eq_true.mp ((List.all_eq_true.mp hzk) j (List.mem_finRange j))) r hr
    have h0 : dotBit (L.lz j) r = false := by simpa using this
    rw [dotBit_comm]; exact h0
  intro heq
  have hcontra : dotBit (L.lx j) (L.lz j) = false := by
    rw [heq]
    exact dotBit_row_combination c.n w c.hx (L.lz j) (hlz j) hhx hzrow
  rw [hcontra] at hdelta; exact absurd hdelta (by decide)

/-! ## §3. Headline: valid ⇒ genuine, with no rank -/

/-- **A valid logical basis is GENUINE — parametrically, with no rank computation.**  Every
    logical operator is neither a stabilizer of its own type (Z̄ⱼ not a Z-stabilizer, X̄ⱼ not
    an X-stabilizer): they are real elements of N(S)\S.  So a `valid` basis of `k` operators
    certifies `k` genuine logical qubits WITHOUT computing `n − rank − rank` — the route that
    makes lp16/lp20 logical-qubit genuineness reachable without `native_decide`. -/
theorem valid_basis_genuine (c : CSSCode) (k : Nat) (L : LogicalBasis c k) (hv : L.valid = true)
    (hlx : ∀ i : Fin k, (L.lx i).length = c.n) (hlz : ∀ i : Fin k, (L.lz i).length = c.n)
    (hhx : ∀ r ∈ c.hx, r.length = c.n) (hhz : ∀ r ∈ c.hz, r.length = c.n) :
    (∀ (j : Fin k) (w : BoolVec), L.lz j ≠ row_combination w c.hz)
    ∧ (∀ (j : Fin k) (w : BoolVec), L.lx j ≠ row_combination w c.hx) :=
  ⟨fun j w => valid_logical_not_Zstabilizer c k L hv hlx hhz j w,
   fun j w => valid_logical_not_Xstabilizer c k L hv hlz hhx j w⟩

end FormalRV.QEC.LogicalGenuine
