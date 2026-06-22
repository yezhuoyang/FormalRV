/-
  FormalRV.Shor.CFS.ResidueFold — the |P|-register CFS residue fold: a single CONCRETE `Gate` running
  |P| base-disjoint residue circuits (one per prime), with the residue-VECTOR semantics and the
  closed-form resource, both proven through the construction (no extra hypotheses beyond the genuine
  per-prime multiplier invertibility the in-place uncompute requires).

  Construction (all concrete):
    * `residueWidth`         — the qubit width of one residue register;
    * `residueFold`          — `foldl seq (residueGateAt (j·width) … (P j) …)` over `range numP`;
    * `globalInput`          — the integer→bits encoding: |P| copies of the clean `y=1` input, one per
                               register block (`mulInputOf … 1` indexed by the within-block position).

  Disjointness is proven, not assumed: `residueGateAt b` fixes qubits `< b` (`shiftGate_frame`) and
  `≥ b+width` (`residueGateAt_frame_above`, via the base gate's `WellTyped` + `applyNat_oob`).
-/
import FormalRV.Shor.CFS.ResidueGateAt
import FormalRV.Shor.CFS.ResidueUnitary

namespace FormalRV.CFS

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Arithmetic (shiftGate applyNat_shiftGate applyNat_shiftGate_at tcount_shiftGate
  shiftGate_frame applyNat_congr_lt)

/-- The qubit width of one residue register (the dim bound of the windowed in-place multiplier). -/
def residueWidth (w bits numWin : Nat) : Nat := 1 + 2 * w + (2 * bits + 1) + numWin * w + 1

/-- **Right frame.**  The residue gate at base `b` fixes every qubit at or above `b + width`
    (its register occupies exactly `[b, b+width)`), via the base gate's well-typedness + `applyNat_oob`. -/
theorem residueGateAt_frame_above (b w bits numWin pj : Nat) (cs cinvs : Nat → Nat) (m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (f : Nat → Bool) (q : Nat)
    (hq : b + residueWidth w bits numWin ≤ q) :
    Gate.applyNat (residueGateAt b w bits numWin pj cs cinvs m) f q = f q := by
  unfold residueGateAt
  rw [applyNat_shiftGate b _ f q, if_pos (by omega : b ≤ q),
      Gate.applyNat_oob
        (windowedModNMulInPlaceSeq_wellTyped w bits pj numWin cs cinvs m
          (residueWidth w bits numWin) hw hbits (le_refl _))
        (fun j => f (j + b)) (show residueWidth w bits numWin ≤ q - b by
          unfold residueWidth at hq ⊢; omega)]
  show f (q - b + b) = f q
  rw [Nat.sub_add_cancel (by omega)]

/-- The |P|-register residue fold: `numP` base-disjoint residue circuits in sequence, register `j` at
    base `j·width` running the residue multiplier mod the `j`-th prime `P j`. -/
def residueFold (P : Nat → Nat) (ainvss : Nat → Nat → Nat)
    (numP w bits numWin g N e m : Nat) : Gate :=
  (List.range numP).foldl
    (fun gg j =>
      Gate.seq gg
        (residueGateAt (j * residueWidth w bits numWin) w bits numWin (P j)
          (residueConst g N (P j) e) (ainvss j) m))
    Gate.I

/-- **The fold fixes everything at or above its top.**  After `numP` residue registers (each of width
    `width`, placed at bases `0, width, 2·width, …`), every qubit `≥ numP·width` is untouched — the
    induction backbone for register-block disjointness. -/
theorem residueFold_fixes_above (P : Nat → Nat) (ainvss : Nat → Nat → Nat)
    (w bits numWin g N e m : Nat) (hw : 0 < w) (hbits : numWin * w = bits) :
    ∀ (numP : Nat) (f : Nat → Bool) (q : Nat),
      numP * residueWidth w bits numWin ≤ q →
      Gate.applyNat (residueFold P ainvss numP w bits numWin g N e m) f q = f q := by
  intro numP
  induction numP with
  | zero => intro f q _; rfl
  | succ k ih =>
      intro f q hq
      have hstep : residueFold P ainvss (k + 1) w bits numWin g N e m
          = Gate.seq (residueFold P ainvss k w bits numWin g N e m)
              (residueGateAt (k * residueWidth w bits numWin) w bits numWin (P k)
                (residueConst g N (P k) e) (ainvss k) m) := by
        rw [residueFold, residueFold, List.range_succ, List.foldl_append]; rfl
      rw [hstep, Gate.applyNat_seq,
          residueGateAt_frame_above (k * residueWidth w bits numWin) w bits numWin (P k)
            (residueConst g N (P k) e) (ainvss k) m hw hbits _ q
            (by have : (k + 1) * residueWidth w bits numWin ≤ q := hq; nlinarith [Nat.add_mul k 1 (residueWidth w bits numWin)]),
          ih f q (by nlinarith [Nat.add_mul k 1 (residueWidth w bits numWin)])]

/-- **Resource (exact).**  The fold's Toffoli count is `numP` times the per-register count
    `m·numWin·(16·w·2^w + 16·bits)` — counted on the actual `Gate`, base- and prime-independent. -/
theorem residueFold_toffoli (P : Nat → Nat) (ainvss : Nat → Nat → Nat)
    (numP w bits numWin g N e m : Nat) :
    toffoliCount (residueFold P ainvss numP w bits numWin g N e m)
      = numP * (m * numWin * (16 * w * 2 ^ w + 16 * bits)) := by
  have hC : ∀ j, tcount (residueGateAt (j * residueWidth w bits numWin) w bits numWin (P j)
      (residueConst g N (P j) e) (ainvss j) m) = m * (2 * (numWin * (56 * w * 2 ^ w + 56 * bits))) := by
    intro j
    unfold residueGateAt
    rw [tcount_shiftGate, tcount_windowedModNMulInPlaceSeq]
  rw [toffoliCount, residueFold,
      tcount_foldl_seq_const _ (m * (2 * (numWin * (56 * w * 2 ^ w + 56 * bits)))) hC,
      show tcount Gate.I = 0 from rfl, Nat.zero_add, List.length_range,
      show numP * (m * (2 * (numWin * (56 * w * 2 ^ w + 56 * bits))))
          = numP * (m * numWin * (16 * w * 2 ^ w + 16 * bits)) * 7 from by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **LOCAL value.**  The residue gate at base `b` computes the residue from an input that matches the
    clean encoding only WITHIN its own register block `[b, b+width)` — the surrounding qubits may hold
    other registers' data.  Bridges `residueGate_verified` (clean global input) through the qubit-shift
    transport and the `applyNat_congr_lt` input-locality. -/
theorem residueGateAt_value_local (b w bits numWin pj g N e m : Nat) (ainvs : Nat → Nat)
    (F : Nat → Bool) (hw : 0 < w) (hbits : numWin * w = bits) (hpj1 : 1 < pj) (hpj2 : 2 * pj ≤ 2 ^ bits)
    (hinv : ∀ k, k < m → ainvs k < pj ∧ residueConst g N pj e k * ainvs k % pj = 1)
    (hFloc : ∀ p, p < residueWidth w bits numWin →
      F (p + b) = mulInputOf cuccaroAdder w bits numWin 1 p) :
    decodeReg (fun i => b + (1 + 2 * w + (2 * bits + 1) + i)) bits
        (Gate.applyNat (residueGateAt b w bits numWin pj (residueConst g N pj e) ainvs m) F)
      = modexpProd g N m e % pj := by
  set G := windowedModNMulInPlaceSeq w bits pj numWin (residueConst g N pj e) ainvs m with hG
  have hkey : ∀ i, Gate.applyNat (shiftGate b G) F (b + (1 + 2 * w + (2 * bits + 1) + i))
      = Gate.applyNat G (fun j => F (j + b)) (1 + 2 * w + (2 * bits + 1) + i) := by
    intro i
    rw [Nat.add_comm b (1 + 2 * w + (2 * bits + 1) + i)]
    exact applyNat_shiftGate_at b G F (1 + 2 * w + (2 * bits + 1) + i)
  unfold residueGateAt
  rw [← hG, decodeReg_congr (fun i => b + (1 + 2 * w + (2 * bits + 1) + i))
        (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits
        (Gate.applyNat (shiftGate b G) F) (Gate.applyNat G (fun j => F (j + b)))
        (fun i _ => hkey i)]
  have hwt := windowedModNMulInPlaceSeq_wellTyped w bits pj numWin (residueConst g N pj e) ainvs m
    (residueWidth w bits numWin) hw hbits (le_refl _)
  have hcongr := applyNat_congr_lt (residueWidth w bits numWin) G hwt
    (fun j => F (j + b)) (mulInputOf cuccaroAdder w bits numWin 1) (fun p hp => hFloc p hp)
  rw [decodeReg_ext (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits
        (Gate.applyNat G (fun j => F (j + b)))
        (Gate.applyNat G (mulInputOf cuccaroAdder w bits numWin 1))
        (fun i hi => hcongr (1 + 2 * w + (2 * bits + 1) + i) (by unfold residueWidth; omega))]
  exact (residueGate_verified w bits numWin pj g N e m ainvs hw hbits hpj1 hpj2 hinv).1

/-- The integer→bits global input: `|P|` copies of the clean `y=1` encoding, one per register block
    (block `j` at `[j·width, (j+1)·width)` holds `mulInputOf … 1` indexed by the within-block position). -/
def globalInput (w bits numWin : Nat) : Nat → Bool :=
  fun i => mulInputOf cuccaroAdder w bits numWin 1 (i % residueWidth w bits numWin)

/-- **THE |P|-REGISTER RESIDUE FOLD — SEMANTIC (the residue vector).**  Running the concrete fold
    `residueFold` on the concrete `globalInput`, EACH register `j` (`j < numP`) leaves the CFS residue
    `modexpProd g N m e mod (P j)` in its accumulator — the full residue vector reconstruction feeds.
    Proven by induction on `numP` (runway template): the new register's block is untouched by the
    prefix (`residueFold_fixes_above`) so it sees `globalInput`; lower registers are untouched by the
    new gate (`shiftGate_frame`).  The only hypothesis is the genuine per-prime input contract: each
    `P j` is a valid residue prime (`1 < P j`, `2·P j ≤ 2^bits`) with an invertible multiplier table. -/
theorem residueFold_correct (P : Nat → Nat) (ainvss : Nat → Nat → Nat)
    (w bits numWin g N e m : Nat) (hw : 0 < w) (hbits : numWin * w = bits) :
    ∀ (numP : Nat),
      (∀ j, j < numP → 1 < P j ∧ 2 * P j ≤ 2 ^ bits ∧
        ∀ k, k < m → ainvss j k < P j ∧ residueConst g N (P j) e k * ainvss j k % (P j) = 1) →
      ∀ j, j < numP →
        decodeReg (fun i => j * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
            (Gate.applyNat (residueFold P ainvss numP w bits numWin g N e m)
              (globalInput w bits numWin))
          = modexpProd g N m e % (P j) := by
  intro numP
  induction numP with
  | zero => intro _ j hj; omega
  | succ k ih =>
      intro hP j hj
      have hW : 0 < residueWidth w bits numWin := by unfold residueWidth; omega
      have hstep : residueFold P ainvss (k + 1) w bits numWin g N e m
          = Gate.seq (residueFold P ainvss k w bits numWin g N e m)
              (residueGateAt (k * residueWidth w bits numWin) w bits numWin (P k)
                (residueConst g N (P k) e) (ainvss k) m) := by
        rw [residueFold, residueFold, List.range_succ, List.foldl_append]; rfl
      rw [hstep, Gate.applyNat_seq]
      rcases Nat.lt_or_ge j k with hjk | hjk
      · -- j < k: the new register (at base k·width) is above block j and fixes it.
        rw [decodeReg_ext _ bits _
              (Gate.applyNat (residueFold P ainvss k w bits numWin g N e m) (globalInput w bits numWin))
              (fun i hi => by
                apply shiftGate_frame
                calc j * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)
                    < j * residueWidth w bits numWin + residueWidth w bits numWin := by
                      have : 1 + 2 * w + (2 * bits + 1) + i < residueWidth w bits numWin := by
                        unfold residueWidth; omega
                      omega
                  _ = (j + 1) * residueWidth w bits numWin := by ring
                  _ ≤ k * residueWidth w bits numWin := Nat.mul_le_mul (by omega) (le_refl _))]
        exact ih (fun j' hj' => hP j' (by omega)) j hjk
      · -- j = k: the new register sees globalInput on its own (untouched) block.
        have hjeq : j = k := by omega
        subst hjeq
        obtain ⟨hpj1, hpj2, hinvk⟩ := hP j (by omega)
        exact residueGateAt_value_local (j * residueWidth w bits numWin) w bits numWin (P j) g N e m
          (ainvss j) (Gate.applyNat (residueFold P ainvss j w bits numWin g N e m)
            (globalInput w bits numWin)) hw hbits hpj1 hpj2 hinvk
          (fun p hp => by
            rw [residueFold_fixes_above P ainvss w bits numWin g N e m hw hbits j
                  (globalInput w bits numWin) (p + j * residueWidth w bits numWin)
                  (by omega)]
            show globalInput w bits numWin (p + j * residueWidth w bits numWin)
                = mulInputOf cuccaroAdder w bits numWin 1 p
            unfold globalInput
            rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp])

end FormalRV.CFS
