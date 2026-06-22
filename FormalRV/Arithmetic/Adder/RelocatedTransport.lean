/-
  FormalRV.Arithmetic.Adder.RelocatedTransport
  ─────────────────────────────────────────────
  The RELOCATED contiguous two-base adder: a `TwoBaseBoundedAdder` whose accumulator
  block `[accBase, accBase+n)` and addend block `[addBase, addBase+n)` are at
  INDEPENDENT bases, with carry at `addBase + n` (John's convention), built by a
  GAP-PARAMETERIZED de-interleave relabel of the verified Cuccaro adder.

  This GENERALIZES `contiguousPackedAdder` (the gap-0 / `addBase = accBase+n` case)
  to any `addBase ≥ accBase + n`.  Motivation (see `Shor/GidneyInPlace/Adder/Def/ProductAddLayout`):
  the faithful Gidney two-register product-add needs, in pass 2 (`a -= b·kInv`,
  accumulator `a`), the addend block at `accBase + 2·bits` (register `b` sits in
  between), which the packed adder cannot host.

  The relabel `relocate accBase addBase n`:
    carry-in `accBase`           ↦ `addBase + n`        (the global carry)
    augend bit i (`accBase+2i+1`) ↦ `accBase + i`        (contiguous accumulator)
    addend bit i (`accBase+2i+2`) ↦ `addBase + i`        (relocated addend)
    fill `[accBase+2n+1, addBase+n]` ↦ gap `[accBase+n, addBase)`  (bijective filler)
  It is a genuine permutation of `[accBase, addBase+n]` (identity outside), proven
  injective by a division-free left inverse — the same method as `deinterleave`.

  SCOPE: this is layout/adder transport only.  It does NOT build the product-add
  wrapper and proves NO product-add arithmetic.
-/
import FormalRV.Arithmetic.Adder.ContiguousTransport

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## §1. The gap-parameterized de-interleave `relocate` and its inverse. -/

/-- Relocating de-interleave: Cuccaro(base `accBase`) → accumulator at `accBase+i`,
    addend at `addBase+i`, carry at `addBase+n`, gap positions filled bijectively.
    Valid as a permutation when `accBase + n ≤ addBase`. -/
def relocate (accBase addBase n : Nat) : Nat → Nat := fun p =>
  if p < accBase then p
  else if p = accBase then addBase + n
  else if p < accBase + 2 * n + 1 then
    (if (p - accBase) % 2 = 1 then accBase + (p - accBase) / 2
     else addBase + ((p - accBase) / 2 - 1))
  else if p ≤ addBase + n then p - n - 1
  else p

/-- Division-free left inverse of `relocate`. -/
def relocateInv (accBase addBase n : Nat) : Nat → Nat := fun r =>
  if r < accBase then r
  else if r = addBase + n then accBase
  else if r < accBase + n then accBase + 2 * (r - accBase) + 1
  else if r < addBase then r + n + 1
  else if r < addBase + n then accBase + 2 * (r - addBase) + 2
  else r

@[simp] theorem relocate_carry (accBase addBase n : Nat) :
    relocate accBase addBase n accBase = addBase + n := by
  unfold relocate; simp

theorem relocate_augend (accBase addBase n i : Nat) (hi : i < n) :
    relocate accBase addBase n (accBase + 2 * i + 1) = accBase + i := by
  unfold relocate
  have h1 : ¬ (accBase + 2 * i + 1 < accBase) := by omega
  have h2 : ¬ (accBase + 2 * i + 1 = accBase) := by omega
  have h3 : accBase + 2 * i + 1 < accBase + 2 * n + 1 := by omega
  have h4 : (accBase + 2 * i + 1 - accBase) % 2 = 1 := by omega
  rw [if_neg h1, if_neg h2, if_pos h3, if_pos h4]; omega

theorem relocate_addend (accBase addBase n i : Nat) (hi : i < n) :
    relocate accBase addBase n (accBase + 2 * i + 2) = addBase + i := by
  unfold relocate
  have h1 : ¬ (accBase + 2 * i + 2 < accBase) := by omega
  have h2 : ¬ (accBase + 2 * i + 2 = accBase) := by omega
  have h3 : accBase + 2 * i + 2 < accBase + 2 * n + 1 := by omega
  have h4 : ¬ ((accBase + 2 * i + 2 - accBase) % 2 = 1) := by omega
  rw [if_neg h1, if_neg h2, if_pos h3, if_neg h4]; omega

/-- Outside the bounding interval `[accBase, addBase+n]`, `relocate` is the identity
    (needs validity so that `p > addBase+n` cannot fall in the de-interleave range). -/
theorem relocate_outside (accBase addBase n p : Nat) (hv : accBase + n ≤ addBase)
    (h : p < accBase ∨ addBase + n < p) :
    relocate accBase addBase n p = p := by
  rcases h with h | h <;> · unfold relocate; split_ifs <;> omega

/-- `relocateInv` is a left inverse of `relocate` (so `relocate` is injective), under
    the validity precondition `accBase + n ≤ addBase`. -/
theorem relocateInv_leftInverse (accBase addBase n : Nat) (hv : accBase + n ≤ addBase) :
    Function.LeftInverse (relocateInv accBase addBase n) (relocate accBase addBase n) := by
  intro p
  unfold relocate relocateInv
  split_ifs <;> omega

theorem relocate_injective (accBase addBase n : Nat) (hv : accBase + n ≤ addBase) :
    Function.Injective (relocate accBase addBase n) :=
  (relocateInv_leftInverse accBase addBase n hv).injective

/-- `relocate` maps the block `[0, addBase+n+1)` into itself (for well-typedness). -/
theorem relocate_maps_lt (accBase addBase n x : Nat)
    (hx : x < addBase + n + 1) : relocate accBase addBase n x < addBase + n + 1 := by
  unfold relocate; split_ifs <;> omega

/-! ## §2. The relocated circuit and its transported obligations. -/

/-- The relocated contiguous adder circuit: the verified Cuccaro adder at base
    `accBase`, relabeled by `relocate`. -/
def relocatedAdderCircuit (accBase addBase n : Nat) : Gate :=
  relabelGate (relocate accBase addBase n) (cuccaro_n_bit_adder_full n accBase)

/-- Transported `sumCorrect`: accumulator `[accBase, accBase+n)`, addend
    `[addBase, addBase+n)`, clean carry-in at `addBase+n`. -/
theorem relocated_sumCorrect (n accBase addBase : Nat) (f : Nat → Bool)
    (hv : accBase + n ≤ addBase) (hclean : f (addBase + n) = false) :
    decodeReg (fun i => accBase + i) n (Gate.applyNat (relocatedAdderCircuit accBase addBase n) f)
      = (decodeReg (fun i => accBase + i) n f
          + decodeReg (fun i => addBase + i) n f) % 2 ^ n := by
  have hσ : Function.Injective (relocate accBase addBase n) := relocate_injective accBase addBase n hv
  have htrans : ∀ p, Gate.applyNat (relocatedAdderCircuit accBase addBase n) f
      (relocate accBase addBase n p)
      = Gate.applyNat (cuccaro_n_bit_adder_full n accBase)
          (fun q' => f (relocate accBase addBase n q')) p := fun p =>
    applyNat_relabelGate (relocate accBase addBase n) hσ (cuccaro_n_bit_adder_full n accBase) f p
  have hcleanσ : cuccaroAdder.ancClean (fun q' => f (relocate accBase addBase n q')) n accBase := by
    show (fun q' => f (relocate accBase addBase n q')) accBase = false
    show f (relocate accBase addBase n accBase) = false
    rw [relocate_carry]; exact hclean
  have hsum := cuccaroAdder.sumCorrect n accBase (fun q' => f (relocate accBase addBase n q')) hcleanσ
  rw [decodeReg_congr (fun i => accBase + i) (fun i => accBase + 2 * i + 1) n
        (Gate.applyNat (relocatedAdderCircuit accBase addBase n) f)
        (Gate.applyNat (cuccaro_n_bit_adder_full n accBase)
          (fun q' => f (relocate accBase addBase n q')))
        (fun i hi => by
          show Gate.applyNat (relocatedAdderCircuit accBase addBase n) f (accBase + i) = _
          rw [← relocate_augend accBase addBase n i hi]; exact htrans (accBase + 2 * i + 1))]
  rw [decodeReg_congr (fun i => accBase + i) (fun i => accBase + 2 * i + 1) n f
        (fun q' => f (relocate accBase addBase n q'))
        (fun i hi => by
          show f (accBase + i) = f (relocate accBase addBase n (accBase + 2 * i + 1))
          rw [relocate_augend accBase addBase n i hi])]
  rw [decodeReg_congr (fun i => addBase + i) (fun i => accBase + 2 * i + 2) n f
        (fun q' => f (relocate accBase addBase n q'))
        (fun i hi => by
          show f (addBase + i) = f (relocate accBase addBase n (accBase + 2 * i + 2))
          rw [relocate_addend accBase addBase n i hi])]
  exact hsum

/-- Transported `addendRestored`. -/
theorem relocated_addendRestored (n accBase addBase : Nat) (f : Nat → Bool)
    (hv : accBase + n ≤ addBase) (i : Nat) (hi : i < n) :
    Gate.applyNat (relocatedAdderCircuit accBase addBase n) f (addBase + i) = f (addBase + i) := by
  have hσ := relocate_injective accBase addBase n hv
  have htrans := applyNat_relabelGate (relocate accBase addBase n) hσ
    (cuccaro_n_bit_adder_full n accBase) f (accBase + 2 * i + 2)
  rw [relocate_addend accBase addBase n i hi] at htrans
  show Gate.applyNat (relabelGate (relocate accBase addBase n)
      (cuccaro_n_bit_adder_full n accBase)) f (addBase + i) = _
  rw [htrans, (cuccaro_n_bit_adder_full_correct n accBase
        (fun q' => f (relocate accBase addBase n q'))).2.2 i hi]
  show f (relocate accBase addBase n (accBase + 2 * i + 2)) = f (addBase + i)
  rw [relocate_addend accBase addBase n i hi]

/-- Transported `ancRestored`: the carry-in at `addBase+n` is returned clean. -/
theorem relocated_ancRestored (n accBase addBase : Nat) (f : Nat → Bool)
    (hv : accBase + n ≤ addBase) (hclean : f (addBase + n) = false) :
    Gate.applyNat (relocatedAdderCircuit accBase addBase n) f (addBase + n) = false := by
  have hσ := relocate_injective accBase addBase n hv
  have htrans := applyNat_relabelGate (relocate accBase addBase n) hσ
    (cuccaro_n_bit_adder_full n accBase) f accBase
  rw [relocate_carry] at htrans
  show Gate.applyNat (relabelGate (relocate accBase addBase n)
      (cuccaro_n_bit_adder_full n accBase)) f (addBase + n) = false
  rw [htrans, (cuccaro_n_bit_adder_full_correct n accBase
        (fun q' => f (relocate accBase addBase n q'))).1]
  show f (relocate accBase addBase n accBase) = false
  rw [relocate_carry]; exact hclean

/-- Transported `frame` (bounding interval `[accBase, addBase+n+1)`). -/
theorem relocated_frame (n accBase addBase : Nat) (f : Nat → Bool) (p : Nat)
    (hv : accBase + n ≤ addBase)
    (hp : ¬ inBlock accBase (addBase + n + 1 - accBase) p) :
    Gate.applyNat (relocatedAdderCircuit accBase addBase n) f p = f p := by
  have hσ := relocate_injective accBase addBase n hv
  have hout : p < accBase ∨ addBase + n < p := by unfold inBlock at hp; omega
  have hrel : relocate accBase addBase n p = p := relocate_outside accBase addBase n p hv hout
  have htrans := applyNat_relabelGate (relocate accBase addBase n) hσ
    (cuccaro_n_bit_adder_full n accBase) f p
  rw [hrel] at htrans
  show Gate.applyNat (relabelGate (relocate accBase addBase n)
      (cuccaro_n_bit_adder_full n accBase)) f p = f p
  rw [htrans]
  have hframe : Gate.applyNat (cuccaro_n_bit_adder_full n accBase)
      (fun q' => f (relocate accBase addBase n q')) p
      = (fun q' => f (relocate accBase addBase n q')) p := by
    rcases hout with hlo | hhi
    · exact cuccaro_n_bit_adder_full_frame_below n accBase _ p hlo
    · exact cuccaro_n_bit_adder_full_frame_above n accBase _ p (by omega)
  rw [hframe]
  show f (relocate accBase addBase n p) = f p
  rw [hrel]

/-- **Gap-frame (the load-bearing preservation fact).**  The gap `[accBase+n, addBase)`
    — which for the faithful pass-2 layout IS register `b`, used as the multiplicand —
    is left UNTOUCHED by the relocated adder, even though it lies INSIDE the coarse
    bounding frame.  Proof: a gap position `p` is `relocate (p+n+1)`, and `p+n+1` lies
    in the fill domain ABOVE the Cuccaro support, so Cuccaro's frame-above applies. -/
theorem relocated_gap_frame (n accBase addBase : Nat) (f : Nat → Bool) (p : Nat)
    (hv : accBase + n ≤ addBase) (h1 : accBase + n ≤ p) (h2 : p < addBase) :
    Gate.applyNat (relocatedAdderCircuit accBase addBase n) f p = f p := by
  have hσ := relocate_injective accBase addBase n hv
  have hpre : relocate accBase addBase n (p + n + 1) = p := by
    unfold relocate; split_ifs <;> omega
  have htrans := applyNat_relabelGate (relocate accBase addBase n) hσ
    (cuccaro_n_bit_adder_full n accBase) f (p + n + 1)
  rw [hpre] at htrans
  show Gate.applyNat (relabelGate (relocate accBase addBase n)
      (cuccaro_n_bit_adder_full n accBase)) f p = f p
  rw [htrans, cuccaro_n_bit_adder_full_frame_above n accBase _ (p + n + 1) (by omega)]
  show f (relocate accBase addBase n (p + n + 1)) = f p
  rw [hpre]

/-- Transported `wellTyped` at any dimension `dim ≥ addBase + n + 1`. -/
theorem relocated_wellTyped (n accBase addBase dim : Nat) (hv : accBase + n ≤ addBase)
    (hdim : addBase + n + 1 ≤ dim) :
    Gate.WellTyped dim (relocatedAdderCircuit accBase addBase n) := by
  unfold relocatedAdderCircuit
  refine wellTyped_relabelGate (relocate accBase addBase n)
    (relocate_injective accBase addBase n hv) dim (fun x hx => ?_) _
    (cuccaro_n_bit_adder_full_wellTyped n accBase dim (by omega))
  by_cases hx2 : x < addBase + n + 1
  · exact lt_of_lt_of_le (relocate_maps_lt accBase addBase n x hx2) hdim
  · rw [relocate_outside accBase addBase n x hv (Or.inr (by omega))]; exact hx

/-! ## §3. The relocated adder as a `TwoBaseBoundedAdder` instance. -/

/-- **The relocated contiguous adder** (generalizes `contiguousPackedAdder` to an
    independent addend base; carry at `addBase + n`; valid when `accBase + n ≤ addBase`). -/
def relocatedContiguousAdder : TwoBaseBoundedAdder where
  span     := fun n accBase addBase => addBase + n + 1 - accBase
  accIdx   := fun _ accBase i => accBase + i
  addIdx   := fun _ addBase i => addBase + i
  valid    := fun n accBase addBase => accBase + n ≤ addBase
  ancClean := fun f n _ addBase => f (addBase + n) = false
  circuit  := fun n accBase addBase => relocatedAdderCircuit accBase addBase n
  sumCorrect := fun n accBase addBase f hv hclean =>
    relocated_sumCorrect n accBase addBase f hv hclean
  addendRestored := fun n accBase addBase f hv _ i hi =>
    relocated_addendRestored n accBase addBase f hv i hi
  ancRestored := fun n accBase addBase f hv hclean =>
    relocated_ancRestored n accBase addBase f hv hclean
  frame := fun n accBase addBase f p hv hp =>
    relocated_frame n accBase addBase f p hv hp
  wellTyped := by
    intro n accBase addBase hv
    have hdim : accBase + (addBase + n + 1 - accBase) = addBase + n + 1 := by omega
    rw [hdim]; exact relocated_wellTyped n accBase addBase (addBase + n + 1) hv (le_refl _)
  accIdx_inBlock := fun n accBase addBase i hv hi => by unfold inBlock; omega
  addIdx_inBlock := fun n accBase addBase i hv hi => by unfold inBlock; omega
  addIdx_inj := fun n addBase i j h => by omega
  acc_add_disjoint := fun n accBase addBase i j hv hi _ => by omega
  ancClean_ext := by
    intro n accBase addBase f g hv hagree hclean
    show g (addBase + n) = false
    have hp : inBlock accBase (addBase + n + 1 - accBase) (addBase + n) := by unfold inBlock; omega
    have hne : ∀ i, i < n → addBase + n ≠ accBase + i ∧ addBase + n ≠ addBase + i :=
      fun i hi => by omega
    rw [← hagree (addBase + n) hp hne]
    exact hclean

/-! ## §4. Faithful-layout instantiation (pass 1 packed, pass 2 spread).

The faithful `cosetDim` layout (`Shor/GidneyInPlace/Adder/Def/ProductAddLayout`): lookup zone,
then register `a` at `1+2w`, register `b` at `1+2w+bits`, shared addend-temp at
`1+2w+2bits`, carry at `1+2w+3bits`.  Both passes use `relocatedContiguousAdder`
with `addBase = 1+2w+2bits` (the shared temp) and carry `= addBase+bits = 1+2w+3bits`. -/

/-- Pass 1 (`b += a·k`): accumulator `b` at `1+2w+bits`, addend at the shared temp
    `1+2w+2bits` — the gap-0 (packed) case. `valid` holds. -/
theorem relocated_pass1_valid (w bits : Nat) :
    relocatedContiguousAdder.valid bits (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) := by
  show (1 + 2 * w + bits) + bits ≤ (1 + 2 * w + 2 * bits); omega

/-- Pass 2 (`a -= b·kInv`): accumulator `a` at `1+2w`, addend at the shared temp
    `1+2w+2bits` — the gap-`bits` (spread) case that the packed adder could not host.
    `valid` holds. -/
theorem relocated_pass2_valid (w bits : Nat) :
    relocatedContiguousAdder.valid bits (1 + 2 * w) (1 + 2 * w + 2 * bits) := by
  show (1 + 2 * w) + bits ≤ (1 + 2 * w + 2 * bits); omega

/-- **Block disjointness for both passes** (carry, acc block, addend block pairwise
    distinct for the in-use indices).  The disjointness of ALL source/intermediate
    Cuccaro indices under the relabel is exactly `relocate_injective`. -/
theorem relocated_faithful_blocks_disjoint (w bits i j : Nat)
    (hi : i < bits) (hj : j < bits) :
    -- pass 2: acc a [1+2w, 1+2w+bits), addend [1+2w+2bits, 1+2w+3bits), carry 1+2w+3bits
    (1 + 2 * w + i ≠ 1 + 2 * w + 2 * bits + j)
    ∧ (1 + 2 * w + i ≠ 1 + 2 * w + 3 * bits)
    ∧ (1 + 2 * w + 2 * bits + j ≠ 1 + 2 * w + 3 * bits) := by
  refine ⟨by omega, by omega, by omega⟩

/-- **Pass-1 multiplicand preserved.**  In pass 1 the multiplicand `a` lives at
    `[1+2w, 1+2w+bits)`, BELOW the accumulator base `bReg = 1+2w+bits`, so the adder
    (which acts on `[bReg, …)`) leaves it untouched (the below-footprint frame). -/
theorem relocated_pass1_multiplicand_preserved (w bits : Nat) (f : Nat → Bool)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (relocatedAdderCircuit (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) bits)
        f (1 + 2 * w + i) = f (1 + 2 * w + i) :=
  relocated_frame bits (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) f (1 + 2 * w + i)
    (by omega) (by unfold inBlock; omega)

/-- **Pass-2 multiplicand preserved — the crucial gap fact.**  In pass 2 the
    multiplicand `b` lives at `[1+2w+bits, 1+2w+2bits)`, which is exactly the GAP of
    the adder (accumulator base `aReg = 1+2w`, addend base `1+2w+2bits`).  Although
    `b` lies INSIDE the coarse bounding frame, `relocated_gap_frame` proves the adder
    leaves it untouched — so `b` is preserved while being read as the multiplicand. -/
theorem relocated_pass2_multiplicand_preserved (w bits : Nat) (f : Nat → Bool)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (relocatedAdderCircuit (1 + 2 * w) (1 + 2 * w + 2 * bits) bits)
        f (1 + 2 * w + bits + i) = f (1 + 2 * w + bits + i) :=
  relocated_gap_frame bits (1 + 2 * w) (1 + 2 * w + 2 * bits) f (1 + 2 * w + bits + i)
    (by omega) (by omega) (by omega)

end FormalRV.BQAlgo
