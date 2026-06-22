/-
  FormalRV.Resource.Examples
  ──────────────────────────
  Worked demonstrations of the resource-counting TRIPLE on a concrete gadget:
  (1) a syntactic object, (2) its semantic-correctness theorem, (3) the
  independent counters applied to THAT object = the closed form.

  Contains `#eval` demos, so kept OFF the default build path. Run on demand:
    lake build FormalRV.Resource.Examples
-/
import FormalRV.Resource.Interface
import FormalRV.Arithmetic.Cuccaro.CuccaroAdderResource

namespace FormalRV.Resource

open FormalRV.Framework
open FormalRV.BQAlgo

/-! ## The object: a concrete 5-bit Cuccaro adder (a `Gate` syntax tree). -/

/-! A skeptic constructs the object and runs the counters — no proof to read. -/
#eval countT        (cuccaro_n_bit_adder_full 5 0)   -- TIME:  70  (= 14 × 5)
#eval countToffoli  (cuccaro_n_bit_adder_full 5 0)   -- TIME:  10  (n MAJ + n UMA)
#eval countCNOT     (cuccaro_n_bit_adder_full 5 0)   -- TIME:  20
#eval gateCount     (cuccaro_n_bit_adder_full 5 0)   -- TIME:  30
#eval width         (cuccaro_n_bit_adder_full 5 0)   -- SPACE: 11  (= 2n + 1)

/-! ## (2) semantic correctness + (3) the count, both about the SAME object. -/

-- (2) the object is semantically correct (its headline theorem).
#check (cuccaro_adder_correct 5 0 1 2 (by decide) (by decide) :
    cuccaro_target_val 5 0
        (Gate.applyNat (cuccaro_n_bit_adder_full 5 0) (cuccaro_input_F 0 false 1 2))
      = (1 + 2) % 2 ^ 5)

/-- (3) **The count is the closed form, on the same object** — via the bridge to
the gadget's existing resource theorem.  This is the third leg of the triple:
the independent `countT` walk of `cuccaro_n_bit_adder_full n 0` equals `14·n`. -/
example (n : Nat) : countT (cuccaro_n_bit_adder_full n 0) = 14 * n := by
  rw [countT_eq_tcount]; exact cuccaro_adder_tcount n 0

/-- And `countT` is exactly `7 ×` the (independently-counted) Toffolis — two
counters reconciled on the same tree. -/
example (n : Nat) :
    countT (cuccaro_n_bit_adder_full n 0)
      = 7 * countToffoli (cuccaro_n_bit_adder_full n 0) :=
  countT_eq_seven_countToffoli _

end FormalRV.Resource
