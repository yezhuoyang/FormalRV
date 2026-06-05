import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.ShorSettingCircuitSizing

namespace VerifiedShor
namespace ShorSetting
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)


/-- `BasicSetting → ShorSetting` (drops the upper bound conjunct).
Public alias for `BasicSettingRelaxed_of_BasicSetting`. -/
theorem ofBasicSetting {a r N m n : Nat}
    (h : FormalRV.SQIRPort.BasicSetting a r N m n) :
    ShorSetting a r N m n :=
  FormalRV.BQAlgo.BasicSettingRelaxed_of_BasicSetting h

/-- `0 < a`. -/
theorem a_pos {a r N m n : Nat} (h : ShorSetting a r N m n) : 0 < a :=
  FormalRV.BQAlgo.BasicSettingRelaxed_a_pos h

/-- `a < N`. -/
theorem a_lt {a r N m n : Nat} (h : ShorSetting a r N m n) : a < N :=
  FormalRV.BQAlgo.BasicSettingRelaxed_a_lt h

/-- The order witness. -/
theorem order {a r N m n : Nat} (h : ShorSetting a r N m n) :
    FormalRV.SQIRPort.Order a r N :=
  FormalRV.BQAlgo.BasicSettingRelaxed_order h

/-- `N^2 < 2^m` (QPE precision lower bound). -/
theorem Nsq_lt {a r N m n : Nat} (h : ShorSetting a r N m n) : N^2 < 2^m :=
  FormalRV.BQAlgo.BasicSettingRelaxed_Nsq_lt h

/-- `2^m ≤ 2 * N^2` (QPE precision upper bound). -/
theorem pow_le_two_Nsq {a r N m n : Nat} (h : ShorSetting a r N m n) :
    2^m ≤ 2 * N^2 :=
  FormalRV.BQAlgo.BasicSettingRelaxed_pow_le_2Nsq h

/-- `N < 2^n`. -/
theorem N_lt_pow_n {a r N m n : Nat} (h : ShorSetting a r N m n) : N < 2^n :=
  FormalRV.BQAlgo.BasicSettingRelaxed_N_lt_pow_n h

/-- `N ≤ 2^n`. -/
theorem N_le_pow_n {a r N m n : Nat} (h : ShorSetting a r N m n) : N ≤ 2^n :=
  FormalRV.BQAlgo.BasicSettingRelaxed_N_le_pow_n h

/-- `0 < N`. -/
theorem N_pos {a r N m n : Nat} (h : ShorSetting a r N m n) : 0 < N :=
  FormalRV.BQAlgo.BasicSettingRelaxed_N_pos h

end ShorSetting
end VerifiedShor
