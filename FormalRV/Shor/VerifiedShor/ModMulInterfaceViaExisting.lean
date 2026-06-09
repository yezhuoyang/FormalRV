import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.ShorQFTFallbackCertification

namespace VerifiedShor
namespace ModMul
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




theorem circuitFamily_modMulImpl_via_interfaces
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (h_inv : a * ainv % N = 1) :
    ModMulImpl a N bits (ancillaWidth bits)
      (circuitFamily a ainv N bits) :=
  circuitFamily_modMulImpl a ainv N bits hbits hN_ge_2 hN hN2 h_inv

theorem satisfiesMultiplyCircuitProperty_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    MultiplyCircuitProperty a N bits (ancillaWidth bits)
      (Gate.toUCom (totalDim bits) (gateMCP bits N a ainv)) :=
  satisfiesMultiplyCircuitProperty bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv

end ModMul
end VerifiedShor
