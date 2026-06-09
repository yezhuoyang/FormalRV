import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.ShorQFTRealInterfaceRouting

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




theorem satisfiesMultiplyCircuitProperty_real_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    MultiplyCircuitProperty a N bits (ancillaWidth bits)
      (Gate.toUCom (totalDim bits) (gateMCP bits N a ainv)) :=
  MCPAdapter.sqirCuccaro_satisfiesMultiplyCircuitProperty_real_via_interfaces
    bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv

theorem circuitFamily_modMulImpl_real_via_interfaces
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (h_inv : a * ainv % N = 1) :
    ModMulImpl a N bits (ancillaWidth bits)
      (circuitFamily a ainv N bits) := by
  intro i
  unfold circuitFamily f_modmult_circuit_verified_bits
  have hN_pos : 0 < N := by omega
  have h_ainv_lt_N : (ainv^(2^i)) % N < N := Nat.mod_lt _ hN_pos
  have h_ainv_le : (ainv^(2^i)) % N ≤ N := Nat.le_of_lt h_ainv_lt_N
  have h_inv_i : ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 :=
    pow_iter_inverse_mod a ainv N i hN_ge_2 h_inv
  apply MultiplyCircuitProperty_of_mod hN_pos
  -- Use the R6h-real MCP bridge directly (def-eq through layout projections
  -- handles the form alignment).
  exact MCPAdapter.sqirCuccaro_satisfiesMultiplyCircuitProperty_real_via_interfaces
    bits N ((a^(2^i)) % N) ((ainv^(2^i)) % N)
    hbits hN_pos hN hN2 h_ainv_le h_inv_i

end ModMul
end VerifiedShor
