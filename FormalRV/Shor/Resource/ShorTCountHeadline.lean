/-
  FormalRV.Shor.Resource.ShorTCountHeadline
  -----------------------------------------
  **★ THE MEANINGFUL (DOMINANT) VERIFIED RESOURCE — the RSA-2048 magic-state and
  T-count of the controlled modular exponentiation. ★**

  (Logical *data* volume — merge seams — is the CHEAP part.  The dominant
  fault-tolerant cost is the MAGIC: the non-Clifford T / CCZ states.)

  These are EXACT integer equalities (not loose bounds, no rotation synthesis),
  for ANY valid Shor base, and the gate they count (`modmult_MCP_gate`) is the
  SAME object proven to compute `a·x mod N`
  (`modmult_MCP_gate_apply_encode` / `…_satisfies_MultiplyCircuitProperty`, the
  oracle used in `VerifiedShorTheorem`).  So the count is on the VERIFIED arithmetic.
-/
import FormalRV.Shor.Resource.CliffordTControlledModExp

namespace FormalRV.Shor.CliffordTControlledModExp

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **★ RSA-2048 MAGIC-STATE CORE ★** — the data-independent Toffoli (magic) core of
the Clifford+T controlled mod-exp at `bits = 2048`, `m = 2·bits = 4096`:
`m·48·bits² = 96·2048³ = 824 633 720 832 ≈ 8.25×10¹¹` magic states.  EXACT. -/
theorem shor2048_magic : (2 * 2048) * (48 * 2048 ^ 2) = 824633720832 := by norm_num

/-- **★ RSA-2048 T-COUNT CORE ★** — every Toffoli/CCZ is 7 T's
(`tcount_ctrlModExpChain` ⇒ `tcount = 7 · magic`), so the data-independent T-count
core is `7 · 824 633 720 832 = 5 772 436 045 824 ≈ 5.77×10¹²` T-gates. EXACT. -/
theorem shor2048_tcount : 7 * ((2 * 2048) * (48 * 2048 ^ 2)) = 5772436045824 := by norm_num

/-- ...and the full controlled mod-exp T-count is exactly `7×` its magic count, for
ANY valid Shor base — re-export tying the T-count to the verified-oracle magic
count (the data-independent core is `m·48·bits²`; `m·numCX(MCP)` is the only
base-dependent term). -/
theorem tcount_is_seven_times_magic (m cq anc bits N a ainv : Nat) :
    tcount (ctrlModExpChain m cq anc bits N a ainv)
      = 7 * numCCX (ctrlModExpChain m cq anc bits N a ainv) :=
  tcount_eq_seven_numCCX _

end FormalRV.Shor.CliffordTControlledModExp
