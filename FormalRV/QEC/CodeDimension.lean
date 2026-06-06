/-
  FormalRV.QEC.CodeDimension — the logical-qubit count of a CSS code, DERIVED from its
  constructed parity matrices over GF(2):  k = n − rank(H_X) − rank(H_Z).

  GENERAL / reusable: every qLDPC-code paper uses this to DERIVE `k` from the matrices
  (rather than asserting it).  It lives in the framework `QEC/` layer — not in any one
  paper's folder — so each `Audit/<Paper>/` imports it as general machinery.
-/
import FormalRV.QEC.CSSCode
import FormalRV.QEC.GF2Rank

namespace FormalRV.QEC

open FormalRV.Framework.LDPC

/-- Logical-qubit count derived from a CSS code's parity matrices over GF(2):
    `k = n − rank(H_X) − rank(H_Z)`. -/
def derivedK (c : CSSCode) : Nat := c.n - rank c.hx - rank c.hz

end FormalRV.QEC
