/-
  FormalRV.Audit.CainXu2026.QianxuCodeParams — DERIVE the logical-qubit count k of qianxu's
  codes from their CONSTRUCTED parity matrices (closing the "k is hardcoded" gap the
  self-critique named as THE foundational missing deliverable).

  qianxu's headline [[n,k,d]] (ED Table II): bb18 = [[248,10,18]], lp_20^{3,7} =
  [[4350,1224,≤20]], lp_24^{3,7} = [[5278,1480,≤24]].  Our framework already builds
  these codes with `n` and the CSS condition verified — but `k` was a hardcoded
  parameter (`toQECCode code k d`), never derived.  Here we DERIVE it from the
  matrices via the GF(2)-rank algorithm:  k = n − rank(H_X) − rank(H_Z).

  ## Honest certificate status (axiom hygiene)
  At bb18's 248-qubit scale the kernel `decide` for the rank TIMES OUT, so the
  derivation `k = 10` is certified by `native_decide` — which adds a native-eval
  axiom (NOT kernel-clean `[propext, Classical.choice, Quot.sound]`).  This is the
  only feasible CERTIFICATE at this scale; the k VALUE is genuinely computed from the
  constructed matrices, not asserted.  For lp_20 / lp_24 (4350 / 5278 qubits) even
  native rank is impractical via the list-based `rowReduce`; their k (1224 / 1480)
  follows from the lifted-product homological formula (the proper path for the large
  codes), out of brute-rank reach.  (Distance `d` stays an out-of-scope input.)
-/

import FormalRV.QEC.Instances
import FormalRV.QEC.CodeDimension   -- general helper `derivedK` (k = n − rank Hx − rank Hz)

namespace FormalRV.Audit.CainXu2026.QianxuCodeParams

open FormalRV.QEC.Instances
open FormalRV.QEC   -- brings the general `derivedK`

/-- **bb18's k = 10, DERIVED from its constructed matrices** (n=248, rank H_X =
    rank H_Z = 119), matching the paper's `[[248,10,18]]`.  Not hardcoded — computed
    from `bb18.hx`/`bb18.hz` by the GF(2)-rank algorithm.

    Certificate: `native_decide` (kernel `decide` times out at 248 qubits); this adds
    a native-eval axiom — the k VALUE is derived, the CERTIFICATE is native. -/
theorem bb18_k_derived : derivedK bb18 = 10 := by
  unfold derivedK; native_decide

/-- bb18's n is kernel-clean (the easy half); only the rank-based k needs native. -/
theorem bb18_n : bb18.n = 248 := by decide

/-- The derived k matches the paper's reported logical count for bb18. -/
theorem bb18_k_matches_paper : derivedK bb18 = 10 := bb18_k_derived

end FormalRV.Audit.CainXu2026.QianxuCodeParams
