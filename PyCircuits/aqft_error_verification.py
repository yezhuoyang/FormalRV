"""
Numerical verification (Qiskit + numpy) of the FormalRV AQFT compiler error bounds.

Independently cross-checks the Lean theorems in
  FormalRV/Core/ApproxQFT.lean  and  FormalRV/Shor/AQFTCompile.lean
against ACTUAL unitary simulation — "don't trust the prover, measure it".

Lean claims under test
----------------------
  (T1) dropRotationError_le      : ‖R_z(θ) − I‖_op = 2|sin(θ/2)| ≤ |θ|
  (T2) qftRot_drop_error_le      : ‖R_z(2π/2^k) − I‖_op ≤ 2π/2^k
  (T3) aqft_ladder_error_budget  : Σ_{m=c}^{n-1} π/2^m ≤ 2π/2^c   (closed-form tail)
  (T4) controlled_Rz semantics   : Rz(λ/2);CX;Rz(-λ/2);CX;Rz(λ/2)  ==  CP(λ)
  (T5) THE BRIDGE (NOT formally proved in Lean — the key empirical check):
         the ACTUAL operator-norm error of the compiled (banded) inverse-QFT
         phase ladder vs the exact ladder is  ≤ Σ dropped drop-errors  ≤ 2π/2^cutoff.
  (T6) Full n-qubit QFT vs banded QFT: actual op-norm error ≤ total budget.
  (T7) cutoff ≤ 2 ⇒ kept half-angles ∈ (π/4)·ℤ  (gates are Clifford+T).

Repo conventions reproduced exactly:
  * FormalRV's  rotation 0 0 λ = diag(1, e^{iλ})  is Qiskit's PHASE gate p(λ)
    (NOT qiskit rz, which carries a different global phase).
  * controlled_Rz q t λ := Rz(λ/2)_q ; CX(q,t) ; Rz(-λ/2)_t ; CX(q,t) ; Rz(λ/2)_t
  * inverse_qft_phase_ladder: for target, controls j=target+1..n-1, angle -π/2^(j-target).
  * compileLadder cutoff: keep depth m < cutoff, DROP m ≥ cutoff.
"""
import sys
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass
import numpy as np
from qiskit import QuantumCircuit
from qiskit.quantum_info import Operator

PI = np.pi
TOL = 1e-9
results = []  # (name, passed, detail)


def opnorm(M):
    """Operator (spectral) norm = largest singular value."""
    return np.linalg.norm(M, 2)


def P(theta):
    """FormalRV rotation 0 0 θ = diag(1, e^{iθ}) (phase gate)."""
    return np.array([[1.0, 0.0], [0.0, np.exp(1j * theta)]], dtype=complex)


def drop_error(theta):
    """Exact op-norm cost of dropping R_z(θ): ‖diag(0, e^{iθ}-1)‖ = |e^{iθ}-1|."""
    return opnorm(P(theta) - np.eye(2))


def check(name, passed, detail):
    results.append((name, passed, detail))
    flag = "PASS" if passed else "**FAIL**"
    print(f"[{flag}] {name}\n        {detail}")


# ----------------------------------------------------------------------------
# (T1) per-rotation drop error:  ‖R_z(θ) − I‖ = 2|sin(θ/2)| ≤ |θ|
# ----------------------------------------------------------------------------
print("\n=== (T1) dropRotationError_le:  ‖R_z(θ)−I‖ = 2|sin(θ/2)| ≤ |θ| ===")
worst_eq, worst_bound_margin = 0.0, np.inf
for theta in np.linspace(-2 * PI, 2 * PI, 4001):
    actual = drop_error(theta)
    formula = 2 * abs(np.sin(theta / 2))
    bound = abs(theta)
    worst_eq = max(worst_eq, abs(actual - formula))
    worst_bound_margin = min(worst_bound_margin, bound - actual)
check("T1 actual == 2|sin(θ/2)|", worst_eq < TOL,
      f"max |‖R_z−I‖ − 2|sin(θ/2)|| = {worst_eq:.2e}")
check("T1 ‖R_z(θ)−I‖ ≤ |θ|  (chord ≤ arc)", worst_bound_margin > -TOL,
      f"min slack (|θ| − actual) over 4001 angles = {worst_bound_margin:.3e}")


# ----------------------------------------------------------------------------
# (T2) QFT rotation drop cost:  ‖R_z(2π/2^k) − I‖ ≤ 2π/2^k
# ----------------------------------------------------------------------------
print("\n=== (T2) qftRot_drop_error_le:  ‖R_z(2π/2^k)−I‖ ≤ 2π/2^k ===")
ok = True
for k in range(1, 21):
    actual = drop_error(2 * PI / 2 ** k)
    bound = 2 * PI / 2 ** k
    ok = ok and actual <= bound + TOL
check("T2 ‖R_z(2π/2^k)−I‖ ≤ 2π/2^k  (k=1..20)", ok,
      f"e.g. k=4: actual={drop_error(2*PI/16):.6f} ≤ bound={2*PI/16:.6f}; "
      f"k=8: actual={drop_error(2*PI/256):.6f} ≤ {2*PI/256:.6f}")


# ----------------------------------------------------------------------------
# (T3) closed-form total budget:  Σ_{m=c}^{n-1} π/2^m ≤ 2π/2^c
# ----------------------------------------------------------------------------
print("\n=== (T3) aqft_ladder_error_budget:  Σ_{m=c}^{n-1} π/2^m ≤ 2π/2^c ===")
ok = True
for c in range(0, 8):
    for n in range(c, c + 15):
        s = sum(PI / 2 ** m for m in range(c, n))
        ok = ok and s <= 2 * PI / 2 ** c + TOL
check("T3 geometric tail ≤ 2π/2^c", ok,
      f"e.g. c=2,n→∞: Σ={sum(PI/2**m for m in range(2,40)):.6f} ≤ 2π/2^2={2*PI/4:.6f}")


# ----------------------------------------------------------------------------
# (T4) controlled_Rz decomposition is semantically a controlled phase CP(λ)
# ----------------------------------------------------------------------------
print("\n=== (T4) controlled_Rz(λ) == CP(λ)  [the repo's 5-gate decomposition] ===")

def controlled_Rz_circ(lam):
    """qubit 0 = control q, qubit 1 = target t (FormalRV controlled_Rz)."""
    qc = QuantumCircuit(2)
    qc.p(lam / 2, 0)     # Rz(λ/2) on control
    qc.cx(0, 1)
    qc.p(-lam / 2, 1)    # Rz(-λ/2) on target
    qc.cx(0, 1)
    qc.p(lam / 2, 1)     # Rz(λ/2) on target
    return qc

def CP_matrix(lam):
    M = np.eye(4, dtype=complex)
    M[3, 3] = np.exp(1j * lam)   # |11> picks up phase
    return M

ok = True
for lam in [-PI, -PI / 2, -PI / 4, PI / 3, 1.234]:
    U = Operator(controlled_Rz_circ(lam)).data        # Qiskit-built unitary
    err = opnorm(U - CP_matrix(lam))
    ok = ok and err < TOL
check("T4 Qiskit controlled_Rz == CP(λ)", ok,
      f"max ‖U − CP(λ)‖ over sampled λ < {TOL:.0e} (decomposition is correct)")


# ----------------------------------------------------------------------------
# helpers: build the inverse-QFT phase ladder (one target) and its banded form
# ----------------------------------------------------------------------------
def phase_ladder(n, target, cutoff=None):
    """controls j = target+1 .. n-1, gate controlled_Rz(j, target, -π/2^(j-target)).
       cutoff=None -> exact; else DROP depth m=j-target >= cutoff."""
    qc = QuantumCircuit(n)
    for j in range(target + 1, n):
        m = j - target
        if cutoff is not None and m >= cutoff:
            continue
        lam = -PI / 2 ** m
        qc.p(lam / 2, j)
        qc.cx(j, target)
        qc.p(-lam / 2, target)
        qc.cx(j, target)
        qc.p(lam / 2, target)
    return qc


# ----------------------------------------------------------------------------
# (T5) THE BRIDGE: actual op-norm error of the compiled ladder ≤ budget 2π/2^cutoff
# ----------------------------------------------------------------------------
print("\n=== (T5) BRIDGE: ‖exact ladder − banded ladder‖_op ≤ Σ drop-errors ≤ 2π/2^cutoff ===")
print("    (Σ drop-errors → 2π/2^cutoff is the Lean budget; the op-norm ≤ Σ is the")
print("     subadditive bridge Lean did NOT formalize — here measured directly.)")
all_ok = True
for n in range(2, 8):
    target = 0
    U_exact = Operator(phase_ladder(n, target, cutoff=None)).data
    for cutoff in range(1, n):
        U_band = Operator(phase_ladder(n, target, cutoff=cutoff)).data
        actual = opnorm(U_exact - U_band)
        # sum of the EXACT per-rotation drop errors over dropped depths m=cutoff..n-1
        drop_sum = sum(drop_error(-PI / 2 ** m) for m in range(cutoff, n))
        lean_loose_sum = sum(PI / 2 ** m for m in range(cutoff, n))  # |θ| bound
        budget = 2 * PI / 2 ** cutoff                                # closed form
        ok = (actual <= drop_sum + TOL
              and drop_sum <= lean_loose_sum + TOL
              and lean_loose_sum <= budget + TOL)
        all_ok = all_ok and ok
        if cutoff in (1, 2) and n in (5, 7):
            print(f"    n={n} cutoff={cutoff}: ‖Δ‖_op={actual:.5f} ≤ Σdrop={drop_sum:.5f} "
                  f"≤ Σ|θ|={lean_loose_sum:.5f} ≤ 2π/2^{cutoff}={budget:.5f}")
check("T5 op-norm ladder error ≤ drop-sum ≤ 2π/2^cutoff (n=2..7, all cutoffs)", all_ok,
      "actual operator-norm error never exceeds the proved budget")


# ----------------------------------------------------------------------------
# (T6) full n-qubit QFT vs banded QFT: op-norm error ≤ total budget
# ----------------------------------------------------------------------------
print("\n=== (T6) full QFT vs banded QFT (all targets): op-norm error ≤ total budget ===")
def full_iqft(n, cutoff=None):
    """Full inverse-QFT (no swaps): for target = n-1 .. 0, its phase ladder."""
    qc = QuantumCircuit(n)
    for target in range(n - 1, -1, -1):
        for j in range(target + 1, n):
            m = j - target
            if cutoff is not None and m >= cutoff:
                continue
            lam = -PI / 2 ** m
            qc.p(lam / 2, j); qc.cx(j, target)
            qc.p(-lam / 2, target); qc.cx(j, target); qc.p(lam / 2, target)
        qc.h(target)
    return qc

all_ok = True
for n in range(2, 8):
    U_exact = Operator(full_iqft(n, cutoff=None)).data
    for cutoff in range(1, n):
        U_band = Operator(full_iqft(n, cutoff=cutoff)).data
        actual = opnorm(U_exact - U_band)
        # union bound: sum over every dropped rotation in every ladder
        total_drop = sum(drop_error(-PI / 2 ** (j - t))
                         for t in range(n) for j in range(t + 1, n) if (j - t) >= cutoff)
        # per-ladder closed form ≤ 2π/2^cutoff, and there are n ladders
        budget_per_ladder = 2 * PI / 2 ** cutoff
        n_ladders = n
        ok = (actual <= total_drop + TOL) and (total_drop <= n_ladders * budget_per_ladder + TOL)
        all_ok = all_ok and ok
        if n == 7 and cutoff in (1, 2, 3):
            print(f"    n={n} cutoff={cutoff}: ‖Δ‖_op={actual:.5f} ≤ Σdrop={total_drop:.5f} "
                  f"≤ n·(2π/2^{cutoff})={n_ladders*budget_per_ladder:.5f}")
check("T6 full QFT op-norm error ≤ union-bound budget (n=2..7)", all_ok,
      "the multi-target union bound also holds against actual simulation")


# ----------------------------------------------------------------------------
# (T7) cutoff ≤ 2 ⇒ kept half-angles ∈ (π/4)·ℤ  (gates are Clifford+T)
# ----------------------------------------------------------------------------
print("\n=== (T7) cutoff ≤ 2 ⇒ kept controlled_Rz half-angles ∈ (π/4)ℤ (Clifford+T) ===")
def is_pi_over_4_multiple(angle):
    q = angle / (PI / 4)
    return abs(q - round(q)) < TOL

cutoff = 2
kept_ok, dropped_nonCT = True, []
for m in range(1, 12):
    lam = -PI / 2 ** m
    half_angles = [lam / 2, -lam / 2]  # the Rz angles in controlled_Rz
    ct = all(is_pi_over_4_multiple(a) for a in half_angles)
    if m < cutoff:      # kept
        kept_ok = kept_ok and ct
    else:               # dropped — and indeed NOT Clifford+T for m≥2 (would justify dropping)
        if not ct:
            dropped_nonCT.append(m)
check("T7 kept (m<2) half-angles are π/4-multiples ⇒ Clifford+T", kept_ok,
      f"kept depth m=1: half-angle ±π/4 (= T/T†). dropped non-Clifford+T depths sampled: {dropped_nonCT[:6]}")


# ----------------------------------------------------------------------------
# (T8) consistency: the actual error never exceeds min(proved budget, trivial 2).
#      For any two unitaries ‖U−V‖_op ≤ ‖U‖+‖V‖ = 2, so the HONEST guarantee is
#      min(2π/2^cutoff, 2).  At tiny cutoffs the budget exceeds 2 (loose but never
#      violated); the proved bound is always consistent with the ≤2 floor.
# ----------------------------------------------------------------------------
print("\n=== (T8) consistency: actual ≤ min(2π/2^cutoff, 2)  (proved bound never contradicts ‖U−V‖≤2) ===")
ok, worst = True, 0.0
for n in range(2, 9):
    U_exact = Operator(phase_ladder(n, 0, cutoff=None)).data
    for cutoff in range(1, n):
        actual = opnorm(U_exact - Operator(phase_ladder(n, 0, cutoff)).data)
        guarantee = min(2 * PI / 2 ** cutoff, 2.0)
        ok = ok and (actual <= guarantee + TOL) and (actual <= 2.0 + TOL)
        worst = max(worst, actual - guarantee)
check("T8 actual ≤ min(2π/2^cutoff, 2) and ≤ 2  (n=2..8)", ok,
      f"worst (actual − min(budget,2)) = {worst:.3e} ≤ 0  ⇒ proved bound is consistent")


# ----------------------------------------------------------------------------
print("\n" + "=" * 70)
n_pass = sum(1 for _, p, _ in results if p)
print(f"SUMMARY: {n_pass}/{len(results)} checks passed.")
if n_pass == len(results):
    print("ALL LEAN ERROR BOUNDS CONFIRMED BY QISKIT NUMERICAL SIMULATION.")
else:
    print("SOME CHECKS FAILED — see **FAIL** lines above.")
    for name, p, detail in results:
        if not p:
            print(f"  FAIL: {name} :: {detail}")
