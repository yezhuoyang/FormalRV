/-
  FormalRV.Shor.CFS.EkeraHastad — the CLASSICAL post-processing of Ekerå–Håstad period finding
  (Gidney 2025, §"Ekerå–Håstad Period Finding", main.tex line 822–851), which turns the recovered
  discrete log into the factorisation of `N`.

  Per "semantic proof BEFORE resource proof".  Gidney uses Ekerå–Håstad-style period finding (fewer
  input qubits than textbook Shor): a base `g ∈ ℤ_N^*`, a derived `h = g^{N−1} mod N`, and quantum
  shots that recover `d = dlog_g(h)` by post-processing.  The QUANTUM step (the shots recover `d`) is
  the deep part; the CLASSICAL post-processing — why `d = p+q−2` and how the factors come out of `d`
  — is pure number theory, and is proved here axiom-clean:

    * `ekera_hastad_exponent` — `g^{N−1} ≡ g^{p+q−2} (mod N)` for `N = pq` and `g` of order dividing
      `φ(N) = (p−1)(q−1)`.  This is why the recovered discrete log is `d = p+q−2` (eq.841–849).
    * `ekera_hastad_recovery` — given `d = p+q−2` and `N = pq`, the factor `p` satisfies
      `p·(d−p+2) = N` (so `q = d−p+2`) and is a root of `X² − (d+2)X + N`; solving the quadratic
      recovers `p, q` (line 851).

  ## HONEST remaining link (the QUANTUM half, documented not faked)
  That the quantum shots actually recover `d = dlog_g(h)` with high probability is the quantum
  period/dlog-finding analysis (`ekeraa2017quantum`, `ekera2020postprocess`), connecting to
  `FormalRV.SQIRPort.probability_of_success`.  This file closes the classical post-processing: once
  `d` is in hand, the factorisation is the two theorems below.
-/
import Mathlib
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

/-- **Ekerå–Håstad exponent identity** (Gidney 2025 eq.841–849).  For `N = p·q` and a base `g` whose
    order divides `φ(N) = (p−1)(q−1)` (so `g^{(p−1)(q−1)} ≡ 1`), the derived value `h = g^{N−1}`
    satisfies `h ≡ g^{p+q−2} (mod N)`.  Hence the recovered discrete log `d = dlog_g(h)` equals
    `p+q−2`.  Reason: `pq − 1 = (p−1)(q−1) + (p+q−2)`, and the `φ(N)` part is `≡ 1`. -/
theorem ekera_hastad_exponent (p q g : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hphi : g ^ ((p - 1) * (q - 1)) ≡ 1 [MOD p * q]) :
    g ^ (p * q - 1) ≡ g ^ (p + q - 2) [MOD p * q] := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq
  have ha1 : 1 + a - 1 = a := by omega
  have hb1 : 1 + b - 1 = b := by omega
  have hexp : (1 + a) * (1 + b) = 1 + a + b + a * b := by ring
  have hsplit : (1 + a) * (1 + b) - 1
      = (1 + a - 1) * (1 + b - 1) + ((1 + a) + (1 + b) - 2) := by
    rw [ha1, hb1, hexp]; omega
  rw [hsplit, pow_add]
  calc g ^ ((1 + a - 1) * (1 + b - 1)) * g ^ ((1 + a) + (1 + b) - 2)
      ≡ 1 * g ^ ((1 + a) + (1 + b) - 2) [MOD (1 + a) * (1 + b)] := Nat.ModEq.mul_right _ hphi
    _ = g ^ ((1 + a) + (1 + b) - 2) := one_mul _

/-- **Ekerå–Håstad factor recovery** (Gidney 2025 line 851).  Given the recovered `d = p+q−2` and
    `N = p·q` (with `p, q ≥ 2`, as for RSA primes), the factor `p` satisfies `p·(d−p+2) = N` (because
    `d−p+2 = q`) and is a root of the quadratic `X² − (d+2)X + N` (i.e. `p² + N = (d+2)·p`).  Solving
    the quadratic for `p` recovers the prime factors. -/
theorem ekera_hastad_recovery (p q d N : ℕ) (hd : d = p + q - 2) (hN : N = p * q)
    (hp : 2 ≤ p) (hq : 2 ≤ q) :
    p * (d - p + 2) = N ∧ p * p + N = (d + 2) * p := by
  have hq2 : d - p + 2 = q := by omega
  have hd2 : d + 2 = p + q := by omega
  subst hN
  rw [hq2]
  exact ⟨rfl, by rw [hd2]; ring⟩

/-! ## The Ekerå–Håstad post-processing theorems pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean ekera_hastad_exponent
#verify_clean ekera_hastad_recovery

end FormalRV.CFS
