import FormalRV.Shor.MainAlgorithm.SuccessProbability.QPEEigenstateAndDimCast

namespace FormalRV.SQIRPort

/-! ## Single-orbit action of the modular multiplier (toward the
modmult eigenstate eigenvalue theorem)

This section provides the smallest piece toward proving the
modular-multiplier EIGENSTATE eigenvalue relation
`uc_eval (f i) * ψ_k = exp(...) • ψ_k`: the action of `f i =
U^{a^{2^i}}` on a single orbit basis vector `|a^j mod N⟩|0⟩_anc`.
Combines `ModMulImpl` instantiated at `f i` with the power-product
identity `a^{2^i} · a^j = a^{2^i + j}`. -/

/-- **Single-orbit-basis-vector action**: `f i` (the QPE-i-th
controlled-power gadget, per `ModMulImpl`) applied to the orbit basis
state `|a^j mod N⟩ ⊗ |0⟩_anc` shifts the orbit position by `2^i`.

Specifically: `f i · |a^j mod N⟩ ⊗ |0⟩_anc = |a^(2^i + j) mod N⟩ ⊗ |0⟩_anc`.

This is the lifting of `MultiplyCircuitProperty (a^{2^i})` at the
orbit-input `x = a^j mod N` (which is always `< N` since `0 < N`),
plus the algebraic simplification `(a^{2^i}) · (a^j) % N = a^{2^i + j} % N`
via `Nat.mul_mod` + `pow_add`. -/
theorem MultiplyCircuitProperty_acts_on_orbit_basis
    (a N n anc i j : Nat)
    (f : Nat → BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_N_pos : 0 < N) :
    uc_eval (f i) (basis_vector (2^(n+anc)) ((a^j % N) * 2^anc))
    = basis_vector (2^(n+anc)) ((a^(2^i + j) % N) * 2^anc) := by
  have h_mcp := h_modmul i
  have h_lt : a^j % N < N := Nat.mod_lt _ h_N_pos
  have h_action := h_mcp (a^j % N) h_lt
  rw [h_action]
  congr 2
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← pow_add]

end FormalRV.SQIRPort
