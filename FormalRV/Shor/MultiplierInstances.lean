/-
  FormalRV.Shor.MultiplierInstances — the two verified ripple-adder-lineage
  modular multipliers as instances of the canonical multiplier interface.

  ## `EncodeRoundTripModMul` IS the multiplier interface

  `WindowedShorConnection.EncodeRoundTripModMul N bits anc` is the project's
  canonical contract for a verified in-place modular multiplier: a gate family
  `gate : Nat → Gate` (indexed by the multiplier constant `c`) that is
  well-typed at `bits + anc` and Boolean-round-trips the canonical
  `encodeDataZeroAnc` layout, `|x⟩|0⟩ ↦ |(c·x) % N⟩|0⟩`, for every constant
  `c` invertible mod `N`.  Everything above that round-trip is already proven
  and reusable:

    `EncodeRoundTripModMul`
      → (`.toVerifiedModMulFamily`)   `VerifiedShor.VerifiedModMulFamily`
      → (`.shorCorrect`)              `probability_of_success ≥ κ / (log₂ N)⁴`

  so "any multiplier → modular exponentiation → Shor success bound" is a
  one-line instantiation per multiplier.

  ## The two instances in this file (both kernel-clean, no `sorry`/axioms)

  1. `cuccaroMultiplier` — wraps **`modmult_MCP_gate`** (the SQIR-faithful
     Cuccaro-adder shift-and-add multiplier, `Arithmetic/ModMult`), via its
     proven round-trip `modmult_MCP_gate_apply_encode` and
     `modmult_MCP_gate_wellTyped`.  Ancilla block: `sqir_modmult_rev_anc bits`.
  2. `gidneyMultiplier` — wraps **`modMultInPlaceShor`** (the Gidney
     ripple-carry in-place multiplier with register-swap adapters,
     `Arithmetic/ModMult/ShorOracle`), via its proven round-trip
     `modMultInPlaceShor_correct` and `modMultInPlaceShor_wellTyped`.
     Data register: `multBits`; ancilla block: `adder_n_qubits (bits+1) + 1`.

  The third (windowed-arithmetic, Pipeline C) multiplier is connected in
  `WindowedShorConnection` §9 (`windowedModMulFamily` / `windowed_shor_correct`).

  ## The per-constant modular inverse

  Both underlying gates take the modular inverse of the constant as an extra
  argument, but the interface's `gate : Nat → Gate` takes only `c`.  The
  instances therefore compute the inverse internally (`modInv N c`, a
  choice-extracted canonical inverse) and reduce the constant mod `N`
  (`c % N`), so the SAME gate family is correct for the raw QPE constants
  `c = a^(2^i)` that `toVerifiedModMulFamily` feeds in.  The interface's
  invertibility guard `∃ d, (c·d) % N = 1` is exactly what `modInv_spec`
  needs, and at the Shor use site it is discharged by the per-power witness
  `ainv0^(2^i)` (`mul_pow_mod_one`) — the same pattern as the windowed
  family.

  ## Honesty tier

  Verified (semantic): the round-trips are the existing kernel-clean
  `Gate.applyNat` theorems of the two multipliers; the Shor corollaries are
  the real success-probability bound via the reusable MCP bridge.
-/
import FormalRV.Shor.WindowedShorConnection

namespace FormalRV.BQAlgo.MultiplierInstances

open FormalRV.SQIRPort
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open VerifiedShor
open FormalRV.BQAlgo.WindowedShorConnection

/-! ## §1. The internal per-constant modular inverse. -/

open Classical in
/-- Canonical modular inverse of `c` mod `N`, extracted by choice from the
    invertibility predicate: the chosen `d < N` with `(c·d) % N = 1` when one
    exists, else `0`.  This lets a gate family indexed ONLY by the constant
    `c` (as `EncodeRoundTripModMul.gate` requires) embed the inverse the
    underlying circuits need. -/
noncomputable def modInv (N c : Nat) : Nat :=
  if h : ∃ d, d < N ∧ (c * d) % N = 1 then h.choose else 0

/-- `modInv` is a genuine bounded inverse whenever any inverse exists:
    `modInv N c < N` and `(c · modInv N c) % N = 1`. -/
theorem modInv_spec (N c : Nat) (hN_pos : 0 < N) (hc : ∃ d, (c * d) % N = 1) :
    modInv N c < N ∧ (c * modInv N c) % N = 1 := by
  obtain ⟨d, hd⟩ := hc
  have h : ∃ e, e < N ∧ (c * e) % N = 1 := by
    refine ⟨d % N, Nat.mod_lt _ hN_pos, ?_⟩
    rw [Nat.mul_mod, Nat.mod_mod_of_dvd d dvd_rfl, ← Nat.mul_mod]
    exact hd
  unfold modInv
  rw [dif_pos h]
  exact h.choose_spec

/-- The chosen inverse is positive (an inverse of anything is never `0`,
    since `(c·0) % N = 0 ≠ 1`). -/
theorem modInv_pos (N c : Nat) (hN_pos : 0 < N) (hc : ∃ d, (c * d) % N = 1) :
    0 < modInv N c := by
  rcases Nat.eq_zero_or_pos (modInv N c) with h0 | h
  · have h_inv := (modInv_spec N c hN_pos hc).2
    rw [h0, Nat.mul_zero, Nat.zero_mod] at h_inv
    omega
  · exact h

/-! ## §2. Instance 1: the SQIR-faithful Cuccaro multiplier
       (`modmult_MCP_gate`, `Arithmetic/ModMult`). -/

/-- **The Cuccaro/SQIR modular multiplier as an `EncodeRoundTripModMul`.**

    Underlying verified gate: `modmult_MCP_gate bits N a ainv` — the
    SQIR-faithful in-place shift-and-add multiplier built from Cuccaro
    modular adders (`Arithmetic/ModMult/ModMultDef.lean`), with round-trip
    correctness `modmult_MCP_gate_apply_encode` and well-typedness
    `modmult_MCP_gate_wellTyped` at total dimension
    `bits + sqir_modmult_rev_anc bits`.

    Per constant `c`, the instance reduces the constant (`c % N`) and
    computes its inverse internally (`modInv N c`); the interface's
    invertibility guard supplies exactly the witness `modInv_spec` needs.
    Standing hypotheses: the standard sizing bundle
    `1 ≤ bits`, `0 < N`, `N ≤ 2^bits`, `2·N ≤ 2^bits`. -/
noncomputable def cuccaroMultiplier (bits N : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) :
    EncodeRoundTripModMul N bits (sqir_modmult_rev_anc bits) where
  gate := fun c => modmult_MCP_gate bits N (c % N) (modInv N c)
  wellTyped := fun c =>
    modmult_MCP_gate_wellTyped bits N (c % N) (modInv N c) hbits hN_pos hN hN2
  roundTrip := by
    intro c x hx hc
    obtain ⟨h_lt, h_inv⟩ := modInv_spec N c hN_pos hc
    have h_inv' : (c % N * modInv N c) % N = 1 := by
      rw [Nat.mod_mul_mod]; exact h_inv
    show Gate.applyNat (modmult_MCP_gate bits N (c % N) (modInv N c))
        (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) ((c * x) % N)
    rw [modmult_MCP_gate_apply_encode bits N (c % N) (modInv N c) x
          hbits hN_pos hN hN2 (Nat.le_of_lt h_lt) hx h_inv',
        Nat.mod_mul_mod]

/-- **One line to the framework family**: the Cuccaro multiplier as a
    `VerifiedModMulFamily` (QPE iterate `i` multiplies by `a^(2^i) mod N`),
    given a base inverse `a · ainv0 ≡ 1 (mod N)`. -/
noncomputable def cuccaroMultiplier_verifiedModMulFamily
    (bits N a ainv0 : Nat)
    (hbits : 1 ≤ bits) (hN1 : 1 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1) :
    VerifiedModMulFamily a N bits (sqir_modmult_rev_anc bits) :=
  (cuccaroMultiplier bits N hbits (by omega) hN hN2).toVerifiedModMulFamily
    a hN ainv0 hN1 h_inv0

/-- **One line to Shor**: the Cuccaro multiplier achieves the canonical Shor
    success-probability bound `≥ κ / (log₂ N)⁴`. -/
theorem cuccaroMultiplier_shor_correct
    (bits N a ainv0 r m : Nat)
    (hbits : 1 ≤ bits) (hN1 : 1 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (sqir_modmult_rev_anc bits)
        (cuccaroMultiplier_verifiedModMulFamily bits N a ainv0
          hbits hN1 hN hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  (cuccaroMultiplier_verifiedModMulFamily bits N a ainv0
    hbits hN1 hN hN2 h_inv0).shorCorrect r m h_setting

/-! ## §3. Instance 2: the Gidney ripple-carry multiplier
       (`modMultInPlaceShor`, `Arithmetic/ModMult/ShorOracle`). -/

/-- **The Gidney modular multiplier as an `EncodeRoundTripModMul`.**

    Underlying verified gate: `modMultInPlaceShor bits N a ainv multBits` —
    the Shor-layout wrapper (SWAP → in-place Gidney ripple-carry multiplier →
    SWAP, `Arithmetic/ModMult/ShorOracle/Def.lean`), with round-trip
    correctness `modMultInPlaceShor_correct` and well-typedness
    `modMultInPlaceShor_wellTyped` at total dimension
    `multBits + (adder_n_qubits (bits+1) + 1)`.

    Per constant `c`, the instance reduces the constant (`c % N`) and
    computes its inverse internally (`modInv N c`).  Unlike the Cuccaro
    chain, `modMultInPlaceShor_correct` additionally requires every
    shift-and-add table constant `(a·2^j) % N` (and its inverse-side
    analogue) to be nonzero, which holds because `c % N` and `N − modInv N c`
    are coprime to `N` and `2^j` is too — hence the extra standing
    hypotheses `1 < N` and `Nat.Coprime 2 N` (i.e. `N` odd, automatic for
    Shor moduli).  Sizing bundle: `1 ≤ bits`, `N ≤ 2^bits`,
    `0 < multBits ≤ bits + 1`, `N ≤ 2^multBits`. -/
noncomputable def gidneyMultiplier (bits N multBits : Nat)
    (hbits : 1 ≤ bits) (hN1 : 1 < N) (hN : N ≤ 2 ^ bits)
    (h_multBits_le : multBits ≤ bits + 1) (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2 ^ multBits)
    (h_cop_two : Nat.Coprime 2 N) :
    EncodeRoundTripModMul N multBits (adder_n_qubits (bits + 1) + 1) where
  gate := fun c => modMultInPlaceShor bits N (c % N) (modInv N c) multBits
  wellTyped := fun c =>
    modMultInPlaceShor_wellTyped bits N (c % N) (modInv N c) multBits
      hbits h_multBits_le h_multBits_pos
  roundTrip := by
    intro c x hx hc
    have hN_pos : 0 < N := by omega
    obtain ⟨d, hd⟩ := hc
    have h_cop_c : Nat.Coprime c N := coprime_of_mul_mod_one c d N hd
    obtain ⟨h_lt, h_inv⟩ := modInv_spec N c hN_pos ⟨d, hd⟩
    have h_inv' : (c % N * modInv N c) % N = 1 := by
      rw [Nat.mod_mul_mod]; exact h_inv
    have h_cop_cmod : Nat.Coprime (c % N) N :=
      (ZMod.coprime_mod_iff_coprime c N).mpr h_cop_c
    have h_cop_inv : Nat.Coprime (modInv N c) N :=
      coprime_inv_of_mul_mod_one (c % N) (modInv N c) N h_inv'
    -- Per-bit table constants are nonzero: `(c%N)·2^j` is coprime to `N`.
    have h_const_a : ∀ j, j < multBits → 0 < (c % N * 2 ^ j) % N := by
      intro j _
      apply coprime_mod_pos _ _ hN1
      apply Nat.Coprime.mul_left
      · exact h_cop_cmod
      · exact h_cop_two.pow_left j
    -- Inverse-side table constants: `N − modInv N c` is coprime to `N`.
    have h_const_inv : ∀ j, j < multBits →
        0 < ((N - modInv N c) % N * 2 ^ j) % N := by
      intro j _
      apply coprime_mod_pos _ _ hN1
      apply Nat.Coprime.mul_left
      · exact (ZMod.coprime_mod_iff_coprime _ _).mpr
          ((Nat.coprime_self_sub_left (Nat.le_of_lt h_lt)).mpr h_cop_inv)
      · exact h_cop_two.pow_left j
    show Gate.applyNat (modMultInPlaceShor bits N (c % N) (modInv N c) multBits)
        (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) x)
      = encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) ((c * x) % N)
    rw [modMultInPlaceShor_correct bits N (c % N) (modInv N c) multBits x
          hbits hN_pos hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
          (coprime_mod_pos c N hN1 h_cop_c) (Nat.mod_lt _ hN_pos)
          (modInv_pos N c hN_pos ⟨d, hd⟩) h_lt h_inv' hx
          h_const_a h_const_inv,
        Nat.mod_mul_mod]

/-- **One line to the framework family**: the Gidney multiplier as a
    `VerifiedModMulFamily` (QPE iterate `i` multiplies by `a^(2^i) mod N`),
    given a base inverse `a · ainv0 ≡ 1 (mod N)`. -/
noncomputable def gidneyMultiplier_verifiedModMulFamily
    (bits N multBits a ainv0 : Nat)
    (hbits : 1 ≤ bits) (hN1 : 1 < N) (hN : N ≤ 2 ^ bits)
    (h_multBits_le : multBits ≤ bits + 1) (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2 ^ multBits)
    (h_cop_two : Nat.Coprime 2 N)
    (h_inv0 : a * ainv0 % N = 1) :
    VerifiedModMulFamily a N multBits (adder_n_qubits (bits + 1) + 1) :=
  (gidneyMultiplier bits N multBits hbits hN1 hN h_multBits_le h_multBits_pos
      h_N_le_pow_multBits h_cop_two).toVerifiedModMulFamily
    a h_N_le_pow_multBits ainv0 hN1 h_inv0

/-- **One line to Shor**: the Gidney multiplier achieves the canonical Shor
    success-probability bound `≥ κ / (log₂ N)⁴`. -/
theorem gidneyMultiplier_shor_correct
    (bits N multBits a ainv0 r m : Nat)
    (hbits : 1 ≤ bits) (hN1 : 1 < N) (hN : N ≤ 2 ^ bits)
    (h_multBits_le : multBits ≤ bits + 1) (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2 ^ multBits)
    (h_cop_two : Nat.Coprime 2 N)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m multBits) :
    probability_of_success a r N m multBits (adder_n_qubits (bits + 1) + 1)
        (gidneyMultiplier_verifiedModMulFamily bits N multBits a ainv0
          hbits hN1 hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
          h_cop_two h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  (gidneyMultiplier_verifiedModMulFamily bits N multBits a ainv0
    hbits hN1 hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
    h_cop_two h_inv0).shorCorrect r m h_setting

end FormalRV.BQAlgo.MultiplierInstances
