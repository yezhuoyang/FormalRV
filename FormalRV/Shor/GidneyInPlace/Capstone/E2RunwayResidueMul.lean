/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayResidueMul — M1 DE-RISK SPIKE (attempt A).
  ════════════════════════════════════════════════════════════════════════════

  GOAL.  Determine whether a reversible `Gate` realizing `guardedShift` (RunwayShiftPerm.lean:33)
  is buildable, and build the CORE on-support decode lemma:

      data-block value  z + j·N   ↦   (c·z)%N + j·N   =  guardedShift D N c (z + j·N)
      (on support: z < N, j < 2^cm, budget 2^cm·N ≤ D = 2^bits), scratch restored, WellTyped.

  REGISTER LAYOUT (matches `windowedModNEncodeGate 1 bits N bits`, footprint `3·bits + 5`):
    • data block: wires `0..bits-1`, BIG-endian (`encodeDataZeroAnc` / `nat_to_funbool`):
        position `i` carries weight `2^(bits-1-i)`, value read by `decodeReg (fun i => bits-1-i) bits`.
    • ancilla   : wires `bits .. bits + (2·bits+5) - 1`, all clean (false) on input/output.
    The total dim is `D' = bits + (2·bits + 5) = 3·bits + 5 ≥ bits`.

  STRATEGY (prompt).  Three reversible stages: (A) DIVMOD-by-N v=z+jN ↦ (z | j-in-scratch);
  (B) residue multiply z ↦ (c·z)%N by REUSING the verified `windowedModNEncodeGate` (z<N ⇒ exact);
  (C) recombine = reverse of (A), restoring offset j·N onto the new residue and cleaning scratch.

  OUTCOME OF THIS SPIKE (see header note at bottom + the StructuredOutput report):
    • Stage (B) (residue multiply) is FULLY VERIFIED and reused from `windowedModNEncodeGate_apply`.
    • The `cm = 0` (single-block, j = 0) case of the FULL deliverable lemma is PROVED end-to-end,
      kernel-clean — it settles "a reversible Gate realizing guardedShift on-support is buildable
      and its decode lemma is provable" affirmatively, with the residue-multiply leg load-bearing.
    • The arithmetic identity for general `cm` is reduced to `guarded_on_support` and isolated.
    • The BLOCKER for general `cm` is the DIVMOD-by-N divider (Stage A/C): no off-the-shelf verified
      divmod-by-N exists (CuccaroModReduce.lean is a documented *blocker* file), so building it is the
      remaining Large work — characterized precisely below.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.WindowedModNShor
import FormalRV.Shor.GidneyInPlace.Ideal.Def.RunwayShiftPerm
import FormalRV.Shor.GidneyInPlace.Gate.Def.GatePerm

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayResidueMul

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.BQAlgo.MultiplierInstances (modInv modInv_spec)
open FormalRV.Shor.GidneyInPlace.RunwayShiftPerm (guardedShift guarded_on_support)
open FormalRV.Shor.WindowedCircuit (decodeReg_eq_mod_of_testBit)

/-! ## §0. Layout constants. -/

/-- Total dimension of the scratch register: data block `bits` + windowed ancilla `2·bits+5`. -/
abbrev dim' (bits : Nat) : Nat := bits + (2 * 1 + 2 * bits + 3)

/-- The on-support data-block encode at the windowed multiplier's layout: data value `v` in the
    top `bits` BIG-endian positions, zero ancilla (`2·bits+5` clean wires above). -/
abbrev encScratch (bits v : Nat) : Nat → Bool :=
  encodeDataZeroAnc bits (2 * 1 + 2 * bits + 3) v

/-- BIG-endian data-block reader matching `encScratch`: wire `i` carries weight `2^(bits-1-i)`. -/
abbrev decBE (bits : Nat) : Nat → Nat := fun i => bits - 1 - i

/-! ## §1. The on-support decode roundtrip: `decBE` reads `encScratch`'s value back.

`encScratch bits v` puts `v` BIG-endian in wires `0..bits-1`; the BIG-endian reader `decBE`
recovers exactly `v` (for `v < 2^bits`).  This pins the decode convention used in the headline. -/

/-- `decodeReg decBE bits (encScratch bits v) = v` for `v < 2^bits`. -/
theorem decBE_encScratch (bits v : Nat) (hv : v < 2 ^ bits) :
    decodeReg (decBE bits) bits (encScratch bits v) = v := by
  have h : ∀ i, i < bits → encScratch bits v (decBE bits i) = v.testBit i := by
    intro i hi
    show encodeDataZeroAnc bits (2 * 1 + 2 * bits + 3) v (bits - 1 - i) = v.testBit i
    rw [encodeDataZeroAnc_data hv (by omega),
        VerifiedShor.Windowed.nat_to_funbool_eq_testBit]
    congr 1
    omega
  rw [decodeReg_eq_mod_of_testBit (decBE bits) bits v (encScratch bits v) h,
      Nat.mod_eq_of_lt hv]

/-! ## §2. STAGE (B), FULLY VERIFIED: the residue-multiply leg (the part that works).

The verified `windowedModNEncodeGate 1 bits N bits c cinv` sends, on the support `z < N`,
the data block `z ↦ (c·z)%N`, with clean ancilla and well-typed at `dim' bits = 3·bits+5`.
This is a direct repackage of `windowedModNEncodeGate_apply` / `_wellTyped` in our `decBE` /
`encScratch` decode convention. -/

/-- **Residue-multiply leg (decode form).**  On the support `z < N`, the windowed multiplier
    realizes `z ↦ (c·z)%N` at the data block, read by `decBE`. -/
theorem residueMul_decode (bits N c cinv z : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hz : z < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1) :
    decodeReg (decBE bits) bits
        (Gate.applyNat (windowedModNEncodeGate 1 bits N bits c cinv) (encScratch bits z))
      = (c * z) % N := by
  have happ := windowedModNEncodeGate_apply 1 bits bits N c cinv z
    (by norm_num) (by omega) hbits hN_pos hN2 hz hcinv hinv
  -- `encScratch bits z = encodeDataZeroAnc bits (2*1+2*bits+3) z` definitionally.
  rw [show encScratch bits z = encodeDataZeroAnc bits (2 * 1 + 2 * bits + 3) z from rfl] at *
  rw [happ]
  exact decBE_encScratch bits _ (by
    have : (c * z) % N < N := Nat.mod_lt _ hN_pos
    omega)

/-- **Residue-multiply leg, well-typed at `dim' bits`.** -/
theorem residueMul_wellTyped (bits N c cinv : Nat) :
    Gate.WellTyped (dim' bits) (windowedModNEncodeGate 1 bits N bits c cinv) :=
  windowedModNEncodeGate_wellTyped 1 bits N bits c cinv (by norm_num) (by omega)

/-! ## §3. THE GATE + the headline decode lemma.

`guardedShiftGate` is, for the residue-multiply CORE, the verified windowed multiplier.  The full
M1 construction conjugates it by a DIVMOD-by-N gate (Stage A) and its reverse (Stage C) so the
offset `j·N` survives; that divider is the isolated blocker (see §5).  For `cm = 0` (the support is
a SINGLE block `j = 0`, input `= z < N`) NO divider is needed and the headline decode lemma holds
END-TO-END by reusing Stage (B). -/

/-- **The guarded-shift gate (residue-multiply core).**  At `cm = 0` this IS the realized
    `guardedShift` on the support; for `cm > 0` it must be wrapped by a divmod-by-N conjugation
    (Stage A / C) — the residue multiply itself is this gate. -/
def guardedShiftGate (bits cm N c cinv : Nat) : Gate :=
  windowedModNEncodeGate 1 bits N bits c cinv

/-- **HEADLINE (cm = 0 case of the full deliverable) — fully built, kernel-clean.**
    On the support `z + j·N` with `j < 2^0` (so `j = 0`), the gate realizes
    `guardedShift (2^bits) N c (z + j·N) = (c·z)%N + j·N` at the data block (read by `decBE`),
    leaves the scratch clean, and is well-typed at `dim' bits = 3·bits + 5`. -/
theorem guardedShiftGate_apply_on_support_cm0
    (bits N c cinv : Nat)
    (hbits : 1 ≤ bits) (hN : 1 < N) (hbudget : 2 ^ 0 * N ≤ 2 ^ bits) (h2N : 2 * N ≤ 2 ^ bits)
    (hcinv : cinv < N) (hinv : c * cinv % N = 1) (hc : c < N)
    (z j : Nat) (hz : z < N) (hj : j < 2 ^ 0) :
    decodeReg (decBE bits) bits
        (Gate.applyNat (guardedShiftGate bits 0 N c cinv) (encScratch bits (z + j * N)))
      = (c * z) % N + j * N
    ∧ guardedShift (2 ^ bits) N c (z + j * N) = (c * z) % N + j * N
    ∧ (∀ p, dim' bits ≤ p →
        Gate.applyNat (guardedShiftGate bits 0 N c cinv) (encScratch bits (z + j * N)) p
          = encScratch bits (z + j * N) p)
    ∧ Gate.WellTyped (dim' bits) (guardedShiftGate bits 0 N c cinv) := by
  have hN_pos : 0 < N := by omega
  have hj0 : j = 0 := by omega
  subst hj0
  have hzv : z + 0 * N = z := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- decode = (c·z)%N + 0·N = (c·z)%N  (Stage B verbatim)
    rw [hzv, show (c * z) % N + 0 * N = (c * z) % N from by ring]
    exact residueMul_decode bits N c cinv z hbits hN_pos h2N hz hcinv hinv
  · -- arithmetic identity from `guarded_on_support` at j = 0
    rw [show (c * z) % N + 0 * N = (c * z) % N from by ring]
    have := guarded_on_support (2 ^ bits) N 0 c z 0 hN_pos hz (by omega) (by simpa using hbudget)
    simpa using this
  · -- scratch / out-of-block frame: `applyNat` of a `dim'`-well-typed gate fixes `p ≥ dim'`
    intro p hp
    exact FormalRV.Shor.GidneyInPlace.GatePerm.applyNat_frame
      (guardedShiftGate bits 0 N c cinv) (dim' bits) (residueMul_wellTyped bits N c cinv) _ p hp
  · exact residueMul_wellTyped bits N c cinv

/-! ## §4. The GENERAL arithmetic target, reduced to `guarded_on_support`.

For ANY `cm`, the data-block VALUE the full gate must produce on the support is exactly
`guardedShift (2^bits) N c (z + j·N) = (c·z)%N + j·N` (under the full-blocks budget).  This is the
specification the divmod-wrapped gate must hit; it is settled purely arithmetically here, so the
ONLY remaining work for general `cm` is the reversible divider that separates `z` and `j`. -/

/-- **General arithmetic target (no circuit) — the value the full gate must produce.** -/
theorem guardedShift_target (bits cm N c z j : Nat)
    (hN : 0 < N) (hz : z < N) (hj : j < 2 ^ cm) (hbudget : 2 ^ cm * N ≤ 2 ^ bits) :
    guardedShift (2 ^ bits) N c (z + j * N) = (c * z) % N + j * N :=
  guarded_on_support (2 ^ bits) N cm c z j hN hz hj hbudget

/-! ## §5. THE BLOCKER for general `cm` (precise, with file:line evidence).

To preserve the offset `j·N` while multiplying only the residue `z`, the full gate must conjugate
the verified residue multiply (§2/§3) by a reversible DIVMOD-by-N stage:

  (A) `v = z + j·N  ↦  (z in data block | j in scratch)`   [needs verified divmod-by-N]
  (B) residue multiply  `z ↦ (c·z)%N`                       [DONE — `residueMul_decode`]
  (C) reverse of (A): repack `(c·z)%N + j·N`, cleaning scratch.

The divider is the crux and is NOT available off the shelf:
  • `CuccaroModReduce.lean` is a DOCUMENTED BLOCKER file: the clean exact-budget Cuccaro subtract
    "restores ALL non-target ancilla", so the borrow flag is NOT readable from a single qubit; a
    modular-reduction step needs an extra flag qubit and careful protocol
    (CuccaroSubConst.lean:146 `cuccaro_subConstGate_clean_state_loses_underflow_info`;
     CuccaroModReduce.lean:164 `cuccaro_subConstGate_not_modular_reduction`).
  • A full `cm`-step long division additionally needs an inductive partial-quotient/partial-
    remainder invariant across the `cm` compare+conditional-subtract iterations, plus a clean
    reverse leg — a multi-file verified gadget, not a spike-sized object.
  • The available `regCompareXor` (WindowedModN.lean:313) + `CuccaroSubConst`/`CuccaroAddConst`
    are exactly the per-step pieces; assembling+verifying the loop is the remaining (Large) work.

The arithmetic spec the assembled divmod must hit is pinned by §4 (`guardedShift_target`); the
residue leg it wraps is pinned by §2 (`residueMul_decode`).  Hence feasibility hinges SOLELY on a
verified reversible divmod-by-N. -/

end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayResidueMul
