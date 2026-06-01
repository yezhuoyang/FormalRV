import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRCondAdd

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate



/-! ## Tick 62 — Clean modular-add candidate definition. -/

/-- **Clean modular add-constant candidate** for `0 < c < N`.

Structure: dirty-flag candidate ; compareConst(c) ; X(flagPos).
The compareConst(c) XORs `decide(c ≤ (x+c) % N) = ¬decide(N ≤ x+c)`
into the flag, then X negates.  Net flag effect:
  `flag → ¬(flag XOR decide(N ≤ x+c) XOR ¬decide(N ≤ x+c))
        = ¬(flag XOR true)
        = flag`,
so the flag is restored.  The cleanup also re-touches the target /
read / carry workspace, but by the comparator's workspace_restored
property these end up at the same values as the dirty-flag stage.

**Caveat on `c = 0`:** `compareConst(0)` cannot be implemented in
`bits` bits because `K = 2^bits` overflows the read register.  For
`c = 0` the modular add is the identity and the dirty flag is
already `false`; the clean candidate is correct only for `0 < c`.
A wrapper that dispatches `c = 0` to identity is straightforward
but introduces a conditional gate structure (deferred). -/
def sqir_style_modAddConst_clean_candidate
    (bits q_start N c flagPos : Nat) : Gate :=
  seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
      (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
           (Gate.X flagPos))

/-! ## Tick 64 — Total clean SQIR mod-add-constant wrapper (including c = 0). -/

/-- **Deliverable A — total clean modular add-constant gate.**

Wraps the clean candidate (which requires `0 < c`) so that the `c = 0`
case dispatches to the identity gate.  This is the official clean
mod-add-constant primitive at the SQIR-faithful layout `q_start = 2,
flagPos = 1, dim = sqir_modmult_rev_anc bits`. -/
def sqir_style_modAddConst_clean_gate (bits N c : Nat) : Gate :=
  if c = 0 then Gate.I else sqir_style_modAddConst_clean_candidate bits 2 N c 1

/-! ## Tick 65 — Definitions: controlled compareConst, candidate, wrapper. -/

/-- **Controlled compareConst** — masked-prepare variant of
`sqir_style_compareConst_candidate`.  When `controlIdx = false`,
identity at every position; when `controlIdx = true`, equivalent to
`sqir_style_compareConst_candidate bits q_start c flagPos`. -/
def sqir_controlledCompareConst
    (bits q_start c controlIdx flagPos : Nat) : Gate :=
  seq (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)
      (seq (cuccaro_maj_chain bits q_start)
           (seq (Gate.CX (q_start + 2 * bits) flagPos)
                (seq (cuccaro_maj_chain_inv bits q_start)
                     (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx))))

/-- **Controlled SQIR-style mod-N add-constant candidate** for `0 < c`. -/
def sqir_style_controlledModAddConst_candidate
    (bits q_start N c controlIdx flagPos : Nat) : Gate :=
  seq (sqir_conditionalAddConstGate bits q_start c controlIdx)
      (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
           (seq (sqir_conditionalSubConstGate bits q_start N flagPos)
                (seq (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
                     (Gate.CX controlIdx flagPos))))

/-- **Total controlled SQIR mod-N add-constant** wrapper handling `c = 0`. -/
def sqir_style_controlledModAddConst_gate
    (bits q_start N c controlIdx flagPos : Nat) : Gate :=
  if c = 0 then Gate.I
  else sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos

/-! ## Status note (Tick 60).

Landed in this tick (all kernel-clean except as noted):
- `sqir_style_modAddConst_dirtyFlag_read_decode` (Deliverable A.1).
- `sqir_style_modAddConst_dirtyFlag_carry_in_restored` (Deliverable A.2).
- `sqir_style_modAddConst_dirtyFlag_flag_value` (Deliverable A.3).
- `sqir_style_modAddConst_dirtyFlag_candidate_wellTyped_sqir_dim`
  (Deliverable B).
- `sqir_style_modAddConst_dirtyFlag_clean_except_flag` (Deliverable C):
  full 5-conjunct bundle.
- `sqir_style_modAddConst_dirtyFlag_candidate_wellTyped_sqir_layout`
  (Deliverable D, partial — WellTyped only).
- `BasicSetting_twoN_le_pow_succ` (Deliverable E): the sizing relation,
  expressed for `bits := n + 1`.

Honesty disclosures:
- **Flag remains dirty.** The bundle theorem name includes
  `clean_except_flag` and the 5th conjunct states the flag's value.
  This is NOT clean modular addition.
- **Semantic theorems require `h_flag_above`.**  The SQIR-style
  comparator's flag theorem was set up with the flag above workspace;
  extending to below-workspace flag (as in SQIR's exact layout with
  flagPos = 1 < q_start = 2) is deferred.  WellTyped at the SQIR-exact
  layout IS proved (Deliverable D, partial).
- **Sizing is `bits = n + 1`.** Deliverable E shows `2 * N ≤ 2^(n+1)`
  follows from `N < 2^n` (the upper half of `BasicSetting`).  The other
  half `2^n ≤ 2 * N` is NOT used by the modadd primitive; it constrains
  Shor's m-precision register, not the mod-N add's bit width.  Future
  Shor integration should instantiate `bits := n + 1`.
- **Original SQIR placeholder axioms NOT YET CLOSED.**
  `f_modmult_circuit`, `f_modmult_circuit_MMI`, and
  `f_modmult_circuit_uc_well_typed` remain untouched.

Next steps (Tick 61+):
1. Below-workspace flag adaptation for `compareConst`'s flag and
   workspace theorems — enables target_decode + workspace at the
   SQIR-exact layout (flagPos = 1 < q_start = 2).
2. Flag uncomputation design — the path from dirty-flag mod-N add to
   clean mod-N add.  Candidate: rerun the comparator on the final
   output `(x+c) % N` (which is `< N`), so the comparator returns
   `decide(N ≤ (x+c)%N) = false`, XORing the dirty flag back to false.
3. Controlled mod-N add (Phase 3 of the modarith-to-modexp plan). -/

end FormalRV.BQAlgo
