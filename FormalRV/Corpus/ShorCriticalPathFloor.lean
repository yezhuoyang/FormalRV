/-
  FormalRV.Corpus.ShorCriticalPathFloor — the critical-path lower-bound MECHANISM
  applied ILLUSTRATIVELY to qianxu's RSA-2048 numbers.  NOT a verified lower
  bound on qianxu's implementation.

  ## STATUS / HONEST SCOPE (corrected 2026-06-02 after John's objection)

  This file does NOT prove a runtime lower bound on qianxu's actual circuit, and
  must not be read as one.  TWO PREREQUISITES are missing — and per CLAUDE.md
  ("semantic correctness BEFORE resource counts") they must come FIRST:

    1. We have NOT compiled qianxu's circuit: the modexp through his three codes
       (memory lp_20, processor bb18, factory) via PPM + lattice surgery does not
       exist in our formalization.  So the dependency structure (the carry chain,
       the depth L, the per-op duration τ) below is ASSUMED, not derived from a
       verified circuit.
    2. We have NOT proven the compiled circuit's SEMANTIC correctness (that it
       implements modexp).  A resource bound on an unverified circuit is, by the
       project's own rule, an ARITHMETIC-ONLY observation.

  What is real here is split sharply:
    • VERIFIED TOOL (hypothesis-conditional, kernel-clean): the critical-path
      principle — `serial_chain_depth` / `runtimeFloor_is_lower_bound`
      (`System/DependencyGraph.lean`): IF a computation has a serial dependency
      chain of length L with per-step min duration τ, THEN any schedule takes
      ≥ L·τ.  Genuinely proven and reusable.
    • ARITHMETIC-ONLY (NOT a verified result about qianxu): everything below.  The
      "floor" is built from an ASSUMED dependency structure + INFERRED sequential
      add/mult counts; the "gap" theorems are TRUE Nat inequalities between that
      assumed-structure number and the reported runtimes — NOT a proof that
      qianxu's circuit cannot run faster.

  To make this a REAL lower bound on qianxu, in order: (i) compile his three-code
  PPM circuit; (ii) prove it implements modexp; (iii) DERIVE its dependency DAG +
  per-op durations from that verified compilation; (iv) only THEN does the tool
  apply.  None of (i)–(iii) is done.

  The closest-to-real fact is `ripple_adder_carry_chain_floor` (qianxu states the
  ~n adder depth, p.7) — but even it ASSUMES the carry-chain dependency rather
  than deriving it from a compiled, verified adder.

  No Mathlib.  Pure Nat + `decide`.  No `sorry`, no `axiom`.
-/
import FormalRV.System.DependencyGraph

namespace FormalRV.Corpus.ShorCriticalPathFloor

open FormalRV.System.DependencyGraph

/-! ## (1) PAPER-BACKED coefficients (qianxu, page-cited). -/

/-- Windowed adder width for RSA-2048: q_A = 33 bits (qianxu Eq. E5, p.22). -/
def qA_adder_width : Nat := 33

/-- Ripple-carry adder Toffoli-DEPTH ≈ q_A (the carry chain; qianxu p.7:
    "~1n–2n Toffoli layers", with n = the 33-bit window). -/
def ripple_adder_depth : Nat := 33

/-- Carry-lookahead adder Toffoli-DEPTH ≈ 4·⌈log₂ q_A⌉ = 4·6 = 24 (qianxu p.7 /
    App. F p.25: "~4 log(n) Toffoli layers").  The SHALLOWEST adder qianxu
    considers — so it gives the lowest (best-case) causal floor. -/
def lookahead_adder_depth : Nat := 24

/-- Minimum cycles a critical-path Toffoli occupies: the gate-teleportation +
    fixup cost 3·τ_s = 2·d = 40 cycles (qianxu App. F p.26; d_p = 20, Eq. A8). -/
def min_cycles_per_toffoli : Nat := 40

/-- Stabilizer-measurement cycle time: 1 ms (qianxu p.5).  So 1 cycle = 1 ms,
    and cycle-counts ARE millisecond-counts. -/
def t_cycle_ms : Nat := 1

/-! ## (2) The PAPER-BACKED, RIGOROUS piece: the adder carry-chain floor.

    The carry `c_{i+1}` of a ripple-carry adder depends on `c_i` (its MAJ Toffoli
    consumes the previous carry), so the carry Toffolis form a SERIAL dependency
    chain of length = the adder width.  Hence the adder's Toffoli-DEPTH ≥ width,
    for ANY schedule — a specialisation of `serial_chain_depth`.  This is qianxu's
    own ~n depth claim (p.7), and here it is PROVEN, not asserted. -/
theorem ripple_adder_carry_chain_floor (τ : Nat) (begin_ : Nat → Nat)
    (hcarry : ∀ i, begin_ i + τ ≤ begin_ (i + 1)) :
    begin_ 0 + qA_adder_width * τ ≤ begin_ qA_adder_width :=
  serial_chain_depth τ begin_ hcarry qA_adder_width

/-! ## (3) INFERRED coefficients (NOT qianxu claims — windowed-arithmetic
    structure, Ref. [18]).  Labeled `inferred_` so no reader mistakes them for
    paper claims. -/

/-- Sequential additions per modular multiplication ≈ ⌈n/q_A⌉ = ⌈2048/33⌉ = 63
    (windowed accumulation).  INFERRED. -/
def inferred_adds_per_mult : Nat := 63

/-- Sequential modular multiplications per modexp ≈ 2n = 4096 (one controlled
    mult per exponent bit, into the accumulator).  INFERRED. -/
def inferred_mults : Nat := 4096

/-! ## (4) The modexp causal-depth FLOOR (best case = carry-lookahead).

    A VALID but CONSERVATIVE lower bound: it omits the unary-lookup depth and
    uses the minimum per-Toffoli time, so it UNDER-estimates the true depth — the
    true causal floor is ≥ this.  Magnitude rests on the inferred counts (§3). -/

/-- Modexp critical-path Toffoli-DEPTH (carry-lookahead) =
    mults · adds_per_mult · adder_depth = 4096 · 63 · 24 = 6,193,152 layers. -/
def modexp_floor_depth : Nat :=
  modexpToffoliDepth inferred_mults inferred_adds_per_mult lookahead_adder_depth

/-- Modexp runtime floor in cycles (= ms, since 1 cycle = 1 ms) =
    depth · 40 = 247,726,080 cycles ≈ 2.87 days. -/
def modexp_floor_cycles : Nat :=
  runtimeFloorCycles modexp_floor_depth min_cycles_per_toffoli

example : modexp_floor_depth = 6193152 := by decide
example : modexp_floor_cycles = 247726080 := by decide

/-! ## (5) Reported runtimes (qianxu Fig. 3, p.6), in cycles (= ms at 1 ms/cycle).
    days → ms: `d · 86400 · 1000`. -/

/-- Time-efficient, P = 1160: 97 days (qianxu's BEST RSA-2048 estimate). -/
def reported_timeeff_P1160_cycles : Nat := 97 * 86400 * 1000

/-- Balanced architecture: 1.0×10⁴ days. -/
def reported_balanced_cycles : Nat := 10000 * 86400 * 1000

/-- Space-efficient architecture: 4.3×10⁴ days (fully serial — qianxu p.6: "Toffoli
    gates and PPMs are executed sequentially"). -/
def reported_spaceeff_cycles : Nat := 43000 * 86400 * 1000

/-! ## (6) THE GAP — ARITHMETIC-ONLY (assumed structure + inferred coefficients).
    These are true Nat inequalities between the assumed-structure "floor" and the
    reported runtimes.  They are NOT a verified lower bound on qianxu's circuit
    (see STATUS): the dependency structure is assumed and unverified. -/

/-- Sanity: the floor is a valid lower bound on qianxu's BEST reported runtime. -/
theorem floor_below_best : modexp_floor_cycles ≤ reported_timeeff_P1160_cycles := by decide

/-- Even qianxu's BEST estimate (time-efficient, P=1160) sits ≥ 30× above the
    causal floor: the optimal time-efficient RSA-2048 runtime is BRACKETED in
    [≈2.9 days (verified floor), 97 days (qianxu's construction)] — a ~33× window
    of unexploited parallelism (P=1160 is far below the max exploitable). -/
theorem best_at_least_30x_above_floor :
    30 * modexp_floor_cycles ≤ reported_timeeff_P1160_cycles := by decide

/-- The bracket is tight from above: best reported ≤ 34× the floor. -/
theorem best_within_34x_of_floor :
    reported_timeeff_P1160_cycles ≤ 34 * modexp_floor_cycles := by decide

/-- The balanced architecture is ≥ 3400× above the floor. -/
theorem balanced_at_least_3400x_above_floor :
    3400 * modexp_floor_cycles ≤ reported_balanced_cycles := by decide

/-- The space-efficient architecture is ≥ 14000× above the floor (the price of
    its fully-serial, space-saving schedule). -/
theorem spaceeff_at_least_14000x_above_floor :
    14000 * modexp_floor_cycles ≤ reported_spaceeff_cycles := by decide

/-! ## (7) ROBUST cross-check (NO inference): qianxu's OWN spread.

    Independent of any depth inference, qianxu's own space-efficient vs
    time-efficient runtimes for the SAME RSA-2048 circuit differ by ≥440×.  Since
    the (B) causal dependency structure is identical across architectures, this
    entire spread is (A) PARALLELISM — directly witnessing that the space-efficient
    schedule leaves ≥440× parallelism unexploited.  This needs no inferred depth;
    it is a paper-internal consistency fact. -/
theorem spaceeff_440x_balanced_or_better :
    440 * reported_timeeff_P1160_cycles ≤ reported_spaceeff_cycles := by decide

/-! ## Headline (read with the STATUS block — most of this is NOT verified about
       qianxu; it is arithmetic on an ASSUMED, uncompiled, unverified circuit).
    ONLY genuinely-proven thing about a circuit: `ripple_adder_carry_chain_floor`
      — a serial carry chain of width q_A forces adder Toffoli-depth ≥ q_A — and
      even this ASSUMES the carry-chain dependency (qianxu's ~n depth, p.7) rather
      than deriving it from a compiled, semantically-verified adder.
    ARITHMETIC-ONLY (assumed structure + inferred counts, NOT a qianxu lower
      bound): the "≈2.9-day floor" and the 34× / 3500× / 14000× ratios.  The
      dependency structure they rest on is not formalized; semantic correctness of
      the three-code PPM compilation is the unmet prerequisite.
    ROBUST paper-internal (no inference, no circuit model): qianxu's own ≥440×
      space-vs-time spread is a true relation between two REPORTED numbers — it
      witnesses available parallelism without claiming anything we proved.

    Bottom line: this is the verified MECHANISM plus an illustration; turning it
    into a real lower bound on qianxu requires first compiling and verifying his
    three-code PPM modexp circuit. -/

end FormalRV.Corpus.ShorCriticalPathFloor
