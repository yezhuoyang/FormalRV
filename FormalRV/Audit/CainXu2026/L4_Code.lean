/-
  Audit · cain-xu-2026 · LAYER 4 — THE qLDPC CODE (lifted-product / bivariate-bicycle)
  ----------------------------------------------------------------------------
  The code parameters are DERIVED from the constructed parity matrices (not
  asserted): k = n − rank H_X − rank H_Z via the GF(2)-rank algorithm.
    • bb18  = [[248,10,18]]   (k = 10 DERIVED, native_decide)
    • lp_20 = [[4350,1224,20]] (k = 1224 DERIVED, native_decide)
  ✅ = verify-clean semantic; ➗ = native_decide numeric (the rank-based k at scale).

  This is the LOW code layer.  It also carries:
    • the recorded (algorithm, code, hardware) tuple `cainxu_instance`
      (so the data lives in one low place; L1/Hardware re-present their slice);
    • the `ResourceBounds` machinery (qubit/time lower + upper bounds and the
      soundness lemmas, was `QianxuBounds`) — the FULL-LP resource brackets and
      the verifier's lower-≤-upper gates rest on these defs, so they live low.

  ONE flat namespace `FormalRV.Audit.CainXu2026`.
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge
import FormalRV.QEC.Instances
import FormalRV.QEC.CodeDimension   -- general helper `derivedK` (k = n − rank Hx − rank Hz)
import FormalRV.QEC.GF2Rank
import FormalRV.Framework.ResourceBounds
import FormalRV.System.DependencyGraph
import FormalRV.Audit.CainXu2026.Hardware

namespace FormalRV.Audit.CainXu2026

open FormalRV.Framework FormalRV.Qualtran
open FormalRV.QEC.Instances
open FormalRV.QEC   -- brings the general `derivedK`
open FormalRV.Framework.LDPC
open FormalRV.Framework.Resource
open FormalRV.System.DependencyGraph

/-============================================================================
  PART A — The recorded parametric tuple (was CainXu)
============================================================================-/

/-- The Cain–Xu Shor instance: factor an RSA-2048 modulus with `q_A = 33`
Ekerå–Håstad windows (qianxu p. 5).  The `N` literal is placeholder — the
parametric review applies to any 2048-bit composite the paper instantiates. -/
def cainxu_shor : ShorAlgorithm :=
  { N := 0, q_A := 33 }

/-- The Cain–Xu LP qLDPC code: bivariate-bicycle `[[144, 12, 12]]` instance
(qianxu Sec. 3).  Parity-check matrices placeholder `[]` here — the explicit
matrix encoding is the real `bb18` / `lp20` constructions below. -/
def cainxu_code : QECCode :=
  { n := 144, k := 12, d := 12, hx := [], hz := [] }

/-- The full parametric tuple for the Cain–Xu corpus instance. -/
def cainxu_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (cainxu_shor, cainxu_code, cainxu_hw)

/-- Smoke: paper-stated parameters read back correctly through the tuple.
q_A = 33 (qianxu p. 5); (n,k,d) = (144,12,12) (qianxu Sec. 3);
physical_error = 1e-3 (Bluvstein). -/
example : cainxu_instance.1.q_A = 33 := by rfl
example : cainxu_instance.2.1.n = 144 ∧
          cainxu_instance.2.1.k = 12 ∧
          cainxu_instance.2.1.d = 12 := by exact ⟨rfl, rfl, rfl⟩
example : cainxu_instance.2.2.physical_error_thousandths = 1 := by rfl

/-- Helper: build a `length-n` `Bool` vector from a list of non-zero positions. -/
def makeRow (positions : List Nat) (n : Nat) : List Bool :=
  (List.range n).map (fun i => positions.contains i)

/-- The first X-type stabilizer of the BB `[[144, 12, 12]]` code with the
Bravyi-style choice `A = x³ + y + y²` / `B = y³ + x + x²` — weight 6, showing the
framework can carry real parity-check matrix rows. -/
def bb_first_x_check : List Bool :=
  makeRow [1, 2, 18, 75, 78, 84] 144

example : bb_first_x_check.length = 144 := by native_decide
example : (bb_first_x_check.filter id).length = 6 := by native_decide

/-============================================================================
  PART B — bb18 [[248,10,18]]: k DERIVED from the constructed matrices
           (was QianxuCodeParams)
============================================================================-/

/-- **bb18's k = 10, DERIVED from its constructed matrices** (n=248, rank H_X =
    rank H_Z = 119), matching the paper's `[[248,10,18]]`.  Not hardcoded —
    computed from `bb18.hx`/`bb18.hz` by the GF(2)-rank algorithm.

    Certificate: `native_decide` (kernel `decide` times out at 248 qubits); this
    adds a native-eval axiom — the k VALUE is derived, the CERTIFICATE is native. -/
theorem bb18_k_derived : derivedK bb18 = 10 := by
  unfold derivedK; native_decide

/-- bb18's n is kernel-clean (the easy half); only the rank-based k needs native. -/
theorem bb18_n : bb18.n = 248 := by decide

/-- The derived k matches the paper's reported logical count for bb18. -/
theorem bb18_k_matches_paper : derivedK bb18 = 10 := bb18_k_derived

/-============================================================================
  PART C — ResourceBounds machinery (was QianxuBounds)
============================================================================-/

/-! ## §C.1. Naive constructions' costs (qianxu's two undetailed pieces, filled in) -/

/-- Memory blocks needed to hold `q_A` live logical qubits at code rate `k_m`. -/
def memoryBlocks (q_A k_m : Nat) : Nat := (q_A + k_m - 1) / k_m

/-- QUBIT lower bound (irreducible data block): the live logicals MUST be encoded. -/
def qubitLower (q_A n_m k_m : Nat) : Nat := memoryBlocks q_A k_m * n_m

/-- QUBIT upper bound (naive zoned build, no sharing): memory + processor +
    3·factory + operation-zone ancilla + reservoir. -/
def qubitUpper (N_m N_p N_f N_A N_res : Nat) : Nat := N_m + N_p + 3 * N_f + N_A + N_res

/-- Per-Toffoli cost in µs: τ_s surgery cycles × cycle time. -/
def perToffoli (tau_s cycle : Nat) : Nat := tau_s * cycle

/-- TIME lower bound (irreducible critical path): Toffoli DEPTH × per-Toffoli. -/
def timeLower (depth tau_s cycle : Nat) : Nat := depth * perToffoli tau_s cycle

/-- TIME upper bound (naive sequential, no parallelisation): Toffoli COUNT ×
    per-Toffoli. -/
def timeUpper (toff tau_s cycle : Nat) : Nat := toff * perToffoli tau_s cycle

/-! ## §C.2. Soundness — the lower bounds never exceed the naive upper bounds -/

/-- QUBIT: the data block fits within the naive zoned build, provided the memory
    zone `N_m` actually covers the required blocks. -/
theorem qubit_lower_le_upper (q_A n_m k_m N_m N_p N_f N_A N_res : Nat)
    (hmem : qubitLower q_A n_m k_m ≤ N_m) :
    qubitLower q_A n_m k_m ≤ qubitUpper N_m N_p N_f N_A N_res := by
  unfold qubitUpper; omega

/-- TIME: depth ≤ count ⇒ the critical-path floor ≤ the naive sequential ceiling. -/
theorem time_lower_le_upper (depth toff tau_s cycle : Nat) (h : depth ≤ toff) :
    timeLower depth tau_s cycle ≤ timeUpper toff tau_s cycle := by
  unfold timeLower timeUpper
  exact Nat.mul_le_mul_right _ h

/-! ## §C.3. The TIME lower bound holds for ALL schedules (critical path) -/

/-- For ANY start-time schedule `begin_` of the modexp critical path (each Toffoli
    taking at least `perToffoli` and depending on the previous), the depth-th
    Toffoli finishes no earlier than `begin_ 0 + timeLower depth …` — no
    parallelism beats the critical path. -/
theorem time_floor_all_schedules (depth tau_s cycle : Nat) (begin_ : Nat → Nat)
    (hdep : ∀ i, begin_ i + perToffoli tau_s cycle ≤ begin_ (i + 1)) :
    begin_ 0 + timeLower depth tau_s cycle ≤ begin_ depth :=
  runtimeFloor_is_lower_bound (perToffoli tau_s cycle) begin_ hdep depth

/-! ## §C.4. qianxu instances (lp_20^{3,7} memory: [[4350, 1224, 20]]) + the GAP -/

/-- QUBIT bounds for a discrete-log-scale instance (q_A = 512 live logicals;
    memory lp_20^{3,7}; processor N_p = 1000; one factory bank 2565; N_𝒜 = 894;
    reservoir 900), against qianxu's ~10,000-qubit headline. -/
def qianxu_qubit_bounds : ResourceBounds :=
  { lower    := qubitLower 512 4350 1224          -- 1 block × 4350 = 4350
    upper    := qubitUpper 4350 1000 2565 894 900 -- 4350+1000+7695+894+900 = 14,839
    reported := 10_000 }

theorem qianxu_qubit_bracketed : qianxu_qubit_bounds.bracketed = true := by decide

theorem qianxu_qubit_gap : qianxu_qubit_bounds.optimizationGap = 4_839 := by decide

theorem qianxu_qubit_floor : qianxu_qubit_bounds.lower = 4350 := by decide

/-- TIME bounds: naive SEQUENTIAL upper vs critical-path lower, for a modexp of
    Toffoli count `T = 10^6` and depth `D = 10^4` (carry-chain), τ_s = 13,
    cycle = 1000 µs.  Reported = qianxu's parallel figure (D-limited). -/
def qianxu_time_bounds : ResourceBounds :=
  { lower    := timeLower 10_000 13 1000        -- 10^4 · 13 · 1000 = 1.3×10^8 µs
    upper    := timeUpper 1_000_000 13 1000     -- 10^6 · 13 · 1000 = 1.3×10^10 µs
    reported := 130_000_000 }

theorem qianxu_time_bracketed : qianxu_time_bounds.bracketed = true := by decide

theorem qianxu_time_gap : qianxu_time_bounds.optimizationGap = 12_870_000_000 := by decide

theorem qianxu_time_respects_floor : qianxu_time_bounds.respectsFloor = true := by decide

/-============================================================================
  PART D — FULL LP-code logical counts + resource brackets (was QianxuFullLP)
============================================================================-/

/-! ## §D.1. FULL LP-code logical-qubit counts, DERIVED from the matrices -/

/-- **lp_16^{3,7}: k = 744, derived from the parity matrices** (n=2610, rank H_X =
    rank H_Z = 933), matching the paper's [[2610, 744, 16]].  Certified by
    `native_decide` (kernel `decide` times out at this scale). -/
theorem lp16_k_derived : lp16.n - rank lp16.hx - rank lp16.hz = 744 := by native_decide

def lp20_n : Nat := 4350

/-- **lp_20^{3,7}: k = 1224, DERIVED from the parity matrices** (n=4350), matching
    the paper's [[4350,1224,20]].  Certified by `native_decide` (kernel `decide`
    times out at 4350 columns; native adds a native-eval axiom, flagged). -/
theorem lp20_k_derived : lp20.n - rank lp20.hx - rank lp20.hz = 1224 := by native_decide

def lp20_k : Nat := 1224   -- now backed by `lp20_k_derived` (native_decide), matches paper
def lp20_d : Nat := 20

/-! ## §D.2. Resource bounds + GAPS for the FULL lp_20 memory instance -/

/-- QUBIT bounds for the full lp_20 instance.  Lower = one memory block (4350
    holds k=1224 logicals); upper = the naive zoned build with the REAL
    code/factory/ancilla sizes; reported = qianxu's ~10,000-qubit headline. -/
def lp20_qubit_bounds : ResourceBounds :=
  { lower    := qubitLower 1224 4350 1224              -- ⌈1224/1224⌉·4350 = 4350
    upper    := qubitUpper 4350 1122 2565 894 900      -- 4350+1122+7695+894+900 = 14,961
    reported := 10_000 }

theorem lp20_qubit_bracketed : lp20_qubit_bounds.bracketed = true := by decide

/-- **QUBIT GAP (full lp_20 code): 4,961** — the factory-sharing / multi-block
    packing the paper claims but we do not construct. -/
theorem lp20_qubit_gap : lp20_qubit_bounds.optimizationGap = 4_961 := by decide

/-- TIME bounds for the full lp_20 instance: modexp Toffoli count `T = 10^9`,
    depth `D = 10^6`, τ_s=13, 1 ms cycle.  Reported = qianxu's parallel figure. -/
def lp20_time_bounds : ResourceBounds :=
  { lower    := timeLower 1_000_000 13 1000        -- 10^6 · 13 · 1000 = 1.3×10^10 µs
    upper    := timeUpper 1_000_000_000 13 1000    -- 10^9 · 13 · 1000 = 1.3×10^13 µs
    reported := 13_000_000_000 }

theorem lp20_time_bracketed : lp20_time_bounds.bracketed = true := by decide

/-- **TIME GAP (full lp_20 code): 12,987×10^9 µs** — the ~1000× parallelisation
    the paper does not construct in detail. -/
theorem lp20_time_gap : lp20_time_bounds.optimizationGap = 12_987_000_000_000 := by decide

/-! ## §D.3. The headline -/

/-- **FULL LP-CODE REPORT.**  The paper's lp_16 logical count is DERIVED (=744),
    the qubit resource of the full lp_20 instance is bracketed [4350, 14961] with a
    4961 optimization gap, and the time is bracketed with a ~1000× parallelisation
    gap. -/
theorem full_lp_report :
    lp16.n - rank lp16.hx - rank lp16.hz = 744
    ∧ lp20_qubit_bounds.bracketed = true ∧ lp20_qubit_bounds.optimizationGap = 4_961
    ∧ lp20_time_bounds.bracketed = true := by
  refine ⟨lp16_k_derived, lp20_qubit_bracketed, lp20_qubit_gap, lp20_time_bracketed⟩

end FormalRV.Audit.CainXu2026

#check @FormalRV.Audit.CainXu2026.cainxu_code           -- QECCode (LP qLDPC tile)
-- ➗ k DERIVED from the constructed matrices via GF(2) rank (native_decide):
#check @FormalRV.Audit.CainXu2026.bb18_k_derived        -- bb18 k = 10
#check @FormalRV.Audit.CainXu2026.lp20_k_derived        -- lp_20 k = 1224
