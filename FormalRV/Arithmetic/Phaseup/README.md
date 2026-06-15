# Phaseup (Gidney 2025)

The reusable **phaseup** gadget is Gidney 2025's third arithmetic subroutine: a phase-gradient **table lookup** that applies the table-indexed diagonal phase `(−1)^(ctrl ∧ F(addr))` to a basis state whose address wires hold the query `addr`, at **SELECT-SWAP √-cost** `O(2^(w/2))` instead of the linear `O(2^w)` of a full table read. The same subroutine is shared by the **Pinnacle** factoring pipeline. Import `FormalRV.Arithmetic.Phaseup` to get the whole verified gadget (defs + diagonal-phase correctness + end-to-end channel corollary + Toffoli counts with the √-advantage as a theorem) as the single public entry point any paper audit can use.

Phaseup is a **diagonal operator at the amplitude / `BaseUCom` layer** — it stamps a phase, it does **not** flip any Boolean wire. So its correctness is a statement about `uc_eval (phaseup …) * |f⟩`, NOT a Boolean `applyNat` equation. The phase mechanism is **not re-proved here**: `phaseup` wraps the verified `FormalRV.Shor.SplitPhaseFixup.splitPhaseLookup`, and every correctness / count theorem re-exports a `SplitPhaseFixup` / `PhaseLookupFixup` headline under the gadget's public name.

## The spine — where everything lives
| Aspect | File | Headline theorem |
|---|---|---|
| Defs | `PhaseupDef` | `phaseup` (√-cost SELECT-SWAP), `phaseupFull` (unsplit full read), `phaseupSkeleton` / `phaseupFullSkeleton` (Gate-level T-content twins) |
| Correctness (phase action) | `PhaseupCorrectness` | `phaseup_diagonal` (phase `(−1)^(ctrl ∧ F(addr))`, decoder form), `phaseup_diagonal_addr` (address form, `(−1)^(F v)`) |
| Correctness (end-to-end channel) | `PhaseupCorrectness` | `measWordUncompute_phaseup` (phaseup as the per-bit fixup of the measured lookup-uncompute = perfect uncompute at √-cost) |
| Resource (counts + √-advantage) | `PhaseupResource` | `toffoli_phaseup` (= `4·(2^w1−1)+2·(2^w2−1)`), `toffoli_phaseupFull` (= `2·(2^w−1)`), `phaseup_toffoli_sqrt` (split ≤ full), `phaseup_toffoli_sqrt_strict`/`_balanced` |
| Example | `Example.lean` | `#eval` split-vs-full Toffoli counts (18 vs 30 at w=4; 90 vs 510 at w=8) + `decide`-checked counts + `phaseup_diagonal_addr` runs |

## The exact headline statements

```lean
-- diagonal phase action (the load-bearing correctness)
theorem phaseup_diagonal (dim w1 w2 base : Nat) (F : Nat → Bool) (f : Nat → Bool)
    (hbase : 2 * (w1 + w2) < base) (hdim : base + 2 ^ w1 ≤ dim)
    (hand : ∀ i, i < w1 + w2 → f (ulookup_and_idx i) = false)   -- AND-ladder clean
    (hhot : ∀ h, h < 2 ^ w1 → f (base + h) = false) :            -- one-hot ancillas clean
    uc_eval (phaseup dim F w1 w2 base) * f_to_vec dim f
      = (if f ulookup_ctrl_idx && F (decAddr (w1 + w2) f) then (-1 : ℂ) else 1)
          • f_to_vec dim f

-- the √-cost
theorem toffoli_phaseup (w1 w2 base : Nat) :
    toffoliCount (phaseupSkeleton w1 w2 base) = 4 * (2 ^ w1 - 1) + 2 * (2 ^ w2 - 1)

-- the √-advantage, as a theorem (split ≤ full table read, for w2 ≥ 1)
theorem phaseup_toffoli_sqrt (w1 w2 base : Nat) (hw2 : 1 ≤ w2) :
    toffoliCount (phaseupSkeleton w1 w2 base)
      ≤ toffoliCount (phaseupFullSkeleton (w1 + w2))
```

## What the gadget is — the SELECT-SWAP √-cost

The address `addr = hi‖lo` is split into the **high `w1` levels** (`hi`) and the **low `w2` levels** (`lo`), with `w = w1 + w2`. A linear table read costs `2·(2^w − 1)` Toffolis. The phaseup instead runs three stages on a one-hot ancilla register (`2^w1` wires at `base + h`):

1. **One-hot the hi half** (SELECT) — a Gray-code read over the high `w1` address levels writes the one-hot marker `ctrl ∧ [addr_hi = h]` into the `2^w1` ancilla wires. Cost `2·(2^w1 − 1)` Toffoli.
2. **CZ-leaf phase walk over the lo half** (SWAP) — a `phaseWalk`-shaped walk over the low `w2` levels whose leaf for lo-row `ℓ` applies `CZ(ladderTop, base + h)` for every `h` with `F(h·2^w2 + ℓ)` set. Exactly one `(ℓ, h)` pair fires, so the product telescopes to the single phase `(−1)^(ctrl ∧ F(addr))`. Cost `2·(2^w2 − 1)` Toffoli; **all CZs are Clifford (T-free)**.
3. **Un-one-hot the hi half** — stage 1 again (the leaf word-CNOTs are self-inverse). Cost `2·(2^w1 − 1)` Toffoli.

Total `= 4·(2^w1 − 1) + 2·(2^w2 − 1) = 4·2^w1 + 2·2^w2 − 6` Toffoli, i.e. `O(2^w1 + 2^w2)`. At the **balanced split** `w1 = w2 = w/2` this is `6·(2^(w/2) − 1) = O(√(2^w))` — vs the full read's `2·(2^w − 1) = O(2^w)`. That gap **is** the SELECT-SWAP √-advantage, and it is a *theorem* here: `phaseup_toffoli_sqrt` (`≤`), strict once both halves are real (`phaseup_toffoli_sqrt_strict`, `_balanced`).

```
  address split  addr = hi‖lo   (w = w1 + w2)

   ctrl ─●─────────────────────────────────────────────────●───
         │  ┌── stage 1: SELECT ──┐ ┌─ stage 2: SWAP ─┐ ┌── stage 3 ──┐
   hi ───┤  │  Gray-walk over the │ │                 │ │  un-one-hot │
  levels │  │  HI levels → one-hot│ │   (hi fixed by  │ │  (stage 1   │
         │  │  marker on ancillas │ │    the marker)  │ │   reversed) │
         │  └─────────┬───────────┘ │                 │ └──────┬──────┘
   lo ───┤            │             │  CZ-leaf walk   │        │
  levels │            ▼             │  over LO levels │        ▼
         │   one-hot[h] := ctrl ∧   │  leaf ℓ:  CZ(•, │   one-hot wires
         │   [addr_hi = h]          │  base+h) ∀ h s.t.│   cleared back
         │   (2·(2^w1−1) Toff)      │  F(h‖ℓ)   (T-free│   (2·(2^w1−1) Toff)
   one-  │                          │  CZ; 2·(2^w2−1)  │
   hot ──┴── base+0 … base+(2^w1−1) ─── Toff) ─────────┴────────────────
   wires

   net phase on |ctrl, addr, clean ancillas⟩ :  (−1)^(ctrl ∧ F(addr))
   net Toffoli : 4·(2^w1−1) + 2·(2^w2−1)  ≈ O(√(2^w)) balanced
```

## Correctness (the theorems to audit)

- **Phase action** — `phaseup_diagonal`: on every basis state whose AND-ladder and one-hot ancillas are clean (ctrl and address arbitrary), phaseup is diagonal with phase `(−1)^(ctrl ∧ F(decAddr (w1+w2) f))`. Address form `phaseup_diagonal_addr`: ctrl set + address holding `v < 2^w` ⟹ exactly `(−1)^(F v)`. Both re-export `splitPhaseLookup_diagonal` / `_addr` verbatim.
- **End-to-end channel** — `measWordUncompute_phaseup`: using `phaseup dim (fun v => (T v).testBit j) w1 w2 base` as the per-bit fixup `P j` of Gidney's measurement-based lookup-uncompute is the **perfect uncompute** on every lookup-computed family (`SplitGoodState`: ctrl set, ladders + one-hot ancillas clean): coefficients intact, all `W` word bits released as `|0…0⟩`, no second lookup — at the √-cost. Re-exports `measWordUncompute_splitPhaseLookup`.

### The required clean-ancilla hypotheses (honest)
`phaseup_diagonal` carries two hypotheses, surfaced **honestly** and NOT discharged away:
- `hand : ∀ i < w, f (ulookup_and_idx i) = false` — the AND-ladder ancillas are clean;
- `hhot : ∀ h < 2^w1, f (base + h) = false` — the one-hot ancillas are clean.

No address-driven phase circuit on this wire layout can act diagonally on a state whose AND-ladder is **dirty** (the abstract `hP` of `measWordUncompute_qrom` is strictly stronger than any ancilla-using circuit satisfies — see the `PhaseLookupFixup` module note). These hypotheses are exactly the conditions the channel corollary's `SplitGoodState` bundles, and they hold on every lookup-computed family the uncompute consumes — so this is the gadget's genuine operating frame, not a gap.

## Resource (the count theorems)
- `toffoli_phaseup (w1 w2 base) = 4·(2^w1 − 1) + 2·(2^w2 − 1)` — closed form `4·2^w1 + 2·2^w2 − 6` (`toffoli_phaseup_closed`); balanced `6·(2^k − 1)` (`toffoli_phaseup_balanced`).
- `toffoli_phaseupFull (w) = 2·(2^w − 1)` — the full table read.
- `phaseup_toffoli_sqrt` — split `≤` full for `w2 ≥ 1`; `phaseup_toffoli_sqrt_strict` — strict for `w1 ≥ 1, w2 ≥ 2`; `phaseup_toffoli_sqrt_balanced` — strict at `w1 = w2 = k ≥ 2`.

| phaseup at width `w` | Toffoli |
|---|---|
| **split phaseup** (`w = 4` as `2+2`) | **18** (√) |
| full table read `phaseupFull 4` | 30 |
| **split phaseup** (`w = 8` as `4+4`) | **90** (√) |
| full table read `phaseupFull 8` | 510 |

## Honest scope
- Phaseup is a **diagonal `BaseUCom`** — correctness is the phase it stamps (`phaseup_diagonal`), there is no Boolean `applyNat` statement to make. The cost is stated on the **Gate-level T-content twin** `phaseupSkeleton` because `BaseUCom` carries no T-counter; the twin's CZ leaves are Clifford (T-free), matching the real walk.
- `phaseup_diagonal` requires clean AND-ladder + one-hot ancillas (`hand`, `hhot`); these are the gadget's operating frame, met by every family the channel feeds it (`SplitGoodState`).
- The `base` parameter places the `2^w1` one-hot ancillas above the lookup block (`2·w < base`); the channel corollary additionally needs the word register above the one-hot block (`base + 2^w1 ≤ pos j`). Canonical choice `base = 2·w + 1`.
- Kernel-clean: no `sorry`, no `native_decide`, no added axioms. The headlines `phaseup_diagonal`, `toffoli_phaseup`, `phaseup_toffoli_sqrt`, `measWordUncompute_phaseup` use only `[propext, Classical.choice, Quot.sound]`.

## For auditors
`import FormalRV.Arithmetic.Phaseup` — the umbrella pulls the whole verified gadget. For Gidney 2025 / Pinnacle: `phaseup` is the phase-gradient table lookup, `phaseup_diagonal` is its faithful diagonal phase `(−1)^(ctrl ∧ F(addr))`, `toffoli_phaseup` is the SELECT-SWAP `O(2^(w/2))` cost, and `phaseup_toffoli_sqrt` is the verified √-advantage over a full table read. Reproduce the counts and the phase runs: `lake env lean FormalRV/Arithmetic/Phaseup/Example.lean`.
