/-
  FormalRV.Shor.PPM.ShorLPAllocation — LP-code BLOCK ALLOCATION for the
  complete PPM-based Shor implementation (step 1 of full fault-tolerant
  compilation, John 2026-06-10).

  ## The verified implementation being allocated

  The recon-confirmed COMPLETE candidate (kernel axioms exactly
  {propext, Classical.choice, Quot.sound}; no sorry, no project axiom):

    * core    `shorModMul_compiles_to_PPM_with_factory`
              (Shor/PPM/ShorModMulPPMFactoryE2E.lean): the magic-PPM
              compilation of the modular multiplier
              `compileArithmeticGateToMagicPPM (ModMul.gateMCP bits N a ainv)`
              runs to completion on a factory-provisioned certified-T pool
              and OBSERVES `(a*x) % N`;
    * package `shor_succeeds_with_ppm_realized_modmult`
              (∧ success probability ≥ κ/(log₂N)⁴);
    * QEC-bound `surface_shor_ppm_physically_realized`.

  Named modelling contracts (per those files' honesty boundaries, unchanged
  here): `teleportCCXRel` success-branch, abstract `TFactoryContract`,
  no per-request failure probability, QPE stays unitary.

  ## What THIS file adds

  The PPM program addresses `Q bits = bits + ModMul.ancillaWidth bits
  = 4·bits + 11` logical qubits (the width of `encodeDataZeroAnc` in the
  run-and-observe theorem; 23 at the verified `bits = 3` smoke instance).
  We allocate `Q/3 + 1` blocks of the lpTiny [[15,3,d]] LIFTED-PRODUCT code
  — whose imported basis is KERNEL-CERTIFIED (`lpTinyImportedBasis_valid`)
  — under the naive sequential index map (virtual `i` ↦ block `i/3`,
  index `i%3`), and discharge the FULL layout obligation `BlockLayout.wf`
  UNCONDITIONALLY for every `bits` (structural half by the parametric
  `uniformLayout_wfStructural`, basis half by the lpTiny certificate).

  No `sorry`, no `axiom`; kernel `decide` only.
-/

import FormalRV.Shor.VerifiedShor.ShorSuccessProbabilityTheorems
import FormalRV.QEC.BlockAddressing
import FormalRV.QEC.Codes.LiftedProduct.LPTinyBasisImport
import FormalRV.QEC.Codes.LiftedProduct.LPTinyBasisFullCert

namespace FormalRV.Shor.LPAllocation

open FormalRV.QEC FormalRV.QEC.BlockLayout
open VerifiedShor

/-! ## The demand of the verified PPM program -/

/-- Logical-qubit demand of the PPM-compiled modular multiplier at `bits`:
    the data register plus the verified multiplier's ancilla block — the
    exact width `shorModMul_compiles_to_PPM_with_factory` encodes
    (`encodeDataZeroAnc bits (ancillaWidth bits) ·`). -/
def shorQ (bits : Nat) : Nat := bits + ModMul.ancillaWidth bits

/-- `Q = 4·bits + 11` in closed form. -/
theorem shorQ_closed (bits : Nat) : shorQ bits = 4 * bits + 11 := by
  simp only [shorQ, ModMul.ancillaWidth, FormalRV.BQAlgo.sqir_modmult_rev_anc]
  omega

/-- The verified `bits = 3` smoke instance addresses 23 logical qubits. -/
theorem shorQ_3 : shorQ 3 = 23 := by decide

/-! ## The LP block allocation with naive sequential indexing -/

/-- The lpTiny [[15,3,d]] block with its kernel-certified imported basis. -/
def lpBlock : CodeBlock :=
  ⟨"LP", FormalRV.QEC.Algebraic.lpTiny, 3, Codes.LP.lpTinyImportedBasis⟩

/-- The block allocation for the FULL PPM program at any `bits`. -/
def shorLayout (bits : Nat) : BlockLayout :=
  uniformLayout lpBlock (shorQ bits)

private theorem all_replicate {α : Type} (p : α → Bool) (b : α)
    (h : p b = true) : ∀ m, (List.replicate m b).all p = true := by
  intro m
  induction m with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.all_cons, h, ih]; rfl

/-- **The layout obligation, discharged UNCONDITIONALLY for every `bits`**:
    structural half parametric (`uniformLayout_wfStructural`), basis half
    by the lpTiny kernel certificate — no accepted hypotheses here. -/
theorem shorLayout_wf (bits : Nat) : (shorLayout bits).wf = true := by
  refine wf_of _ (uniformLayout_wfStructural lpBlock (shorQ bits) (by decide)) ?_
  show ((List.replicate (blocksFor (shorQ bits) lpBlock.k) lpBlock).all
      (fun b => b.basis.valid)) = true
  exact all_replicate (fun b : FormalRV.QEC.CodeBlock => b.basis.valid) lpBlock
    (show (fun b : FormalRV.QEC.CodeBlock => b.basis.valid) lpBlock = true from
      Codes.LP.lpTinyImportedBasis_valid) _

/-! ## Demand figures handed to the System layer -/

/-- Blocks allocated: `Q/3 + 1`. -/
theorem shorLayout_blocks (bits : Nat) :
    (shorLayout bits).blocks.length = shorQ bits / 3 + 1 := by
  simp [shorLayout, uniformLayout, blocksFor, lpBlock]

/-- Data-qubit demand: blocks × 15. -/
theorem shorLayout_totalN (bits : Nat) :
    (shorLayout bits).totalN = (shorQ bits / 3 + 1) * 15 :=
  uniformLayout_totalN lpBlock (shorQ bits)

/-- The `bits = 3` instance: 23 logical qubits → 8 LP blocks → 120 data
    qubits (vs 23 unprotected — the QEC demand made explicit). -/
theorem shorLayout_3_blocks : (shorLayout 3).blocks.length = 8 := by
  rw [shorLayout_blocks]
  decide

theorem shorLayout_3_totalN : (shorLayout 3).totalN = 120 := by
  rw [shorLayout_totalN]
  decide

/-! ## The naive indexing in action (the PPM-syntax view) -/

/-- `Measure X[2]Z[3]` on the Shor program's virtual logicals resolves
    CROSS-BLOCK under the naive map: virtual 2 ↦ block 0 index 2,
    virtual 3 ↦ block 1 index 0. -/
theorem shor_demo_resolves :
    (shorLayout 3).resolve [(2, .x), (3, .z)]
      = [(⟨0, 2⟩, .x), (⟨1, 0⟩, .z)] := by decide

end FormalRV.Shor.LPAllocation
