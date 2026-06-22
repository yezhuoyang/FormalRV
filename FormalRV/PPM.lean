/-
  FormalRV.PPM — the Pauli-Product-Measurement layer, organised as a hierarchy:
    Syntax/ — the PPM IR: Pauli / PauliString / PPM / PPMCommand data types + syntactic ops
    Semantics/ — state-vector & operational semantics, denotation, observation bridges
    Rules/ — Clifford conjugation & rewrite laws, ZX
    Compiler/ — circuit -> PPM lowering, its correctness, and backend trace lowering
    Magic/ — magic-state teleportation gadgets & Toffoli/CCZ magic schemes
    Resource/ — PPM-level resource counters + anchored count theorems
    QECBridge/ — PPM <-> QEC layering & magic-factory provisioning interfaces
    Gadgets/ — per-gadget compiled-PPM semantic correctness vs the compiler contract
    Pipeline/ — Shor end-to-end assemblies + paper-specific instantiations
    Codegen/ — PPM -> OpenQASM text emission
  See PPM/README.md for the layer map and the honesty boundaries.
-/
import FormalRV.PPM.Syntax
import FormalRV.PPM.Semantics
import FormalRV.PPM.Rules
import FormalRV.PPM.Compiler
import FormalRV.PPM.Magic
import FormalRV.PPM.Resource
import FormalRV.PPM.QECBridge
import FormalRV.PPM.Gadgets
import FormalRV.PPM.Pipeline
import FormalRV.PPM.Codegen
