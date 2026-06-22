#!/usr/bin/env python3
"""One-shot PPM hierarchy restructure: git-mv 48 flat files into
Syntax/Semantics/Rules/Compiler/Magic/Resource/QECBridge/Pipeline/Codegen,
rewrite every import site repo-wide (except other agents' in-flight files,
which keep working via 2 back-compat stubs), and regenerate the umbrellas."""
import io, os, re, subprocess, sys

REPO = r"C:\Users\Panda\Documents\FormalRV"
os.chdir(REPO)

# old module suffix (under FormalRV.PPM.) -> (new folder, new file stem)
MOVES = {
    # Syntax — the PPM IR + Pauli algebra data types
    "PPM": ("Syntax", "Core"),
    "PauliSemantics": ("Syntax", "PauliSemantics"),
    "PauliOps": ("Syntax", "PauliOps"),
    # Semantics — state/denotation/measurement semantics + observation bridges
    "LogicalState": ("Semantics", "LogicalState"),
    "PPMDenote": ("Semantics", "PPMDenote"),
    "PPMSemanticsGeneral": ("Semantics", "PPMSemanticsGeneral"),
    "PPMOperational": ("Semantics", "PPMOperational"),
    "StabilizerBasisBridge": ("Semantics", "StabilizerBasisBridge"),
    "GadgetChannel": ("Semantics", "GadgetChannel"),
    "CircuitToPPMSemanticBridge": ("Semantics", "CircuitToPPMSemanticBridge"),
    "CircuitToPPMObservationBridge": ("Semantics", "CircuitToPPMObservationBridge"),
    # Rules — Clifford conjugation / rewrite laws / ZX
    "CliffordConj": ("Rules", "CliffordConj"),
    "CliffordPPMRules": ("Rules", "CliffordPPMRules"),
    "PPMUpdateInvariants": ("Rules", "PPMUpdateInvariants"),
    "EightTToCCZScheme": ("Rules", "EightTToCCZScheme"),
    "ToffoliFromCCZ": ("Rules", "ToffoliFromCCZ"),
    "ZXSpiderFusion": ("Rules", "ZXSpiderFusion"),
    "ZXStabilizer": ("Rules", "ZXStabilizer"),
    # Compiler — circuit -> PPM lowering + its correctness
    "CircuitToPPMInterface.CircuitToPPMInterfaceOverview": ("Compiler", "CircuitToPPMInterfaceOverview"),
    "CircuitToPPMInterface.CircuitFragmentClassifierAndCompiler": ("Compiler", "CircuitFragmentClassifierAndCompiler"),
    "CircuitToPPMInterface.EnrichedPPMStateAndIntegration": ("Compiler", "EnrichedPPMStateAndIntegration"),
    "CircuitToPPMInterface.SurgeryGadgetLoweringAndQECInstance": ("Compiler", "SurgeryGadgetLoweringAndQECInstance"),
    "CircuitToPPMInterface.PPMBackendLoweringModel": ("Compiler", "PPMBackendLoweringModel"),
    "CircuitToPPMInterface.BackendCertificationAndTraceLowering": ("Compiler", "BackendCertificationAndTraceLowering"),
    "CircuitToPPMInterface.CircuitToPPMInterfaceModuleEnd": ("Compiler", "CircuitToPPMInterfaceModuleEnd"),
    "CircuitToPPMInterface": ("Compiler", "CircuitToPPMInterface"),
    "PPMCompilerCorrectness": ("Compiler", "PPMCompilerCorrectness"),
    "StabProgram": ("Compiler", "StabProgram"),
    "ToffoliScheme": ("Compiler", "ToffoliScheme"),
    "ToffoliSchemeDischarge": ("Compiler", "ToffoliSchemeDischarge"),
    "PPMGadgetInstance": ("Compiler", "PPMGadgetInstance"),
    # Magic — magic-state schemes / teleportation gadgets / factories-as-magic
    "CircuitToPPMMagicFactory": ("Magic", "CircuitToPPMMagicFactory"),
    "CircuitToPPMToffoliMagic": ("Magic", "CircuitToPPMToffoliMagic"),
    "MagicGadgetInterface": ("Magic", "MagicGadgetInterface"),
    "MagicStateTeleport": ("Magic", "MagicStateTeleport"),
    "TGadgetTeleport": ("Magic", "TGadgetTeleport"),
    "CCZGadgetTeleport": ("Magic", "CCZGadgetTeleport"),
    "GidneyAND": ("Magic", "GidneyAND"),
    # Resource — PPM-level counters + anchored count theorems
    "CircuitToPPMResource": ("Resource", "CircuitToPPMResource"),
    "GateToPPMResource": ("Resource", "GateToPPMResource"),
    "PPMResourceCount": ("Resource", "PPMResourceCount"),
    "ModMultPPMResource": ("Resource", "ModMultPPMResource"),
    # QECBridge — PPM <-> QEC / factory provisioning interfaces
    "LayeredPPMQECInterface": ("QECBridge", "LayeredPPMQECInterface"),
    "CircuitToPPMFactoryProvision": ("QECBridge", "CircuitToPPMFactoryProvision"),
    "FactoryHierarchy": ("QECBridge", "FactoryHierarchy"),
    # Pipeline — Shor-specific end-to-end assemblies + paper instantiations
    "PPMShorPipeline": ("Pipeline", "PPMShorPipeline"),
    "GE2021PPMSysInv": ("Pipeline", "GE2021PPMSysInv"),
    # Codegen — PPM -> QASM text
    "PPMToQASM": ("Codegen", "PPMToQASM"),
}

STUBS = {"GE2021PPMSysInv", "PPMToQASM"}  # imported by other agents' in-flight files

def old_path(suffix):
    return os.path.join("FormalRV", "PPM", *suffix.split(".")) + ".lean"

def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True, shell=False)
    if r.returncode != 0:
        print("FAIL:", " ".join(cmd), "\n", r.stdout, r.stderr); sys.exit(1)

# in-flight files (other agents') — never rewrite these
churn = subprocess.run(["git", "status", "--short"], capture_output=True, text=True).stdout
inflight = set()
for line in churn.splitlines():
    parts = line.split()
    if parts and parts[-1].endswith(".lean"):
        inflight.add(parts[-1].replace("\\", "/"))

# 1. git mv
for suffix, (folder, stem) in MOVES.items():
    src = old_path(suffix)
    dst = os.path.join("FormalRV", "PPM", folder, stem + ".lean")
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    assert os.path.exists(src), f"missing {src}"
    run(["git", "mv", src, dst])
print(f"moved {len(MOVES)} files")

# 2. rewrite import/module references repo-wide (longest module names first)
repl = []
for suffix, (folder, stem) in MOVES.items():
    repl.append((f"FormalRV.PPM.{suffix}", f"FormalRV.PPM.{folder}.{stem}"))
repl.sort(key=lambda p: -len(p[0]))
pat = re.compile("|".join(re.escape(o) + r"(?![A-Za-z0-9_.])" for o, _ in repl))
lookup = {o: n for o, n in repl}

rewritten = 0
for root, _, files in os.walk("FormalRV"):
    for fn in files:
        if not fn.endswith(".lean"): continue
        p = os.path.join(root, fn).replace("\\", "/")
        if p in inflight: continue
        s = io.open(p, encoding="utf-8").read()
        s2 = pat.sub(lambda m: lookup[m.group(0)], s)
        if s2 != s:
            io.open(p, "w", encoding="utf-8", newline="\n").write(s2)
            rewritten += 1
print(f"rewrote imports in {rewritten} files")

# 3. back-compat stubs for in-flight importers
for suffix in STUBS:
    folder, stem = MOVES[suffix]
    p = old_path(suffix)
    io.open(p, "w", encoding="utf-8", newline="\n").write(
        f"/-\n  Back-compat re-export: `FormalRV.PPM.{suffix}` moved to\n"
        f"  `FormalRV.PPM.{folder}.{stem}` (PPM hierarchy restructure, 2026-06-10).\n"
        f"  This stub keeps in-flight importers working; remove once they migrate.\n-/\n"
        f"import FormalRV.PPM.{folder}.{stem}\n")
print(f"wrote {len(STUBS)} stubs")

# 4. per-folder umbrellas + top umbrella
folders = {}
for suffix, (folder, stem) in MOVES.items():
    folders.setdefault(folder, []).append(stem)
DESC = {
    "Syntax": "the PPM IR: Pauli / PauliString / PPM / PPMCommand data types + syntactic ops",
    "Semantics": "state-vector & operational semantics, denotation, observation bridges",
    "Rules": "Clifford conjugation & rewrite laws, ZX",
    "Compiler": "circuit -> PPM lowering, its correctness, and backend trace lowering",
    "Magic": "magic-state teleportation gadgets & Toffoli/CCZ magic schemes",
    "Resource": "PPM-level resource counters + anchored count theorems",
    "QECBridge": "PPM <-> QEC layering & magic-factory provisioning interfaces",
    "Pipeline": "Shor end-to-end assemblies + paper-specific instantiations",
    "Codegen": "PPM -> OpenQASM text emission",
}
ORDER = ["Syntax", "Semantics", "Rules", "Compiler", "Magic", "Resource", "QECBridge", "Pipeline", "Codegen"]
for folder in ORDER:
    stems = sorted(folders[folder])
    body = (f"/-\n  FormalRV.PPM.{folder} — {DESC[folder]}.\n"
            f"  (PPM hierarchy restructure, 2026-06-10.)\n-/\n"
            + "\n".join(f"import FormalRV.PPM.{folder}.{s}" for s in stems) + "\n")
    io.open(os.path.join("FormalRV", "PPM", folder + ".lean"), "w", encoding="utf-8", newline="\n").write(body)
top = ("/-\n  FormalRV.PPM — the Pauli-Product-Measurement layer, organised as a hierarchy:\n"
       + "".join(f"    {f}/ — {DESC[f]}\n" for f in ORDER)
       + "  See PPM/README.md for the layer map and the honesty boundaries.\n-/\n"
       + "\n".join(f"import FormalRV.PPM.{f}" for f in ORDER) + "\n")
io.open(os.path.join("FormalRV", "PPM.lean"), "w", encoding="utf-8", newline="\n").write(top)
print("umbrellas written")
print("DONE")
