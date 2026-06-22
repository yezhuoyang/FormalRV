#!/usr/bin/env python3
"""Rewrite Lean `import <old>` lines to `import <new>` across the repo.

Exact whole-line match (after rstrip) so we never touch namespace references,
docstrings, or `#check FormalRV.X` sites -- only real import statements.
Edit MAP for each reorg phase and run from the repo root.
"""
import io, os

# old fully-qualified module  ->  new fully-qualified module
G_RES = "FormalRV.Shor.Resource"
G_PPM = "FormalRV.Shor.PPM"
G_OF = "FormalRV.Shor.OrderFinding"
MAP = {
    # B: Resource
    "FormalRV.Shor.ControlledModExpCount": f"{G_RES}.ControlledModExpCount",
    "FormalRV.Shor.ModExpToffoliCount": f"{G_RES}.ModExpToffoliCount",
    "FormalRV.Shor.CliffordTControlledModExp": f"{G_RES}.CliffordTControlledModExp",
    "FormalRV.Shor.ShorCriticalPathFloor": f"{G_RES}.ShorCriticalPathFloor",
    "FormalRV.Shor.ShorFullMachineRequirement": f"{G_RES}.ShorFullMachineRequirement",
    # C: PPM / surgery realization + emit
    "FormalRV.Shor.PPMShorMaster": f"{G_PPM}.PPMShorMaster",
    "FormalRV.Shor.ShorPPMEndToEnd": f"{G_PPM}.ShorPPMEndToEnd",
    "FormalRV.Shor.ShorPPMUnitaryReduction": f"{G_PPM}.ShorPPMUnitaryReduction",
    "FormalRV.Shor.ShorModMulPPMFactoryE2E": f"{G_PPM}.ShorModMulPPMFactoryE2E",
    "FormalRV.Shor.TeleportCCXGrounded": f"{G_PPM}.TeleportCCXGrounded",
    "FormalRV.Shor.ShorEmit": f"{G_PPM}.ShorEmit",
    "FormalRV.Shor.ShorEmitDistance": f"{G_PPM}.ShorEmitDistance",
    # D: OrderFinding (version-agnostic textbook core)
    "FormalRV.Shor.Eigenstate": f"{G_OF}.Eigenstate",
    "FormalRV.Shor.TotientLowerBound": f"{G_OF}.TotientLowerBound",
    "FormalRV.Shor.EncodingAgnostic": f"{G_OF}.EncodingAgnostic",
    "FormalRV.Shor.ProbabilityTransfer": f"{G_OF}.ProbabilityTransfer",
    "FormalRV.Shor.SuccessSensitivity": f"{G_OF}.SuccessSensitivity",
}

SKIP_DIRS = {".lake", ".git", ".elan", "build", ".vscode"}
changed = 0
for dirpath, dirs, files in os.walk("."):
    dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
    for fn in files:
        if not fn.endswith(".lean"):
            continue
        p = os.path.join(dirpath, fn)
        with io.open(p, "r", encoding="utf-8") as f:
            lines = f.readlines()
        touched = False
        for i, ln in enumerate(lines):
            stripped = ln.rstrip("\r\n")
            for old, new in MAP.items():
                if stripped == f"import {old}":
                    lines[i] = f"import {new}\n"
                    touched = True
        if touched:
            with io.open(p, "w", encoding="utf-8", newline="") as f:
                f.writelines(lines)
            changed += 1
            print(f"  rewrote imports in {p}")
print(f"Done: {changed} file(s) updated for {len(MAP)} module move(s).")
