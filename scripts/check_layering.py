#!/usr/bin/env python3
"""Layering guard for the QEC refactor (2026-06).

The QEC layer is the *demand side* of fault-tolerant Shor: a syntactic object
over infinitely many virtual qubits, with logical-cycle time only.  Hardware
mapping, wallclock time, and system calls live in FormalRV/System (the supply
side).  This script enforces the import discipline that keeps those layers
separate:

  R1. No file under FormalRV/QEC/ may directly import FormalRV.System.*
      (hardware/scheduling must not leak into the demand layer).
  R2. No file under FormalRV/QEC/ may import FormalRV.Shor.* or
      FormalRV.Audit.* (no upward imports from the algorithm/audit layers).
  R3. No file under FormalRV/Resource/ may import anything except
      FormalRV.Core.*, FormalRV.QEC.Circuit.* (circuit IRs), or other
      FormalRV.Resource.* modules (counters import only IRs, never gadget
      builders or proofs — see FormalRV/Resource/README.md).

Known residue (documented, NOT checked here): some QEC/LatticeSurgery files
import PPM contract modules that *transitively* reach FormalRV.System
(e.g. MagicInjectionSurgery -> PPM.CircuitToPPMToffoliMagic).  Direct imports
are the enforceable boundary; the transitive cleanup is tracked in
FormalRV/QEC/README.md.

Exit code 0 = clean, 1 = violations (printed one per line).
"""

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
IMPORT_RE = re.compile(r"^import\s+(FormalRV\.[A-Za-z0-9_.]+)", re.M)

RULES = [
    # (rule id, file glob, forbidden module prefixes, allowed exceptions)
    ("R1", "FormalRV/QEC/**/*.lean", ("FormalRV.System.", "FormalRV.System"), ()),
    ("R2", "FormalRV/QEC/**/*.lean", ("FormalRV.Shor.", "FormalRV.Audit."), ()),
]

# Only LEAF IR modules are importable by counters — NOT the compiler /
# semantics / count-theorem modules under QEC/Circuit/, which import gadget
# builders and proofs (the Resource charter forbids counters seeing those).
RESOURCE_ALLOWED_PREFIXES = (
    "FormalRV.Core.",
    "FormalRV.Resource.",
)
RESOURCE_ALLOWED_EXACT = {
    "FormalRV.QEC.Circuit.PhysCircuit",   # the QEC physical-circuit leaf IR
    "FormalRV.PPM.Syntax.Program",        # the PPM program leaf IR (zero imports)
    "FormalRV.PauliRotation.Syntax",      # the Pauli-rotation leaf IR (imports only the PPM leaf)
}
# Examples.lean is deliberately off the default build path and demonstrates the
# (object, proof, count) triple, so it may import gadget-land.
RESOURCE_EXEMPT_FILES = {"Examples.lean"}


def main() -> int:
    violations = []

    for rule, glob, forbidden, exceptions in RULES:
        for path in sorted(REPO.glob(glob)):
            text = path.read_text(encoding="utf-8")
            for mod in IMPORT_RE.findall(text):
                if mod in exceptions:
                    continue
                if any(mod == p.rstrip(".") or mod.startswith(p) for p in forbidden):
                    violations.append(f"{rule}: {path.relative_to(REPO)} imports {mod}")

    for path in sorted(REPO.glob("FormalRV/Resource/**/*.lean")):
        if path.name in RESOURCE_EXEMPT_FILES:
            continue
        text = path.read_text(encoding="utf-8")
        for mod in IMPORT_RE.findall(text):
            if mod.startswith(RESOURCE_ALLOWED_PREFIXES) or mod in RESOURCE_ALLOWED_EXACT:
                continue
            violations.append(
                f"R3: {path.relative_to(REPO)} imports {mod} "
                f"(counters may import only Core/*, Resource/*, or leaf IR modules)"
            )

    if violations:
        print(f"layering check FAILED ({len(violations)} violation(s)):")
        for v in violations:
            print(" ", v)
        return 1

    print("layering check OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
