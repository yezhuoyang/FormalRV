"""
Step 1: verify the SAT-synthesized LaSsynth designs with stimzx.

For each `results/*.lasre.json` (a Tan-Niu-Gidney optimized, minimum-spacetime-volume
lattice surgery), `LatticeSurgerySolution.verify_stabilizers_stimzx` uses Gidney's
stimzx to deduce the design's external stabilizers (port flows) from its ZX graph
and checks them equal to the specified port stabilizers.

Because stimzx's algorithm interprets every spider as a postselected parity
measurement (stimzx/_zx_graph_solver.py), `verify = True` is a PPM-level
certificate: the optimizer's output realizes its function as a sequence of
Pauli-product measurements -- exactly our framework's `zxToPPM` semantics.

Run:  LASSYNTH_DIR=<isca24_SAT_scalpel> python PyCircuits/lasre_verify.py
"""
import os, sys, json, glob

SCALPEL = os.environ.get("LASSYNTH_DIR",
    r"C:/Users/yezhu/Documents/resourceFormal/scalpel_x/isca24_SAT_scalpel")
sys.path.insert(0, SCALPEL)
try:
    from lassynth.lattice_surgery_synthesis import LatticeSurgerySolution
except ImportError:
    sys.exit(f"lassynth not found - set LASSYNTH_DIR (tried {SCALPEL})")

results = sorted(glob.glob(os.path.join(SCALPEL, "results", "*.lasre.json")))
all_ok = True
print("Verifying SAT-synthesized LaSsynth designs via stimzx (PPM-level oracle):\n")
for path in results:
    name = os.path.basename(path).replace(".lasre.json", "")
    lasre = json.load(open(path))
    if "stabilizers" not in lasre or "ports" not in lasre:
        print(f"  {name:28s}  (skip: no port-stabilizer spec)")
        continue
    spec = {"ports": lasre["ports"], "stabilizers": lasre["stabilizers"]}
    try:
        ok = LatticeSurgerySolution(lasre).verify_stabilizers_stimzx(spec)
    except Exception as e:
        ok = False
        print(f"  {name:28s}  ERROR {type(e).__name__}: {e}")
        all_ok = False
        continue
    all_ok = all_ok and ok
    vol = f"{lasre['n_i']}x{lasre['n_j']}x{lasre['n_k']}"
    print(f"  {name:28s}  verify={ok!s:5s}  "
          f"(ports={lasre['n_p']}, stabs={lasre['n_s']}, volume={vol})")

print("\nAll designs verify True (PPM-realized)." if all_ok else "\nSome design FAILED.")
sys.exit(0 if all_ok else 1)
