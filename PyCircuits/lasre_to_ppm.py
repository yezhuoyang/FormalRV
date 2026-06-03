"""
LaSre -> PPM importer.

Turns a Tan-Niu-Gidney LaSsynth design (a `.lasre.json`, the SAT-synthesized
*optimized* lattice surgery) into our framework's ZX / PPM representation, so any
LaSsynth-optimized surgery enters our verified PPM pipeline.

Pipeline:
  .lasre.json
    --(LaSsynth)-->  ZX graph (networkx; cube=spider, pipe=wire; Tan section II-D)
    --(this file)--> our ZXDiagram  (each Z/X spider = a Pauli-product MEASUREMENT
                                     over its incident edge-qubits = our `mkSpider`)
                     emitted as a Lean def in FormalRV.PPM.ZXStabilizer terms.

Correctness oracle: LaSsynth's `verify_stabilizers_stimzx` (Gidney's stimzx).
stimzx's own algorithm interprets *every spider as a postselected parity
measurement* (see stimzx/_zx_graph_solver.py) -- i.e. exactly our `zxToPPM`
(Z-spider = measure prod Z, X-spider = measure prod X).  So `verify=True` is a
PPM-level certificate that the optimized design realizes its port stabilizers.

Run:  LASSYNTH_DIR=<isca24_SAT_scalpel> python PyCircuits/lasre_to_ppm.py majority_gate
"""
import os, sys, json

SCALPEL = os.environ.get("LASSYNTH_DIR",
    r"C:/Users/yezhu/Documents/resourceFormal/scalpel_x/isca24_SAT_scalpel")
sys.path.insert(0, SCALPEL)
try:
    from lassynth.lattice_surgery_synthesis import LatticeSurgerySolution
except ImportError:
    sys.exit(f"lassynth not found - set LASSYNTH_DIR (tried {SCALPEL})")


def load(name):
    with open(os.path.join(SCALPEL, "results", f"{name}.lasre.json")) as fh:
        return json.load(fh)


def zx_graph(lasre):
    return LatticeSurgerySolution(lasre).after_default_optimizations().to_networkx_graph()


def extract(g):
    """ZX graph -> (n_edges, spiders, h_edges, ports).

    Edges are the qubits (each undirected edge carries an EPR pair in stimzx's
    semantics).  Each Z/X spider measures the parity over its incident edges.
    """
    edges = sorted({frozenset(e) for e in g.edges() if e[0] != e[1]}, key=lambda s: sorted(s))
    eidx = {e: i for i, e in enumerate(edges)}

    def inc(n):
        return sorted({eidx[frozenset((n, m))] for m in g.neighbors(n)
                       if m != n and frozenset((n, m)) in eidx})

    spiders, h_edges, ports = [], [], []
    for n in sorted(g.nodes):
        v = g.nodes[n]["value"]
        if v.kind in ("Z", "X"):
            spiders.append((v.kind, inc(n), v.quarter_turns))
        elif v.kind == "H":
            h_edges.append(inc(n))
        elif v.kind in ("in", "out"):
            ports.append((v.kind, n, inc(n)))
    return len(edges), spiders, h_edges, ports


def to_lean(name, n_edges, spiders):
    rows = ",\n".join(
        f"    mkSpider ZXColor.{c} {idxs} {n_edges}".replace(" ", " ")
        for (c, idxs, _qt) in spiders)
    return (f"/-- ZXDiagram of the SAT-synthesized `{name}` lattice surgery "
            f"(LaSsynth), imported by `PyCircuits/lasre_to_ppm.py`.\n"
            f"    {len(spiders)} Z/X measurement spiders over {n_edges} edge-qubits. -/\n"
            f"def {name}_zx : ZXDiagram :=\n  [\n{rows}\n  ]\n")


def verify(lasre):
    sol = LatticeSurgerySolution(lasre)
    spec = {"ports": lasre["ports"], "stabilizers": lasre["stabilizers"]}
    return sol.verify_stabilizers_stimzx(spec)


HEADER = """/-
  FormalRV.Corpus.LaSsynthImport — SAT-synthesized lattice surgeries (Tan, Niu &
  Gidney, "A SAT Scalpel for Lattice Surgery", ISCA 2024) imported into our ZX/PPM
  IR by `PyCircuits/lasre_to_ppm.py`.

  Each design's `.lasre.json` (the *optimized*, minimum-spacetime-volume LaS that
  LaSsynth's SAT solver produces) is parsed into a `ZXDiagram`: every Z/X
  cube-spider becomes a Pauli-product MEASUREMENT (`mkSpider`).  This is the user's
  thesis — "all lattice surgery, even optimized, goes through PPM" — applied to
  REAL optimizer output: the synthesized design is, in our framework, a PPM program.

  Correctness is certified externally by stimzx (`verify_stabilizers_stimzx = True`,
  see `PyCircuits/lasre_verify.py`), whose algorithm interprets every spider as a
  postselected parity measurement — identical to our `zxToPPM`.  `factory121` is a
  PURE measurement fragment (0 H domain-walls), so its import is fully faithful;
  `majority_gate` additionally has 6 H domain-walls (basis changes), recorded
  separately for the faithful replay.

  GENERATED — do not edit by hand.  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.ZXStabilizer

namespace FormalRV.Corpus.LaSsynthImport

open FormalRV.Framework.ZX
"""


def emit_file(names, out_path):
    blocks = [HEADER]
    for name in names:
        lasre = load(name)
        g = zx_graph(lasre)
        n_edges, spiders, h_edges, ports = extract(g)
        assert verify(lasre), f"{name} failed stimzx verification"
        blocks.append(to_lean(name, n_edges, spiders))
        if h_edges:
            walls = ",\n".join(f"    {w}" for w in h_edges)
            blocks.append(f"/-- `{name}` H domain-walls (basis-change nodes), each "
                          f"over its incident edge-qubits. -/\n"
                          f"def {name}_hwalls : List (List Nat) :=\n  [\n{walls}\n  ]\n")
        blocks.append(
            f"/-- The optimized `{name}` imported as {len(spiders)} Pauli-product "
            f"measurements (every spider is a PPM), and the ZX→PPM translation\n"
            f"    yields exactly one measurement per spider. -/\n"
            f"example : {name}_zx.length = {len(spiders)} := rfl\n"
            f"example : (zxToPPM {name}_zx).length = {name}_zx.length := by "
            f"simp [zxToPPM]\n")
    blocks.append("end FormalRV.Corpus.LaSsynthImport\n")
    with open(out_path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(blocks))
    print(f"wrote {out_path}")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--emit":
        emit_file(["factory121", "majority_gate"], sys.argv[2])
    else:
        name = sys.argv[1] if len(sys.argv) > 1 else "majority_gate"
        lasre = load(name)
        g = zx_graph(lasre)
        n_edges, spiders, h_edges, ports = extract(g)
        from collections import Counter
        kinds = Counter(c for c, _, _ in spiders)
        print(f"=== {name} ===")
        print(f"  ZX graph: {g.number_of_nodes()} nodes, {g.number_of_edges()} edges")
        print(f"  measurement spiders: {len(spiders)}  ({dict(kinds)});  "
              f"H domain-walls: {len(h_edges)};  ports: {len(ports)}")
        print(f"  stimzx verify_stabilizers (PPM-level certificate): {verify(lasre)}")
        print("\n--- Lean ZXDiagram (first 3 spiders) ---")
        print(to_lean(name, n_edges, spiders[:3]))
