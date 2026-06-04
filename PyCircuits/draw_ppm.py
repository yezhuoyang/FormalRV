"""
Render FormalRV's compiled PPM programs in the Litinski "Game of Surface Codes"
Pauli-product-measurement style: logical qubits as horizontal wires, each
multi-qubit Pauli measurement drawn as a vertical column of colour-coded Pauli
boxes (X orange, Y yellow, Z green) joined by a bar, magic-T injections in
purple, and deferred Pauli-frame updates as dashed boxes.

The programs below are the VERBATIM output of `compileArithmeticGateToPPM`
(FormalRV/PPM/CircuitToPPMInterface/Part2.lean:159):
  X q     -> [frame X on q]
  CX c t  -> [measure ZZ on {c,t},  frame X on t]
  CCX a b t -> [useMagicT t,  measure ZZZ on {a,b,t},  frame X on t]
  seq     -> concatenation.

Run:  python PyCircuits/draw_ppm.py     Out: docs/diagrams/ppm_*.png
"""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)

PCOL = {"X": "#ED8936", "Y": "#ECC94B", "Z": "#48BB78"}   # Pauli palette
MAGIC = "#9F7AEA"                                          # magic-T injection


def draw_ppm(program, nq, title, outfile, qlabels=None, colw=1.0, captions=True):
    """program: list of columns. Each column is a dict:
       {'op':'measure','pauli':'Z','qubits':[...]}        joint Pauli measurement
       {'op':'frame','pauli':'X','qubits':[q]}            deferred Pauli-frame update
       {'op':'magicT','qubits':[q]}                       consume one |T> token
    colw: horizontal spacing per column (shrink for long programs).
    """
    ncol = len(program)
    xright = 0.8 + ncol * colw + 0.3
    fig, ax = plt.subplots(figsize=(1.7 + 1.05 * ncol * colw, 0.7 + 0.85 * nq))
    ax.set_xlim(-0.2, xright); ax.set_ylim(-0.7, nq - 0.3); ax.axis("off")
    ypos = lambda q: nq - 1 - q                      # q0 on top
    # qubit wires + labels
    for q in range(nq):
        ax.plot([0.1, xright - 0.2], [ypos(q), ypos(q)], color="#999", lw=1.2, zorder=1)
        lab = qlabels[q] if qlabels else f"q{q}"
        ax.text(-0.05, ypos(q), f"$|{lab}\\rangle$", ha="right", va="center", fontsize=12)
    bw = min(0.62, 0.86 * colw); bh = 0.62
    for i, col in enumerate(program):
        x = 0.8 + i * colw
        qs = col["qubits"]
        # connecting bar for multi-qubit measurements
        if col["op"] == "measure" and len(qs) > 1:
            ax.plot([x, x], [ypos(max(qs)), ypos(min(qs))], color="#2f855a", lw=2.4, zorder=2)
        for q in qs:
            y = ypos(q)
            if col["op"] == "measure":
                p = col["pauli"]; fc = PCOL[p]
                ax.add_patch(FancyBboxPatch((x - bw / 2, y - bh / 2), bw, bh,
                             boxstyle="round,pad=0.02", fc=fc, ec="#1a4731", lw=1.6, zorder=3))
                ax.text(x, y, p, ha="center", va="center", fontsize=12.5, fontweight="bold", color="white", zorder=4)
            elif col["op"] == "frame":
                p = col["pauli"]
                ax.add_patch(FancyBboxPatch((x - bw / 2, y - bh / 2), bw, bh,
                             boxstyle="round,pad=0.02", fc=PCOL[p] + "55", ec=PCOL[p],
                             lw=1.6, ls="--", zorder=3))
                ax.text(x, y, p, ha="center", va="center", fontsize=11.5, fontweight="bold", color="#9c4221", zorder=4)
            elif col["op"] == "magicT":
                ax.add_patch(FancyBboxPatch((x - bw / 2, y - bh / 2), bw, bh,
                             boxstyle="round,pad=0.02", fc=MAGIC, ec="#44337a", lw=1.6, zorder=3))
                ax.text(x, y, "T", ha="center", va="center", fontsize=12.5, fontweight="bold", color="white", zorder=4)
        # column caption
        if captions:
            cap = {"measure": "$M_{" + col.get("pauli", "") * len(qs) + "}$",
                   "frame": "frame", "magicT": "$|T\\rangle$"}[col["op"]]
            ax.text(x, -0.55, cap, ha="center", va="center", fontsize=9, color="#444")
    ax.set_title(title, fontsize=11.5, fontweight="bold")
    # legend
    handles = [plt.Line2D([0], [0], marker="s", ls="", ms=11, mfc=PCOL["Z"], mec="#1a4731", label="Z measure"),
               plt.Line2D([0], [0], marker="s", ls="", ms=11, mfc=PCOL["X"] + "55", mec=PCOL["X"], label="X frame (deferred)"),
               plt.Line2D([0], [0], marker="s", ls="", ms=11, mfc=MAGIC, mec="#44337a", label="magic-T inject")]
    ax.legend(handles=handles, loc="upper center", bbox_to_anchor=(0.5, -0.02),
              ncol=3, frameon=False, fontsize=9)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, outfile), dpi=140, bbox_inches="tight")
    plt.close(fig)
    print(f"  drew {outfile}  ({ncol} PPM columns, {nq} qubits)")


print("FormalRV compiled PPM programs (Litinski PPM style):")

# compileArithmeticGateToPPM (CX 0 1)
draw_ppm([{"op": "measure", "pauli": "Z", "qubits": [0, 1]},
          {"op": "frame", "pauli": "X", "qubits": [1]}],
         2, "compileArithmeticGateToPPM (CX 0 1)  —  CNOT as a joint ZZ measurement + X-frame",
         "ppm_cx.png")

# compileArithmeticGateToPPM (CCX 0 1 2)
draw_ppm([{"op": "magicT", "qubits": [2]},
          {"op": "measure", "pauli": "Z", "qubits": [0, 1, 2]},
          {"op": "frame", "pauli": "X", "qubits": [2]}],
         3, "compileArithmeticGateToPPM (CCX 0 1 2)  —  Toffoli = magic-T inject + joint ZZZ + X-frame",
         "ppm_ccx.png")

# a small composite: seq (CX 0 1) (CCX 0 1 2)  (concatenation of programs)
draw_ppm([{"op": "measure", "pauli": "Z", "qubits": [0, 1]},
          {"op": "frame", "pauli": "X", "qubits": [1]},
          {"op": "magicT", "qubits": [2]},
          {"op": "measure", "pauli": "Z", "qubits": [0, 1, 2]},
          {"op": "frame", "pauli": "X", "qubits": [2]}],
         3, "compileArithmeticGateToPPM (seq (CX 0 1) (CCX 0 1 2))  —  programs concatenate",
         "ppm_seq.png")

# ---- the FULL compiled PPM program of the verified 3-bit Cuccaro adder ----
# parsed from PyCircuits/ppm/adder3_ppm.txt (emitted by scripts/EmitAdderPPM.lean)
def parse_ppm_file(path):
    prog = []
    for ln in open(path):
        p = ln.split()
        if not p:
            continue
        if p[0] == "M":      # M Z 2,1
            prog.append({"op": "measure", "pauli": p[1], "qubits": [int(x) for x in p[2].split(",")]})
        elif p[0] == "F":    # F 1   (X-frame)
            prog.append({"op": "frame", "pauli": "X", "qubits": [int(x) for x in p[1].split(",")]})
        elif p[0] == "T":    # T 2
            prog.append({"op": "magicT", "qubits": [int(p[1])]})
    return prog


_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
adder_path = os.path.join(_root, "PyCircuits", "ppm", "adder3_ppm.txt")
if os.path.exists(adder_path):
    prog = parse_ppm_file(adder_path)
    nT = sum(1 for c in prog if c["op"] == "magicT")
    print("Full 3-bit Cuccaro adder PPM program:")
    draw_ppm(prog, 7,
             "Full PPM program of the verified 3-bit Cuccaro adder  (cuccaro_n_bit_adder_full 3 0)\n"
             f"{len(prog)} PPM commands · {nT} magic-T injections · forward MAJ chain then reverse-UMA chain",
             "ppm_adder3.png", colw=0.5, captions=False)

print("\nPPM diagrams written to docs/diagrams/")
