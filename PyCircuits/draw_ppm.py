"""
Render FormalRV's compiled PPM programs in the Litinski "Game of Surface Codes"
Pauli-product-measurement style: logical qubits as horizontal wires, each
multi-qubit Pauli measurement a vertical column of colour-coded Pauli boxes
(X orange, Y yellow, Z green) joined by a bar; magic-T injections purple;
deferred Pauli-frame updates dashed; and (optionally) a classical
measurement-record lane of blue outcome boxes showing where each measured bit lands.

Programs are the VERBATIM output of `compileArithmeticGateToPPM`
(FormalRV/PPM/CircuitToPPMInterface/Part2.lean:159):
  X q       -> [frame X on q]
  CX c t    -> [measure ZZ on {c,t},  frame X on t]
  CCX a b t -> [useMagicT t,  measure ZZZ on {a,b,t},  frame X on t]
  seq       -> concatenation.
The adder/multiplier programs are emitted by scripts/EmitAdderPPM.lean.

Run:  python PyCircuits/draw_ppm.py     Out: docs/diagrams/ppm_*.png
"""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)

PCOL = {"X": "#ED8936", "Y": "#ECC94B", "Z": "#48BB78"}   # Pauli palette
MAGIC = "#9F7AEA"                                          # magic-T injection
REC = "#3182CE"                                            # classical readout / record bit


def _draw_columns(ax, program, nq, y0, colw, bw, qlabels=None):
    """Draw the qubit wires + Pauli-box columns for one program block, with the
    bottom qubit wire at height y0 (qubit q at y0 + (nq-1-q))."""
    bh = 0.62
    xright = 0.8 + len(program) * colw + 0.3
    ypos = lambda q: y0 + (nq - 1 - q)
    for q in range(nq):
        ax.plot([0.1, xright - 0.2], [ypos(q), ypos(q)], color="#999", lw=1.2, zorder=1)
        lab = qlabels[q] if qlabels else f"q{q}"
        ax.text(-0.05, ypos(q), f"$|{lab}\\rangle$", ha="right", va="center", fontsize=11)
    for i, col in enumerate(program):
        x = 0.8 + i * colw
        qs = col["qubits"]
        if col["op"] == "measure" and len(qs) > 1:
            ax.plot([x, x], [ypos(max(qs)), ypos(min(qs))], color="#2f855a", lw=2.2, zorder=2)
        for q in qs:
            y = ypos(q)
            if col["op"] == "measure":
                ax.add_patch(FancyBboxPatch((x - bw / 2, y - bh / 2), bw, bh, boxstyle="round,pad=0.02",
                             fc=PCOL[col["pauli"]], ec="#1a4731", lw=1.5, zorder=3))
                ax.text(x, y, col["pauli"], ha="center", va="center", fontsize=11.5, fontweight="bold", color="white", zorder=4)
            elif col["op"] == "frame":
                p = col["pauli"]
                ax.add_patch(FancyBboxPatch((x - bw / 2, y - bh / 2), bw, bh, boxstyle="round,pad=0.02",
                             fc=PCOL[p] + "55", ec=PCOL[p], lw=1.5, ls="--", zorder=3))
                ax.text(x, y, p, ha="center", va="center", fontsize=10.5, fontweight="bold", color="#9c4221", zorder=4)
            elif col["op"] == "magicT":
                ax.add_patch(FancyBboxPatch((x - bw / 2, y - bh / 2), bw, bh, boxstyle="round,pad=0.02",
                             fc=MAGIC, ec="#44337a", lw=1.5, zorder=3))
                ax.text(x, y, "T", ha="center", va="center", fontsize=11.5, fontweight="bold", color="white", zorder=4)
    return xright, ypos


def _legend(ax, record=False):
    h = [plt.Line2D([0], [0], marker="s", ls="", ms=11, mfc=PCOL["Z"], mec="#1a4731", label="Z measure"),
         plt.Line2D([0], [0], marker="s", ls="", ms=11, mfc=PCOL["X"] + "55", mec=PCOL["X"], label="X frame (deferred)"),
         plt.Line2D([0], [0], marker="s", ls="", ms=11, mfc=MAGIC, mec="#44337a", label="magic-T inject")]
    if record:
        h.append(plt.Line2D([0], [0], marker="s", ls="", ms=11, mfc=REC, mec="#1a365d", label="measurement record bit"))
    ax.legend(handles=h, loc="upper center", bbox_to_anchor=(0.5, -0.02), ncol=len(h), frameon=False, fontsize=9)


def draw_ppm(program, nq, title, outfile, qlabels=None, colw=1.0, captions=True, record=False):
    ncol = len(program)
    y_rec = -1.6
    fig, ax = plt.subplots(figsize=(1.7 + 1.05 * ncol * colw, (0.7 + 0.85 * nq) + (1.3 if record else 0)))
    bw = min(0.62, 0.86 * colw)
    xright, ypos = _draw_columns(ax, program, nq, 0.0, colw, bw, qlabels)
    ax.set_xlim(-0.2, xright); ax.set_ylim((-2.2 if record else -0.7), nq - 0.3); ax.axis("off")
    bh = 0.62
    if record:
        ax.plot([0.1, xright - 0.2], [y_rec, y_rec], color="#888", lw=1.0)
        ax.plot([0.1, xright - 0.2], [y_rec - 0.07, y_rec - 0.07], color="#888", lw=1.0)
        ax.text(-0.05, y_rec, "$c$", ha="right", va="center", fontsize=11)
        mk = 0
    for i, col in enumerate(program):
        x = 0.8 + i * colw
        if record and col["op"] == "measure":
            ax.plot([x, x], [ypos(min(col["qubits"])) - bh / 2, y_rec + bh / 2], ls=":", color=REC, lw=1.3, zorder=2)
            ax.add_patch(FancyBboxPatch((x - bw / 2, y_rec - bh / 2), bw, bh, boxstyle="round,pad=0.02",
                         fc=REC, ec="#1a365d", lw=1.4, zorder=3))
            ax.text(x, y_rec, f"$m_{{{mk}}}$", ha="center", va="center", fontsize=9.5, fontweight="bold", color="white", zorder=4)
            mk += 1
        if captions:
            cap = {"measure": "$M_{" + col.get("pauli", "") * len(col["qubits"]) + "}$",
                   "frame": "frame", "magicT": "$|T\\rangle$"}[col["op"]]
            ax.text(x, -0.55, cap, ha="center", va="center", fontsize=9, color="#444")
    ax.set_title(title, fontsize=11.5, fontweight="bold")
    _legend(ax, record)
    fig.tight_layout(); fig.savefig(os.path.join(OUT, outfile), dpi=140, bbox_inches="tight"); plt.close(fig)
    print(f"  drew {outfile}  ({ncol} PPM columns, {nq} qubits{', + record' if record else ''})")


def draw_ppm_folded(program, nq, title, outfile, fold=50, colw=0.5):
    """Long programs wrapped into stacked rows of `fold` columns each."""
    chunks = [program[i:i + fold] for i in range(0, len(program), fold)]
    nrows = len(chunks)
    rowh = nq + 1.4
    bw = min(0.6, 0.86 * colw)
    fig, ax = plt.subplots(figsize=(1.9 + 1.02 * fold * colw, 0.8 + 0.62 * rowh * nrows))
    xr_max = 0.8 + fold * colw + 0.3
    for r, chunk in enumerate(chunks):
        y0 = (nrows - 1 - r) * rowh
        _draw_columns(ax, chunk, nq, y0, colw, bw)
        ax.text(xr_max - 0.1, y0 + nq - 1 + 0.5, f"cmds {r*fold}–{r*fold + len(chunk) - 1}",
                ha="right", va="bottom", fontsize=8, color="#888")
    ax.set_xlim(-0.3, xr_max); ax.set_ylim(-0.8, (nrows - 1) * rowh + nq - 0.2); ax.axis("off")
    ax.set_title(title, fontsize=12, fontweight="bold")
    _legend(ax)
    fig.tight_layout(); fig.savefig(os.path.join(OUT, outfile), dpi=130, bbox_inches="tight"); plt.close(fig)
    print(f"  drew {outfile}  ({len(program)} PPM columns folded into {nrows} rows, {nq} qubits)")


def parse_ppm_file(path):
    prog = []
    for ln in open(path):
        p = ln.split()
        if not p:
            continue
        if p[0] == "M":
            prog.append({"op": "measure", "pauli": p[1], "qubits": [int(x) for x in p[2].split(",")]})
        elif p[0] == "F":
            prog.append({"op": "frame", "pauli": "X", "qubits": [int(x) for x in p[1].split(",")]})
        elif p[0] == "T":
            prog.append({"op": "magicT", "qubits": [int(p[1])]})
    return prog


print("FormalRV compiled PPM programs (Litinski PPM style):")

# small gadgets, WITH the measurement-record lane (where the classical bits land)
draw_ppm([{"op": "measure", "pauli": "Z", "qubits": [0, 1]},
          {"op": "frame", "pauli": "X", "qubits": [1]}],
         2, "compileArithmeticGateToPPM (CX 0 1)  —  CNOT = joint ZZ measurement + X-frame; outcome bit m₀",
         "ppm_cx.png", record=True)

draw_ppm([{"op": "magicT", "qubits": [2]},
          {"op": "measure", "pauli": "Z", "qubits": [0, 1, 2]},
          {"op": "frame", "pauli": "X", "qubits": [2]}],
         3, "compileArithmeticGateToPPM (CCX 0 1 2)  —  Toffoli = magic-T + joint ZZZ + X-frame; outcome m₀",
         "ppm_ccx.png", record=True)

draw_ppm([{"op": "measure", "pauli": "Z", "qubits": [0, 1]}, {"op": "frame", "pauli": "X", "qubits": [1]},
          {"op": "magicT", "qubits": [2]}, {"op": "measure", "pauli": "Z", "qubits": [0, 1, 2]},
          {"op": "frame", "pauli": "X", "qubits": [2]}],
         3, "compileArithmeticGateToPPM (seq (CX 0 1) (CCX 0 1 2))  —  programs concatenate; records m₀, m₁",
         "ppm_seq.png", record=True)

# full compiled programs (emitted by scripts/EmitAdderPPM.lean)
adder = os.path.join(ROOT, "PyCircuits", "ppm", "adder3_ppm.txt")
if os.path.exists(adder):
    prog = parse_ppm_file(adder)
    nT = sum(1 for c in prog if c["op"] == "magicT")
    print("Full 3-bit Cuccaro adder PPM program:")
    draw_ppm(prog, 7,
             "Full PPM program of the verified 3-bit Cuccaro adder  (cuccaro_n_bit_adder_full 3 0)\n"
             f"{len(prog)} PPM commands · {nT} magic-T injections · forward MAJ chain then reverse-UMA chain",
             "ppm_adder3.png", colw=0.5, captions=False)

mm = os.path.join(ROOT, "PyCircuits", "ppm", "modmult_215_7_ppm.txt")
if os.path.exists(mm):
    prog = parse_ppm_file(mm)
    nT = sum(1 for c in prog if c["op"] == "magicT")
    print("Full modular-multiplier PPM program:")
    draw_ppm_folded(prog, 9,
                    "Full PPM program of the verified modular multiplier  (sqir_modmult_const_gate 2 15 7,  x ↦ 7x mod 15)\n"
                    f"{len(prog)} PPM commands · {nT} magic-T injections (= 32 Toffolis) · folded into rows",
                    "ppm_modmult.png", fold=50, colw=0.5)

print("\nPPM diagrams written to docs/diagrams/")
