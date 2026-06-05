"""
FormalRV lattice-surgery 3D renderer — Gidney/Fowler "AutoCCZ layout" visual style
(arXiv:1905.08916, Fig.13 MAJ / Fig.16 adder): logical qubits are thick white tubes routed
through spacetime with dark edges, merges are coloured connectors, open ports are labelled
red/green end-caps, and a translucent volume bounds the block.

The cube/pipe GEOMETRY comes from a real (tqec-validated) `BlockGraph`; this module only
renders it cleanly.  Needs the tqec venv (Python <=3.13).  Run with it:
    <tqecvenv>/python PyCircuits/draw_ls_blocks.py
Out: docs/diagrams/ls_*.png
"""
import os, sys
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection
from matplotlib.patches import Patch
import tqec.gallery as gallery
from tqec import Basis, BlockGraph
from tqec.computation.cube import Port
from tqec.utils.position import Position3D as P3

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)
WHITE, EDGE = "#f6f7f9", "#15181d"
XRED, ZBLUE, PORTC, SGATE, VOL = "#e2483a", "#3b6fd4", "#2faa55", "#f2c037", "#17b8c9"


def basis_col(b):
    return XRED if b == Basis.X else ZBLUE


def box(ax, o, s, faces, ec=EDGE, lw=1.3, zsort="max"):
    """faces: dict among x/y/z -> colour (or None to skip a pair of faces)."""
    x, y, z = o; dx, dy, dz = s
    v = [(x, y, z), (x+dx, y, z), (x+dx, y+dy, z), (x, y+dy, z),
         (x, y, z+dz), (x+dx, y, z+dz), (x+dx, y+dy, z+dz), (x, y+dy, z+dz)]
    quad = {"x": [[v[0], v[3], v[7], v[4]], [v[1], v[2], v[6], v[5]]],
            "y": [[v[0], v[1], v[5], v[4]], [v[3], v[2], v[6], v[7]]],
            "z": [[v[0], v[1], v[2], v[3]], [v[4], v[5], v[6], v[7]]]}
    for key, fc in faces.items():
        if fc is None:
            continue
        pc = Poly3DCollection(quad[key], facecolor=fc, edgecolor=ec, linewidths=lw)
        pc.set_sort_zpos(None)
        ax.add_collection3d(pc)


def render_bg(bg, title, fname, port_labels=None, elev=20, azim=-54, body=WHITE):
    cubes = list(bg.cubes)
    xs = [c.position.x for c in cubes]; ys = [c.position.y for c in cubes]; zs = [c.position.z for c in cubes]
    fig = plt.figure(figsize=(7.2, 6.6)); ax = fig.add_subplot(111, projection="3d")
    ax.view_init(elev=elev, azim=azim); ax.set_axis_off()
    cw, pw = 0.5, 0.42

    # translucent bounding volume (the block's spacetime footprint)
    bx0, bx1 = min(xs)-0.55, max(xs)+0.55
    by0, by1 = min(ys)-0.55, max(ys)+0.55
    bz0, bz1 = min(zs)-0.55, max(zs)+0.55
    box(ax, (bx0, by0, bz0), (bx1-bx0, by1-by0, bz1-bz0),
        {"x": VOL, "y": VOL, "z": VOL}, ec=VOL, lw=0.6)
    for c in ax.collections[-6:]:
        c.set_alpha(0.06)

    # logical-patch cubes — white tubes; ports as coloured labelled caps
    portpos = {(p.x, p.y, p.z): lab for lab, p in bg.ports.items()} if bg.ports else {}
    for c in cubes:
        p = c.position; o = (p.x - cw/2, p.y - cw/2, p.z - cw/2)
        if c.is_port:
            box(ax, o, (cw, cw, cw), {"x": PORTC, "y": PORTC, "z": PORTC}, lw=1.0)
            lab = (port_labels or {}).get(c.label, c.label)
            if lab:
                ax.text(p.x, p.y, p.z + 0.55 if p.z >= max(zs) else p.z - 0.6,
                        lab, color="#b3261e", fontsize=8.5, fontweight="bold", ha="center")
        else:
            box(ax, o, (cw, cw, cw), {"x": body, "y": body, "z": body})

    # pipes — temporal/idle = white tube; spatial merge = coloured connector
    for pp in bg.pipes:
        u, w = pp.u.position, pp.v.position
        k = pp.kind
        d = "x" if u.x != w.x else ("y" if u.y != w.y else "z")
        lo = {"x": min(u.x, w.x), "y": min(u.y, w.y), "z": min(u.z, w.z)}
        o = [lo["x"]-pw/2, lo["y"]-pw/2, lo["z"]-pw/2]; s = [pw, pw, pw]
        di = {"x": 0, "y": 1, "z": 2}[d]; o[di] = lo[d] + cw/2; s[di] = 1 - cw
        if d == "z":
            faces = {"x": body, "y": body, "z": None}
        else:                                       # spatial merge -> colour by merged basis
            mb = getattr(k, ("x" if d == "y" else "y"), None)
            col = basis_col(mb) if mb in (Basis.X, Basis.Z) else XRED
            faces = {"x": None if d == "x" else col, "y": None if d == "y" else col, "z": col}
        box(ax, tuple(o), tuple(s), faces, lw=1.1)

    m = max(bx1-bx0, by1-by0, bz1-bz0)
    ax.set_xlim(bx0, bx0+m); ax.set_ylim(by0, by0+m); ax.set_zlim(bz0, bz0+m)
    ax.set_box_aspect((1, 1, 1))
    ax.text2D(0.5, 1.0, title, transform=ax.transAxes, ha="center", va="top", fontsize=11, fontweight="bold")
    ax.legend(handles=[Patch(fc=body, ec=EDGE, label="logical patch / idle tube"),
                       Patch(fc=XRED, label="X-merge"), Patch(fc=ZBLUE, label="Z-merge"),
                       Patch(fc=PORTC, label="open port (in/out)")],
              loc="lower center", bbox_to_anchor=(0.5, -0.02), ncol=4, fontsize=7.6, framealpha=0.92)
    fig.savefig(os.path.join(OUT, fname), dpi=145, bbox_inches="tight"); plt.close(fig)
    print(f"  {fname}: cubes={bg.num_cubes} pipes={bg.num_pipes} ports={bg.num_ports}")


def merge_block_from_schedule(path, rounds=2):
    """Compact, tqec-validated block graph from FormalRV's verified surgery schedule:
    data and ancilla patches in a line (ancilla BETWEEN its data partners), each `Gate2q`
    coupling -> an x-merge, time compressed to a few rounds.  Small (MAJ-scale), unlike the
    full 147-cube Cuccaro tower — the repeating surgery primitive of the adder."""
    g2q = []
    for ln in open(path):
        p = ln.split()
        if p and p[0] == "GATE2Q":
            g2q.append((int(p[1]), int(p[2]), int(p[3])))
    sites = sorted({s for a, b, _ in g2q for s in (a, b)})
    adj = {s: set() for s in sites}
    for a, b, _ in g2q:
        adj[a].add(b); adj[b].add(a)
    start = min(sites, key=lambda s: (len(adj[s]), s))
    order, seen, cur = [], set(), start
    while cur is not None:
        order.append(cur); seen.add(cur)
        nxt = sorted(n for n in adj[cur] if n not in seen)
        cur = nxt[0] if nxt else next((s for s in sorted(sites) if s not in seen), None)
    xof = {s: i for i, s in enumerate(order)}
    times = sorted({t for _, _, t in g2q})[: 2 * rounds]    # keep a few rounds -> compact
    zof = {t: i + 1 for i, t in enumerate(times)}
    zmax = len(times) + 1
    bg = BlockGraph("formalrv_adder_merge_block")
    for s in sites:
        x = xof[s]
        bg.add_cube(P3(x, 0, 0), Port(), f"s{s}_in"); bg.add_cube(P3(x, 0, zmax), Port(), f"s{s}_out")
        for z in range(1, zmax):
            bg.add_cube(P3(x, 0, z), "ZXZ")
        for z in range(zmax):
            bg.add_pipe(P3(x, 0, z), P3(x, 0, z + 1))
    for a, b, t in g2q:
        if t in zof and abs(xof[a] - xof[b]) == 1:
            bg.add_pipe(P3(xof[a], 0, zof[t]), P3(xof[b], 0, zof[t]))
    bg.validate()
    return bg, {f"s{s}_in": f"site {s}" for s in sites}


if __name__ == "__main__":
    import os as _os
    ROOT = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
    print("FormalRV lattice-surgery blocks (Gidney/Fowler style):")
    render_bg(gallery.cnot(),
              "Lattice-surgery CNOT  —  3D surface-code spacetime (tqec-validated)",
              "ls_cnot.png",
              port_labels={"In_Control": "ctrl in", "Out_Control": "ctrl out",
                           "In_Target": "targ in", "Out_Target": "targ out"})
    bg, labs = merge_block_from_schedule(_os.path.join(ROOT, "PyCircuits/syscalls/ppm_block.txt"), rounds=2)
    render_bg(bg, "Adder surgery primitive (2 rounds) — from the verified schedule (tqec-validated)",
              "ls_adder_block.png", port_labels=labs, elev=18, azim=-58)
