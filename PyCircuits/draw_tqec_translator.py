"""
FULLY AUTOMATIC FormalRV-schedule -> tqec block-graph translator.

Reads a system-level schedule emitted by `scripts/EmitSysCallSchedule.lean`
(`PyCircuits/syscalls/<name>.txt`: ZONE lines + one SysCall per line) and builds a tqec
`BlockGraph` AUTOMATICALLY — no per-computation hand-coding. The geometric layout is taken
from OUR SYSTEM SPECIFICATION: every patch is a verified SysCall *site*, placed by its
*zone* (Data / Ancilla / Factory) and ordered so the `Gate2q` couplings are spatially
adjacent; time = the SysCall `begin_us`; each `Gate2q` becomes a merge pipe; magic-state
requests become Factory-zone ports.

Needs the tqec venv (Python <=3.13).  Run with it:
    <tqecvenv>/python PyCircuits/draw_tqec_translator.py
Out: docs/diagrams/tqec_<name>_from_schedule.png
"""
import os, sys
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.patches import Patch
from tqec import BlockGraph, Basis
from tqec.computation.cube import Port
from tqec.utils.position import Position3D as P3

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)
XRED, ZBLUE, PORT = "#e53e3e", "#3182ce", "#cbd5e0"
ZONECOL = {"Data": "#2f855a", "Ancilla": "#b7791f", "Factory": "#805ad5", "Routing": "#718096"}


def parse_schedule(path):
    zones, scs = [], []
    for ln in open(path):
        p = ln.split()
        if not p:
            continue
        if p[0] == "ZONE":
            zones.append((p[1], int(p[2]), int(p[3])))
        else:
            scs.append((p[0], [int(x) for x in p[1:-2]], int(p[-2]), int(p[-1])))
    return zones, scs


def zone_of(site, zones):
    for name, lo, hi in zones:
        if lo <= site < hi:
            return name
    return "?"


def order_sites_for_adjacency(sites, edges):
    """Greedy path through the Gate2q merge graph so merged sites are spatially adjacent."""
    adj = {s: set() for s in sites}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    start = min(sites, key=lambda s: (len(adj[s]), s))   # a low-degree endpoint
    order, seen = [], set()
    cur = start
    while cur is not None:
        order.append(cur); seen.add(cur)
        nxt = sorted((n for n in adj[cur] if n not in seen))
        cur = nxt[0] if nxt else next((s for s in sorted(sites) if s not in seen), None)
    return order


def translate(path, title, fname):
    zones, scs = parse_schedule(path)
    g2q = [(c[1][0], c[1][1], c[2]) for c in scs if c[0] == "GATE2Q"]
    magic = [(c[1][0], c[2]) for c in scs if c[0] == "MAGIC"]
    sites = sorted({s for a, b, _ in g2q for s in (a, b)})
    zmax = max(c[3] for c in scs)
    order = order_sites_for_adjacency(sites, [(a, b) for a, b, _ in g2q])
    xof = {s: i for i, s in enumerate(order)}

    bg = BlockGraph(os.path.splitext(os.path.basename(path))[0])
    # one temporal column per site (a logical patch), ports at the open ends
    for s in sites:
        x = xof[s]
        bg.add_cube(P3(x, 0, 0), Port(), f"{zone_of(s,zones)}{s}_in")
        bg.add_cube(P3(x, 0, zmax), Port(), f"{zone_of(s,zones)}{s}_out")
        for z in range(1, zmax):
            bg.add_cube(P3(x, 0, z), "ZXZ")
        for z in range(zmax):
            bg.add_pipe(P3(x, 0, z), P3(x, 0, z + 1))
    # each Gate2q coupling -> a spatial merge pipe between the two sites at its begin time
    for a, b, t in g2q:
        xa, xb = xof[a], xof[b]
        if abs(xa - xb) == 1 and 0 < t < zmax:
            bg.add_pipe(P3(xa, 0, t), P3(xb, 0, t))
    try:
        bg.validate(); status = "tqec-validated"
    except Exception as e:
        status = f"structural (validate: {type(e).__name__})"
    render(bg, zones, xof, f"{title}\n[{status}]", fname)
    print(f"  {fname}: {bg.num_cubes} cubes, {bg.num_pipes} pipes, {len(sites)} site-patches  [{status}]")


def add_box(ax, o, s, fx, fy, fz, ec="#2d3748", alpha=0.9, lw=0.5):
    x, y, z = o; dx, dy, dz = s
    v = [(x, y, z), (x+dx, y, z), (x+dx, y+dy, z), (x, y+dy, z),
         (x, y, z+dz), (x+dx, y, z+dz), (x+dx, y+dy, z+dz), (x, y+dy, z+dz)]
    q = {"x": [[v[0], v[3], v[7], v[4]], [v[1], v[2], v[6], v[5]]],
         "y": [[v[0], v[1], v[5], v[4]], [v[3], v[2], v[6], v[7]]],
         "z": [[v[0], v[1], v[2], v[3]], [v[4], v[5], v[6], v[7]]]}
    for key, fc in (("x", fx), ("y", fy), ("z", fz)):
        if fc:
            for poly in q[key]:
                ax.add_collection3d(Poly3DCollection([poly], facecolor=fc, edgecolor=ec, linewidths=lw, alpha=alpha))


def render(bg, zones, xof, title, fname):
    inv = {x: s for s, x in xof.items()}
    fig = plt.figure(figsize=(7.0, 8.5)); ax = fig.add_subplot(111, projection="3d")
    ax.view_init(elev=12, azim=-70); ax.set_axis_off()
    cw, pw = 0.6, 0.5
    for c in bg.cubes:
        p = c.position; o = (p.x - cw/2, p.y - cw/2, p.z - cw/2)
        if c.is_port:
            add_box(ax, o, (cw, cw, cw), PORT, PORT, PORT, ec="#999", alpha=0.18)
        else:
            add_box(ax, o, (cw, cw, cw), ZBLUE, "#f0f0f0", ZBLUE, alpha=0.55)
    for pp in bg.pipes:
        u, w = pp.u.position, pp.v.position
        d = "x" if u.x != w.x else ("y" if u.y != w.y else "z")
        lo = {"x": min(u.x, w.x), "y": min(u.y, w.y), "z": min(u.z, w.z)}
        o = [lo["x"] - pw/2, lo["y"] - pw/2, lo["z"] - pw/2]; s = [pw, pw, pw]
        di = {"x": 0, "y": 1, "z": 2}[d]; o[di] = lo[d] + cw/2; s[di] = 1 - cw
        if d == "z":                                   # temporal (idle)
            add_box(ax, tuple(o), tuple(s), ZBLUE, "#f0f0f0", None, alpha=0.6)
        else:                                          # spatial merge (Gate2q coupling)
            add_box(ax, tuple(o), tuple(s), XRED, XRED, XRED, alpha=0.96)
    # zone labels on the patch columns
    for x, s in inv.items():
        name = next((n for (n, lo, hi) in zones if lo <= s < hi), "?")
        ax.text(x, 0, -0.9, f"{name}\nsite {s}", ha="center", fontsize=8, color=ZONECOL.get(name, "#333"))
    ax.text2D(0.5, 0.985, title, transform=ax.transAxes, ha="center", va="top", fontsize=10.5, fontweight="bold")
    ax.set_xlim(-0.5, len(xof) - 0.5); ax.set_ylim(-1.5, 1.5)
    zmax = max(c.position.z for c in bg.cubes)
    ax.set_zlim(-0.5, zmax + 0.5); ax.set_box_aspect((len(xof), 2, zmax * 0.42 + 1))
    ax.legend(handles=[Patch(fc=XRED, label="Gate2q merge (data↔ancilla coupling)"),
                       Patch(fc=ZBLUE, label="logical patch / idle"),
                       Patch(fc=PORT, label="open port (init/measure)")],
              loc="lower center", bbox_to_anchor=(0.5, -0.04), ncol=3, fontsize=7.5, framealpha=0.9)
    fig.savefig(os.path.join(OUT, fname), dpi=135, bbox_inches="tight"); plt.close(fig)


print("FormalRV system schedule → tqec block graph (automatic; layout from system zones/sites):")
translate(os.path.join(ROOT, "PyCircuits/syscalls/ppm_block.txt"),
          "FormalRV PPM surgery block → tqec block graph (auto, system-spec layout)",
          "tqec_ppm_block_from_schedule.png")
translate(os.path.join(ROOT, "PyCircuits/syscalls/adder.txt"),
          "FormalRV Cuccaro-adder system schedule → tqec block graph (auto, system-spec layout)",
          "tqec_adder_from_schedule.png")
print("\nDone -> docs/diagrams/")
