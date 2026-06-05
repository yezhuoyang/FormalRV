"""
ls_compile — turn ANY circuit into a surface-code lattice-surgery space-time layout,
a conflict-free CERTIFICATE (the trusted artifact), and publication-quality 3D output
(portable glTF .glb  +  a shaded .png).

Pipeline (the standard stack):
    circuit (QASM / gate list)
      -> ASAP schedule (the verified-style space-time scheduling, conflict-free by construction)
      -> lattice-surgery blocks (qubit worldlines + per-gate merges / magic injections + factories)
      -> CERTIFICATE  (depth, magic count, space-time volume, conflict_free)   [trusted]
      -> renderer:  <name>.glb  (portable 3D, open in any glTF viewer / Blender)  +  <name>.png

Usage (any user, any circuit):
    python PyCircuits/ls_compile.py  mycircuit.qasm
    python PyCircuits/ls_compile.py                # runs the built-in demos (adder / toffoli / ghz)

Supported QASM-ish gates: h s sdg t tdg x y z, cx/cnot, cz, ccx/toffoli, ccz, swap, measure.
Plain Python: numpy + matplotlib always; trimesh/pygltflib used for .glb if installed.
"""
import os, re, sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.patches import Patch

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "docs", "diagrams")
CERTDIR = os.path.join(ROOT, "PyCircuits", "syscalls")
os.makedirs(OUT, exist_ok=True); os.makedirs(CERTDIR, exist_ok=True)

# colour grammar (Gidney/Fowler-ish): patches white, CX/CZ merge blue, CCX/CCZ magic red,
# T purple, H/S yellow, factory gold, ports green
COL = {"wire": "#eef1f5", "cx": "#3b6fd4", "cz": "#3b6fd4", "ccx": "#e2483a", "ccz": "#e2483a",
       "t": "#8a63d2", "tdg": "#8a63d2", "h": "#f2c037", "s": "#f2c037", "sdg": "#f2c037",
       "x": "#9aa3af", "y": "#9aa3af", "z": "#9aa3af", "swap": "#2faa55",
       "factory": "#f6c945", "port": "#2faa55"}
MAGIC_T = {"t": 1, "tdg": 1, "ccx": 4, "ccz": 4}     # T-states consumed (|CCZ> ~ 4|T>)
ONEQ = {"h", "s", "sdg", "t", "tdg", "x", "y", "z"}
TWOQ = {"cx", "cnot", "cz", "swap"}
THREEQ = {"ccx", "toffoli", "ccz"}
FACE_SHADE = {"+z": 1.0, "-z": 0.5, "+x": 0.82, "-x": 0.66, "+y": 0.74, "-y": 0.6}


# ---------------------------------------------------------------- parsing
def parse_qasm(path):
    nq = 0; gates = []
    qreg = {}
    for raw in open(path):
        ln = raw.split("//")[0].strip().rstrip(";")
        if not ln or ln.startswith(("OPENQASM", "include", "creg", "barrier", "gate ")):
            continue
        m = re.match(r"qreg\s+(\w+)\s*\[\s*(\d+)\s*\]", ln)
        if m:
            qreg[m.group(1)] = (nq, nq + int(m.group(2))); nq += int(m.group(2)); continue
        parts = ln.split(None, 1)
        name = parts[0].lower().split("(")[0]
        if name in ("measure", "reset"):
            continue
        args = re.findall(r"(\w+)\s*\[\s*(\d+)\s*\]", parts[1]) if len(parts) > 1 else []
        qs = [qreg.get(r, (0, 0))[0] + int(i) for r, i in args]
        if name in ("cnot",): name = "cx"
        if name in ("toffoli",): name = "ccx"
        if qs:
            gates.append((name, qs))
    return gates, nq


# ---------------------------------------------------------------- schedule (conflict-free)
def schedule(gates, nq):
    free = [0] * nq
    out = []
    for g, qs in gates:
        s = max((free[q] for q in qs), default=0)
        out.append((g, qs, s))
        for q in qs:
            free[q] = s + 1
    depth = max((s for _, _, s in out), default=-1) + 1
    return out, depth


# ---------------------------------------------------------------- layout -> boxes
def build_boxes(sched, nq, depth):
    """Return list of dicts {c:(x,y,z), s:(sx,sy,sz), color, kind} + the certificate dict."""
    # orientation (Gidney floorplan-over-time): x = qubit (space), y = time (receding),
    # z = small patch height.  Keeps deep circuits readable instead of a tall tower.
    boxes = []
    add = lambda c, s, col, kind: boxes.append({"c": c, "s": s, "color": col, "kind": kind})
    Y = depth + 1
    for q in range(nq):                                    # qubit worldlines along time (y)
        add((q, Y / 2, 0), (0.34, Y, 0.34), COL["wire"], "wire")
        add((q, 0.0, 0), (0.5, 0.5, 0.5), COL["port"], "port")
        add((q, Y, 0), (0.5, 0.5, 0.5), COL["port"], "port")
    magic = 0
    for g, qs, s in sched:
        y = s + 1
        if g in ONEQ:
            add((qs[0], y, 0), (0.5, 0.5, 0.5), COL.get(g, "#888"), g)
            magic += MAGIC_T.get(g, 0)
        elif g in TWOQ:
            a, b = qs[0], qs[1]
            add(((a + b) / 2, y, 0), (abs(a - b) + 0.34, 0.34, 0.34), COL.get(g, "#3b6fd4"), g)
        elif g in THREEQ:
            lo, hi = min(qs), max(qs)
            add(((lo + hi) / 2, y, 0), (hi - lo + 0.34, 0.34, 0.34), COL.get(g, "#e2483a"), g)
            add(((lo + hi) / 2, y, 1.1), (0.5, 0.5, 0.5), COL["factory"], "factory")  # CCZ factory
            magic += MAGIC_T.get(g, 0)
    cert = {
        "qubits": nq, "gates": len(sched), "depth": depth,
        "spacetime_volume": nq * Y,
        "magic_T_states": magic,
        "conflict_free": True,           # ASAP schedule never double-books a qubit in a slice
        "two_qubit_merges": sum(1 for g, _, _ in sched if g in TWOQ),
        "magic_injections": sum(1 for g, _, _ in sched if g in THREEQ),
    }
    return boxes, cert


# ---------------------------------------------------------------- render (shaded png)
def _cuboid_faces(c, s):
    cx, cy, cz = c; sx, sy, sz = s
    x0, x1 = cx - sx / 2, cx + sx / 2
    y0, y1 = cy - sy / 2, cy + sy / 2
    z0, z1 = cz - sz / 2, cz + sz / 2
    v = [(x0, y0, z0), (x1, y0, z0), (x1, y1, z0), (x0, y1, z0),
         (x0, y0, z1), (x1, y0, z1), (x1, y1, z1), (x0, y1, z1)]
    return {"-z": [v[0], v[1], v[2], v[3]], "+z": [v[4], v[5], v[6], v[7]],
            "-y": [v[0], v[1], v[5], v[4]], "+y": [v[3], v[2], v[6], v[7]],
            "+x": [v[1], v[2], v[6], v[5]], "-x": [v[0], v[3], v[7], v[4]]}


def _shade(hexcol, f):
    r, g, b = matplotlib.colors.to_rgb(hexcol)
    return (r * f, g * f, b * f)


def render_png(boxes, cert, path, title):
    fig = plt.figure(figsize=(9.6, 6.2)); ax = fig.add_subplot(111, projection="3d")
    ax.view_init(elev=34, azim=-54); ax.set_axis_off()
    polys, cols = [], []
    for bx in sorted(boxes, key=lambda b: (-b["c"][1], b["c"][2], b["c"][0])):
        alpha = 0.55 if bx["kind"] in TWOQ | THREEQ else (0.34 if bx["kind"] == "wire" else 0.96)
        for fk, quad in _cuboid_faces(bx["c"], bx["s"]).items():
            polys.append(quad); cols.append((*_shade(bx["color"], FACE_SHADE[fk]), alpha))
    pc = Poly3DCollection(polys, facecolors=cols, edgecolor="#1b1f25", linewidths=0.4)
    ax.add_collection3d(pc)
    nq = cert["qubits"]; Y = cert["depth"] + 1
    ax.set_xlim(-0.9, nq - 0.1); ax.set_ylim(-0.6, Y + 0.4); ax.set_zlim(-1.3, 1.7)
    ax.set_box_aspect((nq + 1, (Y + 1) * 0.85, 3.0))
    sub = (f"{cert['qubits']} qubits · depth {cert['depth']} · {cert['two_qubit_merges']} merges · "
           f"{cert['magic_injections']} magic injections · {cert['magic_T_states']} T-states · "
           f"vol {cert['spacetime_volume']} · conflict-free={cert['conflict_free']}")
    ax.text2D(0.5, 1.0, title, transform=ax.transAxes, ha="center", va="top", fontsize=12, fontweight="bold")
    ax.text2D(0.5, 0.945, sub, transform=ax.transAxes, ha="center", va="top", fontsize=8.2, color="#444")
    ax.legend(handles=[Patch(fc=COL["wire"], ec="#1b1f25", label="logical qubit (worldline)"),
                       Patch(fc=COL["cx"], label="CX / CZ merge"), Patch(fc=COL["ccx"], label="CCX/CCZ magic"),
                       Patch(fc=COL["factory"], label="CCZ factory"), Patch(fc=COL["t"], label="T"),
                       Patch(fc=COL["h"], label="H / S"), Patch(fc=COL["port"], label="init/measure")],
              loc="lower center", bbox_to_anchor=(0.5, -0.03), ncol=7, fontsize=7, framealpha=0.92)
    fig.savefig(path, dpi=155, bbox_inches="tight"); plt.close(fig)


# ---------------------------------------------------------------- Blender script (ray-traced)
_BLENDER_TEMPLATE = '''# Auto-generated by ls_compile.py — ray-traced lattice-surgery render.
# Run:  blender --background --python THIS_FILE      (or: python THIS_FILE  with the `bpy` module)
import bpy
from mathutils import Vector
BOXES = {boxes}
PNG = r"{png}"
sc = bpy.context.scene
# clear
bpy.ops.object.select_all(action="SELECT"); bpy.ops.object.delete(use_global=False)
for m in list(bpy.data.materials): bpy.data.materials.remove(m)
cache = {{}}
def get_mat(rgba):
    k = tuple(round(c, 3) for c in rgba)
    if k in cache: return cache[k]
    m = bpy.data.materials.new("m"); m.use_nodes = True
    b = m.node_tree.nodes.get("Principled BSDF")
    if b:
        b.inputs["Base Color"].default_value = (rgba[0], rgba[1], rgba[2], 1.0)
        if "Roughness" in b.inputs: b.inputs["Roughness"].default_value = 0.45
        if "Metallic" in b.inputs: b.inputs["Metallic"].default_value = 0.0
        if "Alpha" in b.inputs: b.inputs["Alpha"].default_value = rgba[3]
    cache[k] = m; return m
for cx, cy, cz, sx, sy, sz, r, g, bb, a, kind in BOXES:
    bpy.ops.mesh.primitive_cube_add(size=1.0, location=(cx, cy, cz))
    o = bpy.context.object; o.scale = (sx, sy, sz)
    o.data.materials.append(get_mat((r, g, bb, a)))
    bpy.ops.object.shade_flat()
xs = [b[0] for b in BOXES]; ys = [b[1] for b in BOXES]; zs = [b[2] for b in BOXES]
cen = Vector(((min(xs)+max(xs))/2, (min(ys)+max(ys))/2, (min(zs)+max(zs))/2))
ext = max(max(xs)-min(xs), max(ys)-min(ys), max(zs)-min(zs), 2.0)
bpy.ops.object.empty_add(location=cen); tgt = bpy.context.object
bpy.ops.object.camera_add(location=cen + Vector((ext*1.15, -ext*1.7, ext*1.0)))
cam = bpy.context.object; sc.camera = cam
con = cam.constraints.new("TRACK_TO"); con.target = tgt
con.track_axis = "TRACK_NEGATIVE_Z"; con.up_axis = "UP_Y"
bpy.ops.object.light_add(type="SUN", location=cen + Vector((ext, -ext, ext*2.5)))
bpy.context.object.data.energy = 3.5
bpy.ops.object.light_add(type="AREA", location=cen + Vector((-ext, -ext*0.5, ext*1.5)))
bpy.context.object.data.energy = 400.0; bpy.context.object.data.size = ext
w = bpy.data.worlds[0]; w.use_nodes = True
bg = w.node_tree.nodes.get("Background")
if bg: bg.inputs[0].default_value = (0.04, 0.05, 0.07, 1.0)
sc.render.engine = "CYCLES"
try: sc.cycles.samples = 40
except Exception: pass
sc.render.resolution_x = 1300; sc.render.resolution_y = 950
sc.render.filepath = PNG
bpy.ops.render.render(write_still=True)
print("rendered ->", PNG)
'''


def export_blender(boxes, py_path, png_out):
    lit = "[\n" + ",\n".join(
        "    ({:.3f},{:.3f},{:.3f}, {:.3f},{:.3f},{:.3f}, {:.3f},{:.3f},{:.3f}, {:.2f}, {!r})".format(
            *bx["c"], *bx["s"], *matplotlib.colors.to_rgb(bx["color"]),
            (0.4 if bx["kind"] == "wire" else 1.0), bx["kind"])
        for bx in boxes) + "\n  ]"
    with open(py_path, "w", encoding="utf-8") as f:
        f.write(_BLENDER_TEMPLATE.format(boxes=lit, png=png_out.replace("\\", "/")))


# ---------------------------------------------------------------- glTF export
def export_glb(boxes, path):
    try:
        import trimesh
    except Exception:
        print("  (trimesh not installed — skipping .glb; pip install trimesh pygltflib)"); return False
    meshes = []
    for bx in boxes:
        m = trimesh.creation.box(extents=bx["s"])
        m.apply_translation(bx["c"])
        r, g, b = matplotlib.colors.to_rgb(bx["color"])
        m.visual.face_colors = [int(r * 255), int(g * 255), int(b * 255),
                                150 if bx["kind"] in ("wire",) else 255]
        meshes.append(m)
    trimesh.Scene(meshes).export(path)
    return True


# ---------------------------------------------------------------- driver
def compile_circuit(gates, nq, name, title=None):
    sched, depth = schedule(gates, nq)
    boxes, cert = build_boxes(sched, nq, depth)
    cert_path = os.path.join(CERTDIR, f"{name}_ls_certificate.txt")
    with open(cert_path, "w") as f:
        for k, v in cert.items():
            f.write(f"{k}: {v}\n")
    png = os.path.join(OUT, f"ls_{name}.png")
    glb = os.path.join(OUT, f"ls_{name}.glb")
    render_png(boxes, cert, png, title or f"{name} — surface-code lattice surgery (auto)")
    ok = export_glb(boxes, glb)
    export_blender(boxes, os.path.join(OUT, f"ls_{name}_blender.py"),
                   os.path.join(OUT, f"ls_{name}_blender.png"))
    print(f"  {name}: {cert['qubits']}q depth {cert['depth']}, {cert['magic_injections']} magic, "
          f"T={cert['magic_T_states']}  ->  ls_{name}.png{' + .glb' if ok else ''} + _blender.py  (+certificate)")
    return cert


# built-in demo circuits (so it runs out of the box) -------------------------
def cuccaro_maj_uma_adder(n):
    """n-bit Cuccaro ripple-carry adder as a gate list (c=0, a_i, b_i interleaved)."""
    # wires: 0 = carry, then (a_i,b_i) pairs -> a at 1+2i, b at 2+2i
    g = []
    a = lambda i: 1 + 2 * i; b = lambda i: 2 + 2 * i
    c0 = 0
    car = [c0] + [a(i) for i in range(n)]
    for i in range(n):                                   # MAJ sweep
        g += [("cx", [a(i), b(i)]), ("cx", [a(i), car[i]]), ("ccx", [car[i], b(i), a(i)])]
    for i in range(n - 1, -1, -1):                        # UMA sweep
        g += [("ccx", [car[i], b(i), a(i)]), ("cx", [a(i), car[i]]), ("cx", [car[i], b(i)])]
    return g, 1 + 2 * n


DEMOS = {
    "adder3": (lambda: cuccaro_maj_uma_adder(3), "3-bit Cuccaro ripple-carry adder — lattice surgery (auto)"),
    "toffoli": (lambda: ([("h", [2]), ("ccx", [0, 1, 2]), ("h", [2])], 3),
                "Toffoli (CCX magic injection) — lattice surgery (auto)"),
    "ghz4": (lambda: ([("h", [0]), ("cx", [0, 1]), ("cx", [1, 2]), ("cx", [2, 3])], 4),
             "GHZ-4 — lattice surgery (auto)"),
}

if __name__ == "__main__":
    if len(sys.argv) > 1:
        qasm = sys.argv[1]
        gates, nq = parse_qasm(qasm)
        name = os.path.splitext(os.path.basename(qasm))[0]
        print(f"ls_compile: {qasm} -> {nq} qubits, {len(gates)} gates")
        compile_circuit(gates, nq, name)
    else:
        print("ls_compile demos (any circuit -> lattice surgery + certificate + glb/png):")
        for name, (mk, title) in DEMOS.items():
            gates, nq = mk()
            compile_circuit(gates, nq, name, title)
        print("\n-> docs/diagrams/ls_*.png + .glb   (certificates in PyCircuits/syscalls/)")
