"""
Render the README gadget circuit diagrams from the VERIFIED-Lean-emitted circuits.

Every circuit here is loaded from a `.qasm` / `.stim` file produced by the Lean
emitters (`scripts/EmitQASM.lean`, `scripts/EmitPPMQASM.lean`, `emit_shor_demo.lean`)
— the same Gate-IR / PPM-IR / surgery circuits FormalRV proves correct. The QPE
diagram is the only SCHEMATIC: its controlled-U block IS the emitted verified
modular multiplier, but the H / inverse-QFT frame is QPE's standard structure
(FormalRV proves the measured-phase peak bound, not a Gate-IR QFT).

Run:  python PyCircuits/draw_diagrams.py
Out:  docs/diagrams/*.png
"""
import os
import qiskit.qasm2 as q2
import qiskit.qasm3 as q3
from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit.circuit import Gate
from qiskit.visualization import circuit_drawer
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
QDIR = os.path.join(ROOT, "PyCircuits", "qasm")
OUT = os.path.join(ROOT, "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)


def save(qc, name, fold=-1, scale=1.0, title=None):
    style = {"name": "iqp"}
    circuit_drawer(qc, output="mpl", filename=os.path.join(OUT, name + ".png"),
                   fold=fold, scale=scale, style=style, plot_barriers=False)
    print(f"  drew {name}.png  ({qc.num_qubits} qubits, {qc.size()} ops)")


# --- 1/2/3: circuits emitted as OpenQASM 2 (Gate IR: X/CX/CCX) -----------------
print("OpenQASM-2 Gate-IR circuits (emitted by scripts/EmitQASM.lean):")
save(q2.load(os.path.join(QDIR, "toffoli.qasm")), "toffoli", scale=1.2)
save(q2.load(os.path.join(QDIR, "cuccaro_adder_3bit.qasm")), "cuccaro_adder_3bit", fold=40)
save(q2.load(os.path.join(QDIR, "modmult_const_2_15_7.qasm")), "modmult_const_2_15_7", fold=26)

# --- 5/6: PPM magic-state teleportation gadgets, emitted as OpenQASM 3 ----------
print("OpenQASM-3 PPM gadgets (emitted by scripts/EmitPPMQASM.lean):")
save(q3.load(os.path.join(QDIR, "t_gadget.qasm")), "t_gadget", scale=1.3)
save(q3.load(os.path.join(QDIR, "ccz_gadget.qasm")), "ccz_gadget", fold=24)

# --- 4: QPE schematic (verified peak bound; controlled-U = emitted modmult) -----
print("QPE schematic (frame standard; controlled-U is the emitted verified modmult):")
cnt = QuantumRegister(3, "ctrl")
tgt = QuantumRegister(4, "x")
cl = ClassicalRegister(3, "c")
qpe = QuantumCircuit(cnt, tgt, cl)
qpe.h(cnt[:])
qpe.x(tgt[0])  # |x> = |1>
for j in range(3):
    u = QuantumCircuit(4, name=f"U^(2^{j})  x->7^(2^{j}) x mod 15")
    u.id(range(4))  # opaque box; the real action is the emitted verified modmult
    qpe.append(u.to_gate().control(1), [cnt[j], *tgt])
qpe.append(Gate("QFT†", 3, []), cnt[:])
qpe.measure(cnt[:], cl[:])
save(qpe, "qpe_frame", scale=1.0)

# --- 7-QEC: surface-code surgery syndrome extraction (from emitted Stim) ---------
# Parse PyCircuits/surface3_surgery.stim; render its FIRST X-check + FIRST Z-check
# blocks as a faithful Qiskit circuit (RX=|+> prep, MX=X-basis meas; R/M=Z-basis).
print("QEC surface-code surgery syndrome blocks (from emitted Stim):")
stim_path = os.path.join(ROOT, "PyCircuits", "surface3_surgery.stim")
lines = [l.strip() for l in open(stim_path) if l.strip()]


def first_block(start_op, meas_op):
    """Return (ancilla, [data...]) for the first start_op..meas_op block."""
    anc, data, collecting = None, [], False
    for ln in lines:
        p = ln.split()
        if p[0] == start_op:
            anc, data, collecting = int(p[1]), [], True
        elif collecting and p[0] == "CX":
            a, b = int(p[1]), int(p[2])
            data.append(b if a == anc else a)
        elif collecting and p[0] == meas_op and int(p[1]) == anc:
            return anc, data
    return anc, data


xa, xd = first_block("RX", "MX")   # X-stabilizer: ancilla in |+>, CX anc->data, MX
za, zd = first_block("R", "M")     # Z-stabilizer: ancilla in |0>, CX data->anc, M
used = sorted(set([xa] + xd + [za] + zd))
idx = {q: i for i, q in enumerate(used)}
qr = QuantumRegister(len(used), "q")
cr = ClassicalRegister(2, "syn")
qec = QuantumCircuit(qr, cr)
# X-check block
qec.h(qr[idx[xa]])
for d in xd:
    qec.cx(qr[idx[xa]], qr[idx[d]])
qec.h(qr[idx[xa]])
qec.measure(qr[idx[xa]], cr[0])
qec.barrier()
# Z-check block
for d in zd:
    qec.cx(qr[idx[d]], qr[idx[za]])
qec.measure(qr[idx[za]], cr[1])
save(qec, "surface3_syndrome", scale=1.1)

# --- QEC: surface-code parity-check matrices (heatmap, from emitted Stim) -------
print("QEC parity-check matrices Hx / Hz (from emitted Stim):")
MERGED_N = 14  # surface3 merged code: 13 data + 1 surgery ancilla; syndrome ancillas are >= 14


def parity_rows(start_op, meas_op):
    rows, cur, anc = [], None, None
    for ln in lines:
        p = ln.split()
        if p[0] == start_op:
            cur, anc = set(), int(p[1])
        elif cur is not None and p[0] == "CX":
            a, b = int(p[1]), int(p[2])
            d = b if a == anc else a       # the data qubit this check touches
            if d < MERGED_N:
                cur.add(d)
        elif cur is not None and p[0] == meas_op and int(p[1]) == anc:
            rows.append(sorted(cur)); cur = None
    return rows


import numpy as np
hx = parity_rows("RX", "MX")
hz = parity_rows("R", "M")
Hx = np.zeros((len(hx), MERGED_N)); Hz = np.zeros((len(hz), MERGED_N))
for i, s in enumerate(hx):
    for c in s:
        Hx[i, c] = 1
for i, s in enumerate(hz):
    for c in s:
        Hz[i, c] = 1
figq, (a1, a2) = plt.subplots(1, 2, figsize=(11, 4.0))
for ax, H, name, color in [(a1, Hx, f"Hx  ({len(hx)} X-checks)", "#c53030"),
                           (a2, Hz, f"Hz  ({len(hz)} Z-checks)", "#2b6cb0")]:
    ax.imshow(H, cmap=matplotlib.colors.ListedColormap(["#f0f0f0", color]), aspect="auto")
    ax.set_title(f"surface3 [[13,1,3]] merged code: {name}", fontsize=11)
    ax.set_xlabel("data / surgery-ancilla qubit (0..13)")
    ax.set_ylabel("stabilizer (row)")
    ax.set_xticks(range(MERGED_N)); ax.set_yticks(range(H.shape[0]))
    ax.set_xticks([x - 0.5 for x in range(MERGED_N + 1)], minor=True)
    ax.set_yticks([y - 0.5 for y in range(H.shape[0] + 1)], minor=True)
    ax.grid(which="minor", color="white", linewidth=1.2)
figq.tight_layout()
figq.savefig(os.path.join(OUT, "surface3_parity.png"), dpi=130)
print(f"  drew surface3_parity.png  (Hx {Hx.shape}, Hz {Hz.shape})")

# --- 7-SCHED: verified scheduling invariants (matplotlib) -----------------------
print("System scheduling invariants (matplotlib):")
fig, (axL, axR) = plt.subplots(1, 2, figsize=(11, 4.2))

# Left: scheduleFootprint_replicate — footprint = n * 28 (surface3 gadget = 28).
n = list(range(0, 21))
axL.plot(n, [28 * k for k in n], "o-", color="#2b6cb0", lw=2, ms=4)
axL.set_title("scheduleFootprint_replicate\nfootprint = n x gadgetFootprint = 28 n", fontsize=11)
axL.set_xlabel("# surgery merges  n"); axL.set_ylabel("physical qubits")
axL.grid(alpha=0.3)
axL.annotate("28 = merged_n(14) + |hx|(8) + |hz|(6)", (10, 28 * 10),
             textcoords="offset points", xytext=(-8, 14), fontsize=9, color="#444")

# Right: gidney_ekera_2021_reproduced — verified naive ceiling vs reported.
labels = ["qubits\n(/1e6)", "time\n(hours)"]
verified = [19.4432, 20.25]      # ge2021_naive: 19.44M qubits, 20.25h naive-time ceiling
reported = [20.0, 8.0]           # ge2021 reported headline
x = range(len(labels)); w = 0.36
axR.bar([i - w / 2 for i in x], verified, w, label="FormalRV verified ceiling", color="#2f855a")
axR.bar([i + w / 2 for i in x], reported, w, label="GE2021 reported", color="#dd6b20")
axR.set_xticks(list(x)); axR.set_xticklabels(labels)
axR.set_title("gidney_ekera_2021_reproduced\nqubits: 19.44M <= 20M (~3%);  8h is 2-3x under 20.25h", fontsize=11)
axR.legend(fontsize=9); axR.grid(axis="y", alpha=0.3)

fig.tight_layout()
fig.savefig(os.path.join(OUT, "scheduling_invariants.png"), dpi=130)
print("  drew scheduling_invariants.png")

# --- SYSTEM: the zoned Architecture design (neutral_atom_mini, from Architecture.lean) ---
print("System zone design (neutral_atom_mini):")
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
figz, axz = plt.subplots(figsize=(9.5, 6.2))
axz.set_xlim(0, 10); axz.set_ylim(0, 8); axz.axis("off")
# zone id, role, capacity, (x,y), color  — verbatim from neutral_atom_mini
zones = {
    1: ("Processor", 21, (4.0, 3.4), "#2b6cb0"),
    0: ("Memory",   100, (0.4, 3.4), "#2f855a"),
    2: ("Ancilla",   10, (4.0, 0.4), "#b7791f"),
    3: ("Factory",    5, (4.0, 6.2), "#c53030"),
}
boxw, boxh = 3.0, 1.4
centers = {}
for zid, (role, cap, (x, y), col) in zones.items():
    axz.add_patch(FancyBboxPatch((x, y), boxw, boxh, boxstyle="round,pad=0.05",
                  linewidth=2, edgecolor=col, facecolor=col + "22"))
    axz.text(x + boxw / 2, y + boxh - 0.32, f"Zone {zid}: {role}", ha="center",
             fontsize=12, fontweight="bold", color=col)
    axz.text(x + boxw / 2, y + 0.42, f"capacity {cap}  ·  routing 15 µs", ha="center", fontsize=9.5, color="#333")
    centers[zid] = (x + boxw / 2, y + boxh / 2)
# channels: (src, dst, kind label) — all 15 µs latency, 99.9% fidelity, 67 transits/ms
chans = [(2, 1, "AncillaSupply"), (3, 1, "MagicSupply"), (0, 1, "MemoryLoad")]
for src, dst, kind in chans:
    (xs, ys), (xd, yd) = centers[src], centers[dst]
    axz.add_patch(FancyArrowPatch((xs, ys), (xd, yd), arrowstyle="-|>", mutation_scale=18,
                  linewidth=2, color="#555", connectionstyle="arc3,rad=0.0",
                  shrinkA=42, shrinkB=42))
    mx, my = (xs + xd) / 2, (ys + yd) / 2
    axz.text(mx, my + 0.18, kind, ha="center", fontsize=9, color="#222",
             bbox=dict(boxstyle="round,pad=0.15", fc="white", ec="#999"))
axz.text(5.0, 7.7, "FormalRV zoned Architecture — neutral_atom_mini "
         "(t_stab 1000 µs · t_react 100 µs · channels 15 µs / 99.9%)",
         ha="center", fontsize=10.5, fontweight="bold")
figz.savefig(os.path.join(OUT, "zone_design.png"), dpi=130, bbox_inches="tight")
print("  drew zone_design.png")

print("\nAll diagrams written to docs/diagrams/")
