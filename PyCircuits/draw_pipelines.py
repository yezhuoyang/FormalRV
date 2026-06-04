"""
Three pipeline diagrams:
  ppm_rules.png        — PPM rewrite rules in Litinski style, backed by FormalRV's
                         Pauli-commutation (PPM.lean) + Gottesman update (PPMOperational.lean).
  aqft_error_budget.png— Shor -> Clifford+T: the AQFT cutoff error bound 2*pi/2^c
                         (compileLadder_error_budget, AQFTCompile.lean:138).
  syscall_timeline.png — T-state/ancilla/routing scheduling: a Gantt of the verified
                         16-us PPM SysCall block (compileSurgeryGadgetToSysCalls surgery_ppm_A).

Run:  python PyCircuits/draw_pipelines.py     Out: docs/diagrams/*.png
"""
import os, math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)
PCOL = {"X": "#ED8936", "Y": "#ECC94B", "Z": "#48BB78"}


def pbox(ax, x, y, p, w=0.56, h=0.56):
    ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle="round,pad=0.02",
                 fc=PCOL[p], ec="#1a4731", lw=1.5, zorder=3))
    ax.text(x, y, p, ha="center", va="center", fontsize=12, fontweight="bold", color="white", zorder=4)


# ---------- 1. PPM rewrite rules ----------
fig, (axA, axB) = plt.subplots(1, 2, figsize=(11, 3.6))
# (a) commutation: M_ZZ ; M_XX  =  M_XX ; M_ZZ
axA.set_xlim(0, 8); axA.set_ylim(-1.2, 2.2); axA.axis("off")
for q in (0, 1):
    axA.plot([0.2, 3.4], [q, q], color="#999", lw=1.1)
    axA.plot([4.6, 7.8], [q, q], color="#999", lw=1.1)
    axA.text(0.05, q, f"$q_{q}$", ha="right", va="center", fontsize=10)
axA.plot([1, 1], [0, 1], color="#2f855a", lw=2.2); pbox(axA, 1, 0, "Z"); pbox(axA, 1, 1, "Z")
axA.plot([2.4, 2.4], [0, 1], color="#9c4221", lw=2.2); pbox(axA, 2.4, 0, "X"); pbox(axA, 2.4, 1, "X")
axA.plot([5.4, 5.4], [0, 1], color="#9c4221", lw=2.2); pbox(axA, 5.4, 0, "X"); pbox(axA, 5.4, 1, "X")
axA.plot([6.8, 6.8], [0, 1], color="#2f855a", lw=2.2); pbox(axA, 6.8, 0, "Z"); pbox(axA, 6.8, 1, "Z")
axA.text(4.0, 0.5, "=", ha="center", va="center", fontsize=22)
axA.set_title("(a) commuting PPMs reorder", fontsize=11, fontweight="bold")
axA.text(4.0, -0.9, r"$Z\!\otimes\!Z$ and $X\!\otimes\!X$ share an even # of anticommuting sites"
                    "\n→ commutes  (PPM.lean: commutes / commutes_self)", ha="center", fontsize=8.6, color="#444")

# (b) Gottesman measurement update: stab <X> --M_Z--> stab <Z>
axB.set_xlim(0, 8); axB.set_ylim(-1.2, 2.2); axB.axis("off")
axB.plot([0.4, 7.6], [0.6, 0.6], color="#999", lw=1.1)
axB.text(0.25, 0.6, r"$|+\rangle$", ha="right", va="center", fontsize=10)
axB.text(1.1, 1.5, "stabilizer", ha="center", fontsize=8.5, color="#444")
pbox(axB, 1.1, 0.6, "X")
axB.add_patch(FancyArrowPatch((2.1, 0.6), (4.3, 0.6), arrowstyle="-|>", mutation_scale=16, lw=2, color="#555"))
axB.text(3.2, 1.0, r"measure $Z$", ha="center", fontsize=9.5, color="#222")
axB.text(3.2, 0.18, r"$apply\_PPM\_pos$", ha="center", fontsize=8.2, color="#666")
pbox(axB, 5.3, 0.6, "Z")
axB.text(5.3, 1.5, "new stabilizer", ha="center", fontsize=8.5, color="#444")
axB.set_title("(b) measuring an anticommuting Pauli replaces the stabilizer", fontsize=10.5, fontweight="bold")
axB.text(4.0, -0.9, r"$Z$ anticommutes $X$  ⇒  stabilizer $X \mapsto Z$  (PPM_Z_on_plus_pos),"
                    "\npreserving validity (PPM_preserves_validity_plus_Z)", ha="center", fontsize=8.6, color="#444")
fig.suptitle("PPM rewrite rules — backed by FormalRV's Pauli algebra + Gottesman update (decide-checked)",
             fontsize=11.5, fontweight="bold")
fig.tight_layout(rect=[0, 0, 1, 0.93])
fig.savefig(os.path.join(OUT, "ppm_rules.png"), dpi=140, bbox_inches="tight"); plt.close(fig)
print("  drew ppm_rules.png")

# ---------- 2. AQFT error budget ----------
fig, ax = plt.subplots(figsize=(7.2, 4.2))
cs = list(range(0, 7))
err = [2 * math.pi / 2 ** c for c in cs]
ax.plot(cs, err, "o-", color="#805ad5", lw=2, ms=6)
ax.axhline(0, color="#ccc", lw=0.8)
ax.annotate(f"c=2 → ≤ π/2 ≈ {math.pi/2:.3f}", (2, math.pi / 2), textcoords="offset points",
            xytext=(18, 14), fontsize=10, color="#44337a",
            arrowprops=dict(arrowstyle="->", color="#44337a"))
ax.scatter([2], [math.pi / 2], s=90, color="#d53f8c", zorder=5)
ax.set_title("Shor → Clifford+T: approximate-QFT cutoff error\n"
             "compileLadder_error_budget:  Σ_{m≥c} π/2^m ≤ 2π/2^c  (Verified, no axiom)", fontsize=11)
ax.set_xlabel("AQFT cutoff c  (keep rotations of depth m < c)")
ax.set_ylabel("max ladder error  (radians)")
ax.grid(alpha=0.3)
ax.text(3.4, 4.6, "kept rotations are Clifford+T:\n m=0 → S/S†,  m=1 → T/T†\n(compileLadder_isCliffordT, c≤2)",
        fontsize=9, color="#444", bbox=dict(boxstyle="round,pad=0.3", fc="#faf5ff", ec="#b794f4"))
fig.tight_layout()
fig.savefig(os.path.join(OUT, "aqft_error_budget.png"), dpi=140, bbox_inches="tight"); plt.close(fig)
print("  drew aqft_error_budget.png")

# ---------- 3. SysCall scheduling timeline (one verified 16-us PPM block) ----------
# from compileSurgeryGadgetToSysCalls surgery_ppm_A: 3 rounds x (FreshAnc,Gate2q,Gate2q,Meas,Decode)+PFU
rows = ["RequestFreshAncilla", "Gate2q", "Measure", "DecodeSyndrome", "PauliFrameUpdate"]
rcol = {"RequestFreshAncilla": "#38a169", "Gate2q": "#3182ce", "Measure": "#dd6b20",
        "DecodeSyndrome": "#e53e3e", "PauliFrameUpdate": "#805ad5"}
# (row, begin, end) — exact from compileSurgeryGadgetRound (5*round offset)
bars = []
for r in range(3):
    t = 5 * r
    bars += [("RequestFreshAncilla", t, t + 1), ("Gate2q", t + 1, t + 2), ("Gate2q", t + 2, t + 3),
             ("Measure", t + 3, t + 4), ("DecodeSyndrome", t + 4, t + 5)]
bars.append(("PauliFrameUpdate", 15, 16))
fig, ax = plt.subplots(figsize=(11, 3.8))
yof = {k: i for i, k in enumerate(reversed(rows))}
for (k, b, e) in bars:
    ax.add_patch(plt.Rectangle((b, yof[k] - 0.34), e - b, 0.68, fc=rcol[k], ec="#222", lw=0.8))
ax.set_yticks(range(len(rows))); ax.set_yticklabels(list(reversed(rows)), fontsize=10)
ax.set_xlim(-0.3, 16.5); ax.set_ylim(-0.9, len(rows) + 0.15)
ax.set_xlabel("time (µs)  —  ancilla site 100 (zone 1), data sites 0 & 50 (zone 0)")
ax.set_xticks(range(0, 17))
ax.set_title("Scheduling T-state / ancilla / routing — verified 16-µs PPM block\n"
             "compileSurgeryGadgetToSysCalls surgery_ppm_A  (adder_n1_strict_system_ok, native_decide)",
             fontsize=11)
# ancilla lifecycle annotations on the RequestFreshAncilla / Measure row
ax.text(0.5, len(rows) - 0.55, "site100\nFree→Live", fontsize=7.2, ha="center", va="bottom", color="#276749")
ax.text(3.5, 2.5, "Live→Dirty", fontsize=7.2, ha="center", color="#9c4221")
ax.text(5.5, len(rows) - 0.55, "Dirty→Live\n(re-alloc)", fontsize=7.2, ha="center", va="bottom", color="#276749")
# feedback-after-decode causal edge: DecodeSyndrome(2) [14,15) -> PauliFrameUpdate(0) [15,16)
ax.annotate("", xy=(15, 0), xytext=(14.5, 1), arrowprops=dict(arrowstyle="->", ls="--", color="#444"))
ax.text(13.7, 0.5, "feedback_after_decode_ok\n(decode ends ≤ feedback begins)", fontsize=7.4, ha="right", color="#444")
ax.text(8, -0.62, "operation_capacity_ok: max_gate2q_active = 1 → Gate2q never overlap", fontsize=8.4, ha="center", color="#555")
fig.tight_layout()
fig.savefig(os.path.join(OUT, "syscall_timeline.png"), dpi=140, bbox_inches="tight"); plt.close(fig)
print("  drew syscall_timeline.png")

print("\nPipeline diagrams written to docs/diagrams/")
