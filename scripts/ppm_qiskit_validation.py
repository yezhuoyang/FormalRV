# PPM-vs-Qiskit numerical validation
# ----------------------------------
# Independently validates the FormalRV PauliRotation->PPM lowering:
#   the Python interpreter below mirrors the Lean branch semantics
#   (stmtDenote/progDenote) STATEMENT BY STATEMENT, and Qiskit supplies
#   the reference unitaries (CX, CCZ, CCX, T-rotations).
# Conventions match the Lean development exactly:
#   - wire q <-> bit q of the index (little-endian; same as Qiskit),
#   - Y entry convention: (Yv)(i) = (+/- i) v(i ^ 2^q), -i iff source bit set,
#   - measurements apply branch projectors (1 +/- P)/2 immediately,
#   - corrections apply their Pauli immediately (the decided convention).
import numpy as np, itertools, sys
from qiskit import QuantumCircuit
from qiskit.quantum_info import Operator

rng = np.random.default_rng(11)
FAIL = []

def check(name, ok):
    print(('PASS  ' if ok else 'FAIL  ') + name)
    if not ok:
        FAIL.append(name)

# ---------- Pauli-product action (mirrors axisMat) ----------
def apply_axis(v, axis, n):
    idx = np.arange(2 ** n)
    flip = 0
    for (q, k) in axis:
        if k in ('x', 'y'):
            flip ^= 1 << q
    src = idx ^ flip
    phase = np.ones(2 ** n, complex)
    for (q, k) in axis:
        bits = (src >> q) & 1
        if k == 'z':
            phase = phase * (1 - 2 * bits)
        elif k == 'y':
            phase = phase * (1j * (1 - 2 * bits))
    return phase * v[src]

def proj_half(v, axis, n, outcome):
    s = -1 if outcome else 1
    return 0.5 * (v + s * apply_axis(v, axis, n))

# ---------- PPM branch interpreter (mirrors stmtDenote/progDenote) ----------
def xor_parity(outs, sel):
    p = False
    for c in sel:
        p ^= (outs[c] if c < len(outs) else False)
    return p

def q_parity(outs, mons):
    p = False
    for mon in mons:
        a = True
        for c in mon:
            a = a and (outs[c] if c < len(outs) else False)
        p ^= a
    return p

def prog_denote(v, prog, n, omega):
    outs = []
    for st in prog:
        kind = st[0]
        o = omega[len(outs)] if kind in ('measure', 'measureSel', 'measureSel2') else None
        if kind == 'measure':
            _, dst, P = st
            v = proj_half(v, P, n, o); outs.append(o)
        elif kind == 'measureSel':
            _, sel, dst, Pt, Pe = st
            v = proj_half(v, Pt if xor_parity(outs, sel) else Pe, n, o); outs.append(o)
        elif kind == 'measureSel2':
            _, s1, s2, dst, P00, P01, P10, P11 = st
            a, b = xor_parity(outs, s1), xor_parity(outs, s2)
            P = (P11 if b else P10) if a else (P01 if b else P00)
            v = proj_half(v, P, n, o); outs.append(o)
        elif kind == 'frame':
            v = apply_axis(v, st[1], n)
        elif kind == 'correct':
            _, par, thn, els = st
            v = apply_axis(v, thn if xor_parity(outs, par) else els, n) \
                if (thn if xor_parity(outs, par) else els) else v
        elif kind == 'correctQ':
            _, mons, thn, els = st
            P = thn if q_parity(outs, mons) else els
            v = apply_axis(v, P, n) if P else v
        elif kind in ('useT', 'useCCZ'):
            pass
    return v, outs

# ---------- The rotation IR + lowering (mirrors Compile/Lowering) ----------
def rot_of(theta, axis, n):
    def f(v):
        return np.cos(theta) * v - 1j * np.sin(theta) * apply_axis(v, axis, n)
    return f

ANGLE = {'pi': np.pi, 'half': np.pi / 2, 'quarter': np.pi / 4, 'eighth': np.pi / 8}

def seq_denote(v, rots, n):
    for (neg, ang, axis) in rots:
        th = -ANGLE[ang] if neg else ANGLE[ang]
        v = rot_of(th, axis, n)(v)
    return v

def lower_rot(a, c, neg, ang, axis):
    if ang == 'pi':
        return []
    if ang == 'half':
        return [('frame', axis)]
    if ang == 'quarter':
        prog = [('measure', c, axis + [(a, 'z')]),
                ('measure', c + 1, [(a, 'x')]),
                ('correct', [c, c + 1], axis, [])]
        if neg:
            prog.append(('frame', axis))
        return prog
    if ang == 'eighth':
        return [('useT', a),
                ('measure', c, axis + [(a, 'z')]),
                ('measureSel', [c], c + 1, [(a, 'y')], [(a, 'x')]),
                ('correct', [c, c + 1] if neg else [c + 1], axis, [])]

def lower_flat(a, c, rots):
    prog = []
    for (neg, ang, axis) in rots:
        prog += lower_rot(a, c, neg, ang, axis)
        if ang in ('quarter', 'eighth'):
            a += 1; c += 2
    return prog

def anc_in_amp(neg, ang):
    if ang == 'quarter':
        return 1j
    if ang == 'eighth':
        return np.exp(-1j * np.pi / 4) if neg else np.exp(1j * np.pi / 4)
    return None

def lowered_input(psi, rots, m):
    v = psi
    n = m
    for (neg, ang, axis) in rots:
        amp = anc_in_amp(neg, ang)
        if amp is not None:
            v = np.concatenate([v, amp * v]); n += 1
    return v, n

# ---------- The gate dictionary (mirrors Compile.lean) ----------
def mk2(c, kc, t, kt):
    return [(c, kc), (t, kt)] if c < t else [(t, kt), (c, kc)]

def h_rots(q):
    return [(False, 'quarter', [(q, 'z')]), (False, 'quarter', [(q, 'x')]),
            (False, 'quarter', [(q, 'z')])]

def cx_rots(c, t):
    return [(False, 'quarter', mk2(c, 'z', t, 'x')),
            (True, 'quarter', [(c, 'z')]), (True, 'quarter', [(t, 'x')])]

def ccz_rots(a, b, c):
    return [(False, 'eighth', [(a, 'z')]), (False, 'eighth', [(b, 'z')]),
            (False, 'eighth', [(c, 'z')]),
            (True, 'eighth', [(a, 'z'), (b, 'z')]),
            (True, 'eighth', [(a, 'z'), (c, 'z')]),
            (True, 'eighth', [(b, 'z'), (c, 'z')]),
            (False, 'eighth', [(a, 'z'), (b, 'z'), (c, 'z')])]

def ccx_rots(a, b, t):
    s = sorted([a, b, t])
    return h_rots(t) + ccz_rots(*s) + h_rots(t)

# ---------- helpers ----------
def qiskit_unitary(build, n):
    qc = QuantumCircuit(n)
    build(qc)
    return Operator(qc).data  # little-endian, matches our convention

def split_data_anc(v, m, n):
    return v.reshape(2 ** (n - m), 2 ** m)  # [anc, data]

def proportional(u, w):
    nu, nw = np.linalg.norm(u), np.linalg.norm(w)
    if nu < 1e-12 or nw < 1e-12:
        return nu < 1e-12 and nw < 1e-12
    k = np.argmax(np.abs(u))
    return np.allclose(u / u[k], w / w[k], atol=1e-9)

def branch_data_ok(v, m, n, target):
    # v should be (scalar) * target (x) (collapsed ancillas): rank-1 with data factor prop. to target
    W = split_data_anc(v, m, n)
    c = W @ target.conj()
    R = np.outer(c, target) / (target.conj() @ target)
    return np.allclose(R, W, atol=1e-9)

def validate_gadget(name, rots, m, U_ref, n_branches='all', samples=300):
    psi = rng.normal(size=2 ** m) + 1j * rng.normal(size=2 ** m)
    psi /= np.linalg.norm(psi)
    target = U_ref @ psi
    prog = lower_flat(m, 0, rots)
    v0, n = lowered_input(psi, rots, m)
    slots = sum(2 for (neg, ang, _) in rots if ang in ('quarter', 'eighth'))
    # consistency: lowered rotation semantics == reference (up to global phase)
    check(f'{name}: rotation-IR semantics == Qiskit unitary (up to phase)',
          proportional(seq_denote(psi.copy(), rots, m), target))
    branches = (itertools.product([False, True], repeat=slots) if n_branches == 'all'
                else (tuple(rng.integers(0, 2, slots).astype(bool)) for _ in range(samples)))
    ok, total_prob = True, 0.0
    norm_in = np.linalg.norm(v0)
    exhaustive = n_branches == 'all'
    for om in branches:
        v, outs = prog_denote(v0.copy(), prog, n, list(om))
        if not branch_data_ok(v, m, n, target):
            ok = False
            print('   branch FAILED:', om)
            break
        if exhaustive:
            total_prob += (np.linalg.norm(v) / norm_in) ** 2
    check(f'{name}: lowered PPM == {name} on data, EVERY branch '
          f'({"all " + str(2**slots) if exhaustive else str(samples) + " sampled"})', ok)
    if exhaustive:
        check(f'{name}: branch probabilities sum to 1',
              abs(total_prob - 1) < 1e-9)

print('=== 1. T-block: pi/8 rotation lowering (both chiralities, all 4 branches) ===')
for neg in (False, True):
    th = -np.pi / 8 if neg else np.pi / 8
    qc = QuantumCircuit(1); qc.rz(2 * th, 0)
    U = Operator(qc).data * np.exp(1j * th)  # e^{-i th Z}
    validate_gadget(f'T-block(neg={neg})', [(neg, 'eighth', [(0, 'z')])], 1, U)

print('=== 2. S-block: pi/4 rotation lowering (both chiralities) ===')
for neg in (False, True):
    th = -np.pi / 4 if neg else np.pi / 4
    qc = QuantumCircuit(1); qc.rz(2 * th, 0)
    U = Operator(qc).data * np.exp(1j * th)
    validate_gadget(f'S-block(neg={neg})', [(neg, 'quarter', [(0, 'z')])], 1, U)

print('=== 3. CX gadget: dictionary + full lowering, all 64 branches ===')
validate_gadget('CX(0,1)', cx_rots(0, 1), 2,
                qiskit_unitary(lambda qc: qc.cx(0, 1), 2))

print('=== 4. CCZ via 7T (route A), sampled branches (2^14 total) ===')
validate_gadget('CCZ-7T', ccz_rots(0, 1, 2), 3,
                qiskit_unitary(lambda qc: qc.ccz(0, 1, 2), 3),
                n_branches='sample', samples=200)

print('=== 5. CCX (Toffoli): H-conjugated CCZ, sampled branches (2^26 total) ===')
validate_gadget('CCX(0,1,2)', ccx_rots(0, 1, 2), 3,
                qiskit_unitary(lambda qc: qc.ccx(0, 1, 2), 3),
                n_branches='sample', samples=100)

print('=== 6. Composed circuit CX;CCX;CX, sampled branches ===')
rots_combo = cx_rots(0, 1) + ccx_rots(0, 1, 2) + cx_rots(1, 2)
def build_combo(qc):
    qc.cx(0, 1); qc.ccx(0, 1, 2); qc.cx(1, 2)
validate_gadget('CX;CCX;CX', rots_combo, 3,
                qiskit_unitary(build_combo, 3), n_branches='sample', samples=100)

print('=== 7. ROUTE B: the 1-CCZ teleport block as PPM statements, ALL 64 branches ===')
# the exact statement list the mode-2 lowering emits (data 0,1,2; ancillas m..m+2)
m = 3
def ccz_block_prog(m, c0):
    a1, a2, a3 = m, m + 1, m + 2
    return [
        ('useCCZ', a1, a2, a3),
        ('measure', c0,     [(0, 'z'), (a1, 'z')]),
        ('measure', c0 + 1, [(1, 'z'), (a2, 'z')]),
        ('measure', c0 + 2, [(2, 'z'), (a3, 'z')]),
        # destruction of a1: X_{a1} twisted by Z_{a2}^{m3}, Z_{a3}^{m2}
        ('measureSel2', [c0 + 2], [c0 + 1], c0 + 3,
            [(a1, 'x')], [(a1, 'x'), (a3, 'z')],
            [(a1, 'x'), (a2, 'z')], [(a1, 'x'), (a2, 'z'), (a3, 'z')]),
        # destruction of a2: Z_{a1}^{m3} . X_{a2} . Z_{a3}^{m1}
        ('measureSel2', [c0 + 2], [c0], c0 + 4,
            [(a2, 'x')], [(a2, 'x'), (a3, 'z')],
            [(a1, 'z'), (a2, 'x')], [(a1, 'z'), (a2, 'x'), (a3, 'z')]),
        # destruction of a3: Z_{a1}^{m2} . Z_{a2}^{m1} . X_{a3}
        ('measureSel2', [c0 + 1], [c0], c0 + 5,
            [(a3, 'x')], [(a2, 'z'), (a3, 'x')],
            [(a1, 'z'), (a3, 'x')], [(a1, 'z'), (a2, 'z'), (a3, 'x')]),
        # corrections: Z_{d_i} on b_i ^^ (m_j AND m_k)
        ('correctQ', [[c0 + 3], [c0 + 1, c0 + 2]], [(0, 'z')], []),
        ('correctQ', [[c0 + 4], [c0,     c0 + 2]], [(1, 'z')], []),
        ('correctQ', [[c0 + 5], [c0,     c0 + 1]], [(2, 'z')], []),
    ]

psi = rng.normal(size=8) + 1j * rng.normal(size=8)
psi /= np.linalg.norm(psi)
U_ccz = qiskit_unitary(lambda qc: qc.ccz(0, 1, 2), 3)
target = U_ccz @ psi
# input: psi (x) |CCZ> at wires 3,4,5 (unnormalized +-1 amps, as in tensorTriple)
ccz_state = np.ones(8); ccz_state[7] = -1
v0 = np.zeros(64, complex)
for anc in range(8):
    v0[anc * 8:(anc + 1) * 8] = ccz_state[anc] * psi
prog = ccz_block_prog(3, 0)
ok, prob = True, 0.0
for om in itertools.product([False, True], repeat=6):
    v, outs = prog_denote(v0.copy(), prog, 6, list(om))
    if not branch_data_ok(v, 3, 6, target):
        ok = False; print('   branch FAILED:', om); break
    # exact closed form: scalar = 1/8 * (-1)^{<m,b>} on the (1/(2sqrt2))-normalized input
    mm, bb = om[:3], om[3:]
    sgn = (-1) ** ((mm[0] & bb[0]) ^ (mm[1] & bb[1]) ^ (mm[2] & bb[2]))
    colF = np.array([(-1) ** ((bb[0] & y1) ^ (bb[1] & y2) ^ (bb[2] & y3)
                              ^ (mm[2] & y1 & y2) ^ (mm[1] & y1 & y3) ^ (mm[0] & y2 & y3))
                     for y3 in (0, 1) for y2 in (0, 1) for y1 in (0, 1)], complex)
    # wire order: anc index bits (a1,a2,a3) = (y1,y2,y3), little-endian within anc block
    rhs = np.zeros(64, complex)
    for anc in range(8):
        y1, y2, y3 = anc & 1, (anc >> 1) & 1, (anc >> 2) & 1
        cf = (-1) ** ((bb[0] & y1) ^ (bb[1] & y2) ^ (bb[2] & y3)
                      ^ (mm[2] & y1 & y2) ^ (mm[1] & y1 & y3) ^ (mm[0] & y2 & y3))
        rhs[anc * 8:(anc + 1) * 8] = cf * target
    rhs = (sgn / 8) * rhs
    if not np.allclose(v, rhs, atol=1e-9):
        ok = False; print('   closed form FAILED:', om); break
    prob += (np.linalg.norm(v) / np.linalg.norm(v0)) ** 2
check('CCZ-1CCZ block (PPM statements): EXACT closed form on all 64 branches', ok)
check('CCZ-1CCZ block: branch probabilities sum to 1', abs(prob - 1) < 1e-9)

print()
if FAIL:
    print(f'{len(FAIL)} FAILURES'); sys.exit(1)
print('ALL VALIDATIONS PASSED')
