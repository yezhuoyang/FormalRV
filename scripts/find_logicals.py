#!/usr/bin/env python3
"""find_logicals.py — EXTERNAL logical-operator solver for the FormalRV QEC layer.

Computes, for each CSS code dumped by scripts/DumpCodeMatrices.lean, a
symplectically PAIRED logical basis (lz, lx) over GF(2):

    lz = basis of ker(H_X) / rowspace(H_Z)
    lx = basis of ker(H_Z) / rowspace(H_X), re-paired so dot(lx_i, lz_j) = delta_ij

and emits a Lean import file per code containing the `LogicalBasis` data plus
the kernel-`decide` certificate theorem `..._valid`.  Lean verifies ONLY the
cheap certificate (`x_in_ker_hz && z_in_ker_hx && pairs_delta` — dot products,
no Gaussian elimination); genuineness (outside the stabilizer rowspace)
follows from the parametric `LogicalGenuine.valid_basis_genuine`.  This tool
is UNTRUSTED by design.

Usage:
    lake env lean --run scripts/DumpCodeMatrices.lean > PyCircuits/code_matrices.txt
    python scripts/find_logicals.py PyCircuits/code_matrices.txt lpTiny \
        FormalRV/QEC/Codes/LiftedProduct/LPTinyBasisImport.lean \
        FormalRV.QEC.Algebraic.lpTiny FormalRV.QEC.Codes.LP lpTinyImported
"""
import ast
import sys


# ---------- GF(2) linear algebra (bitset rows: int with bit j = column j) ----------

def to_bits(row):
    v = 0
    for j, b in enumerate(row):
        if b:
            v |= 1 << j
    return v


def to_list(v, n):
    return [(v >> j) & 1 for j in range(n)]


class Echelon:
    """Incremental GF(2) echelon form over bitset rows (pivot = lowest set bit)."""

    def __init__(self, rows=()):
        self.piv = {}  # pivot column -> reduced row
        for r in rows:
            self.add(r)

    def reduce(self, v):
        """FULLY reduce v (clear every pivot column), return (v, lowest free col).
        Stored rows have lowest set bit = their pivot, so a low-to-high scan
        with rescan-after-XOR fully reduces."""
        first = None
        w = v
        while w:
            c = (w & -w).bit_length() - 1
            if c in self.piv:
                v ^= self.piv[c]
                w = v & ~((1 << (c + 1)) - 1)
            else:
                if first is None:
                    first = c
                w &= ~(1 << c)
        return (v, first) if v else (0, None)

    def add(self, v):
        v, c = self.reduce(v)
        if v == 0:
            return False
        for c2, r2 in self.piv.items():
            if r2 >> c & 1:
                self.piv[c2] = r2 ^ v
        self.piv[c] = v
        return True

    @property
    def rank(self):
        return len(self.piv)


def kernel_basis_bits(rows, n):
    """Basis of ker over GF(2) for bitset rows with n columns."""
    e = Echelon(rows)
    pivots = sorted(e.piv)
    red = [e.piv[c] for c in pivots]
    pivset = set(pivots)
    basis = []
    for f in range(n):
        if f in pivset:
            continue
        v = 1 << f
        for i, p in enumerate(pivots):
            if red[i] >> f & 1:
                v |= 1 << p
        basis.append(v)
    return basis


def dot_bits(a, b):
    return (a & b).bit_count() & 1


def quotient_basis_bits(ker, mod_rows):
    """Filter ker to vectors independent mod rowspace(mod_rows), incrementally."""
    e = Echelon(mod_rows)
    out = []
    for v in ker:
        if e.add(v):
            out.append(v)
    return out


def gf2_inv_bits(rows, k):
    """Invert a k x k GF(2) matrix given as bitset rows; returns bitset rows."""
    aug = [rows[i] | (1 << (k + i)) for i in range(k)]
    for c in range(k):
        piv = next((i for i in range(c, k) if aug[i] >> c & 1), None)
        if piv is None:
            raise SystemExit("pairing matrix singular - bases not dual")
        aug[c], aug[piv] = aug[piv], aug[c]
        for i in range(k):
            if i != c and aug[i] >> c & 1:
                aug[i] ^= aug[c]
    return [r >> k for r in aug]


def paired_bases(hx_l, hz_l, n):
    hx = [to_bits(r) for r in hx_l]
    hz = [to_bits(r) for r in hz_l]
    lz = quotient_basis_bits(kernel_basis_bits(hx, n), hz)
    lx = quotient_basis_bits(kernel_basis_bits(hz, n), hx)
    assert len(lz) == len(lx), "k mismatch (%d vs %d)" % (len(lz), len(lx))
    k = len(lz)
    P = [to_bits([dot_bits(lx[i], lz[j]) for j in range(k)]) for i in range(k)]
    Pinv = gf2_inv_bits(P, k)
    lx2 = []
    for i in range(k):
        v = 0
        for j in range(k):
            if Pinv[i] >> j & 1:
                v ^= lx[j]
        lx2.append(v)
    # sanity (the tool self-checks; Lean re-verifies independently)
    ex, ez = Echelon(hx), Echelon(hz)
    for i, x in enumerate(lx2):
        assert all(dot_bits(r, x) == 0 for r in hz), "lx not in ker hz"
        assert ex.reduce(x)[0] != 0, "lx in rowspace hx"
        for j, z in enumerate(lz):
            assert dot_bits(x, z) == (1 if i == j else 0), "pairing failed"
    for z in lz:
        assert all(dot_bits(r, z) == 0 for r in hx), "lz not in ker hx"
        assert ez.reduce(z)[0] != 0, "lz in rowspace hz"
    return [to_list(v, n) for v in lz], [to_list(v, n) for v in lx2]


# ---------- I/O ----------

def parse_dump(path, want):
    # PowerShell `>` emits UTF-16 LE with BOM; plain tools emit UTF-8.
    enc = "utf-16" if open(path, "rb").read(2) in (b"\xff\xfe", b"\xfe\xff") else "utf-8"
    code = {}
    name = None
    key = None
    buf = []
    depth = 0
    for line in open(path, encoding=enc):
        line = line.strip()
        if key is None and line.startswith("CODE "):
            _, name, n = line.split()
            if name == want:
                code["n"] = int(n)
        elif key is None and name == want and (line.startswith("HX ") or line.startswith("HZ ")):
            key = "hx" if line.startswith("HX ") else "hz"
            buf = [line[3:]]
            depth = line.count("[") - line.count("]")
            if depth == 0:
                key, buf = _finish(code, key, buf)
        elif key is not None:
            buf.append(line)
            depth += line.count("[") - line.count("]")
            if depth == 0:
                key, buf = _finish(code, key, buf)
        if "hx" in code and "hz" in code:
            return code
    return code


def _finish(code, key, buf):
    code[key] = ast.literal_eval(
        " ".join(buf).replace("true", "1").replace("false", "0"))
    return None, []


def lean_hex(v):
    """A BoolVec as ONE Nat hex literal (bit j = entry j) — the slim,
    lossless encoding decoded in Lean by `FormalRV.QEC.bitsToVec`."""
    return "0x%x" % to_bits(v)


TEMPLATE = """/-
  {leanfile} — GENERATED by scripts/find_logicals.py (UNTRUSTED external
  GF(2) solver).  Vectors are stored as Nat bitset hex literals and decoded
  by `FormalRV.QEC.bitsToVec` (lossless; ≈27× slimmer than Bool-list
  literals).  Lean verifies ONLY the cheap certificate below
  (`LogicalBasis.valid`: in-kernel + symplectic delta-pairing on the DECODED
  vectors, pure dot products — no Gaussian elimination, and no trust in the
  encoding); genuineness (outside the stabilizer rowspace) follows
  parametrically from `LogicalGenuine.valid_basis_genuine`.
  Regenerate: see the script header.  Do not edit by hand.
-/
import FormalRV.QEC.Logical
import FormalRV.QEC.Instances
import FormalRV.QEC.BasisCodec

-- kernel recursion headroom for `decide` over width-{n} vectors
set_option maxRecDepth 2000000

namespace {ns}

open FormalRV.QEC

/-- Imported logical-Z bitsets ({k} logical qubits), found externally. -/
def {base}_lzBits : List Nat :=
  [{lzs}]

/-- Imported logical-X bitsets, externally re-paired to the delta pairing. -/
def {base}_lxBits : List Nat :=
  [{lxs}]

def {base}_lz : List FormalRV.Framework.LDPC.BoolVec :=
  {base}_lzBits.map (bitsToVec {n})

def {base}_lx : List FormalRV.Framework.LDPC.BoolVec :=
  {base}_lxBits.map (bitsToVec {n})

/-- The imported PAIRED basis (naive sequential indexing: logical `i` is the
    `i`-th basis vector — the audit convention). -/
def {base}Basis : LogicalBasis {code} {k} :=
  ⟨fun i => {base}_lx.getD i.val [], fun i => {base}_lz.getD i.val []⟩

end {ns}
"""

CERT_TEMPLATE = """/-
  {certfile} — the LIST-LEVEL full-basis certificate for {base}
  (GENERATED; see scripts/find_logicals.py).  At paper scale (k ≈ 10³) the
  k² pairing over `List Bool` makes this a LONG off-path kernel run — build
  on demand (`lake env lean <this file>`); the kernel-fast bitset
  certificate (`GF2Bits.validBitsCert`) and per-measured-logical
  certificates are the scalable alternatives.
-/
import {datamodule}

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace {ns}

open FormalRV.QEC

/-- **The certificate** (kernel `decide`; `valid_basis_genuine` upgrades it
    to genuineness parametrically). -/
theorem {base}Basis_valid : ({base}Basis).valid = true := by decide

end {ns}
"""


def main():
    dump, codename, leanfile, leancode, ns, base = sys.argv[1:7]
    c = parse_dump(dump, codename)
    lz, lx = paired_bases(c["hx"], c["hz"], c["n"])
    text = TEMPLATE.format(
        leanfile=leanfile, ns=ns, base=base, code=leancode, k=len(lz), n=c["n"],
        lzs=",\n   ".join(lean_hex(v) for v in lz),
        lxs=",\n   ".join(lean_hex(v) for v in lx))
    open(leanfile, "w", encoding="utf-8", newline="\n").write(text)
    certfile = leanfile.replace("BasisImport.lean", "BasisFullCert.lean")
    datamodule = ("FormalRV." + leanfile.replace("\\", "/").split("FormalRV/", 2)[-1]
                  [:-5].replace("/", "."))
    open(certfile, "w", encoding="utf-8", newline="\n").write(
        CERT_TEMPLATE.format(certfile=certfile, base=base, ns=ns,
                             datamodule=datamodule))
    print(f"{codename}: k = {len(lz)} -> {leanfile} + {certfile}")


if __name__ == "__main__":
    main()
