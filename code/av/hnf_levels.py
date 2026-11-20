"""M2a-v: independent recomputation of Z_signed(p,k), Z_cheap(p,k) by Hermite normal form over Z,
covering EVERY offset v (not a bounded v range), plus the mu slice level L(p,k) for point 5.

Slice model (Theorem A): on squarefree n with r = omega(n) slice primes, f(n) == s_r = sum_z a_z z^r.
Target D_k at offset v: s_1 = p^v * unit, s_r == 0 mod p^(v+k) for r >= 2  (N = v + k).

Method: lattice Lam in Z^(R+1) spanned by the node columns (z^2, ..., z^R, z) and p^N e_i.
HNF with the s_1 coordinate last; the sublattice with all constraint coordinates zero is g Z in the last
coordinate; feasible at v iff v_p(g) <= v.  Rows r = 2..R with R = d + 1 + 3 (extra rows as a check), and
R covering a full period mod p^N when that is small.
All offsets: let c = v_p(det Vandermonde(nodes, rows 1..d)). For v >= c, p^N Z_p^d lies inside the moment
lattice, so feasibility at v >= c is decided by one test; feasibility is upward closed in v (multiply a by p).
Hence "some v works" iff "v = c works".  We nevertheless test every v = 0..c.
Usage: python3 -I hnf_levels.py
"""
from math import factorial


def vp(x, p):
    x = abs(x)
    if x == 0:
        return 10 ** 9
    c = 0
    while x % p == 0:
        x //= p
        c += 1
    return c


def S(m):
    s = 1
    while factorial(s) % m:
        s += 1
    return s


def ext_gcd(a, b):
    if b == 0:
        return (a, 1, 0) if a >= 0 else (-a, -1, 0)
    g, x, y = ext_gcd(b, a % b)
    return g, y, x - (a // b) * y


def hnf(rows, ncols, P=None):
    """Row-style echelon form over Z (unimodular row ops). Returns list of (pivot_col, row).
    If P is given, the lattice contains P*Z^ncols; then the rows still to be processed generate
    lattice-intersect-{first col coords zero}, which contains P e_j (j >= col): we add those and reduce
    mod P (valid, keeps entries small)."""
    rows = [list(r) for r in rows if any(r)]
    out = []
    col = 0
    while rows and col < ncols:
        if P is not None:
            rows = [[x % P for x in r] for r in rows]
            for j in range(col, ncols):
                e = [0] * ncols
                e[j] = P
                rows.append(e)
            rows = [r for r in rows if any(r)]
        nz = [r for r in rows if r[col] != 0]
        rest = [r for r in rows if r[col] == 0]
        if not nz:
            col += 1
            continue
        piv = nz[0]
        for r in nz[1:]:
            a, b = piv[col], r[col]
            g, x, y = ext_gcd(a, b)
            newp = [x * u + y * w for u, w in zip(piv, r)]
            other = [(b // g) * u - (a // g) * w for u, w in zip(piv, r)]
            assert other[col] == 0
            piv = newp
            if any(other):
                rest.append(other)
        out.append((col, piv))
        rows = rest
        col += 1
    return out


def s1_exponent(nodes, p, N, R):
    P = p ** N
    cols = list(range(2, R + 1)) + [1]
    gens = [[pow(z, r, P) for r in cols] for z in nodes]
    for i in range(len(cols)):
        e = [0] * len(cols)
        e[i] = P
        gens.append(e)
    # reduce entries mod P is allowed since P e_i are in the lattice
    H = hnf(gens, len(cols), P)
    last = len(cols) - 1
    g = [row[last] for c, row in H if c == last]
    assert len(g) == 1  # P e_last is in the lattice
    return min(vp(g[0], p), N)


def vandermonde_det_vp(nodes, p):
    v = sum(vp(z, p) for z in nodes)
    for i in range(len(nodes)):
        for j in range(i + 1, len(nodes)):
            v += vp(nodes[j] - nodes[i], p)
    return v


def feasible_some_v(nodes, p, k):
    d = len(nodes)
    c = vandermonde_det_vp(nodes, p)
    oks = []
    for v in range(0, c + 1):
        N = v + k
        phi = p ** N - p ** (N - 1)
        R = max(N, 2) + phi if phi <= 60 else d + 4
        R = max(R, d + 4)
        w = s1_exponent(nodes, p, N, R)
        oks.append(w <= v)
    for i in range(len(oks) - 1):
        assert not (oks[i] and not oks[i + 1]), "upward closure violated"
    return oks[-1], (oks.index(True) if any(oks) else None), c


def nodes_for(Z, signed):
    return [z for z in range(-Z, Z + 1) if z != 0] if signed else list(range(1, Z + 1))


def mu_slice_level(p, k, Lmax=40):
    """least L: exists integer c on nodes 0..L with sum c_z z^r == (-1)^r mod p^k for all r >= 0."""
    P = p ** k
    R = k + 2 * (p ** k - p ** (k - 1)) + 2
    for L in range(0, Lmax + 1):
        nodes = list(range(0, L + 1))
        gens = [[pow(z, r, P) if not (z == 0 and r == 0) else 1 for r in range(R)] for z in nodes]
        for i in range(R):
            e = [0] * R
            e[i] = P
            gens.append(e)
        H = hnf(gens, R, P)
        t = [(-1) ** r % P for r in range(R)]
        for c, row in H:  # reduce target
            if t[c] % row[c] == 0:
                q = t[c] // row[c]
                t = [x - q * y for x, y in zip(t, row)]
        if not any(t):
            return L
    return None


def main():
    print("Z_signed, Z_cheap by HNF over Z, every offset v covered (v = 0..c, c = v_p(det V))")
    for p, kmax in ((2, 5), (3, 5), (5, 3)):
        for k in range(1, kmax + 1):
            for signed in (True, False):
                pred = S(p ** ((k + 1) // 2)) if signed else S(p ** k)
                found = None
                for Z in range(1, pred + 1):
                    ok, vmin, c = feasible_some_v(nodes_for(Z, signed), p, k)
                    if ok:
                        found = (Z, vmin, c)
                        break
                print(f"p={p} k={k} {'signed' if signed else 'cheap '}: least Z={found[0] if found else '>'+str(pred)}"
                      f" (least v={found[1] if found else '-'}, v tested 0..{found[2] if found else c})"
                      f" formula={pred} {'OK' if found and found[0] == pred else 'MISMATCH'}", flush=True)
    print("Fixed v = 1 (outside Theorem H), least Z <= 16:")
    for p in (2, 3):
        for signed in (True, False):
            row = []
            for k in range(1, 5):
                z = None
                for Z in range(1, 17):
                    nodes = nodes_for(Z, signed)
                    N = 1 + k
                    if s1_exponent(nodes, p, N, max(len(nodes) + 4, max(N, 2) + p ** N)) <= 1:
                        z = Z
                        break
                row.append(z)
            print(f"  p={p} {'signed' if signed else 'cheap '} v=1: k=1..4 -> {row}")
    print("Point 5: mu slice level L(p,k) (nodes 0..L, target (-1)^r, v = 0) vs Z_cheap = S(p^k):")
    for p, kmax in ((2, 5), (3, 3), (5, 2)):
        for k in range(1, kmax + 1):
            L = mu_slice_level(p, k)
            print(f"  p={p} k={k}: slice L={L}, L+1={L + 1 if L is not None else None}, S(p^k)={S(p ** k)}", flush=True)


if __name__ == '__main__':
    main()
