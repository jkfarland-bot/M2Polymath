"""M2a: exact degree levels Z_signed(p,k), Z_cheap(p,k) from slice moments.

Written from the definitions (not from any A19 script). Exact integer arithmetic.

Slice model: f(n) = s_r = sum_z a_z z^r (mod p^N) when omega(n) = r on the slice.
Target D_k with offset v: s_1 = p^v * unit (mod p^(v+k)), s_r = 0 (mod p^(v+k)) for all r >= 2.

For a node set T and N = v + k we compute the ideal of Z/p^N formed by all values s_1(a)
over integer vectors a with s_r(a) = 0 mod p^N for every r >= 2.  That ideal is p^w Z/p^N;
the target is reachable at offset v iff w <= v (w < N automatically then).

Rows r >= 2 are handled in two ways:
  'full'  : r = 2 .. max(N,2) + phi(p^N) - 1 (z^r mod p^N is periodic in r from r = N on, period | phi(p^N));
            this is sound from first principles.
  'short' : r = 2 .. d + 2 where d = |T|; sound because Q(t) = prod_{z in T} (t - z) is monic with
            integer coefficients and sum_z a_z z^r Q(z) = 0 gives an exact integer recurrence for
            s_r, r >= 2, of order d (the rows r = 2..d+1 determine all later rows).
Both modes are run and compared where 'full' is affordable.

Usage: python3 -I moments.py
"""
import sys
from math import factorial


def vp(x, p):
    if x == 0:
        return 10 ** 9
    x = abs(x)
    c = 0
    while x % p == 0:
        x //= p
        c += 1
    return c


def kempner(m):
    s = 1
    while factorial(s) % m:
        s += 1
    return s


def val_mod(x, p, N):
    P = p ** N
    x %= P
    if x == 0:
        return N
    c = 0
    while x % p == 0:
        x //= p
        c += 1
    return c


def s1_ideal_exponent(nodes, p, N, rows):
    """Return w such that {s_1(a) : s_r(a) = 0 mod p^N for r in rows} = p^w Z/p^N."""
    P = p ** N
    rlist = [1] + list(rows)
    gens = [[pow(z, r, P) for r in rlist] for z in nodes]
    for j in range(1, len(rlist)):
        best = None
        for i, g in enumerate(gens):
            e = val_mod(g[j], p, N)
            if e < N and (best is None or e < best[0]):
                best = (e, i)
        if best is None:
            continue
        e, i = best
        piv = gens[i]
        unit = (piv[j] // p ** e) % P
        uinv = pow(unit, -1, P)
        newg = []
        for t, g in enumerate(gens):
            if t == i:
                continue
            if g[j] % P:
                f = val_mod(g[j], p, N)
                fac = ((g[j] // p ** f) * uinv * p ** (f - e)) % P
                g = [(x - fac * y) % P for x, y in zip(g, piv)]
                assert g[j] == 0
            if any(g):
                newg.append(g)
        kill = [(p ** (N - e) * y) % P for y in piv]
        assert kill[j] == 0
        if any(kill):
            newg.append(kill)
        gens = newg
    w = N
    for g in gens:
        w = min(w, val_mod(g[0], p, N))
    return w


def phi_ppow(p, N):
    return p ** N - p ** (N - 1)


def feasible(nodes, p, k, v, mode):
    N = v + k
    if mode == 'full':
        rows = range(2, max(N, 2) + phi_ppow(p, N))
    else:
        rows = range(2, len(nodes) + 3)
    w = s1_ideal_exponent(nodes, p, N, rows)
    return w <= v, w


def nodes_for(Z, signed):
    if signed:
        return [z for z in range(-Z, Z + 1) if z != 0]
    return list(range(1, Z + 1))


def min_Z(p, k, signed, vmax, mode, zmax=60):
    """Least Z such that some v in 0..vmax works; also return least such v."""
    for Z in range(1, zmax + 1):
        nodes = nodes_for(Z, signed)
        for v in range(0, vmax + 1):
            ok, w = feasible(nodes, p, k, v, mode)
            if ok:
                return Z, v
    return None, None


def main():
    out = []
    VMAX = 8
    results = {}
    for p in (2, 3, 5, 7):
        kmax = {2: 8, 3: 6, 5: 5, 7: 4}[p]
        for k in range(1, kmax + 1):
            for signed in (True, False):
                Z, vmin = min_Z(p, k, signed, VMAX, 'short')
                pred = kempner(p ** ((k + 1) // 2)) if signed else kempner(p ** k)
                results[(p, k, signed)] = (Z, vmin, pred)
                out.append(f"p={p} k={k} {'signed' if signed else 'cheap '}: Z={Z} (least v at that Z: {vmin}, v<= {VMAX} tested)  "
                           f"predicted={pred}  {'OK' if Z == pred else 'MISMATCH'}")
                print(out[-1], flush=True)
    # cross-check the short row range against the full periodic row range where affordable
    print("cross-check short vs full row range:", flush=True)
    bad = 0
    checked = 0
    for p in (2, 3, 5):
        for k in (1, 2, 3, 4):
            for signed in (True, False):
                for Z in range(1, 11):
                    nodes = nodes_for(Z, signed)
                    for v in range(0, 5):
                        N = v + k
                        if phi_ppow(p, N) > 3000:
                            continue
                        a = feasible(nodes, p, k, v, 'short')
                        b = feasible(nodes, p, k, v, 'full')
                        checked += 1
                        if a != b:
                            bad += 1
                            print("DISAGREE", p, k, signed, Z, v, a, b)
    print(f"  {checked} (p,k,signed,Z,v) cases, disagreements: {bad}", flush=True)


if __name__ == '__main__':
    main()
