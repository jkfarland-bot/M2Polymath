"""M2a: exhaustive searches (no linear algebra) for tiny cases, and Theorem B checks.

Part 1: for tiny (p, k, node set, v), enumerate every coefficient vector a mod p^(v+k) and test the
        slice target D_k directly on rows r = 2 .. max(N,2)+phi(p^N)-1 (all rows, by periodicity).
Part 2: Theorem B (mod p^2, v = 1, k = 1).  Exhaustive where small: every solution has some z with
        v_p(z) = 1 and a_z not 0 mod p.  Also the 1,2,3 mod 9 claim.
Part 3: Theorem B by linear algebra for larger node sets: force a_z in pZ for all z with v_p(z) = 1
        and show the target becomes infeasible (s_1 ideal exponent w >= 2 mod p^2).
Usage: python3 -I brute.py
"""
import itertools
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from moments import s1_ideal_exponent, vp  # noqa: E402


def rows_all(p, N):
    return range(2, max(N, 2) + p ** N - p ** (N - 1))


def solutions(nodes, p, k, v):
    N = v + k
    P = p ** N
    rows = list(rows_all(p, N))
    pw = {z: [pow(z, r, P) for r in rows] for z in nodes}
    p1 = {z: z % P for z in nodes}
    sols = []
    for a in itertools.product(range(P), repeat=len(nodes)):
        s1 = sum(ai * p1[z] for ai, z in zip(a, nodes)) % P
        if s1 == 0 or vp(s1, p) != v:
            continue
        ok = True
        for j in range(len(rows)):
            if sum(ai * pw[z][j] for ai, z in zip(a, nodes)) % P:
                ok = False
                break
        if ok:
            sols.append(a)
    return sols


def part1():
    print("Part 1: exhaustive tiny cases (count of solutions mod p^(v+k))")
    cases = [
        (2, 1, [1], 0), (2, 1, [1], 1), (2, 1, [1, 2], 0), (2, 1, [1, 2], 1),
        (2, 1, [-1, 1], 1), (2, 1, [-1, 1], 2),
        (2, 2, [1, 2, 3], 1), (2, 2, [1, 2, 3], 2), (2, 2, [1, 2, 3, 4], 2),
        (2, 2, [-2, -1, 1, 2], 1), (2, 2, [-2, -1, 1, 2], 2),
        (2, 3, [-1, 1], 2), (2, 3, [-2, -1, 1, 2], 2),
        (3, 1, [1, 2], 1), (3, 1, [1, 2], 2), (3, 1, [1, 2, 3], 1),
        (3, 1, [-2, -1, 1, 2], 1), (3, 2, [-2, -1, 1, 2], 1),
        (3, 2, [1, 2, 3], 1), (3, 2, [-3, -2, -1, 1, 2, 3], 1),
        (5, 1, [1, 2, 3, 4], 1), (5, 1, [1, 2, 3, 4, 5], 1),
    ]
    for p, k, nodes, v in cases:
        if (p ** (v + k)) ** len(nodes) > 3_000_000:
            print("  skip (too large)", p, k, nodes, v)
            continue
        s = solutions(nodes, p, k, v)
        lin = s1_ideal_exponent(nodes, p, v + k, rows_all(p, v + k)) <= v
        print(f"  p={p} k={k} v={v} nodes={nodes}: {len(s)} solutions; linear algebra says feasible={lin};"
              f" agree={bool(s) == lin}; lower bound sum v_p = {sum(vp(z, p) for z in nodes)} vs k={k}")


def part2():
    print("Part 2: Theorem B exhaustive (mod p^2, v=1, k=1)")
    for p, nodes in [(2, [-4, -3, -2, -1, 0, 1, 2, 3, 4]), (3, [-3, -2, -1, 0, 1, 2, 3]),
                     (3, [0, 1, 2, 3, 4, 5, 6]), (2, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (5, [0, 1, 2, 3, 4, 5])]:
        s = solutions(nodes, p, 1, 1)
        bad = [a for a in s if not any(vp(z, p) == 1 and a[i] % p for i, z in enumerate(nodes))]
        # refinement: sum over v_p(z)=1 of a_z (z/p) is a unit mod p, equal to u where s_1 = p u
        bad2 = 0
        for a in s:
            s1 = sum(ai * z for ai, z in zip(a, nodes)) % (p * p)
            u = s1 // p
            t = sum(a[i] * (z // p) for i, z in enumerate(nodes) if vp(z, p) == 1) % p
            if t != u % p:
                bad2 += 1
        print(f"  p={p} nodes={nodes}: {len(s)} solutions mod {p*p}; violating B: {len(bad)};"
              f" violating refinement sum_(v_p(z)=1) a_z z/p = u mod p: {bad2}")
    print("  1,2,3 mod 9 claim:")
    s = solutions([1, 2, 3], 3, 1, 1)
    forms = sorted(set((a[0] % 9, a[1] % 9, a[2] % 3) for a in s))
    print(f"   solutions (a1 mod 9, a2 mod 9, a3 mod 3): {forms}")


def part3():
    print("Part 3: Theorem B by linear algebra (a_z in pZ forced for v_p(z)=1)")
    for p in (2, 3, 5, 7):
        for Z in range(p, 4 * p + 1):
            for signed in (True, False):
                nodes = [z for z in range(-Z, Z + 1) if z != 0] if signed else list(range(1, Z + 1))
                # generator columns: z for v_p(z) != 1, and p*z-column (i.e. a_z = p b_z) for v_p(z) = 1
                N = 2
                rows = list(rows_all(p, N))
                # emulate scaling by duplicating nodes with weight: implement via direct generator build
                from moments import val_mod  # noqa
                P = p ** N
                gens = []
                for z in nodes:
                    scale = p if vp(z, p) == 1 else 1
                    gens.append([(scale * pow(z, r, P)) % P for r in [1] + rows])
                w = _ideal_from_gens(gens, p, N)
                full = s1_ideal_exponent(nodes, p, N, rows)
                print(f"  p={p} Z={Z} {'signed' if signed else 'cheap '}: unrestricted w={full} (feasible={full <= 1});"
                      f" restricted w={w} (feasible={w <= 1})") if Z in (p, 2 * p, 4 * p) else None
                if w <= 1:
                    print("  COUNTEREXAMPLE to B", p, Z, signed)


def _ideal_from_gens(gens, p, N):
    from moments import val_mod
    P = p ** N
    R = len(gens[0])
    for j in range(1, R):
        best = None
        for i, g in enumerate(gens):
            e = val_mod(g[j], p, N)
            if e < N and (best is None or e < best[0]):
                best = (e, i)
        if best is None:
            continue
        e, i = best
        piv = gens[i]
        uinv = pow((piv[j] // p ** e) % P, -1, P)
        newg = []
        for t, g in enumerate(gens):
            if t == i:
                continue
            if g[j] % P:
                f = val_mod(g[j], p, N)
                fac = ((g[j] // p ** f) * uinv * p ** (f - e)) % P
                g = [(x - fac * y) % P for x, y in zip(g, piv)]
            if any(g):
                newg.append(g)
        kill = [(p ** (N - e) * y) % P for y in piv]
        if any(kill):
            newg.append(kill)
        gens = newg
    w = N
    for g in gens:
        w = min(w, val_mod(g[0], p, N))
    return w


if __name__ == '__main__':
    part1()
    part2()
    part3()
