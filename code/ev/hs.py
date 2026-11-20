# Seat M2e-v independent implementation of S(y,L) from the written proof (REPORT_M2e.md).
import sys, random
from math import isqrt
from fractions import Fraction as Fr

def icbrt(n):
    # pure integer bisection
    lo, hi = 0, 1
    while hi**3 <= n: hi *= 2
    while hi - lo > 1:
        mid = (lo+hi)//2
        if mid**3 <= n: lo = mid
        else: hi = mid
    return lo

STAT = dict(blocks=0, direct=0, cf=0, cfmax_excess=-99, evals=0, ev_excess=-99,
            phase_ok=True, growth_ok=True, maxbits_ratio=0.0, phase1=0, phase2=0)
INSTR = False

def last_conv(u, v, Q):
    # Euclid on u/v; return last convergent a/q with q<=Q (Lemma 2)
    hp, hq, pp, pq = 1, 0, 0, 1   # p_{-1},q_{-1},p_{-2},q_{-2}
    best = None; steps = 0
    while v:
        c = u // v; u, v = v, u - c*v
        np_, nq = c*hp + pp, c*hq + pq
        pp, pq, hp, hq = hp, hq, np_, nq
        steps += 1
        if nq > Q: break
        best = (np_, nq)
    return best, steps

def ext_inv(a, q):
    if q == 1: return 0
    r0, r1, s0, s1 = q, a % q, 0, 1
    while r1:
        c = r0 // r1
        r0, r1, s0, s1 = r1, r0 - c*r1, s1, s0 - c*s1
    assert r0 == 1
    return s0 % q

def count_le(y, T, a, m, q, k):
    # #{0<=l<k : (T-a l)(m+q l) <= y}; P concave (Lemma 6). Own variant: ternary-free,
    # find argmax by bisection on forward difference, then two bisections.
    ev = [0]
    def P(l):
        ev[0] += 1
        return (T - a*l)*(m + q*l)
    lo, hi = 0, k-1
    while lo < hi:
        md = (lo+hi)//2
        if P(md+1) <= P(md): hi = md
        else: lo = md+1
    top = lo
    if P(top) <= y: return k, ev[0]
    lo, hi = 0, top
    while lo < hi:
        md = (lo+hi)//2
        if P(md) > y: hi = md
        else: lo = md+1
    A = lo
    lo, hi = top, k-1
    while lo < hi:
        md = (lo+hi+1)//2
        if P(md) > y: lo = md
        else: hi = md-1
    B = lo
    return k - (B - A + 1), ev[0]

def clog2(k):
    return (k-1).bit_length()

def S(y, L):
    r = isqrt(y)
    if L >= r: return 0
    c0 = icbrt(y)
    total = 0
    b = L+1
    while b <= min(c0, r):
        total += y//b; b += 1; STAT['direct'] += 1
    n0 = max(L+1, c0+1)
    N1 = n0
    prevQ = 0; inphase2 = False; prevn = None
    while n0 <= r:
        R = r - n0 + 1
        Q = icbrt((n0**3)//y)
        (a, q), st = last_conv(y, n0*n0, Q)
        if INSTR:
            assert Q >= 1 and Q**3*y <= n0**3
            assert Q >= prevQ and Q**6 <= y; prevQ = Q
            import math
            STAT['cfmax_excess'] = max(STAT['cfmax_excess'], st - (math.log(Q)/math.log((1+5**.5)/2)+3))
            assert 1 <= q <= Q and abs(y*q - a*n0*n0)*q*Q <= q*n0*n0
            if R < Q: inphase2 = True
            elif inphase2: STAT['phase_ok'] = False
        STAT['cf'] += st
        if R < q:
            for bb in range(n0, r+1): total += y//bb
            STAT['direct'] += R
            if INSTR: assert R < q <= Q and Q**6 <= y
            break
        k = min(Q, R)//q; H = k*q; s = (q*y)//n0
        STAT['blocks'] += 1
        if INSTR:
            if R >= Q:
                STAT['phase1'] += 1
                assert 2*H >= Q and 64*H**3*y >= n0**3   # H >= n0/(4c)
            else:
                STAT['phase2'] += 1
            assert 1 <= k and H <= min(Q, R)
        lin = k*s - a*q*k*(k-1)//2 - k*(a+1)*(q-1)//2
        if INSTR:
            assert (a*q*k*(k-1)) % 2 == 0 and (k*(a+1)*(q-1)) % 2 == 0
            assert lin == sum((s - a*t)//q for t in range(H))
        ai = ext_inv(a, q)
        Js = {0, (q-2) % q, (q-1) % q}
        blk = lin
        for j in Js:
            rho = (ai*(s - j)) % q
            m = n0 + rho
            f = (s - a*rho)//q
            assert (s - a*rho) % q == j
            cnt = 0
            for T in (f, f+1, f+2):
                c_, e_ = count_le(y, T, a, m, q, k)
                cnt += c_; STAT['evals'] += e_
                if INSTR: STAT['ev_excess'] = max(STAT['ev_excess'], e_ - (4*clog2(k)+1))
            exact = k*(f-1) + cnt - a*k*(k-1)//2
            blk += exact - (k*f - a*k*(k-1)//2)
        if INSTR:
            alpha = Fr(y, n0*n0); phi = Fr(q*y, n0) - s
            for t in range(H):
                n = n0+t
                E = Fr(y, n) - (Fr(y, n0) - Fr(a*t, q))
                assert -Fr(1, q) < E < Fr(2, q)
                j = (s - a*t) % q
                assert Fr(y, n0) - Fr(a*t, q) - (s - a*t - j)//q == (j + phi)/q   # frac(g)
                if 1 <= j <= q-3: assert y//n == (s - a*t)//q
                rho, l = t % q, t//q
                f = (s - a*rho)//q
                Fl = y//n + a*l
                assert f-1 <= Fl <= f+2
                if q >= 3 and Fl == f+2: STAT.setdefault('f+2 used q>=3', 0); STAT['f+2 used q>=3'] += 1
                for T in (f, f+1, f+2):
                    v = abs((T - a*l)*(n0 + rho + q*l))
                    STAT['maxbits_ratio'] = max(STAT['maxbits_ratio'], v / y**2)
            assert blk == sum(y//(n0+t) for t in range(H))
        total += blk
        n0 += H
    return total

def brute(y, L):
    return sum(y//b for b in range(L+1, isqrt(y)+1))

def D3(x):
    m = icbrt(x); B = Eab = Ebc = 0
    for a in range(1, m+1):
        y = x//a; h = isqrt(y)
        assert a - 1 <= h
        B += S(y, a-1) - (h*(h-1) - (a-1)*(a-2))//2
        Eab += x//(a*a) - a + 1; Ebc += h - a + 1
    return 6*B - 3*Eab - 3*Ebc + m
