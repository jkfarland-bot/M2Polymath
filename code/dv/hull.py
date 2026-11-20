# Seat M2d-v: exact incomplete hyperbola sum S(N, L) = sum_{L < t <= isqrt(N)} floor(N/t)
# for ARBITRARY lower limit L, via (i) direct columns up to max(L, cbrt N), (ii) axis swap
# (rows above sqrt N), (iii) a Stern-Brocot convex-hull walk on the lattice points just
# outside the hyperbola, run over the swapped range (sqrt N, N/(c+1)].  Exact integers only.
# Step counter: every floor division in a direct column, every outside() test, every
# stack push/pop counts 1.
from math import isqrt


def icbrt(n):
    if n < 2:
        return n
    r = int(round(n ** (1.0 / 3)))
    while r * r * r > n:
        r -= 1
    while (r + 1) ** 3 <= n:
        r += 1
    return r


class Ctr:
    __slots__ = ('steps', 'tail', 'direct', 'walkv')

    def __init__(self):
        self.steps = 0
        self.tail = 0
        self.direct = 0
        self.walkv = 0


def direct(N, a, b, ctr):
    """sum_{a < t <= b} N//t, column by column."""
    if b <= a:
        return 0
    ctr.steps += b - a
    ctr.direct += b - a
    return sum(N // t for t in range(a + 1, b + 1))


def walk(N, a, B, ctr):
    """sum_{a < t <= B} N//t, for a >= isqrt(N) (curve slope <= ~1 on the range).
    Convex-hull walk on lowest outside points (t, N//t + 1)."""
    if B <= a:
        return 0
    tot = 0
    x = a
    # ensure x*x >= N so that every hull edge from here has dy <= dx
    while x * x < N and x < B:
        x += 1
        tot += N // x
        ctr.steps += 1
    if x >= B:
        return tot
    y = N // x + 1
    stk = [(1, 0), (1, 1)]
    st = 0
    while True:
        dx1, dy1 = stk.pop()
        st += 1
        while x + dx1 <= B and (x + dx1) * (y - dy1) > N:
            st += 1
            # columns x+1..x+dx1: floor(N/t) = ceil(seg(t)) - 1, seg linear from y to y-dy1
            tot += dx1 * (y - 1) - ((dx1 - 1) * (dy1 - 1) // 2 + dy1)
            x += dx1
            y -= dy1
            ctr.walkv += 1
        st += 1
        if x + dx1 > B:
            # tail: fewer than dx1 columns left; finish directly
            r = B - x
            st += r
            ctr.tail += r
            tot += sum(N // t for t in range(x + 1, B + 1))
            break
        dx2, dy2 = dx1, dy1
        while True:
            dx1, dy1 = stk[-1]
            st += 1
            if (x + dx1) * (y - dy1) > N:
                break
            dx2, dy2 = dx1, dy1
            stk.pop()
        while True:
            mx, my = dx1 + dx2, dy1 + dy2
            st += 1
            if (x + mx) * (y - my) > N:
                dx1, dy1 = mx, my
                stk.append((dx1, dy1))
            else:
                X = x + mx
                if X * X * dy1 >= N * dx1:
                    break
                dx2, dy2 = mx, my
    ctr.steps += st
    return tot


def S_inc(N, L, ctr):
    """sum_{L < t <= isqrt(N)} floor(N/t), any 0 <= L <= isqrt(N)."""
    r = isqrt(N)
    if L >= r:
        return 0
    c = min(max(L, icbrt(N)), r)
    tot = direct(N, L, c, ctr)
    if c < r:
        M = N // (c + 1)
        tot += r * (r - c) + walk(N, r, M, ctr) - c * (M - r)
    return tot


def D2_fast(N, ctr):
    if N <= 0:
        return 0
    r = isqrt(N)
    return 2 * S_inc(N, 0, ctr) - r * r


def D3_F1_fast(x, ctr):
    """(F1) with the incomplete inner sums done by S_inc."""
    if x <= 0:
        return 0
    m = icbrt(x)
    Bsum = Eab = Ebc = 0
    for a in range(1, m + 1):
        y = x // a
        h = isqrt(y)
        inner = S_inc(y, a - 1, ctr)              # sum_{b=a}^{h} floor(y/b)
        ap = (h * (h - 1) - (a - 1) * (a - 2)) // 2  # sum_{b=a}^{h} (b-1)
        Bsum += inner - ap
        Eab += x // (a * a) - a + 1
        Ebc += h - a + 1
        ctr.steps += 3
    return 6 * Bsum - 3 * Eab - 3 * Ebc + m
