# Least-squares exponent fits for total (F1) cost (exact 1e9..1e13 from t_F1_fast.out,
# sampled 1e15..1e19 from t_F1_sampled.out).
from math import log10, log
data = [(9, 1603592), (10, 6099752), (11, 23033408), (12, 86313562), (13, 321892745),
        (15, 4.436e9), (17, 5.837e10), (19, 8.025e11)]
def fit(pts):
    n = len(pts); sx = sum(p for p, _ in pts); sy = sum(q for _, q in pts)
    sxx = sum(p * p for p, _ in pts); sxy = sum(p * q for p, q in pts)
    return (n * sxy - sx * sy) / (n * sxx - sx * sx)
P = [(e, log10(s)) for e, s in data]
print('slope of log steps vs log x, all points: %.4f' % fit(P))
print('slope, x >= 1e13: %.4f' % fit(P[4:]))
Q = [(e, log10(s / log(10 ** e))) for e, s in data]
print('slope of log(steps/ln x), all: %.4f; x>=1e13: %.4f' % (fit(Q), fit(Q[4:])))
for (e1, s1), (e2, s2) in zip(data, data[1:]):
    print('local slope 1e%d->1e%d: %.4f' % (e1, e2, (log10(s2) - log10(s1)) / (e2 - e1)))
