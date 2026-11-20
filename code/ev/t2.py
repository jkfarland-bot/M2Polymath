import os
import sys, random
sys.path.insert(0,os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'ev'))
import hs
from math import isqrt
random.seed(11)
cnt=0
for i in range(1500):
    e=random.uniform(4,10); y=int(10**e); y=random.randint(y//2,y)
    r=isqrt(y)
    for L in (0, random.randint(0,r), r-1, r, hs.icbrt(y), hs.icbrt(y)+1, random.randint(0, hs.icbrt(y))):
        L=max(0,min(L,r))
        assert hs.S(y,L)==hs.brute(y,L),(y,L); cnt+=1
print("random y<=1e10:",cnt,"ok")
hs.INSTR=True
for i in range(40):
    y=random.randint(10**9,10**10); L=random.randint(0,isqrt(y))
    assert hs.S(y,L)==hs.brute(y,L)
# special forms: squares, cubes, near-squares
for z in [10**10, 10**10-1, 99999**2, 99999**2-1, 2154**3, 2154**3-1, 2*3*5*7*11*13*17*19*23*29]:
    for L in (0,1,isqrt(z)//2):
        assert hs.S(z,L)==hs.brute(z,L)
print("instrumented 1e9..1e10 + special forms ok", hs.STAT)
# D3 vs sieve
N=20000
d3=[0]*(N+1)
d2=[0]*(N+1)
for a in range(1,N+1):
    for b in range(a,N+1,a): d2[b]+=1
for a in range(1,N+1):
    for b in range(a,N+1,a): d3[b]+=d2[b//a]
acc=0
for x in range(1,N+1):
    acc+=d3[x]
    assert hs.D3(x)==acc,x
print("D3 via (F1)+S matches sieve x<=",N, "; D3(10^6) =",hs.D3(10**6))
