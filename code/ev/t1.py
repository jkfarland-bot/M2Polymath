import os
import sys, random, time
sys.path.insert(0,os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'ev'))
import hs
from math import isqrt
hs.INSTR=True
n=0
for y in range(1,2001):
    for L in range(0, isqrt(y)+2):
        assert hs.S(y,L)==hs.brute(y,L),(y,L); n+=1
print("exhaustive y<=2000 all L:",n,"cases ok")
random.seed(7)
for i in range(3000):
    y=random.randint(1,10**7); L=random.randint(0,isqrt(y))
    assert hs.S(y,L)==hs.brute(y,L)
print("instrumented random y<=1e7: ok")
print({k:v for k,v in hs.STAT.items()})
