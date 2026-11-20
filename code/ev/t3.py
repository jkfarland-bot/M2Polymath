import os
import sys, math
sys.path.insert(0,os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'ev'))
import hs
from math import isqrt
for y in [10**8, 10**12, 10**14+7]:
  for L in [0, int(y**0.4), int(y**0.49)]:
    for k in hs.STAT: hs.STAT[k]=0 if not isinstance(hs.STAT[k],bool) else True
    hs.INSTR=False
    hs.S(y,L)
    c=y**(1/3); r=isqrt(y); N1=max(L+1,hs.icbrt(y)+1)
    bound=1+(4*c+1)*math.log(r/N1)+math.log2(y**(1/6))+1
    print(y,L,"blocks",hs.STAT['blocks'],"bound",round(bound),"ops/(y^1/3 ln^2 y)",round((hs.STAT['blocks']+hs.STAT['cf']+hs.STAT['evals']+hs.STAT['direct'])/(c*math.log(y)**2),3))
