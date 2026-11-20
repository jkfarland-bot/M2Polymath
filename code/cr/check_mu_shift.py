# Cold-reader check of the mu -> cheap D_k slice reduction. Exact integer arithmetic.
import itertools, random
from math import comb, gcd
def vp(n,p):
    if n==0: return 10**9
    v=0
    while n%p==0: n//=p; v+=1
    return v
def S(m):
    s,f=1,1
    while f%m: s+=1; f*=s
    return s
def lcm(a,b): return a*b//gcd(a,b)
R=60
# (1) slice values of zeta^z * E_p(g) on squarefree n with omega=r: g(1)*z^r (0^0=1)
def dz(z,n):  # number of ordered z-factorizations, brute
    if z==0: return 1 if n==1 else 0
    if z==1: return 1
    return sum(dz(z-1,n//d) for d in range(1,n+1) if n%d==0)
def Ep(g,p,n):
    m=round(n**(1/p))
    for mm in (m-1,m,m+1):
        if mm>=1 and mm**p==n: return g(mm)
    return 0
def conv(f,h,n): return sum(f(d)*h(n//d) for d in range(1,n+1) if n%d==0)
g=lambda m: 7*m*m-3*m+5
for p in (2,3):
  for z in range(0,4):
    for n,r in [(1,0),(2,1),(6,2),(30,3),(210,4)]:
      val=conv(lambda d:dz(z,d), lambda e:Ep(g,p,e), n)
      assert val==g(1)*z**r, (p,z,n)
# (2) binomial identity on random integer c (no hypothesis)
for _ in range(200):
    L=random.randint(0,6); c=[random.randint(-50,50) for _ in range(L+1)]
    m=[sum(c[z]*z**r for z in range(L+1)) for r in range(R)]
    for r in range(R):
        assert sum(c[z]*(z+1)**r for z in range(L+1))==sum(comb(r,j)*m[j] for j in range(r+1))
# (3) all solutions mod p^k of sum c_z z^r == (-1)^r, r=0..R, nodes 0..L
def sols(p,k,L):
    P=p**k; out=[]
    for c in itertools.product(range(P),repeat=L):
        c0=(1-sum(c))%P; cc=(c0,)+c
        if all((sum(cc[z]*pow(z,r,P) for z in range(L+1))-(-1)**r)%P==0 for r in range(R)):
            out.append(cc)
    return out
for p,k,Lmax in [(2,1,3),(2,2,4),(2,3,4),(2,4,6),(3,1,3),(3,2,6)]:
    P=p**k
    for L in range(0,Lmax+1):
        if (P**L)>600000: break
        ss=sols(p,k,L)
        for cc in ss:
            b={w:cc[w-1] for w in range(1,L+2)}
            for r in range(R):
                assert (sum(b[w]*w**r for w in b)-(1 if r==0 else 0))%P==0
            D=1
            for w in range(1,L+2): D=lcm(D,w)
            a={w:b[w]*D//w for w in b}; assert all(b[w]*D%w==0 for w in b)
            s=[sum(a[w]*w**r for w in a) for r in range(R)]
            assert (s[1]-D)%(D*P)==0
            assert all(s[r]%(D*P)==0 for r in range(2,R))
            v=vp(D,p); u=s[1]//p**v; assert u%p!=0
            T=[w for w in b if a[w]!=0]; q0=1
            for w in T: q0*=w
            assert vp(q0,p)>=k   # H4
        print(f"p={p} k={k} L={L}: #sols mod p^k={len(ss)}  S(p^k)-1={S(P)-1}  consistent={(len(ss)==0) or L>=S(P)-1}")
