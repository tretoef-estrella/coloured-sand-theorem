# Conjecture I model (Grepy Connor, 13 Oct 2026): for m <= p^2+p-2 the tilting lattices are the two-chain lattices
# with glue x_j = C(j+r,j) / p^(1+v_p(a+1)) ; lambda = p-1+r+pa, 1<=r<=p-1. Predictions = sum of blocks with multiplicities (T3).
import sys; sys.path.insert(0,'.')
import tilt3p
from fractions import Fraction as F
from math import comb
from tilt3p import beta
def ivp(x,p):
    if x==0: return 10**9
    v=0
    while x%p==0: x//=p; v+=1
    return v
def bottom_gen(p,lam):
    r=(lam+1)%p
    if lam<p or r==0: return None
    return lam-2*r
def model2(p,lam):
    mu=bottom_gen(p,lam); lp=-1 if mu is None else mu
    N=lam+1+lp+1; basis=[]
    for i in range(lam+1):
        v=[F(0)]*N; v[i]=F(1); basis.append(v)
    dl=0 if mu is None else (lam-mu)//2
    if mu is not None:
        a=(lam+1)//p-1; den=p**(1+ivp(a+1,p))
    for j in range(lp+1):
        v=[F(0)]*N; v[lam+1+j]=F(1); v[j+dl]+=F(comb(j+dl,j),den); basis.append(v)
    return mu,lp,dl,N,basis
tilt3p.model=model2; tilt3p.bottom=bottom_gen
def mult(m,p):
    n={}
    for lam in range(m,-1,-1):
        if (m-lam)%2: continue
        n[lam]=beta(m,lam)-sum(n[mu] for mu in n if bottom_gen(p,mu)==lam)
    return n
def block_cf(p,lam,q,c,k):
    """closed form; returns (sorted positive exponents, free)"""
    e=ivp(q,p); v=[ (10**9 if c+k+i==0 else e+ivp(c+k+i,p)) for i in range(lam+1)]
    free = 1 if c+k==0 else 0
    A=sum(v)
    if lam<p: return ([] if free else [A]), free
    r=(lam+1)%p; a=(lam+1)//p-1
    if r==0: return sorted([1]*a+([] if free else [A-a])), free
    mu=lam-2*r; Ap=sum(v[r:r+mu+1]); al_last=sum(v[(a+1)*p:lam+1])
    if a+1<p:
        E12=Ap-a+1; E11=A-al_last-a; E22=Ap-a+al_last
    else:
        E12=Ap-a+2; E11=A-al_last-a; E22=Ap-a+al_last
    if free: return sorted([1]*(2*a)+[min(E12,E22)]), free
    x=min(E11,E12,E22); y=E11+E22-x
    return sorted([1]*(2*a)+[x,y]), free
def predict_piece(m,q,c,p,use_model=False):
    from collections import Counter
    out=Counter(); free=0
    for lam,n in mult(m,p).items():
        if n<=0:
            if n<0: return None
            continue
        k=(m-lam)//2
        if use_model:
            vals=tilt3p.block(p,lam,q,c,k); ex=[x for x in vals if x is not None and x>0]; fr=sum(1 for x in vals if x is None)
        else:
            ex,fr=block_cf(p,lam,q,c,k)
        for x in ex: out[x]+=n
        free+=fr*n
    return dict(sorted(out.items())),free
