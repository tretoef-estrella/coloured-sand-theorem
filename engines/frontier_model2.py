# Theorem G' model, m <= p^2+p-1 (Grepy Connor, 13 Oct 2026).
# Two-factor tilting T(lam): lam = p-1+r+pa with 1<=r<=p (r=p only for lam=p^2+p-1), bottom mu = lam-2r,
# glue x_j = C(j+r,j)/p^nu, nu = min_{1<=t<=r} v_p C(lam-r+t, t).
import sys; sys.path.insert(0,'.')
import tilt3p
from fractions import Fraction as F
from math import comb
from tilt3p import beta
from collections import Counter
def ivp(x,p):
    if x==0: return 10**9
    v=0
    while x%p==0: x//=p; v+=1
    return v
def params(p,lam):
    """returns None for a simple block, else (r,a,mu,nu)"""
    if lam<p: return None
    r=(lam+1)%p
    if r==0:
        if lam==p*p+p-1: r=p
        else: return None
    a=(lam-(p-1)-r)//p; mu=lam-2*r
    nu=min(ivp(comb(lam-r+t,t),p) for t in range(1,r+1))
    return r,a,mu,nu
def bottom(p,lam):
    P=params(p,lam); return None if P is None else P[2]
def model(p,lam):
    P=params(p,lam); mu=None if P is None else P[2]; lp=-1 if mu is None else mu
    N=lam+1+lp+1; basis=[]
    for i in range(lam+1):
        v=[F(0)]*N; v[i]=F(1); basis.append(v)
    dl=0 if P is None else P[0]
    for j in range(lp+1):
        v=[F(0)]*N; v[lam+1+j]=F(1); v[j+dl]+=F(comb(j+dl,j),p**P[3]); basis.append(v)
    return mu,lp,dl,N,basis
tilt3p.model=model; tilt3p.bottom=bottom
def mult(m,p):
    n={}
    for lam in range(m,-1,-1):
        if (m-lam)%2: continue
        n[lam]=beta(m,lam)-sum(n[mu] for mu in n if bottom(p,mu)==lam)
    return n
def block_cf(p,lam,q,c,k):
    e=ivp(q,p); v=[ (10**9 if c+k+i==0 else e+ivp(c+k+i,p)) for i in range(lam+1)]
    free = 1 if c+k==0 else 0
    A=sum(v); P=params(p,lam)
    if P is None:
        a=(lam+1)//p-1 if lam>=p else 0
        if lam<p: return ([] if free else [A]), free
        return sorted([1]*a+([] if free else [A-a])), free
    r,a,mu,nu=P; Ap=sum(v[r:r+mu+1]); al_last=sum(v[(a+1)*p:lam+1])
    if r<p and a+1<p:   E12=Ap-a+1; E11=A-al_last-a; E22=Ap-a+al_last; ones=2*a
    elif r<p:           E12=Ap-a+2; E11=A-al_last-a; E22=Ap-a+al_last; ones=2*a
    else:  # r=p, a=p-1, lam=p^2+p-1
        E11=A-al_last-p+1; E12=Ap-p+3; E22=Ap-p+1+al_last; ones=2*p-2
    if free: return sorted([1]*ones+[min(E12,E22)]), free
    x=min(E11,E12,E22); y=E11+E22-x
    return sorted([1]*ones+[x,y]), free
def predict_piece(m,q,c,p,use_model=False):
    out=Counter(); free=0
    for lam,n in mult(m,p).items():
        if n<=0:
            if n<0: return None
            continue
        k=(m-lam)//2
        if use_model:
            vals=tilt3p.block(p,lam,q,c,k); ex=[x for x in vals if x is not None and x>0]; fr=sum(1 for x in vals if x is None)
        else: ex,fr=block_cf(p,lam,q,c,k)
        for x in ex: out[x]+=n
        free+=fr*n
    return dict(sorted(out.items())),free
