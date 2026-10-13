# Block lambda = p^2+p-1 = (p-1)+p*p : T = St (x) T(p)^[1], Weyl factors Delta(lambda), Delta(lambda-2p).
# Test glue denominators p and p^2 against the direct data (p=2: m=5,6; p=3: m=11). Grepy Connor.
import sys; sys.path.insert(0,'.')
import tilt3p
from fractions import Fraction as F
from math import comb
from tilt3p import beta
from boolean_X import bool_M, smith_p
from collections import Counter
def ivp(x,p):
    v=0
    while x%p==0: x//=p; v+=1
    return v
DEN={}
def bottom3(p,lam):
    r=(lam+1)%p
    if lam<p: return None
    if r==0:
        if lam==p*p+p-1: return lam-2*p
        return None
    return lam-2*r
def model3(p,lam):
    mu=bottom3(p,lam); lp=-1 if mu is None else mu
    N=lam+1+lp+1; basis=[]
    for i in range(lam+1):
        v=[F(0)]*N; v[i]=F(1); basis.append(v)
    dl=0 if mu is None else (lam-mu)//2
    if mu is not None:
        if lam==p*p+p-1: den=DEN['x']
        else:
            a=(lam+1)//p-1; den=p**(1+ivp(a+1,p))
    for j in range(lp+1):
        v=[F(0)]*N; v[lam+1+j]=F(1); v[j+dl]+=F(comb(j+dl,j),den); basis.append(v)
    return mu,lp,dl,N,basis
tilt3p.model=model3; tilt3p.bottom=bottom3
def mult(m,p):
    n={}
    for lam in range(m,-1,-1):
        if (m-lam)%2: continue
        n[lam]=beta(m,lam)-sum(n[mu] for mu in n if bottom3(p,mu)==lam)
    return n
def pred(m,q,c,p):
    out=Counter(); free=0
    for lam,n in mult(m,p).items():
        if n<=0: continue
        vals=tilt3p.block(p,lam,q,c,(m-lam)//2)
        for x in vals:
            if x is None: free+=n
            elif x>0: out[x]+=n
    return dict(sorted(out.items())),free
for p,m,qs,cs in ((2,5,(2,4,6),(0,1,2,3)),(2,6,(4,6),(1,2,3)),(3,11,(3,6),(0,1,2,3))):
    for q in qs:
        for c in cs:
            g,z=smith_p(bool_M(m,c,q),p); dg=(dict(sorted(g.items())),z)
            res=[]
            for d in (p,p*p):
                DEN['x']=d; res.append('SAME' if pred(m,q,c,p)==dg else 'DIFF')
            st={}
            for d in (p,p*p):
                DEN['x']=d; st[d]=tilt3p.stable(p,p*p+p-1)
            print('p',p,'m',m,'q',q,'c',c,'den p:',res[0],'den p^2:',res[1],'unstable(p,p^2):',st[p],st[p*p],flush=True)
print('FIN-OK')
