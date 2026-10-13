# Gate for CONJECTURE_H_PROOF_v1.md (Grepy Connor, 13 Oct 2026). Model lattices only.
# G1: block closed form vs Smith form of the model lattice, p=5,7, every lambda <= p^2-1 (general rule), random (e,c,k) + (c,k)=(0,0).
# G1c: control, split lattice (no glue) must differ.
# G2: stability of the forced lattice under e^(t), f^(t): p=5 every lambda in [5,24]; p=7 sample.
# G3: out of range, p=5 lambda = 25..28 (a = p-1): stability and formula, recorded.
import sys, random, time; sys.path.insert(0,'.')
import tilt3p
from tilt3p import block, stable, vp
from fractions import Fraction as F
from math import comb
random.seed(20261013)
def bottom_gen(p,lam):
    r=(lam+1)%p
    if lam<p or r==0: return None
    return lam-2*r
tilt3p.bottom=bottom_gen
def ivp(x,p):
    v=0
    while x%p==0: x//=p; v+=1
    return v
def want(p,lam,e,c,k):
    r=(lam+1)%p; a=(lam+1)//p-1 if lam>=p else 0
    Av=[ (10**9 if c+k+i==0 else e+ivp(c+k+i,p)) for i in range(lam+1)]
    free = 1 if (c==0 and k==0) else 0
    if lam<p:
        return sorted([] if free else [sum(Av)]), free
    if r==0:
        a=(lam+1)//p-1
        return sorted([1]*a+([] if free else [sum(Av)-a])), free
    mu=lam-2*r; Ap=sum(e+ivp(c+k+r+j,p) for j in range(mu+1))
    return sorted([1]*(2*a)+[Ap+1-a]+([] if free else [sum(Av)-1-a])), free
def got_of(vals):
    return sorted(v for v in vals if v is not None and v>0), sum(1 for v in vals if v is None)
t0=time.time()
n=bad=0
for p,reps in ((5,4),(7,1)):
    for lam in range(1,p*p):
        trials=[(1,0,0)]+[(random.choice([1,2]),random.randint(0,8),random.randint(0,3)) for _ in range(reps)]
        for e,c,k in trials:
            q=p**e*random.choice([x for x in (1,2,4,8) if x%p])
            g=got_of(block(p,lam,q,c,k)); w=want(p,lam,e,c,k); n+=1
            if g!=w: bad+=1; print('G1 BAD',p,lam,e,c,k,g,w,flush=True)
    print('G1 p',p,'done cases',n,'bad',bad,'t',round(time.time()-t0,1),flush=True)
print('G1 TOTAL',n,'bad',bad,flush=True)
# control: split lattice
orig_model=tilt3p.model
def split_model(p,lam):
    mu,lp,dl,N,basis=orig_model(p,lam)
    for j in range(lp+1):
        v=[F(0)]*N; v[lam+1+j]=F(1); basis[lam+1+j]=v
    return mu,lp,dl,N,basis
tilt3p.model=split_model
nc=diff=0
for p in (5,7):
    for lam in range(p,p*p):
        if (lam+1)%p==0: continue
        e,c,k=1,random.randint(1,6),random.randint(0,2); q=p
        g=got_of(tilt3p.block(p,lam,q,c,k)); w=want(p,lam,e,c,k); nc+=1
        if g!=w: diff+=1
tilt3p.model=orig_model
print('G1c control (split lattice) cases',nc,'differ',diff,flush=True)
# G2 stability
ns=bs=0
for p,lams in ((5,range(5,25)),(7,(8,13,15,20,22,27))):
    for lam in lams:
        if (lam+1)%p==0: continue
        s=stable(p,lam); ns+=1
        if s: bs+=1; print('G2 UNSTABLE',p,lam,s,flush=True)
    print('G2 p',p,'t',round(time.time()-t0,1),flush=True)
print('G2 stability lattices',ns,'unstable',bs,flush=True)
# G3 out of range
for lam in range(25,29):
    s=stable(5,lam)
    e,c,k=1,1,0; g=got_of(block(5,lam,5,c,k)); w=want(5,lam,e,c,k)
    print('G3 p 5 lam',lam,'unstable-checks',s,'model',g,'formula',w,flush=True)
print('FIN-OK t',round(time.time()-t0,1))
