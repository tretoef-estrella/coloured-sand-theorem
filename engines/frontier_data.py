# Frontier m = p^2 .. p^2+p-2: direct Smith forms of q(c+H)+U on B_m, minus the blocks of Theorem G (lambda with a+1<p),
# leaving the blocks with a = p-1. Grepy Connor, 13 Oct 2026. p=3: m=9,10; p=2: m=4.
import sys, itertools; sys.path.insert(0,'.')
import tilt3p
from tilt3p import block, beta
from boolean_X import bool_M, smith_p
from collections import Counter
def bottom_gen(p,lam):
    r=(lam+1)%p
    if lam<p or r==0: return None
    return lam-2*r
tilt3p.bottom=bottom_gen
def mult(m,p):
    n={}
    for lam in range(m,-1,-1):
        if (m-lam)%2: continue
        n[lam]=beta(m,lam)-sum(n[mu] for mu in n if bottom_gen(p,mu)==lam)
    return n
for p,ms,qs in ((2,(4,),(2,4)),(3,(9,10),(3,9,6))):
    for m in ms:
        nl=mult(m,p)
        for q in qs:
            e=0; x=q
            while x%p==0: x//=p; e+=1
            for c in range(0,5):
                Mprec=max(t for t in range(1,40) if p**t<2**31)
                g,z=smith_p(bool_M(m,c,q),p)
                direct=Counter({v:k for v,k in g.items()})
                rest=Counter(); free=0; newb=[]
                for lam,n in nl.items():
                    if n==0: continue
                    a=(lam+1)//p-1 if lam>=p else 0; r=(lam+1)%p
                    if lam>=p and r!=0 and a+1>=p: newb.append((lam,n)); continue
                    for v in block(p,lam,q,c,(m-lam)//2):
                        if v is None: free+=n
                        elif v>0: rest[v]+=n
                left=direct-rest; neg=rest-direct
                print('p',p,'m',m,'q',q,'e',e,'c',c,'new blocks',newb,'left',dict(sorted(left.items())),'negative',dict(neg),'free direct',z,'free rest',free,flush=True)
print('FIN-OK')
