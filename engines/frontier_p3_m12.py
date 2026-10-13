import sys; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
import frontier_model2 as fm
from collections import Counter
from tilt3p import beta
# blocks of m=12, p=3 other than lambda=12: from Theorem G' (all lambda <= 11 two-factor or simple)
p=3; m=12
def mult(m):
    n={}
    for lam in range(m,-1,-1):
        if (m-lam)%2: continue
        # lambda=12 is four-factor: its Weyl factors 12,10,6,4 -> subtract from those below
        n[lam]=beta(m,lam)-sum(n[mu] for mu in n if fm.bottom(p,mu)==lam and mu<12)-(n.get(12,0) if lam in (10,6,4) else 0)
    return n
nl=mult(m); print('multiplicities',nl,flush=True)
for q in (3,6):
    for c in (0,1,2,3):
        g,z=smith_p(bool_M(m,c,q),p); direct=Counter(g)
        rest=Counter(); free=0
        for lam,n in nl.items():
            if n<=0 or lam==12: continue
            ex,fr=fm.block_cf(p,lam,q,c,(m-lam)//2)
            for x in ex: rest[x]+=n
            free+=fr*n
        left=direct-rest; neg=rest-direct
        print('q',q,'c',c,'block12 (left):',dict(sorted(left.items())),'neg',dict(neg),'free direct',z,'free rest',free,flush=True)
print('FIN-OK')
