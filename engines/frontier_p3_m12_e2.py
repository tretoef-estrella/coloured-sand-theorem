# Grepy Connor 13 Oct 2026. Sealed prediction 7: block lambda=12 at p=3, e=2 (q=9), c=1,2, m=12.
# smith_p works modulo 3^19, so factors of exponent >= 19 appear as "zeros". We compare only what is exact:
# the numbers of factors of exponent 1 and 2, and the total number of cyclic factors (= corank mod 3).
import sys; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
import frontier_model2 as fm
from collections import Counter
from tilt3p import beta
p=3; m=12
def mult(m):
    n={}
    for lam in range(m,-1,-1):
        if (m-lam)%2: continue
        n[lam]=beta(m,lam)-sum(n[mu] for mu in n if fm.bottom(p,mu)==lam and mu<12)-(n.get(12,0) if lam in (10,6,4) else 0)
    return n
nl=mult(m); print('multiplicities',nl,flush=True)
for q in (9,):
    for c in (1,2):
        g,z=smith_p(bool_M(m,c,q),p); direct=Counter(g)
        rest=Counter(); free=0
        for lam,n in nl.items():
            if n<=0 or lam==12: continue
            ex,fr=fm.block_cf(p,lam,q,c,(m-lam)//2)
            for x in ex: rest[x]+=n
            free+=fr*n
        tot_direct=sum(direct.values())+z; tot_rest=sum(rest.values())+free
        e1=direct[1]-rest[1]; e2=direct[2]-rest[2]; big=(tot_direct-tot_rest)-e1-e2
        print('q',q,'c',c,'block12: exponent-1 factors',e1,'exponent-2 factors',e2,'factors of exponent >= 3',big,'| direct zeros (exponent>=19)',z,flush=True)
print('FIN-OK')
