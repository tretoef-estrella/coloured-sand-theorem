import sys; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
import frontier_model2 as fm
from math import comb
from collections import Counter
import numpy as np, itertools
ok=bad=0
def direct_piece(m,q,c,p):
    g,z=smith_p(bool_M(m,c,q),p); return dict(sorted(g.items())),z
cases=[(3,11,q,c) for q in (12,15) for c in (4,5,6)]+[(2,5,q,c) for q in (6,10,8) for c in (4,5,6,7)]
for p,m,q,c in cases:
    pd=fm.predict_piece(m,q,c,p); dg=direct_piece(m,q,c,p); good=(pd==dg); ok+=good; bad+=(not good)
    print('piece',p,m,q,c,'OK' if good else 'BAD',pd,dg,flush=True)
def full(d,q,p,fn):
    tot=Counter(); free=0
    for j in range(d+1):
        mu=comb(d,j)*(q-2)**j
        if mu==0: continue
        g,z=fn(d-j,q,j,p)
        for x,n in g.items(): tot[x]+=n*mu
        free+=z*mu
    return dict(sorted(tot.items())),free
for d,q,p in ((11,3,3),(5,4,2),(5,6,2)):
    pr=full(d,q,p,lambda m,q,c,p: fm.predict_piece(m,q,c,p)); di=full(d,q,p,direct_piece); good=(pr==di); ok+=good; bad+=(not good)
    print('FULL',d,q,p,'OK' if good else 'BAD',pr,di,flush=True)
d,q=5,4; V=list(itertools.product(range(q),repeat=d)); idx={v:i for i,v in enumerate(V)}
L=np.zeros((len(V),len(V)),dtype=np.int64)
for v in V:
    i=idx[v]; L[i,i]=d*(q-1)
    for t in range(d):
        for y in range(q):
            if y!=v[t]: w=list(v); w[t]=y; L[i,idx[tuple(w)]]-=1
g,z=smith_p(L,2); pr=full(5,4,2,lambda m,q,c,p: fm.predict_piece(m,q,c,p)); good=(dict(sorted(g.items()))==pr[0] and z==1); ok+=good; bad+=(not good)
print('FULL LAPLACIAN H(5,4) p=2','OK' if good else 'BAD',dict(sorted(g.items())),z,flush=True)
print('TOTAL ok',ok,'bad',bad); print('FIN-OK')
