# Check PREDICCION_SELLADA_4 by direct Smith forms (pieces) and Theorem A assembly; full Laplacian for H(4,6). Grepy Connor.
import sys; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
from frontier_model import predict_piece
from math import comb
from collections import Counter
import numpy as np
ok=bad=0
def direct_piece(m,q,c,p):
    g,z=smith_p(bool_M(m,c,q),p); return dict(sorted(g.items())),z
cases=[(3,m,q,c) for m in (9,10) for q in (12,15,21) for c in (5,6,7,8)]+[(2,4,q,c) for q in (6,10,8) for c in (5,6,7,8)]
for p,m,q,c in cases:
    pd=predict_piece(m,q,c,p); dg=direct_piece(m,q,c,p)
    good = (pd[0]==dg[0] and pd[1]==dg[1]); ok+=good; bad+=(not good)
    print('piece',p,m,q,c,'OK' if good else 'BAD','pred',pd,'direct',dg,flush=True)
def full_pieces(d,q,p,fn):
    tot=Counter(); free=0
    for j in range(d+1):
        mu=comb(d,j)*(q-2)**j
        if mu==0: continue
        g,z=fn(d-j,q,j,p)
        for x,n in g.items(): tot[x]+=n*mu
        free+=z*mu
    return dict(sorted(tot.items())),free
for d,q,p in ((10,3,3),(9,6,3),(4,6,2),(4,10,2)):
    pr=full_pieces(d,q,p,lambda m,q,c,p: predict_piece(m,q,c,p))
    di=full_pieces(d,q,p,direct_piece)
    good=(pr==di); ok+=good; bad+=(not good)
    print('FULL',d,q,p,'OK' if good else 'BAD','pred',pr,'direct pieces',di,flush=True)
# independent: full Laplacian of H(4,6) at p=2
import itertools
d,q=4,6; V=list(itertools.product(range(q),repeat=d)); idx={v:i for i,v in enumerate(V)}
L=np.zeros((len(V),len(V)),dtype=np.int64)
for v in V:
    i=idx[v]; L[i,i]=d*(q-1)
    for t in range(d):
        for y in range(q):
            if y!=v[t]:
                w=list(v); w[t]=y; L[i,idx[tuple(w)]]-=1
g,z=smith_p(L,2); pr=full_pieces(4,6,2,lambda m,q,c,p: predict_piece(m,q,c,p))
good=(dict(sorted(g.items()))==pr[0] and z==1); ok+=good; bad+=(not good)
print('FULL LAPLACIAN H(4,6) p=2','OK' if good else 'BAD',dict(sorted(g.items())),'zeros',z,flush=True)
print('TOTAL ok',ok,'bad',bad); print('FIN-OK')
