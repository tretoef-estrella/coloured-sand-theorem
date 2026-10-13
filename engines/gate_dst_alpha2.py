import sys, itertools; sys.path.insert(0,'.')
import dst_alpha
from dst_alpha import piece_p2
from boolean_X import bool_M, smith_p
from math import comb
from collections import Counter
import numpy as np
M=30
def cmp(pr,dg):
    prl={v:k for v,k in pr[0].items() if v<M}; hi=sum(k for v,k in pr[0].items() if v>=M)+pr[1]
    return prl==dg[0] and hi==dg[1]
# control: alpha forced to 1
orig=dst_alpha.X_alpha
dst_alpha.X_alpha=lambda lam,i,alpha: orig(lam,i,1)
n=d=0
for m in range(2,9):
    for q in (4,8,12,16):
        for c in range(0,4):
            pr=piece_p2(m,q,c); g,z=smith_p(bool_M(m,c,q),2); n+=1; d+= not cmp(pr,(dict(sorted(g.items())),z))
dst_alpha.X_alpha=orig
print('control alpha=1 forced: cases',n,'differ',d,flush=True)
# control 2: no pooling (raw clocks)
orig_fit=dst_alpha.int_fit
dst_alpha.int_fit=lambda xs: xs
n=d=0
for m in range(2,10):
    for q in (2,4,6,8):
        for c in range(0,4):
            pr=piece_p2(m,q,c); g,z=smith_p(bool_M(m,c,q),2); n+=1; d+= not cmp(pr,(dict(sorted(g.items())),z))
dst_alpha.int_fit=orig_fit
print('control no pooling: cases',n,'differ',d,flush=True)
# m=10,11
ok=bad=0
for m in (10,11):
    for q in (2,4,8,12):
        for c in (0,1,3):
            pr=piece_p2(m,q,c); g,z=smith_p(bool_M(m,c,q),2); good=cmp(pr,(dict(sorted(g.items())),z)); ok+=good; bad+=not good
            if not good: print('BAD',m,q,c,flush=True)
print('m=10,11 ok',ok,'bad',bad,flush=True)
# full Laplacians
def full_pred(d,q):
    tot=Counter(); free=0
    for j in range(d+1):
        mu=comb(d,j)*(q-2)**j
        if mu==0: continue
        g,fr=piece_p2(d-j,q,j)
        for x,c in g.items(): tot[x]+=c*mu
        free+=fr*mu
    return dict(sorted(tot.items())),free
for d,q in ((3,4),(4,4),(3,6),(3,8),(2,12),(2,16),(3,10)):
    V=list(itertools.product(range(q),repeat=d)); idx={v:i for i,v in enumerate(V)}
    L=np.zeros((len(V),len(V)),dtype=np.int64)
    for v in V:
        i=idx[v]; L[i,i]=d*(q-1)
        for t in range(d):
            for y in range(q):
                if y!=v[t]: w=list(v); w[t]=y; L[i,idx[tuple(w)]]-=1
    g,z=smith_p(L,2); pr=full_pred(d,q); good=(dict(sorted(g.items()))==pr[0] and z==1 and pr[1]==1)
    print('FULL LAPLACIAN H(%d,%d)'%(d,q),'OK' if good else 'BAD',dict(sorted(g.items())),z,flush=True)
print('FIN-OK')
