# Direct check of the rank formula used in Theorem D: rank_p of the inclusion matrix W_{s,s+1}(m)
#   = sum_{i=0}^{t} [p does not divide (k-i choose t-i)] (C(m,i)-C(m,i-1)),  t=min(s,m-1-s) with k=s+1 or its complement.
import itertools, numpy as np
from math import comb
def rank_mod(M,p):
    M=M.copy()%p; r=0; rows,cols=M.shape
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i,c]%p: piv=i; break
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]; M[r]=(M[r]*pow(int(M[r,c]),-1,p))%p
        for i in range(rows):
            if i!=r and M[i,c]: M[i]=(M[i]-M[i,c]*M[r])%p
        r+=1
        if r==rows: break
    return r
def formula(m,s,p):
    if s<=m-1-s: t,k=s,s+1
    else: t,k=m-s-1,m-s
    return sum(comb(m,i)-(comb(m,i-1) if i else 0) for i in range(t+1) if comb(k-i,t-i)%p)
ok=bad=0
for p in (2,3,5,7):
    for m in range(1,12):
        for s in range(m):
            A=[frozenset(c) for c in itertools.combinations(range(m),s)]; B=[frozenset(c) for c in itertools.combinations(range(m),s+1)]
            W=np.array([[1 if a<=b else 0 for b in B] for a in A],dtype=np.int64)
            r=rank_mod(W,p); f=formula(m,s,p); ok+=r==f; bad+=r!=f
            if r!=f: print('BAD',p,m,s,r,f)
print('ok',ok,'bad',bad)
