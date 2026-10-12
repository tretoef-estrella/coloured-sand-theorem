# Gate of Theorem A: Sylow p-subgroup of coker L(H(d,q)) computed (i) directly from the full Laplacian,
# (ii) from the pieces X_q(d-j,j)^{C(d,j)(q-2)^j}.  Primes p dividing q and not dividing q.  Control: dropping
# the conjugation sign (using q(j+H)-U is equivalent, so instead we perturb the multiplicities) must fail.
import sys, math, itertools, numpy as np; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
def lap(q,d):
    V=list(itertools.product(range(q),repeat=d)); idx={v:i for i,v in enumerate(V)}; n=len(V)
    L=np.zeros((n,n),dtype=np.int64)
    for v in V:
        i=idx[v]; L[i,i]=d*(q-1)
        for a in range(d):
            for x in range(q):
                if x!=v[a]:
                    w=list(v); w[a]=x; L[i,idx[tuple(w)]]=-1
    return L
def pieces(q,p,d,shift=0):
    H={}; Z=0
    for j in range(d+1):
        t=math.comb(d,j)*(q-2)**j+(shift if j==1 else 0)
        if t<=0: continue
        g,z=smith_p(bool_M(d-j,j,q),p); Z+=z*t
        for k,c in g.items(): H[k]=H.get(k,0)+c*t
    return {k:c for k,c in sorted(H.items()) if c},Z
cells=[(3,d) for d in (1,2,3,4,5)]+[(4,d) for d in (1,2,3,4)]+[(5,d) for d in (1,2,3,4)]+[(6,d) for d in (1,2,3)]+[(7,d) for d in (1,2,3)]+[(9,d) for d in (1,2,3)]+[(8,d) for d in (1,2,3)]+[(10,2),(12,2)]
ok=bad=0; ctrl=0
for q,d in cells:
    L=lap(q,d)
    for p in (2,3,5,7):
        if p>q+1 and q%p: continue
        g,z=smith_p(L,p); g=dict(g); P,Z=pieces(q,p,d)
        good=(g==P and z==Z); ok+=good; bad+=not good
        Pc,_=pieces(q,p,d,shift=1); ctrl+=(Pc!=g)
        print('q',q,'d',d,'p',p,'direct',g,'pieces',P,'OK' if good else 'BAD',flush=True)
print('cells x primes',ok+bad,'ok',ok,'bad',bad,'| control (one extra copy of the j=1 piece) differs in',ctrl)
