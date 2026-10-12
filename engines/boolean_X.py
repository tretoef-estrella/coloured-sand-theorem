#!/usr/bin/env python3
# X(m,c,q) := coker of M = q(c+H) + U on the Boolean lattice B_m (basis: subsets of [m]); H = size, U = up operator.
# Theorem candidate: coker L(K_q^d) = (+)_j coker M(d-j, j, q)^{C(d,j)(q-2)^j}   (over Z, any q >= 2).
import sys, numpy as np, math, itertools
sys.path.insert(0,'.')
def bool_M(m,c,q):
    n=1<<m; M=np.zeros((n,n),dtype=np.int64)
    for S in range(n):
        s=bin(S).count('1'); M[S,S]=q*(c+s)
        for x in range(m):
            if not (S>>x)&1: M[S|(1<<x),S]+=1
    return M
def smith_p(W0,p):
    M_=max(m for m in range(1,40) if p**m<2**31); q=p**M_
    W=np.array(W0,dtype=np.int64)%q; mod=q; v=0; hist={}
    while W.size:
        mask=(W%p)!=0
        if not mask.any():
            if v+1>=M_: break
            W//=p; mod//=p; v+=1; continue
        i,j=np.unravel_index(np.argmax(mask),mask.shape)
        ui=pow(int(W[i,j]),-1,mod); row=(W[i,:]*ui)%mod; col=W[:,j].copy()
        W=(W-np.outer(col,row))%mod; W=np.delete(np.delete(W,i,0),j,1)
        hist[v]=hist.get(v,0)+1
    zeros=W.shape[0] if W.size else 0
    return {k:c for k,c in sorted(hist.items()) if k>0},zeros
if __name__=='__main__':
    m,c,q,p=map(int,sys.argv[1:5]); print(smith_p(bool_M(m,c,q),p))
