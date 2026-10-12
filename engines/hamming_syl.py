#!/usr/bin/env python3
# Sylow p-subgroup of the sandpile group K(H(d,p)) of the Hamming graph H(d,p) = K_p^d, p prime.
# Reduction (exact over Z, proved by a unimodular change of basis on each factor Z^p):
#   coker L_d  =~  coker( A(A+pI) )  (+)  coker( A+pI )^{(+)(p-2)},   A = L_{d-1}.
# Smith form over Z/p^M by unit-pivot Schur complements, level by level.
# Usage: hamming_syl.py p d [direct]
import sys, numpy as np, math
p=int(sys.argv[1]); d=int(sys.argv[2]); direct=len(sys.argv)>3
M=max(m for m in range(1,40) if p**m < 2**31); q=p**M
def lap(d):
    K=p*np.eye(p,dtype=np.int64)-np.ones((p,p),dtype=np.int64)
    L=np.zeros((1,1),dtype=np.int64)
    for _ in range(d):
        n=L.shape[0]
        L=np.kron(L,np.eye(p,dtype=np.int64))+np.kron(np.eye(n,dtype=np.int64),K)
    return L
def smith(W0):
    W=np.array(W0,dtype=np.int64)%q; mod=q; v=0; hist={}
    while W.size:
        mask=(W%p)!=0
        if not mask.any():
            if v+1>=M: break
            W//=p; mod//=p; v+=1; continue
        i,j=np.unravel_index(np.argmax(mask),mask.shape)
        u=int(W[i,j]); ui=pow(u,-1,mod)
        row=(W[i,:]*ui)%mod; col=W[:,j].copy()
        W=(W-np.outer(col,row))%mod
        W=np.delete(np.delete(W,i,0),j,1)
        hist[v]=hist.get(v,0)+1
    zeros=W.shape[0] if W.size else 0
    return hist,zeros
def add(h,g,times=1):
    for k,c in g.items(): h[k]=h.get(k,0)+c*times
if direct:
    h,z=smith(lap(d)); H=h
else:
    A=lap(d-1); n=A.shape[0]; I=np.eye(n,dtype=np.int64)
    B=(A+p*I)%q
    AB=np.zeros((n,n),dtype=np.int64)
    # A*B mod q in chunks to avoid overflow: entries of A are small (|a|<=d(p-1)+...), B < q
    AB=(A.astype(object).dot(B.astype(object))%q).astype(np.int64) if n<=243 else None
    if AB is None:
        Bs=B.copy(); AB=np.zeros((n,n),dtype=np.int64)
        nz=[np.nonzero(A[r])[0] for r in range(n)]
        for r in range(n):
            cols=nz[r]; AB[r]=(A[r,cols][:,None]*Bs[cols]).sum(0)%q
    h1,z1=smith(AB); h2,z2=smith(B)
    H={}; add(H,h1); add(H,h2,p-2); z=z1+(p-2)*z2
syl={k:c for k,c in sorted(H.items()) if k>0}
# expected v_p(kappa): kappa = p^{-d} prod_{s=1..d} (p s)^{C(d,s)(p-1)^s}
vk=-d+sum(math.comb(d,s)*(p-1)**s*(1+ (lambda x:(lambda f:f(f,x))(lambda f,x:0 if x%p else 1+f(f,x//p)))(s)) for s in range(1,d+1))
tot=sum(k*c for k,c in syl.items())
print('p=%d d=%d M=%d  zeros=%d  Syl_p K: %s  v_p|K|=%d  expected v_p(kappa)=%d  %s'%(p,d,M,z,syl,tot,vk,'OK' if (tot==vk and z==1) else 'MISMATCH'))
print('FIN-OK')
