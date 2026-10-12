# Independent check with Sage/PARI: full Laplacian of H(d,p), elementary divisors over Z (no reduction lemma).
import sys
from sage.all import matrix, ZZ, identity_matrix, ones_matrix
p=int(sys.argv[1]); d=int(sys.argv[2])
K=p*identity_matrix(ZZ,p)-ones_matrix(ZZ,p)
L=matrix(ZZ,1,1,[0])
for _ in range(d):
    n=L.nrows()
    L=L.tensor_product(identity_matrix(ZZ,p))+identity_matrix(ZZ,n).tensor_product(K)
ed=L.elementary_divisors()
h={}
for e in ed:
    if e==0: continue
    v=ZZ(e).valuation(p)
    if v>0: h[v]=h.get(v,0)+1
print('sage p=%d d=%d Syl_p:'%(p,d),dict(sorted(h.items())),'zeros=',sum(1 for e in ed if e==0))
