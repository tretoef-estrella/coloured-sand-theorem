#!/usr/bin/env python3
# Syl_p K(K_q^d) through the exact Boolean reduction:
#   coker L(K_q^d) = (+)_j coker(q(j+H)+U on B_{d-j})^{C(d,j)(q-2)^j}.
# Usage: hamming_bool.py q p d
import sys, math; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
q,p,d=map(int,sys.argv[1:4])
H={}; Z=0
for j in range(d+1):
    t=math.comb(d,j)*(q-2)**j
    if t==0: continue
    g,z=smith_p(bool_M(d-j,j,q),p); Z+=z*t
    for k,c in g.items(): H[k]=H.get(k,0)+c*t
H={k:c for k,c in sorted(H.items()) if c}
print('q=%d p=%d d=%d Syl_p:'%(q,p,d),H,'zeros=%d'%Z,'N=%d'%sum(H.values()),'exp=%d'%max(H) if H else '')
