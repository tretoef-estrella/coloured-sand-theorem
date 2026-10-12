# Gate: exponent of Syl_p K(K_q^d) (Boolean reduction, exact) against
#   E = max_{1<=s<=d}(e*s + v_p(s)) if e = v_p(q) >= 1,   E = floor(log_p d) if p does not divide q.
# Control: the naive guesses e*d + v_p(d) and e*d must fail somewhere.
import sys, math; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
def vp(x,p):
    v=0
    while x%p==0: x//=p; v+=1
    return v
def flog(d,p):
    k=0
    while p**(k+1)<=d: k+=1
    return k
cells=[(q,p,d) for (q,p,dmax) in [(3,3,9),(4,2,8),(6,2,7),(6,3,7),(8,2,7),(9,3,6),(12,2,6),(12,3,6),(5,5,8),(10,5,6),(7,7,8),
        (4,3,9),(5,3,9),(7,3,8),(5,2,8),(7,2,8),(3,2,8),(7,5,8),(4,5,7)] for d in range(1,dmax+1)]
ok=bad=0; c1=c2=0
for q,p,d in cells:
    H={}
    for j in range(d+1):
        t=math.comb(d,j)*(q-2)**j
        if t==0: continue
        g,z=smith_p(bool_M(d-j,j,q),p)
        for k,c in g.items(): H[k]=H.get(k,0)+c*t
    ex=max(H) if H else 0; e=vp(q,p)
    E=max(e*s+vp(s,p) for s in range(1,d+1)) if e>=1 else flog(d,p)
    ok+=ex==E; bad+=ex!=E
    if e>=1: c1+=(ex!=e*d+vp(d,p)); c2+=(ex!=e*d)
    print(q,p,d,'exp',ex,'E',E,'OK' if ex==E else 'BAD',flush=True)
print('cells',len(cells),'ok',ok,'bad',bad,'| control e*d+v(d) fails',c1,'control e*d fails',c2)
