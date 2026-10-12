# Predictor for X(m,c) = Syl_p coker(q(c+H)+U on B_m), range m <= 2p-2 (tilting modules with <= 2 Weyl factors).
# Guess: T(lam), p<=lam<=2p-2, glued with Delta(2p-2-lam): Z/p^(A-1) + Z/p^(B+1); lam<p: Z/p^A.
import sys; sys.path.insert(0,'.')
from math import comb
from boolean_X import bool_M, smith_p
def vp(x,p):
    if x==0: return None
    v=0
    while x%p==0: x//=p; v+=1
    return v
def b(m,lam):
    if (m-lam)%2 or lam<0 or lam>m: return 0
    k=(m-lam)//2; return comb(m,k)-(comb(m,k-1) if k>0 else 0)
def A(m,lam,c,p,e):
    k=(m-lam)//2; return sum(e+vp(c+r,p) for r in range(k,m-k+1))
def pred(m,c,p,e):
    out={}
    def add(v,n):
        if n and v>0: out[v]=out.get(v,0)+n
    for lam in range(m%2,m+1,2):
        if lam>=p:
            n=b(m,lam); lp=2*p-2-lam
            add(A(m,lam,c,p,e)-1,n); add(A(m,lp,c,p,e)+1,n)
        else:
            n=b(m,lam)-(b(m,2*p-2-lam) if lam<=p-2 else 0); add(A(m,lam,c,p,e),n)
    return dict(sorted(out.items()))
if __name__=='__main__':
    p=int(sys.argv[1]); q=p; e=1; ok=bad=0
    for m in range(p,2*p-1):
        for c in range(1,int(sys.argv[2])+1):
            g,z=smith_p(bool_M(m,c,q),p); g=dict(g); P=pred(m,c,p,e)
            ok+=g==P; bad+=g!=P
            print('p',p,'m',m,'c',c,'meas',g,'pred',P,'OK' if g==P else 'BAD',flush=True)
    print('ok',ok,'bad',bad)
