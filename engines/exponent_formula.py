# Exponent of Syl_p K(K_q^d), q >= 3: E(e,d) = max_{1<=L<=b<=d} [e*L + v_p(L) + v_p(C(b,L))], e = v_p(q)
from math import comb
def vp(x,p):
    if x==0: return 10**9
    v=0
    while x%p==0: x//=p; v+=1
    return v
def E(p,e,d):
    return max(e*L+vp(L,p)+vp(comb(b,L),p) for b in range(1,d+1) for L in range(1,b+1))
def S(p,d): return max(s+vp(s,p) for s in range(1,d+1))
if __name__=='__main__':
    bad=0
    for p in (3,5,7,11,13):
        for d in range(1,200):
            if E(p,1,d)!=S(p,d): bad+=1; print('diff',p,d,E(p,1,d),S(p,d))
    print('E(1,d)==max(s+v(s)) for p<=13, d<200: bad',bad)
