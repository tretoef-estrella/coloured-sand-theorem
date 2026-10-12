# p-rank (number of cyclic factors of Syl_p K(K_q^d), q = p) from Wilson's diagonal form
import sys
from math import comb
def rankU(m,p):
    r=0
    for s in range(0,m):
        t=min(s,m-1-s)
        r+=sum(comb(m,i)-(comb(m,i-1) if i>0 else 0) for i in range(t+1) if (s+1-i)%p!=0) if s<=m-1-s else \
           sum(comb(m,i)-(comb(m,i-1) if i>0 else 0) for i in range(t+1) if ((m-s)-i)%p!=0)
    return r
def N(p,d,q=None):
    q=q or p
    return sum(comb(d,j)*(q-2)**j*(2**(d-j)-rankU(d-j,p)) for j in range(d+1))-1
if __name__=='__main__':
    data={3:[1,4,12,34,96,274,792,2314,6816,20194,60072,179194],5:{5:1557,6:7246,7:34015,8:160794,9:764388,10:3650602,11:17502191},7:{7:416609,8:2763594,9:18426025,10:123375926}}
    ok=bad=0
    for d,v in enumerate(data[3],1):
        n=N(3,d); ok+=n==v; bad+=n!=v; print(3,d,n,v,n==v, 3**(d-1)+2**(d-1)-1)
    for p in (5,7):
        for d,v in data[p].items():
            n=N(p,d); ok+=n==v; bad+=n!=v; print(p,d,n,v,n==v)
    print('ok',ok,'bad',bad)
