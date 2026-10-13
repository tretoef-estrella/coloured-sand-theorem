# number of cyclic summands of Y_p(lam,i,e) = dim T(lam)/p for lam >= p-1, on the proved formulas
import sys; sys.path.insert(0,'.')
from collections import Counter
from dst_alpha import X_alpha
import frontier_model2 as FM
from check_conjI_proved import T, memo
bad=0;n=0
for p in (2,3,5,7):
    memo.clear()
    for lam in range(p-1, (201 if p==2 else p*p+p)):
        dim=sum(T(lam,p).values())
        if p==2:
            g,fr=X_alpha(lam,3,2); cnt=sum(g.values())+fr
            g0,fr0=X_alpha(lam,0,1); cnt0=sum(g0.values())+fr0
            ok = cnt==dim//2 and cnt0==dim//2 and dim%2==0
        else:
            g,fr=FM.block_cf(p,lam,p,1,0); g0,fr0=FM.block_cf(p,lam,p,0,0)
            ok = len(g)+fr==dim//p and len(g0)+fr0==dim//p and dim%p==0
        n+=1; bad+= not ok
        if not ok: print('BAD',p,lam,dim)
print('cases',n,'bad',bad); print('FIN-OK')
