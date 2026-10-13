import sys; sys.path.insert(0,'.')
from dst_alpha import piece_p2, mult_dst
from boolean_X import bool_M, smith_p
from math import comb
ok=bad=0
# sanity: hypercube K(Q_n) is piece m=n, q=2, c=0 (alpha=1): compare to direct
for m in range(1,10):
    for q in (2,4,6,8,10,12,16,24):
        for c in range(0,5):
            pr=piece_p2(m,q,c); g,z=smith_p(bool_M(m,c,q),2); dg=(dict(sorted(g.items())),z)
            M=max(t for t in range(1,40) if 2**t<2**31)
            # high exponents >= M appear as zeros in smith_p
            prl={v:k for v,k in pr[0].items() if v<M}; hi=sum(k for v,k in pr[0].items() if v>=M)+pr[1]
            good=(prl==dg[0] and hi==dg[1]); ok+=good; bad+=(not good)
            if not good: print('BAD m',m,'q',q,'c',c,'pred',pr,'direct',dg,flush=True)
    print('m',m,'ok',ok,'bad',bad,flush=True)
print('TOTAL ok',ok,'bad',bad); print('FIN-OK')
