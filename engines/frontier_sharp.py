# Is m = p^2+p-1 the first failure of the frontier formula? p=2: m=5,6; p=3: m=11. Grepy Connor, 13 Oct 2026.
import sys; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
import frontier_model as fm
def pred(m,q,c,p):
    # extend: treat lam with r==0 as a simple chain (the v3 rule), whatever lam is
    return fm.predict_piece(m,q,c,p)
for p,m,qs,cs in ((2,5,(2,4,6),(0,1,2,3)),(2,6,(4,6),(1,2,3)),(3,11,(3,6),(0,1,2,3))):
    for q in qs:
        for c in cs:
            if q==2 and c>0: pass
            pr=pred(m,q,c,p); g,z=smith_p(bool_M(m,c,q),p); dg=(dict(sorted(g.items())),z)
            print('p',p,'m',m,'q',q,'c',c,'SAME' if pr==dg else 'DIFF','pred',pr,'direct',dg,flush=True)
print('FIN-OK')
