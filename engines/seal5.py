import sys; sys.path.insert(0,'.')
import frontier_model2 as fm
from math import comb
from collections import Counter
import random
# 1. closed form vs model on blocks: every two-factor lam <= p^2+p-1, p=2,3,5,7
random.seed(5); nb=bad=0
for p in (2,3,5,7):
    for lam in range(1,p*p+p):
        for t in range(3 if p<7 else 1):
            e=random.choice([1,2]); q=p**e*random.choice([x for x in (1,3,5,7) if x%p]); c=random.randint(0,6); k=random.randint(0,2)
            if t==0: c=k=0
            cf=fm.block_cf(p,lam,q,c,k); vals=fm.tilt3p.block(p,lam,q,c,k)
            md=(sorted(x for x in vals if x is not None and x>0), sum(1 for x in vals if x is None)); nb+=1
            if cf!=md: bad+=1; print('CF!=MODEL',p,lam,q,c,k,cf,md,flush=True)
print('closed form vs model blocks',nb,'bad',bad,flush=True)
assert bad==0
lines=[]
cases=[(3,11,q,c) for q in (12,15) for c in (4,5,6)]+[(2,5,q,c) for q in (6,10,8) for c in (4,5,6,7)]
for p,m,q,c in cases:
    pd=fm.predict_piece(m,q,c,p); lines.append(f'piece p={p} m={m} q={q} c={c}: {pd[0]} free={pd[1]}')
def full(d,q,p):
    tot=Counter(); free=0
    for j in range(d+1):
        mu=comb(d,j)*(q-2)**j
        if mu==0: continue
        pd,fr=fm.predict_piece(d-j,q,j,p)
        for x,n in pd.items(): tot[x]+=n*mu
        free+=fr*mu
    return dict(sorted(tot.items())),free
for d,q,p in ((11,3,3),(5,4,2),(5,6,2)):
    g,fr=full(d,q,p); lines.append(f'FULL Syl_{p} K(H({d},{q})): {g} free_from_pieces={fr}')
open('PREDICCION_SELLADA_5.txt','w').write('\n'.join(lines)+'\n'); print('\n'.join(lines))
