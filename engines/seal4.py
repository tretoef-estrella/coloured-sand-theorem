import sys; sys.path.insert(0,'.')
from frontier_model import predict_piece
from math import comb
from collections import Counter
lines=[]
cases=[(3,m,q,c) for m in (9,10) for q in (12,15,21) for c in (5,6,7,8)]+[(2,4,q,c) for q in (6,10,8) for c in (5,6,7,8)]
for p,m,q,c in cases:
    pd=predict_piece(m,q,c,p); pm=predict_piece(m,q,c,p,use_model=True)
    assert pd==pm, ('closed form != model',p,m,q,c,pd,pm)
    lines.append(f'piece p={p} m={m} q={q} c={c}: {pd[0]} free={pd[1]}')
# full groups via Theorem A
def full(d,q,p):
    tot=Counter(); free=0
    for j in range(d+1):
        mult=comb(d,j)*(q-2)**j
        if mult==0: continue
        pd,fr=predict_piece(d-j,q,j,p)
        for x,n in pd.items(): tot[x]+=n*mult
        free+=fr*mult
    return dict(sorted(tot.items())),free
for d,q,p in ((10,3,3),(9,6,3),(4,6,2),(4,10,2)):
    g,fr=full(d,q,p)
    lines.append(f'FULL Syl_{p} K(H({d},{q})): {g} free_from_pieces={fr} (Z^1 free summand of coker L expected)')
open('PREDICCION_SELLADA_4.txt','w').write('\n'.join(lines)+'\n')
print('\n'.join(lines))
