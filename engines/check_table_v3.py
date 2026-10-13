# Grepy Connor 13 Oct 2026: the data table of the paper (p=q=3, d=5..9) against Theorem A + Theorem G (formula only).
import sys; sys.path.insert(0,'.')
from collections import Counter
from math import comb
from frontier_model2 import predict_piece
TABLE={5:(12,10,16,53,5),6:(38,37,36,117,24,16,6),7:(86,105,127,285,85,63,41),
       8:(250,211,286,1078,174,133,174,8),9:(942,412,624,3339,449,292,495,133,84,37,9)}
def full(d,q,p):
    tot=Counter(); free=0
    for j in range(d+1):
        mult=comb(d,j)*(q-2)**j
        if mult==0: continue
        pd,fr=predict_piece(d-j,q,j,p)
        for x,n in pd.items(): tot[x]+=n*mult
        free+=fr*mult
    return tot,free
bad=0
for d,row in TABLE.items():
    g,fr=full(d,3,3)
    v=tuple(g.get(i,0) for i in range(1,max(g)+1))
    ok = v==row and fr==1
    bad+= not ok
    print('d',d,'OK' if ok else 'BAD',v,'free',fr)
print('TOTAL bad',bad); print('FIN-OK')
