# Assemble Syl_3 K(H(d,3)) from the tilting model (Theorem A + blocks) and compare with the paper's table.
import sys; sys.path.insert(0,'.')
from math import comb
import tilt3p
def bottom_gen(p,lam):
    r=(lam+1)%p
    if lam<p or r==0: return None
    return lam-2*r
if len(sys.argv)>1 and sys.argv[1]=='gen': tilt3p.bottom=bottom_gen
table={5:(12,10,16,53,5),6:(38,37,36,117,24,16,6),7:(86,105,127,285,85,63,41),8:(250,211,286,1078,174,133,174,8),9:(942,412,624,3339,449,292,495,133,84,37,9)}
q=p=3
for d,row in table.items():
    H={}
    for j in range(d+1):
        t=comb(d,j)*(q-2)**j
        pd,free=tilt3p.predict(d-j,j,q,p)
        for v,k in pd.items(): H[v]=H.get(v,0)+k*t
    got=tuple(H.get(v,0) for v in range(1,max(H)+1))
    print('d',d,'model',got,'paper',row,'OK' if got==row else 'DIFF',flush=True)
