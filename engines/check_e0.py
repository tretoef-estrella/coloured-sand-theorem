import sys, math; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
from glue_full import full
ok=bad=0
for q,p,d in [(4,3,3),(4,3,4),(5,3,3),(5,3,4),(7,3,4),(8,3,4),(7,5,5),(7,5,6),(8,5,7),(6,5,8),(4,2,2),(6,2,2),(8,2,2),(3,2,2),(9,7,7),(8,7,8)]:
    H={}; Z=0
    for j in range(d+1):
        tt=math.comb(d,j)*(q-2)**j
        if tt==0: continue
        g,z=smith_p(bool_M(d-j,j,q),p); Z+=z*tt
        for k,c in g.items(): H[k]=H.get(k,0)+c*tt
    H={k:c for k,c in sorted(H.items()) if c}; P=full(q,p,d); good=(H==P and Z==1)
    ok+=good; bad+=not good
    print('q',q,'p',p,'d',d,'OK' if good else 'BAD meas %s pred %s zeros %d'%(H,P,Z),flush=True)
print('ok',ok,'bad',bad)
