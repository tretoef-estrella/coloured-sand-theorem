import sys, ast, math; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
ok=bad=0
for line in open('../sealed/PREDICCION_SELLADA_3.txt'):
    if not line.startswith('q '): continue
    t=line.split(); q,p,d=int(t[1]),int(t[3]),int(t[5]); P=ast.literal_eval(line.split('pred ')[1])
    H={}; Z=0
    for j in range(d+1):
        tt=math.comb(d,j)*(q-2)**j
        if tt==0: continue
        g,z=smith_p(bool_M(d-j,j,q),p); Z+=z*tt
        for k,c in g.items(): H[k]=H.get(k,0)+c*tt
    H={k:c for k,c in sorted(H.items()) if c}
    good=(H==P and Z==1); ok+=good; bad+=not good
    print('q',q,'p',p,'d',d,'zeros',Z,'OK' if good else 'BAD meas %s pred %s'%(H,P),flush=True)
print('ok',ok,'bad',bad)
