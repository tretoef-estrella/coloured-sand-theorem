import sys; sys.path.insert(0,'.')
import tilt3p
from boolean_X import bool_M, smith_p
def bottom_gen(p,lam):
    r=(lam+1)%p; a=(lam+1)//p-1
    if lam<p or r==0: return None
    return lam-2*r
tilt3p.bottom=bottom_gen
# stability of the general model for p=5,7 up to lam=p^2+p-2
for p in (3,5,7):
    res=[]
    for lam in range(p,p*p+p-1):
        if bottom_gen(p,lam) is None: continue
        res.append((lam,tilt3p.stable(p,lam)))
    print('p',p,'unstable lams:',[l for l,s in res if s],'of',len(res),flush=True)
for m in (9,10):
    for c in range(0,4):
        Mprec=19
        pd,free=tilt3p.predict(m,c,3,3); g,z=smith_p(bool_M(m,c,3),3)
        low={v:k for v,k in pd.items() if v<Mprec}; high=sum(k for v,k in pd.items() if v>=Mprec)+free
        gl={v:k for v,k in g.items() if v<Mprec}
        print('p3 m',m,'c',c,'OK' if (low==gl and high==z) else 'DIFF','pred',pd,free,'got',g,z,flush=True)
