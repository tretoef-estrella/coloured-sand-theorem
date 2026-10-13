import sys; sys.path.insert(0,'.')
import tilt3p
from boolean_X import bool_M, smith_p
def bottom_gen(p,lam):
    r=(lam+1)%p
    if lam<p or r==0: return None
    return lam-2*r
tilt3p.bottom=bottom_gen
for m in (9,10):
    for c in range(0,4):
        Mprec=19
        pd,free=tilt3p.predict(m,c,3,3); g,z=smith_p(bool_M(m,c,3),3)
        low={v:k for v,k in pd.items() if v<Mprec}; high=sum(k for v,k in pd.items() if v>=Mprec)+free
        gl={v:k for v,k in g.items() if v<Mprec}
        print('p3 m',m,'c',c,'OK' if (low==gl and high==z) else 'DIFF','pred',pd,free,'got',g,z,flush=True)
# closed form of the block vs model, lam = p-1+r+p*a, a<=1 (and a<=p-2 for p=5 where lam+1<p^2)
import random
from tilt3p import block
def vp(x,p):
    v=0
    while x%p==0: x//=p; v+=1
    return v
bad=0; n=0
for p in (3,5):
    for lam in range(1,p*p-1):
        r=(lam+1)%p; a=(lam+1)//p-1 if lam>=p else 0
        for t in range(6):
            e=random.choice([1,2]); q=p**e*random.choice([x for x in (1,2,4,7) if x%p]); c=random.randint(1,8); k=random.randint(0,3)
            got=sorted(v for v in block(p,lam,q,c,k) if v and v>0)
            Avals=[e+vp(c+k+i,p) for i in range(lam+1)]; A=sum(Avals)
            if lam<p: want=[A]
            elif r==0: want=sorted([1]*a+[A-a])
            else:
                mu=lam-2*r; dl=r; Ap=sum(e+vp(c+k+dl+j,p) for j in range(mu+1))
                want=sorted([1]*(2*a)+[Ap+1-a,A-1-a])
            n+=1
            if got!=want: bad+=1; print('CF BAD',p,lam,a,r,e,c,k,got,want,flush=True)
print('closed form block checks',n,'bad',bad)
