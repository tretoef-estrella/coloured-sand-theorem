import sys; sys.path.insert(0,'.')
import tilt3p
def bottom_gen(p,lam):
    r=(lam+1)%p
    if lam<p or r==0: return None
    return lam-2*r
tilt3p.bottom=bottom_gen
from tilt3p import block
def vp(x,p):
    v=0
    while x%p==0: x//=p; v+=1
    return v
bad=0;n=0
for p in (3,5):
  for lam in range(1,p*p-1):
    for e in (1,2):
      q=p**e*2
      vals=block(p,lam,q,0,0)
      free=sum(1 for v in vals if v is None); got=sorted(v for v in vals if v is not None and v>0)
      r=(lam+1)%p; a=(lam+1)//p-1 if lam>=p else 0
      if lam<p: want=[]
      elif r==0: want=[1]*a
      else:
        mu=lam-2*r; Ap=sum(e+vp(r+j,p) for j in range(mu+1)); want=sorted([1]*(2*a)+[Ap+1-a])
      n+=1
      if got!=want or free!=1: bad+=1; print('BAD',p,lam,e,got,free,want)
print('c=0 top block checks',n,'bad',bad)
