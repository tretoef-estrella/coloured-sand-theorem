# G2 extension: forced-lattice stability for p=7, every lambda in [7,48] with (lambda+1)%7 != 0. Grepy Connor, 13 Oct 2026.
import sys, time; sys.path.insert(0,'.')
import tilt3p
from tilt3p import stable
def bottom_gen(p,lam):
    r=(lam+1)%p
    if lam<p or r==0: return None
    return lam-2*r
tilt3p.bottom=bottom_gen
t0=time.time(); n=b=0
for lam in range(7,49):
    if (lam+1)%7==0: continue
    s=stable(7,lam); n+=1
    if s: b+=1; print('UNSTABLE',lam,s,flush=True)
    print('lam',lam,'ok' if not s else 'BAD','t',round(time.time()-t0,1),flush=True)
print('G2 p7 lattices',n,'unstable',b)
print('FIN-OK')
