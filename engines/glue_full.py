# Full Syl_p K(K_q^d) predicted by the Glue Rule, for d <= 2p-2 (q with v_p(q)=e).
#   blocks j: m = d-j, c = j, multiplicity C(d,j)(q-2)^j; inside a block, Weyl strings of B_m:
#   lam <= p-2: Z/p^{A(lam)} with mult b(m,lam)-b(m,2p-2-lam); lam = p-1: Z/p^{A}, mult b(m,p-1);
#   p <= lam <= 2p-2: Z/p^{A(lam)-1} + Z/p^{A(2p-2-lam)+1}, mult b(m,lam).
#   A(lam) = sum over the ranks r of the string (r = (m-lam)/2 .. (m+lam)/2) of e + v_p(c+r);
#   a string through a zero diagonal entry (c = 0, lam = m) gives Z, and its partner A(lam')+1 stays.
import sys, math, re
sys.path.insert(0,'.')
from tilt2 import b, vp
def A(m,lam,c,p,e):
    k=(m-lam)//2; vals=[c+r for r in range(k,m-k+1)]
    if 0 in vals: return None
    return sum(e+vp(x,p) for x in vals)
def block(m,c,p,e,out,mult):
    def add(v,n):
        if n and v is not None and v>0: out[v]=out.get(v,0)+n*mult
    for lam in range(m%2,m+1,2):
        if lam>=p:
            n=b(m,lam); a=A(m,lam,c,p,e)
            add(a-1 if a is not None else None,n); add(A(m,2*p-2-lam,c,p,e)+1,n)
        else:
            n=b(m,lam)-(b(m,2*p-2-lam) if lam<=p-2 else 0); add(A(m,lam,c,p,e),n)
def full(q,p,d):
    e=vp(q,p); out={}
    for j in range(d+1):
        t=math.comb(d,j)*(q-2)**j
        if t: block(d-j,j,p,e,out,t)
    return dict(sorted(out.items()))
if __name__=='__main__':
    ok=bad=0
    for f in sys.argv[1:]:
        L=open(f).read(); mm=re.search(r'q=(\d+) p=(\d+) d=(\d+) Syl_p: (\{[^}]*\})',L)
        q,p,d=map(int,mm.groups()[:3]); meas=eval(mm.group(4))
        if d>2*p-2: continue
        P=full(q,p,d); ok+=P==meas; bad+=P!=meas
        print(f,'q',q,'p',p,'d',d,'OK' if P==meas else 'BAD meas %s pred %s'%(meas,P))
    print('ok',ok,'bad',bad)
