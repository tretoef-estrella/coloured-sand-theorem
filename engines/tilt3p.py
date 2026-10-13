# Range m <= 3p-2. Tilting lattices over Z_p modelled explicitly:
#  lam <= p-1 or lam = 2p-1 : Delta_Z(lam) (single chain, f l_i = (i+1) l_{i+1})
#  p <= lam <= 2p-2         : top lam, bottom mu = 2p-2-lam
#  2p <= lam <= 3p-2        : top lam, bottom mu = 4p-2-lam
#  glue: t_j = s_j + C(j+dl,j)/p * l_{j+dl}, dl = (lam-mu)/2   (guess for the second range; proved for the first)
import sys; sys.path.insert(0,'.')
from fractions import Fraction as F
from math import comb
from boolean_X import bool_M, smith_p
def vp(x,p):
    x=F(x)
    if x==0: return 10**9
    v=0; n,dn=x.numerator,x.denominator
    while n%p==0: n//=p; v+=1
    while dn%p==0: dn//=p; v-=1
    return v
def bottom(p,lam):
    if p<=lam<=2*p-2: return 2*p-2-lam
    if 2*p<=lam<=3*p-2: return 4*p-2-lam
    return None
def model(p,lam):
    mu=bottom(p,lam); lp=-1 if mu is None else mu
    N=lam+1+lp+1; basis=[]
    for i in range(lam+1):
        v=[F(0)]*N; v[i]=F(1); basis.append(v)
    dl=0 if mu is None else (lam-mu)//2
    for j in range(lp+1):
        v=[F(0)]*N; v[lam+1+j]=F(1); v[j+dl]+=F(comb(j+dl,j),p); basis.append(v)
    return mu,lp,dl,N,basis
def act(v,r,lam,lp,up):
    w=[F(0)]*len(v)
    for i in range(lam+1):
        if v[i]:
            t=i-r if up else i+r
            if 0<=t<=lam: w[t]+=v[i]*(comb(lam-i+r,r) if up else comb(i+r,r))
    for j in range(lp+1):
        x=v[lam+1+j]
        if x:
            t=j-r if up else j+r
            if 0<=t<=lp: w[lam+1+t]+=x*(comb(lp-j+r,r) if up else comb(j+r,r))
    return w
def coords(v,basis,lam,lp):
    a=[F(0)]*len(basis); v=v[:]
    for j in range(lp+1):
        c=v[lam+1+j]; a[lam+1+j]=c
        for k in range(len(v)): v[k]-=c*basis[lam+1+j][k]
    for i in range(lam+1): a[i]=v[i]
    return a
def smith_vals(Mx,p):
    A=[r[:] for r in Mx]; n=len(A); vals=[]; rows=list(range(n)); cols=list(range(n))
    for _ in range(n):
        best=None
        for i in rows:
            for j in cols:
                if A[i][j]!=0:
                    v=vp(A[i][j],p)
                    if best is None or v<best[0]: best=(v,i,j)
        if best is None: vals.append(None); rows.pop(); cols.pop(); continue
        v,i,j=best; vals.append(v); piv=A[i][j]
        for i2 in rows:
            if i2!=i and A[i2][j]!=0:
                f=A[i2][j]/piv
                for j2 in cols: A[i2][j2]-=f*A[i][j2]
        for j2 in cols:
            if j2!=j and A[i][j2]!=0:
                f=A[i][j2]/piv
                for i2 in rows: A[i2][j2]-=f*A[i2][j]
        rows.remove(i); cols.remove(j)
    return vals
def stable(p,lam):
    mu,lp,dl,N,basis=model(p,lam); bad=0
    for b in basis:
        for r in range(1,lam+1):
            for up in (0,1):
                if any(vp(x,p)<0 for x in coords(act(b,r,lam,lp,up),basis,lam,lp)): bad+=1
    return bad
def block(p,lam,q,c,k):
    mu,lp,dl,N,basis=model(p,lam)
    def lev(idx): return k+idx if idx<=lam else k+dl+(idx-lam-1)
    cols=[]
    for idx,b in enumerate(basis):
        w=act(b,1,lam,lp,0); w=[x+F(q*(c+lev(idx)))*bb for x,bb in zip(w,b)]
        cols.append(coords(w,basis,lam,lp))
    Mx=[[cols[j][i] for j in range(len(basis))] for i in range(len(basis))]
    return smith_vals(Mx,p)
def beta(m,lam):
    if (m-lam)%2 or lam<0 or lam>m: return 0
    k=(m-lam)//2; return comb(m,k)-(comb(m,k-1) if k>0 else 0)
def mult(m,p):
    n={}
    for lam in range(m,-1,-1):
        if (m-lam)%2: continue
        n[lam]=beta(m,lam)-sum(n[mu] for mu in n if bottom(p,mu)==lam)
    return n
def predict(m,c,q,p):
    out={}; free=0
    for lam,nl in mult(m,p).items():
        if nl==0: continue
        if nl<0: return None
        for v in block(p,lam,q,c,(m-lam)//2):
            if v is None: free+=nl
            elif v>0: out[v]=out.get(v,0)+nl
    return dict(sorted(out.items())),free
if __name__=='__main__':
    bad=0; n=0
    for p in (3,5,7):
        for lam in range(p,3*p-1):
            s=stable(p,lam); n+=1
            if s: bad+=1; print('UNSTABLE',p,lam,s)
    print('stability: lams',n,'bad',bad,flush=True)
    cases=[(3,m) for m in range(3,8)]+[(5,m) for m in range(5,11)]
    tot=0; badc=0
    for p,m in cases:
        Mprec=max(t for t in range(1,40) if p**t<2**31)
        for e in (1,2):
            for c in range(0,7):
                q=p**e*(2 if p!=2 else 1)
                if p**e*2 % p**(e+1)==0: q=p**e
                pr=predict(m,c,q,p)
                g,z=smith_p(bool_M(m,c,q),p)
                pd,free=pr
                low={v:k for v,k in pd.items() if v<Mprec}; high=sum(k for v,k in pd.items() if v>=Mprec)+free
                gl={v:k for v,k in g.items() if v<Mprec}
                tot+=1; ok=(low==gl and high==z)
                if not ok: badc+=1; print('BAD',p,m,e,c,'pred',pd,free,'got',g,z,flush=True)
    print('pieces',tot,'bad',badc)
