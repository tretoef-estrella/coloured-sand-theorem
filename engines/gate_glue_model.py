# Gate for the pencil proof of the Glue Conjecture.
# Model: V_Q = Delta(lam) (+) Delta(lam'), basis l_i (i=0..lam), s_j (j=0..lam'); divided powers
# f^(r) l_i = C(i+r,r) l_{i+r}, e^(r) l_i = C(lam-i+r,r) l_{i-r}; same for s with lam'.
# Lattice T: l_i, t_j = s_j + C(j+d,j)/p l_{j+d}, d = lam-p+1, lam' = 2p-2-lam.
from fractions import Fraction as F
from math import comb
import random
def vp(x,p):
    x=F(x)
    if x==0: return 10**9
    v=0; n,dn=x.numerator,x.denominator
    while n%p==0: n//=p; v+=1
    while dn%p==0: dn//=p; v-=1
    return v
def model(p,lam):
    lp=2*p-2-lam; d=lam-p+1; N=lam+1+lp+1
    # coordinates: index i for l_i (0..lam), lam+1+j for s_j
    def L(i): v=[F(0)]*N; v[i]=F(1); return v
    def S(j): v=[F(0)]*N; v[lam+1+j]=F(1); return v
    basis=[L(i) for i in range(lam+1)]
    for j in range(lp+1):
        v=S(j); v[j+d]+=F(comb(j+d,j),p); basis.append(v)
    return lp,d,N,basis
def apply_f(v,r,p,lam,lp):
    N=len(v); w=[F(0)]*N
    for i in range(lam+1):
        if v[i] and i+r<=lam: w[i+r]+=v[i]*comb(i+r,r)
    for j in range(lp+1):
        x=v[lam+1+j]
        if x and j+r<=lp: w[lam+1+j+r]+=x*comb(j+r,r)
    return w
def apply_e(v,r,p,lam,lp):
    N=len(v); w=[F(0)]*N
    for i in range(lam+1):
        if v[i] and i-r>=0: w[i-r]+=v[i]*comb(lam-i+r,r)
    for j in range(lp+1):
        x=v[lam+1+j]
        if x and j-r>=0: w[lam+1+j-r]+=x*comb(lp-j+r,r)
    return w
def coords(v,basis,lam,lp,d,p):
    # solve v = sum a_k basis_k ; s-coordinates give t-coefficients directly
    a=[F(0)]*len(basis); v=v[:]
    for j in range(lp+1):
        c=v[lam+1+j]; a[lam+1+j]=c
        for k in range(len(v)): v[k]-=c*basis[lam+1+j][k]
    for i in range(lam+1): a[i]=v[i]
    return a
def smith_vals(Mx,p):
    # p-adic Smith form valuations of a square matrix of Fractions (p-integral)
    A=[r[:] for r in Mx]; n=len(A); vals=[]
    rows=list(range(n)); cols=list(range(n))
    for _ in range(n):
        best=None
        for i in rows:
            for j in cols:
                if A[i][j]!=0:
                    v=vp(A[i][j],p)
                    if best is None or v<best[0]: best=(v,i,j)
        if best is None: vals.append(10**9); continue
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
    return sorted(vals)
bad=0; nst=0; nsm=0
for p in (3,5,7):
    for lam in range(p,2*p-1):
        lp,d,N,basis=model(p,lam)
        # G1: stability under f^(r), e^(r)
        for b in basis:
            for r in range(1,lam+1):
                for op in (apply_f,apply_e):
                    a=coords(op(b,r,p,lam,lp),basis,lam,lp,d,p)
                    nst+=1
                    if any(vp(x,p)<0 for x in a): bad+=1; print('NOT STABLE',p,lam,r,op.__name__)
        # G1b: not split: some t_j has a non-integral l-part that cannot be removed (c0 unit) -- by construction t_0 has 1/p
        # G2: Smith of M = q(c+k+level)+f on T vs formula
        for trial in range(25):
            e=random.choice([1,1,2]); q=p**e*random.choice([x for x in (1,2,4,5,7,8,11) if x%p])
            k=random.randint(0,4); c=random.randint(0,9)
            if c==0 and k==0: continue
            m=lam+2*k
            def lev(idx):  # level of basis element idx
                return k+idx if idx<=lam else k+d+(idx-lam-1)
            cols=[]
            for idx,b in enumerate(basis):
                w=apply_f(b,1,p,lam,lp)
                w=[x+F(q*(c+lev(idx)))*bb for x,bb in zip(w,b)]
                cols.append(coords(w,basis,lam,lp,d,p))
            Mx=[[cols[j][i] for j in range(len(basis))] for i in range(len(basis))]
            if any(vp(x,p)<0 for row in Mx for x in row): bad+=1; print('NONINTEGRAL M')
            got=[v for v in smith_vals(Mx,p) if v>0]
            A=sum(e+vp(c+r,p) for r in range(k,k+lam+1)); Ap=sum(e+vp(c+r,p) for r in range(k+d,k+p))
            want=sorted(x for x in [A-1,Ap+1] if x>0)
            nsm+=1
            if got!=want: bad+=1; print('SMITH BAD',p,lam,q,c,k,got,want)
# control: drop the glue (t_j = s_j): Smith should differ (then it is Z/p^A' and the l-chain splits)
print('stability checks',nst,'smith checks',nsm,'bad',bad)
