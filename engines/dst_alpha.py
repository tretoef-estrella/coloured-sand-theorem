# X^(alpha)(lam,i) by the closed rule of [DST] (Theorem D + Theorem 7.10 + Prop 5.4), any alpha>=1. Grepy Connor, 13 Oct 2026.
from collections import Counter
def s2(x): return bin(x).count('1')
def kap(a,b): return s2(a)+s2(b)-s2(a+b)
def fam(lam):
    n=lam+1; k=n.bit_length()-1; I=[t for t in range(k) if (n>>t)&1]; return k,I
def int_fit(xs):
    # pool-adjacent-violators for a non-increasing fit; blocks with equal means merged; then integer rounding
    blocks=[]  # [sum,count]
    for x in xs:
        blocks.append([x,1])
        while len(blocks)>=2 and blocks[-2][0]*blocks[-1][1] <= blocks[-1][0]*blocks[-2][1]:
            s,c=blocks.pop(); blocks[-1][0]+=s; blocks[-1][1]+=c
    out=[]
    for S,p in blocks:
        q,r=divmod(S,p); out+= [q+1]*r+[q]*(p-r)
    return out
def X_alpha(lam,i,alpha):
    """returns (Counter of exponents, number of free Z_2)"""
    k,I=fam(lam); K=1<<k
    nxt={}
    for idx,t in enumerate(I): nxt[t]=I[idx+1] if idx+1<len(I) else k
    h={t:nxt[t]-t for t in I}
    out=Counter()
    for a in range(1,k): out[a]+=2**(len(I)+k-1-a)
    dancers=[]
    for mask in range(1<<len(I)):
        D=[I[j] for j in range(len(I)) if (mask>>j)&1]; dancers.append(D)
    o=lambda E: sum(1<<t for t in E)
    dancers.sort(key=o)
    comp=lambda D:[t for t in I if t not in D]
    if i>=1:
        m=i-1
        R=lambda mu,E: sum(h[t]-alpha*(1<<t) for t in E)-kap(mu,o(E))
        xs=[R(m,D)-R(m+K,comp(D)) for D in dancers]
        for y in int_fit(xs): out[k+alpha*K+kap(m,K)+y]+=1
        return out,0
    Rs=lambda E: sum(h[t]-alpha*(1<<t) for t in E)-kap(K-1,o(E))
    xs=[Rs(D)-Rs(comp(D)) for D in dancers[1:]]
    for y in int_fit(xs): out[k+alpha*K+y]+=1
    return out,1
def mult_dst(n):
    # m_lambda(n) by the recursion V.[0]=[1], V.[2l+1]=[2l+2], V.[2l+2]=2[2l+1]+Phi(V.[l]), Phi([nu])=[2nu+1]
    from functools import lru_cache
    @lru_cache(None)
    def Vdot(lam):
        if lam==0: return ((1,1),)
        if lam%2==1: return ((lam+1,1),)
        l=(lam-2)//2; res=Counter({lam-1:2})
        for nu,c in Vdot(l): res[2*nu+1]+=c
        return tuple(sorted(res.items()))
    cur=Counter({0:1})
    for _ in range(n):
        nxt=Counter()
        for lam,c in cur.items():
            for nu,d in Vdot(lam): nxt[nu]+=c*d
        cur=nxt
    return dict(cur)
def piece_p2(m,q,c):
    e=0; x=q
    while x%2==0: x//=2; e+=1
    tot=Counter(); free=0
    for lam,n in mult_dst(m).items():
        g,fr=X_alpha(lam,c+(m-lam)//2,e)
        for v,cnt in g.items(): tot[v]+=cnt*n
        free+=fr*n
    return dict(sorted(tot.items())),free
