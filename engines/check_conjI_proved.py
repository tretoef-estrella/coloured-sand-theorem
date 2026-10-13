# Grepy Connor 13 Oct 2026. Conjecture I on the cases already proved (formula only):
# (a) p=2, every family lam <= 200, alpha=1..5, i=0..8 (DST formula, dst_alpha.X_alpha);
# (b) p odd, lam <= p^2+p-1 (Theorem G block formula, frontier_model2.block_cf), p=3,5,7.
# Also: the number of Weyl factors of T(lam) (Donkin's tensor product theorem, characters) versus 2^|I|.
import sys; sys.path.insert(0,'.')
from collections import Counter
from dst_alpha import X_alpha
import frontier_model2 as FM
def digits(n,p):
    d=[]
    while n: d.append(n%p); n//=p
    return d
def kI(lam,p):
    d=digits(lam+1,p); k=len(d)-1
    return k,sum(1 for t in range(k) if d[t])
def check(groups,free,p,k,nI):
    big=sum(n for x,n in groups.items() if x>k)+free
    small=Counter({x:n for x,n in groups.items() if x<=k})
    return big==2**nI, small
bad=0; cases=0
# (a)
for lam in range(0,201):
    k,nI=kI(lam,2); ref=None
    for al in range(1,6):
        for i in range(0,9):
            g,fr=X_alpha(lam,i,al); cases+=1
            ok,sm=check(g,fr,2,k,nI)
            if ref is None: ref=sm
            if not ok or sm!=ref: bad+=1; print('BAD p=2',lam,al,i,dict(g),fr)
print('(a) p=2 cases',cases,'bad',bad,flush=True)
# (b)
b2=0;c2=0
for p in (3,5,7):
    for lam in range(0,p*p+p):
        k,nI=kI(lam,p); ref=None
        for e in (1,2,3):
            for kk in range(0,3):
                for c in range(0,6):
                    if c==0 and kk>0: continue
                    q=p**e
                    g,fr=FM.block_cf(p,lam,q,c,kk); c2+=1
                    ok,sm=check(Counter(g),fr,p,k,nI)
                    if ref is None: ref=sm
                    if not ok or sm!=ref: b2+=1; print('BAD',p,lam,e,kk,c,g,fr)
print('(b) p odd cases',c2,'bad',b2,flush=True)
# Weyl factors of T(lam) by Donkin, as characters (dict weight->mult), p=2,3,5, lam<=120
def chi(n):
    return Counter({n-2*j:1 for j in range(n+1)}) if n>=0 else Counter()
def frob(ch,p): return Counter({p*w:m for w,m in ch.items()})
def mul(a,b):
    out=Counter()
    for x,m in a.items():
        for y,n in b.items(): out[x+y]+=m*n
    return out
memo={}
def T(lam,p):
    if lam in memo: return memo[lam]
    if lam<=p-2: r=chi(lam)
    elif lam<=2*p-2:
        rr=lam-(p-1); r=chi(lam)+ (chi(p-1-rr) if rr>0 else Counter())
    else:
        rr=(lam-(p-1))%p; b=(lam-(p-1))//p
        r=mul(T(p-1+rr,p),frob(T(b,p),p))
    memo[lam]=r; return r
def weyl_count(ch):
    ch=Counter(ch); n=0
    while True:
        ws=[w for w,m in ch.items() if m!=0]
        if not ws: return n
        top=max(ws); m=ch[top]
        assert m>0
        n+=m
        for w,v in chi(top).items(): ch[w]-=m*v
b3=0;c3=0
for p in (2,3,5):
    memo.clear()
    for lam in range(0,121):
        k,nI=kI(lam,p); c3+=1
        if weyl_count(T(lam,p))!=2**nI: b3+=1; print('WEYL BAD',p,lam,weyl_count(T(lam,p)),2**nI)
print('(c) Weyl-factor count vs 2^|I|: cases',c3,'bad',b3)
print('FIN-OK')
