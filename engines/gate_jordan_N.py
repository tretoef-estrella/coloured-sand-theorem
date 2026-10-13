# Gate: dim_Fp coker(U on B_m) = number of Jordan blocks predicted by the walk
# J2 (x) Ja = J_{a+1}+J_{a-1} (a<p), J2 (x) Jp = 2 Jp, start J1.  p=3 closed form 1+(2^m-1-[m odd])/3.
import itertools
def rank_mod(rows, p, ncols):
    rows=[r[:] for r in rows]; r=0
    for c in range(ncols):
        piv=None
        for i in range(r,len(rows)):
            if rows[i][c]%p: piv=i;break
        if piv is None: continue
        rows[r],rows[piv]=rows[piv],rows[r]
        inv=pow(rows[r][c],p-2,p)
        rows[r]=[x*inv%p for x in rows[r]]
        for i in range(len(rows)):
            if i!=r and rows[i][c]%p:
                f=rows[i][c]; rows[i]=[(a-f*b)%p for a,b in zip(rows[i],rows[r])]
        r+=1
    return r
def coker_U(m,p):
    # rank of U on B_m = sum over s of rank of W_{s,s+1}
    tot=0
    for s in range(m):
        A=list(itertools.combinations(range(m),s)); B=list(itertools.combinations(range(m),s+1))
        idx={b:i for i,b in enumerate(B)}
        rows=[]
        for a in A:
            row=[0]*len(B)
            for x in range(m):
                if x not in a: row[idx[tuple(sorted(a+(x,)))]]=1
            rows.append(row)
        tot+=rank_mod(rows,p,len(B))
    return 2**m-tot
def walk(m,p):
    n=[0]*(p+1); n[1]=1
    for _ in range(m):
        new=[0]*(p+1)
        for a in range(1,p+1):
            if not n[a]: continue
            if a<p:
                new[a+1]+=n[a]
                if a>1: new[a-1]+=n[a]
            else: new[p]+=2*n[a]
        n=new
    return sum(n)
bad=0; tests=0
for p in (3,5,7):
    for m in range(0,13 if p==3 else 12):
        c=coker_U(m,p); w=walk(m,p); tests+=1
        ok=(c==w)
        if p==3: ok = ok and c==1+(2**m-1-(m%2))//3
        if not ok: bad+=1
        print(p,m,c,w,'OK' if ok else 'BAD')
# control: the char-0 count (C(m,m//2)) must differ for some m
from math import comb
ctrl=sum(1 for m in range(3,12) if coker_U(m,3)!=comb(m,m//2))
print('tests',tests,'bad',bad,'control_differs',ctrl)
