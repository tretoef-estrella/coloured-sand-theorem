# High elementary divisors of M = 7(c+H)+U on B_m via N = 7^E M^{-1}:
#   (M^{-1})_{T,S} = (-1)^k k! / prod_{i=0}^{k} 7(c+s+i)  for S subset T, |S|=s, |T|=s+k  (0 otherwise).
#   E = exponent of coker M (exact, Theorem C).  Factor 7^a of M  <->  factor 7^(E-a) of N.
import sys, ast, numpy as np; sys.path.insert(0,'.')
from math import factorial
from boolean_X import smith_p
p=7
def vp(x):
    v=0
    while x%p==0: x//=p; v+=1
    return v
def Nmat(m,c):
    best=0
    for s in range(m+1):
        for k in range(m-s+1):
            val=sum(1+vp(c+s+i) for i in range(k+1))-vp(factorial(k)); best=max(best,val)
    E=best; Mod=p**11; n=1<<m; N=np.zeros((n,n),dtype=np.int64)
    coef={}
    for s in range(m+1):
        for k in range(m-s+1):
            num=factorial(k); den=1
            for i in range(k+1): den*=p*(c+s+i)
            w=vp(den)-vp(num); assert E-w>=0
            nu=num//p**vp(num); du=den//p**vp(den)
            coef[(s,k)]=((-1)**k*nu*pow(du,-1,Mod)*p**(E-w))%Mod
    pc=[bin(S).count('1') for S in range(n)]
    for S in range(n):
        for T in range(n):
            if S&T==S: N[T,S]=coef[(pc[S],pc[T]-pc[S])]
    return N,E
for line in open('../sealed/PREDICCION_SELLADA_2.txt'):
    if not line.startswith('p 7'): continue
    t=line.split(); m=int(t[3]); c=int(t[5])
    if m<10: continue
    P=ast.literal_eval(line.split('pred ')[1]); N,E=Nmat(m,c); g,z=smith_p(N,p); g=dict(g); g[0]=(1<<m)-sum(g.values())-z
    hiM={E-v:cnt for v,cnt in g.items() if E-v>=11}
    Phi={k:v for k,v in P.items() if k>=11}
    print('m',m,'c',c,'E',E,'M high factors via inverse',dict(sorted(hiM.items())),'pred high',Phi,'OK' if hiM==Phi else 'BAD',flush=True)
