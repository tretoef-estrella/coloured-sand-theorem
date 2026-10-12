# Re-check sealed prediction 2 without the precision artifact.
#  m <= 9: exact Smith form mod 7^30 with Python integers (object arrays).
#  m = 10, 11: int64 engine gives exact counts for valuations <= 9 and the number of factors with valuation >= 10;
#             the sum of those valuations follows from v_7(det) = sum_r C(m,r) v_7(7(c+r)).
import sys, ast, numpy as np; sys.path.insert(0,'.')
from math import comb
from boolean_X import bool_M, smith_p
def vp(x,p):
    v=0
    while x%p==0: x//=p; v+=1
    return v
def smith_big(W0,p,M):
    mod=p**M; W=np.array(W0,dtype=object)%mod; v=0; hist={}
    while W.size:
        mask=np.vectorize(lambda x: x%p!=0)(W)
        if not mask.any():
            W=W//p; mod//=p; v+=1; continue
        i,j=np.unravel_index(np.argmax(mask),mask.shape)
        ui=pow(int(W[i,j]),-1,mod); row=(W[i,:]*ui)%mod; col=W[:,j].copy()
        W=(W-np.outer(col,row))%mod; W=np.delete(np.delete(W,i,0),j,1); hist[v]=hist.get(v,0)+1
    return {k:c for k,c in sorted(hist.items()) if k>0}
p=7; ok=bad=0
for line in open('../sealed/PREDICCION_SELLADA_2.txt'):
    if not line.startswith('p 7'): continue
    t=line.split(); m=int(t[3]); c=int(t[5]); P=ast.literal_eval(line.split('pred ')[1])
    if m<=int(sys.argv[1]):
        g=smith_big(bool_M(m,c,7),7,30); res=(g==P); info='exact'
    else:
        g,z=smith_p(bool_M(m,c,7),7); g=dict(g)
        low={k:v for k,v in g.items() if k<=10}; Plow={k:v for k,v in P.items() if k<=10}
        vdet=sum(comb(m,r)*(1+vp(c+r,p)) for r in range(m+1))
        hi_n=z; hi_sum=vdet-sum(k*v for k,v in low.items())
        Phi_n=sum(v for k,v in P.items() if k>=11); Phi_sum=sum(k*v for k,v in P.items() if k>=11)
        res=(low==Plow and hi_n==Phi_n and hi_sum==Phi_sum); info='low+count+sum: hi_n %d/%d hi_sum %d/%d'%(hi_n,Phi_n,hi_sum,Phi_sum)
    ok+=res; bad+=(not res)
    print('m',m,'c',c,'OK' if res else 'BAD',info,flush=True)
print('ok',ok,'bad',bad)
