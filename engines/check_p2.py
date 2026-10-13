import sys; sys.path.insert(0,'.')
import tilt3p
from boolean_X import bool_M, smith_p
p=2
for m in range(1,7):
    for e in (1,2):
        for c in range(0,5):
            q=2**e*(3 if e==1 else 1)
            pd,free=tilt3p.predict(m,c,q,p); g,z=smith_p(bool_M(m,c,q),p)
            M=30
            low={v:k for v,k in pd.items() if v<M}; high=sum(k for v,k in pd.items() if v>=M)+free
            gl={v:k for v,k in g.items() if v<M}
            print('p2 m',m,'q',q,'c',c,'OK' if (low==gl and high==z) else 'DIFF',flush=True)
