import sys; sys.path.insert(0,'.')
from tilt3p import predict
from boolean_X import bool_M, smith_p
# control 1: the naive Conjecture-F formula (tilt2.pred) beyond 2p-2
from tilt2 import pred as predF
bad=0; tot=0
for m in (5,6,7):
    for c in range(1,7):
        g,z=smith_p(bool_M(m,c,3),3); tot+=1
        if predF(m,c,3,1)!=g: bad+=1
print('control: Conjecture F formula beyond 2p-2 (p=3, m=5..7): differs in',bad,'of',tot,flush=True)
# boundary probe
for m in (8,9,10):
    for c in range(0,5):
        Mprec=19
        pd,free=predict(m,c,3,3); g,z=smith_p(bool_M(m,c,3),3)
        low={v:k for v,k in pd.items() if v<Mprec}; high=sum(k for v,k in pd.items() if v>=Mprec)+free
        gl={v:k for v,k in g.items() if v<Mprec}
        print('m',m,'c',c,'OK' if (low==gl and high==z) else 'DIFF', 'pred',pd,free,'got',g,z,flush=True)
