import sys; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
p=int(sys.argv[1]); e=1; q=p
for m in range(p, int(sys.argv[2])+1):
    for c in range(0, int(sys.argv[3])+1):
        g,z=smith_p(bool_M(m,c,q),p)
        print('m',m,'c',c,dict(g),'zeros',z,flush=True)
