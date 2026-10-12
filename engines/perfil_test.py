import sys, time; sys.path.insert(0,'.')
from boolean_X import bool_M, smith_p
def vp(x,p):
    v=0
    while x%p==0: x//=p; v+=1
    return v
p=int(sys.argv[1]); mmax=int(sys.argv[2]); cmax=int(sys.argv[3])
bad=0; tot=0
for m in range(0,mmax+1):
    seen={}
    for c in range(1,cmax+1):
        prof=tuple(vp(c+s,p) for s in range(m+1))
        h,z=smith_p(bool_M(m,c,p),p); key=tuple(sorted(h.items()))
        tot+=1
        if prof in seen and seen[prof][0]!=key:
            bad+=1; print('VIOLATION m=%d c=%d vs c=%d profile %s: %s vs %s'%(m,c,seen[prof][1],prof,key,seen[prof][0]))
        seen.setdefault(prof,(key,c))
    print('m=%d profiles=%d'%(m,len(seen)),flush=True)
print('tested',tot,'violations',bad)
