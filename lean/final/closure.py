# closure.py — the RequestProject modules imported (transitively) by the final check files. Grepy Ship, 15 Oct 2026.
import re, os, sys
P='/Users/rafa/Desktop/ARBOLYAML/HYPERCUBE/lean/proyecto_cubo/'
roots=['checks/CheckColouredSandFinal2A%d.lean'%k for k in range(1,6)]+['checks/CheckColouredSandFinal2B.lean','checks/DepsColouredSand2.lean']
imp=re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)',re.M)
def imports(path): return imp.findall(open(path).read())
seen=set(); other=set(); stack=[]
for r in roots:
    for m in imports(P+r): stack.append(m)
while stack:
    m=stack.pop()
    if not m.startswith('RequestProject'): other.add(m.split('.')[0]); continue
    if m in seen: continue
    f=P+m.replace('.','/')+'.lean'
    if not os.path.exists(f): print('MISSING',m); continue
    seen.add(m); stack+=imports(f)
print(len(seen),'RequestProject modules; external roots:',sorted(other))
open(os.path.dirname(__file__)+'/closure_modules.txt','w').write('\n'.join(sorted(seen))+'\n')
