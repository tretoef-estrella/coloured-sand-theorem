# assemble_final.py — build proyecto_cubo/checks/CheckColouredSandFinal.lean from the 33 per-piece check files.
# Each piece's body goes, unchanged, inside `namespace FinalCheck.<piece> ... end`; imports are gathered at the top. Grepy Ship, 14 Oct 2026.
import re, os, hashlib
H='/Users/rafa/Desktop/ARBOLYAML/HYPERCUBE'
CS=H+'/CONJETURA_HAMMING_2026-10-13/lean/proyecto_cs/checks/'
CU=H+'/lean/proyecto_cubo/checks/'
pieces=[(CS,n) for n in ['CS1','CS2','CS3','CS4','CS5','CS6','CSG1','CSG2']]+[(CU,n) for n in ['CSH1','CSG3','CSG4','CSG5','CSG6','CSG7']+['CSI%d'%i for i in range(1,20)]+['CSX1','CSX2','CSX3']]
imports=[]; bodies=[]; man=[]
for d,n in pieces:
    p=d+'Check%s.lean'%n; t=open(p).read()
    man.append('%s  %s'%(hashlib.md5(t.encode()).hexdigest(),p.replace(H+'/','')))
    lines=t.split('\n'); body=[]
    for L in lines:
        if re.match(r'^\s*(public\s+)?import\s',L):
            m=L.replace('public ','').strip()
            if m not in imports: imports.append(m)
        else: body.append(L)
    bodies.append('\n-- ======== piece %s (from %s) ========\nnamespace FinalCheck.%s\n%s\nend FinalCheck.%s\n'%(n,p.replace(H+'/',''),n,'\n'.join(body),n))
hdr='''-- CheckColouredSandFinal2.lean — the final check of the Coloured Sand Lean project (v3 + Theorems I, TOTAL + the three cases CSX1-3).
-- Assembled by assemble_final.py (Grepy Ship, 14 Oct 2026; v2 15 Oct 2026) from the 36 certified per-piece check files, each body unchanged
-- inside its own namespace FinalCheck.<piece>. Every `#print axioms` line must read [propext, Classical.choice, Quot.sound].
'''
imp='\n'.join(sorted(imports))+'\n'
h=18
for tag,bs in (('A',bodies[:h]),('B',bodies[h:])):
    o=hdr.replace('CheckColouredSandFinal2.lean','CheckColouredSandFinal2%s.lean (half %s: every import, pieces %s)'%(tag,tag,'1-18' if tag=='A' else '19-36'))+imp+''.join(bs)
    open(CU+'CheckColouredSandFinal2%s.lean'%tag,'w').write(o)
    print(tag,len(bs),'pieces',o.count('#print axioms'),'print axioms')
out=hdr+imp+''.join(bodies)
open(H+'/CONJETURA_HAMMING_2026-10-13/lean/final/MANIFEST_checks_md5_v2.txt','w').write('\n'.join(man)+'\n')
print(len(pieces),'pieces',len(imports),'imports',out.count('#print axioms'),'print axioms',out.count('\n'),'lines')
