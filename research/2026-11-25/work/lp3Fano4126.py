import sys,subprocess,re,itertools,math,json
from collections import Counter
from pathlib import Path
d=Path('.pnp'); ns={};exec((d/'rect4126.py').read_text().split('results={}')[0],ns)
chart,rows,group,score=[ns[k] for k in ('chart','rows','group','score')]
which=int(sys.argv[1]);import ast
expr=ast.literal_eval([k for k,v in json.loads((d/'threeRead4126.json').read_text())['3'].items() if v[1] is None][which])
seed=ns['repval'](expr,tuple(range(14)))
stab=[g for g in group if ns['repval'](expr,g)==seed]
def moved(row,g):return sum(1<<g[i] for i in range(14) if row>>i&1)
permrows=[[rows.index(moved(r,g)) for r in rows] for g in stab]
idx={};orbits=[]
for i,j in itertools.product(range(21),range(37)):
 if (i,j) in idx:continue
 orbit={(perm[i],perm[21+j]-21) for perm in permrows}
 for cell in orbit:idx[cell]=len(orbits)
 orbits.append(orbit)
def exprText(co,coef='x'):
 return ' '.join(f'{v:+d} {coef}{k}' for k,v in sorted(co.items()) if v)
obj=exprText({i:len(o) for i,o in enumerate(orbits)})+' -2 z'
constraints=set()
def separate(sig,W,cap,seed=False):
 rr=[i for i in range(21) if sig>>i&1];cc=[j for j in range(37) if not (sig>>(21+j)&1)]
 flip=len(cc)<len(rr)
 short,long=(cc,rr) if flip else (rr,cc)
 for b in range(1,1<<len(short)):
  A=[a for k,a in enumerate(short) if b>>k&1]
  def cell(i,j):return (j,i) if flip else (i,j)
  B=[j for j in long if sum(W[cell(i,j)] for i in A)>1e-8]
  cells=[cell(i,j) for i in A for j in B]
  if sum(W[k] for k in cells) <= cap+1e-7:continue
  c=Counter(idx[k] for k in cells)
  constraints.add(exprText(c)+(' -z <= 0;' if seed else ' <= 1;'))
reps=set(range(14));keep=[]
while reps:
 i=min(reps);keep.append(i);reps.difference_update(g[i] for g in stab)
def save(W):
 for scale in [4,12,60,600,10000,1000000]:
  matrix=[[round(W[i,j]*scale) for j in range(37)] for i in range(21)]
  raw=max(score(s,matrix) for s in chart);t=score(seed,matrix);mass=sum(map(sum,matrix))
  if raw>0 and t<=raw and mass>23*raw+2*t:
   (d/f'custom3Rect4126-{which}.json').write_text(json.dumps({'matrix':matrix,'cap':raw,'seedcap':t,'mass':mass,'expr':expr}))
   print('exact integer mass',mass,'raw',raw,'seed',t,'required >',23*raw+2*t,flush=True);return True
 return False
for step in range(200):
 lp='max: '+obj+';\n'+'\n'.join(sorted(constraints))+ '\n'+'\n'.join(f'-2 <= x{i} <= 2;' for i in range(len(orbits)))+'\n0 <= z <= 1;\n'
 f=d/f'custom3Rect4126-{which}.lp';f.write_text(lp)
 run=subprocess.run(['lp_solve','-S2',str(f)],capture_output=True,text=True)
 if run.returncode or 'Actual values' not in run.stdout:raise RuntimeError((run.stdout+run.stderr)[-800:])
 vals={k:float(v) for k,v in re.findall(r'^\s*(x\d+|z)\s+([-+.\deE]+)\s*$',run.stdout,re.M)}
 W={cell:vals[f'x{k}'] for cell,k in idx.items()};before=len(constraints)
 for i in keep:separate(chart[i],W,1)
 separate(seed,W,vals['z'],True)
 if step%10==0 or len(constraints)==before:print(step,len(constraints),sum(W.values())-2*vals['z'],flush=True)
 if step>=1 and save(W):break
 if len(constraints)==before:break
