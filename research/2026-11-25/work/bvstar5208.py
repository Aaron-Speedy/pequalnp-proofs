from pathlib import Path
s='''import Mathlib
namespace StarBudget5208
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
abbrev T := BitVec 64
def gate (op : Bool) (a b : T) : T := bif op then a ||| b else a &&& b
def mark (op : Bool) (a b : T) (side : BitVec 64) : Bool :=
  !op && ((a &&& b &&& 8) == 8) && (((a ||| b) &&& side) == 0)
'''
atoms=[sum(1<<r for r in range(64) if r>>i&1) for i in range(6)]
atoms+=[atoms[1]|atoms[5]]
target=sum(1<<r for r in range(64) if r&1 and r&30)
for n in range(7,12):
 s+=f'def pick{n} (k : BitVec 4) '+('('+' '.join('w'+str(i) for i in range(7,n))+' : T) ' if n>7 else '')+': T :=\n  '
 for i in range(1,n):
  v=str(atoms[i]) if i<7 else f'w{i}';s+=f'bif k == {i} then {v} else '
 s+=str(atoms[0])+'\n'
s+='theorem impossible '+' '.join(f'(o{i} : Bool) (x{i} y{i} : BitVec 4)' for i in range(5))+' :\n'
for i in range(5):
 args=' '.join(f'w{j+7}' for j in range(i))
 for v,k in [('a','x'),('b','y')]:s+=f'  let {v}{i} := pick{i+7} {k}{i} {args}\n'
 s+=f'  let w{7+i} := gate o{i} a{i} b{i}\n'
s+=f'  w11 = {target} → ('
s+=' || '.join(f'(mark o{i} a{i} b{i} 2 && mark o{j} a{j} b{j} 4)' for i in range(5) for j in range(i+1,5))
s+=') = false := by\n  dsimp only\n  unfold gate mark pick11 pick10 pick9 pick8 pick7\n  bv_decide\nend StarBudget5208\n#print axioms StarBudget5208.impossible\n'
Path('.pnp/StarBudget5208.lean').write_text(s)
