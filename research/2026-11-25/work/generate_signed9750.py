from signed9750_base import *
from pathlib import Path
source='''import Signed9750
namespace PEqualNP.Outside.Signed9750
def bits (r : ℕ) (i : Fin 12) := r.testBit i
theorem weaken {f : Fn Assignment} {a b : ℕ} (le : a ≤ b) (h : LB f b) : LB f a :=
  fun k p => le.trans (h k p)

theorem edgeCost (a b : Fin 12) (ne : a ≠ b) : LB (fun x => x a && x b) 1 := by
  intro k h
  cases k with
  | succ k => omega
  | zero =>
    change primary (fun x => x a && x b) at h
    rcases h with ⟨c,eq⟩ | ⟨j,eq|eq⟩
    · have h0 := congrFun eq (fun _ => false)
      have h1 := congrFun eq (fun _ => true)
      simp_all
    · have d := congrFun eq (fun i => decide (i = j))
      simp at d
      exact False.elim (ne (d.1.trans d.2.symm))
    · have d := congrFun eq (fun _ => false)
      simp [inv] at d

'''
done={}
def terms(s,l):
    return [(i,) for i in vs(l)]+[(i,j) for i,j in sorted(G) if s>>i&1 and s>>j&1]
def expression(ts):
    return ' || '.join('(x '+str(t[0])+' && x '+str(t[1])+')' if len(t)==2 else 'x '+str(t[0]) for t in ts) or 'false'
def val(ts,x):
    return any(all(x>>i&1 for i in t) for t in ts)
def emit(s,l):
    global source
    if (s,l) in done:return done[s,l]
    ts=terms(s,l)
    n,p=tree(s,l)
    name=f'table{s}_{l}'
    txt=f'def {name} (x : Assignment) : Bool := {expression(ts)}\ntheorem low{name} : LB {name} {n} := by\n'
    if p=='nonliteral':
        assert len(ts)==1 and len(ts[0])==2
        txt+=f'  exact edgeCost {ts[0][0]} {ts[0][1]} (by decide)\n'
    else:
        typ,idx=p.split();i=int(idx)
        test=next(x for x in range(4096) if val(ts,x&~(1<<i))!=val(ts,x|(1<<i)))
        bs=[0,1] if typ=='both' else [int(typ=='one')]
        names=[]; witnesses=[]
        for b in bs:
            sub=norm(s&~(1<<i),(l&~(1<<i)) | (adj[i]&s if b else 0))
            g=emit(*sub);names.append(g)
            witness=next(x for x in range(4096) if val(terms(*sub),x))
            witnesses.extend((0,witness))
        method='lbBoth' if typ=='both' else 'lbOne'
        args=[str(i)]+([] if typ=='both' else [str(bool(bs[0])).lower()])+[f'(bits {x})' for x in [test]+witnesses]
        txt+='  apply '+method+' (g := '+names[0]+') '+('(h := '+names[1]+') ' if len(names)==2 else '')+' '.join(args)+'\n'
        for _ in range(1+len(bs)):txt+='  · decide +kernel\n'
        for g in names:
            txt+=f'  · funext x; simp [{name},{g},co,slice,pairAt,Function.update] <;> bv_decide\n'
        for g in names:txt+=f'  · exact weaken (by decide) low{g}\n'
    source+=txt+'\n';done[s,l]=name;return name
emit((1<<12)-1,0)
source+='end PEqualNP.Outside.Signed9750\n#print axioms PEqualNP.Outside.Signed9750.lowtable4095_0\n'
Path('.pnp/SignedGraph9750.lean').write_text(source)
