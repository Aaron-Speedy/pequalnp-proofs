import json,re
from pathlib import Path
d=Path('.pnp')
e=sorted(map(tuple,json.loads((d/'9738-edges.json').read_text())))
bound,n,low,name,mp=json.loads((d/'emb9738.json').read_text())[0]
assert bound==37
source=Path('lean/PEqualNP/Outside/'+name+'.lean').read_text().rsplit('theorem PEqualNP.Outside.',1)[1].split(' : ',1)[1].split(' := by',1)[0]
host=Path('lean/PEqualNP/Outside/L_meta_9738.lean').read_text().split(' : ',1)[1].rsplit(' := by',1)[0].replace('≤ 58','≤ 36')
small=[tuple(map(int,z)) for z in re.findall(r'\((\d+), (\d+)\)',source)]
assert {(mp[i],mp[j]) for i,j in small}==set(p for p in e if p[0] in mp and p[1] in mp)
S='''import MonoPin9738
namespace PEqualNP.Outside.Lower9738
open PEqualNP.Outside.MonoPin9738 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
'''
def lst(es):return '['+','.join(f'({a},{b})' for a,b in es)+']'
def formula(es):
 return ' || '.join(f'(x {a} && x {b})' for a,b in es)
def equival(rank,es,k,label):
 return f'''def {label}Edges : List (Fin {k} × Fin {k}) := {lst(es)}
theorem {label}Spec (x : Fin {k} → Bool) : {rank} x = true ↔
    ∃ u v : Fin {k}, (u.val,v.val) ∈ ({lst(es)} : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
  have same : {rank} x = {label}Edges.any (fun p => x p.1 && x p.2) := by
    simp [{rank},{label}Edges,Bool.or_assoc]
  have mapEq : {label}Edges.map (fun p => (p.1.val,p.2.val)) = {lst(es)} := by decide
  rw [same,List.any_eq_true,← mapEq]
  constructor
  · rintro ⟨⟨u,v⟩,h,p⟩
    exact ⟨u,v,List.mem_map.mpr ⟨(u,v),h,rfl⟩,Bool.and_eq_true.mp p⟩
  · rintro ⟨u,v,h,p,q⟩
    obtain ⟨⟨i,j⟩,mem,eq⟩ := List.mem_map.mp h
    have a : i=u := Fin.ext (congrArg Prod.fst eq)
    have b : j=v := Fin.ext (congrArg Prod.snd eq)
    exact ⟨(i,j),mem,by simp [a,b,p,q]⟩
'''
steps=[];orig=e
for k in range(12):
 S+=f'def f{k} (x : Fin 25 → Bool) : Bool := {formula(e)}\n'
 if k==11:break
 remain=set(range(25))-set(mp)-{v for v,_,_,_ in steps}
 v,w=next((v,w) for v in sorted(remain) for w in range(25) if (min(v,w),max(v,w)) in e and w not in remain)
 e=[p for p in e if v not in p];u,z=e[0];steps.append((v,w,u,z))
S+=equival('f0',orig,25,'host')
S+=f'def target (x : Fin 14 → Bool) : Bool := {formula(small)}\n'
S+=equival('target',small,14,'low')
for i,(v,w,a,b) in enumerate(steps):
 S+=f'''theorem step{i} (s : ℕ) (h : MSize 25 f{i} s) : ∃ t, t+1 ≤ s ∧ MSize 25 f{i+1} t := by
  apply pin f{i} f{i+1} {v} (fun j => decide (j = {w})) (fun j => decide (j = {w} ∨ j = {v}))
    (fun _ => false) (fun j => decide (j = {a} ∨ j = {b})) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f{i},f{i+1},Function.update, Bool.or_assoc]
'''
vals=[mp.index(i) if i in mp else 0 for i in range(25)]
S+='def renameV (i : Fin 25) : Fin 14 := (!['+','.join(map(str,vals))+'] : Fin 25 → Fin 14) i\n'
S+='theorem renameOK (x : Fin 14 → Bool) : f11 (x ∘ renameV) = target x := by\n  change '+formula([(vals[a],vals[b]) for a,b in e])+' = _\n  simp only [target,Bool.or_assoc]\n  all_goals ac_rfl\n'
S+='theorem transfer (known : '+source+') : '+host+' := by\n  rintro ⟨C,mono,size,ev⟩\n  have h0 : MSize 25 f0 C.size := ⟨C,mono,le_rfl,fun x => Bool.eq_iff_iff.mpr ((ev x).trans (hostSpec x).symm)⟩\n'
for i in range(11):S+=f'  obtain ⟨s{i+1},size{i+1},h{i+1}⟩ := step{i} _ h{i}\n'
S+='  obtain ⟨D,hm,hs,he⟩ := relabel_size renameV f11 s11 h11\n  apply known\n  exact ⟨D,hm,by omega,fun x => by rw [he,renameOK,lowSpec]⟩\nend PEqualNP.Outside.Lower9738\n#print axioms PEqualNP.Outside.Lower9738.transfer\n'
(d/'Lower9738.lean').write_text(S)
