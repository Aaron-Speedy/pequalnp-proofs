from pathlib import Path
import json
e=json.load(open('.pnp/9738-edges.json'));gates=[]
def gate(op,a,b):
    i=25+len(gates);gates.append(f'⟨.{op},[{a},{b}]⟩');return i
def join(xs):
    xs=list(xs)
    while len(xs)>1:xs=[gate('or',a,b) for a,b in zip(xs[::2],xs[1::2])]+(xs[-1:] if len(xs)%2 else [])
    return xs[0]
stars=[gate('and',j,join(a for a,b in e if b==j)) for j in range(13,25)]
last=join(stars);assert len(gates)==59
es=','.join(f'({a},{b})' for a,b in e)
src='''import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.Graph9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def edges : List (Fin 25 × Fin 25) := ['''+es+''']
def original : List (ℕ × ℕ) := ['''+es+''']
def C : Circuit := ⟨['''+',\n'.join(gates)+f'''],{last}⟩
theorem size : C.size = 59 := by decide
theorem mono : Monotone2 C := by simp [Monotone2,C]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 3000000 in
theorem evalStars (x : Fin 25 → Bool) : C.eval (List.ofFn x) =
    edges.any (fun p => x p.1 && x p.2) := by
  simp [C,edges,Circuit.eval,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD,
    Bool.and_or_distrib_left,Bool.or_and_distrib_right,Bool.or_assoc]
  all_goals ac_rfl

theorem exactEdges (x : Fin 25 → Bool) : C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 25, (u.val,v.val) ∈ original ∧ x u = true ∧ x v = true := by
  have mapEq : edges.map (fun p => (p.1.val,p.2.val)) = original := by decide
  rw [evalStars,List.any_eq_true]
  constructor
  · rintro ⟨⟨u,v⟩,h,p⟩
    exact ⟨u,v,mapEq ▸ List.mem_map.mpr ⟨(u,v),h,rfl⟩,Bool.and_eq_true.mp p⟩
  · rintro ⟨u,v,h,p,q⟩
    rw [← mapEq] at h
    obtain ⟨⟨i,j⟩,mem,eq⟩ := List.mem_map.mp h
    have a : i = u := Fin.ext (congrArg Prod.fst eq)
    have b : j = v := Fin.ext (congrArg Prod.snd eq)
    exact ⟨(i,j),mem,by simp [a,b,p,q]⟩
end PEqualNP.Outside.Graph9738
#print axioms PEqualNP.Outside.Graph9738.exactEdges
'''
Path('.pnp/Star9738.lean').write_text(src)
