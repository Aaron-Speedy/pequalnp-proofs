from pathlib import Path
P=Path('.pnp')
g=[]
def gate(op,a,b):
 g.append((op,a,b));return 25+len(g)
stars=[];eg=[]
for p in range(13):
 ns=[l for l in range(13) if (p-l)%13 in (0,1,3,9)]
 u=gate('or',13+ns[0],13+ns[1]);v=gate('or',13+ns[2],13+ns[3]);stars.append(gate('and',p,gate('or',u,v)));eg.extend((p,l) for l in ns)
last=stars[1]
for v in stars[2:]:last=gate('or',last,v)
s='''import Join5198
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.MonoPin9738 PEqualNP.Outside.Join5198
open PEqualNP.HeptadCover PEqualNP.GenericRejection
namespace PEqualNP.Outside.Upper5198
'''
for n,es in [('left',eg[:4]),('right',eg[4:])]:
 s+=f'def {n} : List (Fin 13 × Fin 13) := ['+','.join(f'({a},{b})' for a,b in es)+']\n'
s+='def C : Circuit := ⟨['+',\n'.join(f'⟨.{op},[{a},{b}]⟩' for op,a,b in g)+f'],{last}⟩\n'
u=(P/'StarFast9738.lean').read_text();s+=u[u.index('def val '):u.index('set_option maxRecDepth',u.index('def val '))].replace('25','26')
s+='''set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem both (x : Fin 26 → Bool) :
'''
for z,(w,n) in enumerate([(stars[0],'left'),(last,'right')]):
 s+=f'    val x {w} = {n}.any (fun e => x (Fin.castAdd 13 e.1) && x (Fin.natAdd 13 e.2))'+(' ∧\n' if not z else ' := by\n')
for i in range(26):s+=f'  have h{i} : val x {i} = x {i} := val_input x ({i} : Fin 26)\n'
for i,(op,a,b) in enumerate(g):s+=f'  have h{i+26} := step_{op} x {i} {a} {b} (by decide) rfl (by decide) (by decide)\n  change val x {26+i} = _ at h{26+i}\n'
s+='  constructor <;> simp only ['+','.join('h'+str(i) for i in range(89))+']\n  all_goals simp [left,right,Bool.and_or_distrib_left,Bool.or_assoc,Fin.natAdd,Fin.castAdd]\n  all_goals ac_rfl\n'
s+='''
theorem rows (P L : Finset (Fin 13)) :
    W C 29 P L = left.any (fun e => decide (e.1 ∈ P ∧ e.2 ∈ L)) ∧
    W C 88 P L = right.any (fun e => decide (e.1 ∈ P ∧ e.2 ∈ L)) := by
  let x : Fin 26 → Bool := Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
  have eq : List.ofFn x = incidenceInput P L := by simp [x,incidenceInput, List.ofFn_fin_append]
  have h := both x
  unfold val at h
  rw [eq] at h
  simpa [W,run,Circuit.wires,x,decide_and] using h

theorem negative (P : Finset (Fin 13)) :
    W C 29 P (missLines singerLines3 P) = false ∧ W C 88 P (missLines singerLines3 P) = false := by
  have prop (l : List (Fin 13 × Fin 13)) (valid : ∀ e ∈ l, e.1 ∈ singerLines3 e.2) :
      l.any (fun e => decide (e.1 ∈ P ∧ e.2 ∈ missLines singerLines3 P)) = false := by
    apply List.any_eq_false.mpr
    intro e he
    simp only [decide_eq_false_iff_not]
    rintro ⟨p,m⟩
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp m).2 p (valid e he)
  have h := rows P (missLines singerLines3 P)
  exact ⟨h.1.trans (prop _ (by decide)), h.2.trans (prop _ (by decide))⟩

theorem positive : ∀ p l : Fin 13, p ∈ singerLines3 l → W C 29 {p} {l} = true ∨ W C 88 {p} {l} = true := by
  intro p l hp
  have h := rows {p} {l}
  rw [h.1,h.2]
  revert hp l p
  decide +kernel

theorem structure_ok : Monotone2 C ∧ ReadsBack 26 C ∧ C.size=63 ∧
    (∀ j ∈ Finset.range C.size, (gateAt C j).op = GateOp.and →
      ∀ i ∈ (gateAt C j).inputs, 26 ≤ i → (gateAt C (i-26)).op ≠ GateOp.and) := by decide +kernel
theorem exclusive : (W C 29 {0} {0} = true ∧ W C 88 {0} {0} = false) ∧
    (W C 29 {1} {1} = false ∧ W C 88 {1} {1} = true) := by decide +kernel
end PEqualNP.Outside.Upper5198
#print axioms PEqualNP.Outside.Upper5198.negative
'''
(P/'Upper5198.lean').write_text(s)
