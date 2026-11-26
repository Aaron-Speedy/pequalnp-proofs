from pathlib import Path
import json
p=Path('.pnp')
exec((p/'obstructions4131.py').read_text().split('for d in range')[0])
def lit(x):return '['+','.join(map(str,x))+']'
def fs(mask):return '{'+','.join(str(v) for v in range(11) if mask>>v&1)+'}'
es=lit([f'({a},{b})' for a,b in edges])
full=[2047^s for s in ind]
mins=[]
for d in range(7):
 c={induced(s) for s in range(2048) if s.bit_count()==5+d and any(s&i==i for i in ind)}
 mins.append(sorted(m for m in c if not any(a!=m and a&m==a for a in c)))
w=[]
for k in range(2048):
 d=6-k.bit_count()
 w.append(next((m for m in mins[d] if m&induced(2047^k)==m),0) if d>=0 and any(k&t==k for t in full) else 0)
groups=[(0,1),(2,),(3,),(4,5,6)]
s='import PEqualNP.Defs\n\nopen PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership\n\nset_option maxRecDepth 32000 in\nset_option maxHeartbeats 18000000 in\ntheorem PEqualNP.Outside.R_meta_4131_2\n'
base=f'''let E : List (Fin 11 × Fin 11) := {es}
      let G := edgeGraph 11 (E.map fun p => (p.1.val,p.2.val))
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      let U := Ustar G C
      let B := 2*(centreless G C).card+(junk G C).card+(orN G C \\ lam G C).card
      U.card ≤ B → B < 2*U.card → '''
for gid,g in enumerate(groups):
 s+=f'    (h{gid} : '+base
 if len(g)==1:
  s+=f'B-U.card = {g[0]} → ∀ m ∈ ({lit(mins[g[0]])} : List ℕ),\n'
 else:
  s+=f'∀ i : Fin {len(g)}, B-U.card = {g[0]}+i.val → ∀ m ∈ (({lit([lit(mins[d]) for d in g])} : List (List ℕ)).getD i.val []),\n'
 s+='      ∃ j : Fin 16, m.testBit j.val = true ∧ s((E.getD j.val (0,0)).1,(E.getD j.val (0,0)).2) ∉ U)\n'
s+='    : '+json.loads((p/'L-meta-4131.json').read_text())['gap']['statement']+' := by\n'
prior=Path('lean/PEqualNP/Outside/R_meta_4131_1.lean').read_text()
s+=prior[prior.index('  intro es G C'):prior.index('  let single')]
s+=f'''  let E : List (Fin 11 × Fin 11) := {es}
  let covers : List (Finset (Fin 11)) := {lit([fs(k) for k in full])}
  let mins : List (List ℕ) := {lit([lit(a) for a in mins])}
  let rows : List (List ℕ) := {lit([lit(w[i:i+32]) for i in range(0,2048,32)])}
  let number (S : Finset (Fin 11)) := ∑ v ∈ S, 2^v.val
  let witness (S : Finset (Fin 11)) := (rows.getD (number S / 32) []).getD (number S % 32) 0
  have represents : ∀ S : Finset (Fin 11), S.card = 7 →
      E.all (fun p => decide (p.1 ∈ S ∨ p.2 ∈ S)) = true → S ∈ covers := by decide +kernel
  have adj : ∀ j : Fin 16, G.Adj (E.getD j.val (0,0)).1 (E.getD j.val (0,0)).2 := by decide +kernel
  have edgeMem : ∀ p ∈ E, G.Adj p.1 p.2 := by decide +kernel
  have tc := represents T hT (List.all_eq_true.mpr (fun p hp => decide_eq_true (coverT (edgeMem p hp))))
  have usable : covers.any (fun S => decide (K ⊆ S)) = true := List.any_eq_true.mpr ⟨T,tc,decide_eq_true Ksub⟩
  have chart : ∀ S : Finset (Fin 11), S.card ≤ 6 → covers.any (fun V => decide (S ⊆ V)) = true →
      witness S ∈ mins.getD (6-S.card) [] ∧
        ∀ j : Fin 16, (witness S).testBit j.val = true →
           (E.getD j.val (0,0)).1 ∉ S ∧ (E.getD j.val (0,0)).2 ∉ S := by decide +kernel
  obtain ⟨listed,absent⟩ := chart K (by omega) usable
  rw [show 6-K.card=d by omega] at listed
  have block : ∃ j : Fin 16, (witness K).testBit j.val = true ∧
       s((E.getD j.val (0,0)).1,(E.getD j.val (0,0)).2) ∉ U := by
    interval_cases d
'''
for gid,g in enumerate(groups):
 for k,d in enumerate(g):
  i=f' (⟨{k},by decide⟩ : Fin {len(g)})' if len(g)>1 else ''
  s+=f'    · exact h{gid} C size least top junkCount hlo hhi{i} (by omega) _ listed\n'
s+='''  obtain ⟨j,bit,kept⟩ := block
  have ends := absent j bit
  exact (cutK (SimpleGraph.deleteEdges_adj.mpr ⟨adj j,kept⟩)).elim ends.1 ends.2
'''
(p/'R_meta_4131_2.lean').write_text(s)
