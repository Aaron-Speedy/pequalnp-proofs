from pathlib import Path
import json
d=Path('.pnp')
ns={}
exec((d/'rect4126.py').read_text().split('results={}')[0],ns)
def generate(idx):
    data=json.loads((d/f'customRect4126-{idx}.json').read_text())
    sigs=list(ns['chart'])+[ns['repval'](data['expr'],ns['base'])]
    lines=['import Cap4126','namespace CapCase'+str(idx),'open SignedRect4126','open PEqualNP.MetaComplexity','set_option maxRecDepth 100000','set_option maxHeartbeats 5000000']
    lines.append('def signals : List ℕ := '+str(sigs))
    for key,n,start,active in [('positive',21,0,1),('negative',37,21,0)]:
        bit='!' if not active else ''
        lines.append(f'def {key} (i : Fin 15) : Finset (Fin {n}) := Finset.univ.filter fun j => {bit}((signals.getD i.val 0).testBit (j.val + {start}))')
    assert all(-128<=v<128 for row in data['matrix'] for v in row)
    words=[sum((128+v)<<(8*j) for j,v in enumerate(row)) for row in data['matrix']]
    lines.append('def words : List ℕ := '+str(words))
    lines.append('def packed (i : Fin 21) := words.getD i.val 0')
    lines.extend(['def W (i : Fin 21) (j : Fin 37) : ℤ := (((packed i >>> (8*j.val)) % 256 : ℕ) : ℤ) - 128','def X (p : Fin 21) (i : Fin 15) := decide (p ∈ positive i)','def Y (q : Fin 37) (i : Fin 15) := !decide (q ∈ negative i)'])
    for i in range(15):
        cap=data['cap'] if i<14 else data['seedcap']
        lines.extend([f'theorem test{i} : ∀ A ∈ (positive {i}).powerset, (∑ j ∈ negative {i}, max 0 (∑ a ∈ A, W a j)) ≤ {cap} := by\n  letI : Decidable (∀ A ∈ (positive {i}).powerset, (∑ j ∈ negative {i}, max 0 (∑ a ∈ A, W a j)) ≤ {cap}) := Finset.decidableDforallFinset\n  exact of_decide_eq_true rfl'])
    lines.extend(['theorem cap (i : Fin 15) (A : Finset (Fin 21)) (B : Finset (Fin 37))','    (hA : ∀ p ∈ A, X p i = true) (hB : ∀ q ∈ B, Y q i = false) :','    mass W A B ≤ if i = 14 then 0 else 12 := by','  refine (cap_iff W (positive i) (negative i) _).mpr ?_ A (by simpa [X,Finset.subset_iff] using hA) B (by simpa [Y,Finset.subset_iff] using hB)','  fin_cases i'])
    for i in range(15):lines.append(f'  · exact test{i}')
    lines+=['theorem excludes (f : DMFormula 15) (pf : pos f) (sz : 2 + f.leaves ≤ 28)','    (used : 2 ≤ occurrences 14 f) (yes : ∀ p, f.eval (X p) = true)','    (no : ∀ q, f.eval (Y q) = false) : False := by','  apply exclude W X Y 14 Finset.univ Finset.univ 12 0 2 (by decide) (by decide) cap _ f pf sz used (fun p _ => yes p) (fun q _ => no q)','  decide +kernel','end CapCase'+str(idx),'#print axioms CapCase'+str(idx)+'.excludes']
    (d/f'CapCase{idx}.lean').write_text('\n'.join(lines)+'\n')
generate(1)
generate(0)
