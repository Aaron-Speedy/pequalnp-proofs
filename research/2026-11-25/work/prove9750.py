from pathlib import Path
import re
d=Path('lean/PEqualNP/Outside')
s=(d/'L_meta_4109.lean').read_text().split('theorem add_or ')[0].replace('L_meta_4109','L_meta_9750_aux')
s+='\nopen PEqualNP.MetaComplexity\n'
tr=(d/'L_meta_12184.lean').read_text().split('namespace Transfer')[1]
s+=tr[tr.index('theorem getD_snoc_eq'):tr.index('theorem getD_snoc_len')]+tr[tr.index('def wmap ('):tr.index('theorem snoc_swap')]
s+='''
theorem pin {n s : ℕ} (f g : (Fin n → Bool) → Bool) (i : Fin n) (a b u v : Fin n → Bool)
    (same : ∀ j, j ≠ i → a j = b j) (different : f a ≠ f b) (nc : g u ≠ g v)
    (co : ∀ y, f (Function.update y i false) = g y) (hc : HasCircuitSize n f s) :
    ∃ t, t+1 ≤ s ∧ HasCircuitSize n g t := by
  obtain ⟨C,ok,bd,ev⟩ := hc
  obtain ⟨D,okD,save,evD⟩ := one_drop n C ok i false
    ⟨a,b,same,by simpa only [ev] using different⟩ (by
      rintro ⟨c,h⟩
      apply nc
      have hh := (h u).trans (h v).symm
      simpa only [ev,co] using hh)
  exact ⟨D.size,by omega,D,okD,le_rfl,fun y => (evD y).trans ((ev _).trans (co y))⟩

def bits (v : ℕ) (i : Fin 12) := v.testBit i
'''
full_edges=[tuple(map(int,k)) for k in re.findall(r'x (\d+) && x (\d+)',(d/'L_meta_9750.lean').read_text())]
target=[tuple(map(int,k)) for k in re.findall(r'x (\d+) && x (\d+)',(d/'L_meta_7398.lean').read_text().rsplit('theorem PEqualNP.Outside.',1)[1].split(':=')[0])]
def funexpr(edges):return ' || '.join(f'(x {a} && x {b})' for a,b in edges)
es=full_edges.copy()
cuts=[(2,10),(3,11),(8,4),(9,5)]
for k in range(5):
 s+=f'\ndef f{k} (x : Fin 12 → Bool) := '+funexpr(es)+'\n'
 if k<4:es=[e for e in es if cuts[k][0] not in e]
s+='\ndef fSmall (x : Fin 8 → Bool) := '+funexpr(target)+'\n'
mp=[1,6,10,11,5,4,0,7]
s+='\ndef projection : Fin 12 → Fin 8 := !['+','.join(str(mp.index(i) if i in mp else 0) for i in range(12))+']\n'
s+='\ntheorem restrictBound (bound : ∀ t, HasCircuitSize 8 fSmall t → 12 ≤ t) (s : ℕ) (h : HasCircuitSize 12 f0 s) : 16 ≤ s := by\n'
for k,(i,j) in enumerate(cuts):
 s+=f'  obtain ⟨s{k},h{k},c{k}⟩ := pin f{k} f{k+1} {i} (bits {1<<j}) (bits {(1<<j)|(1<<i)}) (bits 0) (bits 129) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by intro y; simp [f{k},f{k+1},Function.update]; try rfl) '+('h' if k==0 else f'c{k-1}')+'\n'
s+='''  have hrel := relabel_size projection f4 s3 c3
  have eq : (fun x : Fin 8 → Bool => f4 (x ∘ projection)) = fSmall := by
    funext x
    simp [f4,fSmall,projection,Function.comp_def]
    all_goals ac_rfl
  rw [eq] at hrel
  have := bound _ hrel
  omega

end PEqualNP.Outside.L_meta_9750_aux
'''
Path('.pnp/Restriction9750.lean').write_text(s)
