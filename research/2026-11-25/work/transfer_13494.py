from pathlib import Path
d=Path('lean/PEqualNP/Outside')
p=d/'L_meta_13494.lean'
orig=p.read_text().split('theorem PEqualNP.Outside.L_meta_13494 :')[1]
base=(d/'L_meta_13343.lean').read_text().split('def wit : Circuit')[0]
base=base.replace('L_meta_13343_aux','L_meta_13494_aux')
src=(d/'L_meta_12184.lean').read_text()
def piece(start,end): return src[src.index(start,src.index('namespace Transfer')):src.index(end,src.index(start,src.index('namespace Transfer')))]
helper=piece('def wiresFrom (','theorem wiresFrom_append')+piece('theorem getD_snoc_eq','theorem getD_snoc_len')+piece('def wmap (','theorem snoc_swap')+piece('def dualGate (','def g0 :')
perm=[0,2,1,5,4,3]
gates=[('and',1,2),('and',6,3),('or',1,2),('and',4,5),('or',8,9),('and',0,10),('or',4,5),('and',7,12),('or',11,13)]
wire=lambda i: perm[i] if i<6 else i
witness=', '.join(f"⟨.{('or' if op=='and' else 'and')}, [{wire(i)}, {wire(j)}]⟩" for op,i,j in gates)
stmt=f'''
def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3941264042 * 2 ^ 32 + 3941132456)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def swapInputs : Fin 6 → Fin 6 := ![0,2,1,5,4,3]

theorem agrees : ∀ x : Fin 6 → Bool, (!(target (fun i => !x (swapInputs i)))) = fG x := by
  decide +kernel

def dualWitness : Circuit := ⟨[{witness}], 14⟩

theorem sameSize : ∀ s, HasCircuitSize 6 target s → ∃ C : Circuit,
    Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = target x := by
  intro s hs
  have hd := dual_size target ⟨fun _ => true, by decide +kernel⟩ s hs
  have hr := relabel_size swapInputs _ s hd
  have hsame : (fun x : Fin 6 → Bool => !(target (fun i => !x (swapInputs i)))) = fG :=
    funext agrees
  change HasCircuitSize 6 (fun x => !(target (fun i => !x (swapInputs i)))) s at hr
  rw [hsame] at hr
  exact ⟨dualWitness, by simp [dualWitness, Monotone2],
    (show dualWitness.size ≤ 9 by decide).trans (lower s hr), by decide +kernel⟩

end Transfer
end PEqualNP.Outside.L_meta_13494_aux

'''
p.write_text(base+'\nnamespace Transfer\n'+helper+stmt+'theorem PEqualNP.Outside.L_meta_13494 :'+orig)
