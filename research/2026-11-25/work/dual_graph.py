from pathlib import Path
import re
p=Path('lean/PEqualNP/Outside/L_meta_612.lean')
s=p.read_text()
bridge=s[s.index('def orCost'):s.index('def meetRows')]
bridge=bridge.replace('.and ∨ g.op = .or','.or ∨ g.op = .and').replace('.and ∨ z.op = .or','.or ∨ z.op = .and').replace('| .or =>','| .and =>')
def dual(t):
    for a,b in [('countBridge','andBridge'),('orCost','andCost'),('gateCol','negGate'),('newCol','newNeg'),('col','negCol'),('circuitSearch','circuitAndSearch')]:
        t=re.sub(r'\b'+a+r'\b',b,t)
    return t
bridge=dual(bridge)
intro='''
def negCol {α : Type} [Fintype α] (w : α → List Bool) (i : ℕ) : Finset α :=
  Finset.univ.filter (fun r => !(w r).getD i false)

def negGate {α : Type} [Fintype α] (w : α → List Bool) (g : Gate) : Finset α :=
  Finset.univ.filter (fun r => !g.op.eval (g.inputs.map (fun i => (w r).getD i false))))

'''
intro=intro.replace('false))))','false)))')
nc=s[s.index('theorem newCol'):s.index('def orCost')]
cc=dual(s[s.index('theorem circuitSearch'):s.index('theorem reachMore')])
cc=cc.replace('inputBank sample','inputBank (fun r i => !(sample r i))').replace('fun r => C.eval','fun r => !C.eval').replace('negCol wires i = ∅','negCol wires i = Finset.univ').replace('Bool.false_eq_true,Finset.notMem_empty','Bool.not_false,Finset.mem_univ').replace('exact he ▸ zero','exact he ▸ ⟨∅,Finset.empty_subset _,by simp⟩').replace('Set.mem_singleton_iff] using ok','Set.mem_singleton_iff, or_comm] using ok')
part=intro+dual(nc)+bridge+cc
marker='end PEqualNP.Outside.L_meta_612_aux'
p.write_text(s.replace(marker,part+'\n'+marker))
