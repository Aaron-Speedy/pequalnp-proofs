from pathlib import Path
import re
s=Path('.pnp/Star9738.lean').read_text().replace('import Mathlib','import MonoPin9738\nopen PEqualNP.Outside.MonoPin9738')
pre=s[:s.index('set_option maxRecDepth')];post=s[s.index('theorem exactEdges'):]
h='''def val (x : Fin 25 → Bool) (w : ℕ) := (run C.gates (List.ofFn x)).getD w false
theorem val_input (x : Fin 25 → Bool) (i : Fin 25) : val x i = x i := by
  unfold val
  rw [run_input _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]
'''
for op,sign in [('or','||'),('and','&&')]:
 h+=f'''theorem step_{op} (x : Fin 25 → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (h : C.gates[j] = ⟨.{op},[a,b]⟩) (ha : a < 25+j) (hb : b < 25+j) :
    val x (25+j) = (val x a {sign} val x b) := by
  have z := run_gate C.gates (List.ofFn x) j hj
  simpa [val,h,GateOp.eval,ha,hb] using z
'''
h+='set_option maxRecDepth 18000 in\nset_option maxHeartbeats 3000000 in\ntheorem evalStars (x : Fin 25 → Bool) : C.eval (List.ofFn x) = edges.any (fun p => x p.1 && x p.2) := by\n'
for i in range(25):h+=f'  have h{i} : val x {i} = x {i} := val_input x ({i} : Fin 25)\n'
gates=re.findall(r'⟨\.(and|or),\[(\d+),(\d+)\]⟩',s)
for j,(op,a,b) in enumerate(gates):
 h+=f'  have h{25+j} := step_{op} x {j} {a} {b} (by decide) rfl (by decide) (by decide)\n  change val x {25+j} = _ at h{25+j}\n'
h+='  change val x 83 = _\n  simp only ['+','.join('h'+str(i) for i in range(84))+']\n  simp [edges,Bool.and_or_distrib_left,Bool.or_and_distrib_right,Bool.or_assoc]\n  all_goals ac_rfl\n'
Path('.pnp/StarFast9738.lean').write_text(pre+h+post)
