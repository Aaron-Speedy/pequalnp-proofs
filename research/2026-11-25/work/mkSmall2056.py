from pathlib import Path
inputs=[43690,52428,61680,65280]
forms=[{x:str(i) for i,x in enumerate(inputs)}]; witnesses={w:f'(.var {i})' for i,w in enumerate(inputs)}
forms[0]=dict(witnesses)
for k in range(1,5):
 row={}
 for j in range((k-1)//2+1):
  for a,ea in forms[j].items():
   for b,eb in forms[k-j-1].items():
    for op,w in [('conj',a&b),('disj',a|b)]:
     if w not in witnesses:row[w]=f'(.{op} {ea} {eb})'
 forms.append(row);witnesses.update(row)
header='''import PEqualNP.Defs
namespace PEqualNP.Outside.Small2056
inductive Formula
  | var (i : Fin 4)
  | conj (a b : Formula)
  | disj (a b : Formula)
def gates : Formula → ℕ
  | .var _ => 0
  | .conj a b | .disj a b => 1+gates a+gates b
abbrev Word := BitVec 16
def vars : List Word := [43690,52428,61680,65280]
def truth : Formula → Word
  | .var i => vars.getD i.val 0
  | .conj a b => truth a &&& truth b
  | .disj a b => truth a ||| truth b
def trace (stock : List Word) : List Word := stock.flatMap fun x => stock.flatMap fun y => [x &&& y,x ||| y]
def ok (n : ℕ) (stock : List Word) : (Word → Bool) → Bool :=
  match n with
  | 0 => fun accept => stock.all accept
  | k+1 => fun accept => stock.all accept && (trace stock).all (fun x => stock.contains x || ok k (x::stock) accept)
inductive Reached : ℕ → List Word → Word → Prop
  | here {k S w} (h : w ∈ S) : Reached k S w
  | next {k S w v} (gate : v ∈ trace S) (fresh : v ∉ S) (tail : Reached k (v::S) w) : Reached (k+1) S w
theorem ok_sound {n S w a} (h : Reached n S w) (cert : ok n S a = true) : a w = true := by
  induction h with
  | @here k S w mem =>
    cases k with
    | zero => exact List.all_eq_true.mp cert w mem
    | succ k => exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp cert).1 w mem
  | @next k S w v gate fresh tail ih =>
    have ch := List.all_eq_true.mp (Bool.and_eq_true_iff.mp cert).2 v gate
    exact ih (by simpa [fresh] using ch)
'''
# A binary decision tree keeps membership lookup logarithmic.
def tree(keys):
 if len(keys)==1:return f'(w == {keys[0]})'
 i=len(keys)//2
 return f'(if w < {keys[i]} then {tree(keys[:i])} else {tree(keys[i:])})'
s=header+'def allowed (w : Word) : Bool := '+tree(sorted(witnesses))+'\n'
s+='def catalog : List (Word × Formula) := ['+ ',\n'.join(f'({k},{v})' for k,v in sorted(witnesses.items()))+']\n'
s+='''theorem validCatalog : ∀ pair ∈ catalog, truth pair.2 = pair.1 ∧ gates pair.2 ≤ 4 := by decide +kernel
theorem lookup (w : Word) (h : allowed w = true) : ∃ f : Formula, truth f = w ∧ gates f ≤ 4 := by
  have finite : ∀ v : Word, allowed v = true → v ∈ catalog.map Prod.fst := by
    intro v hv
    simp only [allowed] at hv
    repeat' split at hv
    all_goals simp only [beq_iff_eq] at hv; subst v; decide +kernel
  obtain ⟨⟨v,f⟩,mem,eq⟩ := List.mem_map.mp (finite w h)
  subst w
  exact ⟨f,validCatalog _ mem⟩
'''
first=sorted({w for a in inputs for b in inputs for w in [a&b,a|b]}-set(inputs))
for i,w in enumerate(first):
 s+=f'set_option maxRecDepth 8000 in\nset_option maxHeartbeats 4000000 in\ntheorem block{i} : ok 3 ({w}::vars) allowed = true := by decide +kernel\n'
s+='theorem small : ∀ w, Reached 4 vars w → ∃ f : Formula, truth f = w ∧ gates f ≤ 4 := by\n  intro w hw\n  apply lookup w\n  apply ok_sound hw\n  change vars.all allowed && (trace vars).all _ = true\n  apply Bool.and_eq_true_iff.mpr\n  refine ⟨by decide +kernel,List.all_eq_true.mpr ?_⟩\n  intro v hv\n  by_cases fresh : v ∈ vars\n  · simp [fresh]\n  · have casesV : ∀ a ∈ trace vars, a ∉ vars → '+ ' ∨ '.join('a = '+str(v) for v in first)+' := by decide +kernel\n    rcases casesV v hv fresh with '+ '|'.join(['rfl']*len(first))+'\n'
for i in range(len(first)):s+=f'    · simp [block{i}]\n'
s+='end PEqualNP.Outside.Small2056\n#print axioms PEqualNP.Outside.Small2056.small\n'
Path('.pnp/Small2056.lean').write_text(s)
