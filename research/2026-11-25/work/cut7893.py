from orbits7893 import P,N,Z,G,chosen
import json
from pathlib import Path
d=Path('.pnp');statement=json.loads((d/'L-meta-7893.json').read_text())['gap']['statement']
hdr='''import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_7893_1
    (plain : ∀ C : Circuit, IsAO2 10 C → C.size ≤ 18 →
      (∀ p ∈ POS, circuitFun 10 C (fun i => p.testBit i.val) = true) →
      ∃ n ∈ NEG, circuitFun 10 C (fun i => n.testBit i.val) = true)
    (rename : ∀ (C : Circuit) (w : ℕ) (σ : Fin 10 → Fin 10), Function.Injective σ → σ 0 = 0 →
      IsAO2 10 C → w ≠ 0 → w < 10+C.size →
      (∀ j g, 10+j ≤ w → C.gates[j]? = some g → 0 ∉ g.inputs) →
      ∃ (D : Circuit) (v : ℕ), IsAO2 10 D ∧ D.size = C.size ∧ v ≠ 0 ∧ v < 10+D.size ∧
        (∀ j g, 10+j ≤ v → D.gates[j]? = some g → 0 ∉ g.inputs) ∧
        ∀ x : Fin 10 → Bool, circuitFun 10 D x = circuitFun 10 C (x ∘ σ) ∧
          (D.wires (List.ofFn x)).getD v false = (C.wires (List.ofFn (x ∘ σ))).getD w false)
    (active : ∀ (C : Circuit) (w : ℕ), IsAO2 10 C → 16 ≤ C.size ∧ C.size ≤ 18 →
      (w ≠ 0 ∧ w < 10+C.size ∧ ∀ j g, 10+j ≤ w → C.gates[j]? = some g → 0 ∉ g.inputs) →
      let b := fun (n : ℕ) (i : Fin 10) => n.testBit i.val
      let f := fun n => (C.wires (List.ofFn (Function.update (b n) 0 false))).getD w false
      (f 6 = true ∨ f 12 = true) →
      (∀ n ∈ ZERO, f n = false) →
      (∀ n ∈ NEG, circuitFun 10 C (b n) = false) →
      ∃ p ∈ POS, circuitFun 10 C (Function.update (b p) 0 (b p 0 || f p)) = false) :
'''
def num(xs):return '('+str(xs)+' : List ℕ)'
def sub(s):return s.replace('POS',num(P)).replace('NEG',num(N)).replace('ZERO',num(Z))
src=sub(hdr)+statement+' := by\n'
src+=sub('''  intro C w ok size valid
  let b (n : ℕ) (i : Fin 10) := n.testBit i.val
  let f (n : ℕ) := (C.wires (List.ofFn (Function.update (b n) 0 false))).getD w false
  let aug (n : ℕ) := Function.update (b n) 0 (b n 0 || f n)
  change (∀ r ∈ ZERO, f r = false) → ¬ ((∀ r ∈ POS, circuitFun 10 C (aug r) = true) ∧
    ∀ r ∈ NEG, circuitFun 10 C (aug r) = false)
  intro zero good
  have negBits : ∀ r ∈ NEG, b r 0 = true ∨ r ∈ ZERO := by decide +kernel
  have neg (r : ℕ) (hr : r ∈ NEG) : circuitFun 10 C (b r) = false := by
    have eq : aug r = b r := by
      unfold aug
      rcases negBits r hr with h|h
      · rw [h]; simp; exact h.symm
      · simp [zero r h]
    rw [← eq]; exact good.2 r hr
  obtain ⟨p,hp,off,hit⟩ : ∃ p ∈ POS, b p 0 = false ∧ f p = true := by
    by_contra! h
    obtain ⟨n,hn,yes⟩ := plain C ok size.2 (fun r hr => by
      have eq : aug r = b r := by
        unfold aug
        cases hb : b r 0 with
        | false => simp [hb,h r hr hb]
        | true => simp [hb]
      rw [← eq]; exact good.1 r hr)
    simp [neg n hn] at yes
''')
# all coordinate permutations as table. If σ maps old bit position i to new position σ(i),
# the encoded old input corresponding to r has old bit i equal to bit σ(i) in r.
src+='  let perms : Fin 12 → (Fin 10 → Fin 10) := ![\n    '+',\n    '.join('!['+','.join(map(str,v))+']' for v in G)+']\n'
src+=sub('''  let code (k : Fin 12) (r : ℕ) : ℕ := ∑ i : Fin 10, if b r (perms k i) then 2^i.val else 0
  have pick : ∀ r ∈ POS, b r 0 = false → ∃ k : Fin 12, code k 6 = r ∨ code k 12 = r := by decide +kernel
  obtain ⟨k,hk⟩ := pick p hp off
  let σ := perms k
  let t := code k
  have cert : ∀ k : Fin 12, Function.Injective (perms k) ∧ perms k 0 = 0 ∧
      (∀ r ∈ POS, code k r ∈ POS) ∧ (∀ r ∈ NEG, code k r ∈ NEG) ∧
      (∀ r ∈ ZERO, code k r ∈ ZERO) ∧
      (∀ r ∈ POS ++ NEG, ∀ i : Fin 10, b (code k r) i = b r (perms k i)) := by decide +kernel
  obtain ⟨inj,fix,pp,nn,zz,bits⟩ := cert k
  obtain ⟨D,v,okD,szD,nz,lt,reads,eval⟩ :=
    rename C w σ inj fix ok valid.1 valid.2.1 valid.2.2
  have upd (x : Fin 10 → Bool) (a : Bool) :
      (Function.update x 0 a) ∘ σ = Function.update (x ∘ σ) 0 a := by
    funext i
    by_cases hi : i=0
    · subst i; simp [Function.comp_apply,show σ 0=0 from fix]
    · have hn : σ i ≠ 0 := fun h => hi (inj (h.trans fix.symm))
      simp [Function.comp_apply,Function.update_of_ne hi,Function.update_of_ne hn]
  let g (r : ℕ) := (D.wires (List.ofFn (Function.update (b r) 0 false))).getD v false
  have bEq (r : ℕ) (h : r ∈ POS ++ NEG) : b r ∘ σ = b (t r) := funext (fun i => (bits r h i).symm)
  have wEq (r : ℕ) (h : r ∈ POS ++ NEG) : g r = f (t r) := by
    unfold g f
    rw [(eval _).2,upd,bEq r h]
  have h6 : 6 ∈ POS ++ NEG := by decide
  have h12 : 12 ∈ POS ++ NEG := by decide
  have fires : g 6 = true ∨ g 12 = true := by
    rcases hk with h|h
    · left; rw [wEq _ h6,show t 6=p from h,hit]
    · right; rw [wEq _ h12,show t 12=p from h,hit]
  have zsub : ∀ n ∈ ZERO, n ∈ NEG := by decide
  obtain ⟨a,ha,bad⟩ := active D v okD (szD ▸ size) ⟨nz,lt,reads⟩ fires
    (fun n hn => (wEq n (List.mem_append_right _ (zsub n hn))).trans (zero _ (zz n hn)))
    (fun n hn => by rw [(eval _).1,bEq n (List.mem_append_right _ hn)]; exact neg _ (nn n hn))
  have mem := List.mem_append_left NEG ha
  change circuitFun 10 D (Function.update (b a) 0 (b a 0 || g a)) = false at bad
  rw [(eval _).1,upd,bEq a mem,wEq a mem] at bad
  have hb : b (t a) 0 = b a 0 := (bits a mem 0).trans (congrArg (b a) fix)
  rw [← hb] at bad
  have yes := good.1 _ (pp a ha)
  change circuitFun 10 C (Function.update (b (t a)) 0 (b (t a) 0 || f (t a))) = true at yes
  simp [yes] at bad
''')
(d/'R_meta_7893_1.lean').write_text(src)
