import MonoPin9738
namespace PEqualNP.Outside.Lower9738
open PEqualNP.Outside.MonoPin9738 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f0 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 1 && x 13) || (x 1 && x 17) || (x 1 && x 23) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 5 && x 14) || (x 5 && x 16) || (x 5 && x 17) || (x 5 && x 21) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 8 && x 17) || (x 8 && x 19) || (x 8 && x 20) || (x 8 && x 24) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23) || (x 12 && x 15) || (x 12 && x 21) || (x 12 && x 23) || (x 12 && x 24)
def f1 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 5 && x 14) || (x 5 && x 16) || (x 5 && x 17) || (x 5 && x 21) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 8 && x 17) || (x 8 && x 19) || (x 8 && x 20) || (x 8 && x 24) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23) || (x 12 && x 15) || (x 12 && x 21) || (x 12 && x 23) || (x 12 && x 24)
def f2 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 8 && x 17) || (x 8 && x 19) || (x 8 && x 20) || (x 8 && x 24) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23) || (x 12 && x 15) || (x 12 && x 21) || (x 12 && x 23) || (x 12 && x 24)
def f3 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23) || (x 12 && x 15) || (x 12 && x 21) || (x 12 && x 23) || (x 12 && x 24)
def f4 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23) || (x 12 && x 15) || (x 12 && x 21) || (x 12 && x 23) || (x 12 && x 24)
def f5 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 12 && x 15) || (x 12 && x 21) || (x 12 && x 23) || (x 12 && x 24)
def f6 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22)
def f7 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22)
def f8 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 6 && x 15) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22)
def f9 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 6 && x 15) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22)
def f10 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 6 && x 15) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 22)
def f11 (x : Fin 25 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 2 && x 13) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 6 && x 15) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 22)
def hostEdges : List (Fin 25 × Fin 25) := [(0,16),(0,22),(0,24),(1,13),(1,17),(1,23),(2,13),(2,14),(2,18),(2,24),(3,14),(3,15),(3,19),(4,13),(4,15),(4,16),(4,20),(5,14),(5,16),(5,17),(5,21),(6,15),(6,17),(6,18),(6,22),(7,16),(7,18),(7,19),(7,23),(8,17),(8,19),(8,20),(8,24),(9,18),(9,20),(9,21),(10,13),(10,19),(10,21),(10,22),(11,14),(11,20),(11,22),(11,23),(12,15),(12,21),(12,23),(12,24)]
theorem hostSpec (x : Fin 25 → Bool) : f0 x = true ↔
    ∃ u v : Fin 25, (u.val,v.val) ∈ ([(0,16),(0,22),(0,24),(1,13),(1,17),(1,23),(2,13),(2,14),(2,18),(2,24),(3,14),(3,15),(3,19),(4,13),(4,15),(4,16),(4,20),(5,14),(5,16),(5,17),(5,21),(6,15),(6,17),(6,18),(6,22),(7,16),(7,18),(7,19),(7,23),(8,17),(8,19),(8,20),(8,24),(9,18),(9,20),(9,21),(10,13),(10,19),(10,21),(10,22),(11,14),(11,20),(11,22),(11,23),(12,15),(12,21),(12,23),(12,24)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
  have same : f0 x = hostEdges.any (fun p => x p.1 && x p.2) := by
    simp [f0,hostEdges,Bool.or_assoc]
  have mapEq : hostEdges.map (fun p => (p.1.val,p.2.val)) = [(0,16),(0,22),(0,24),(1,13),(1,17),(1,23),(2,13),(2,14),(2,18),(2,24),(3,14),(3,15),(3,19),(4,13),(4,15),(4,16),(4,20),(5,14),(5,16),(5,17),(5,21),(6,15),(6,17),(6,18),(6,22),(7,16),(7,18),(7,19),(7,23),(8,17),(8,19),(8,20),(8,24),(9,18),(9,20),(9,21),(10,13),(10,19),(10,21),(10,22),(11,14),(11,20),(11,22),(11,23),(12,15),(12,21),(12,23),(12,24)] := by decide
  rw [same,List.any_eq_true,← mapEq]
  constructor
  · rintro ⟨⟨u,v⟩,h,p⟩
    exact ⟨u,v,List.mem_map.mpr ⟨(u,v),h,rfl⟩,by simpa using p⟩
  · rintro ⟨u,v,h,p,q⟩
    obtain ⟨⟨i,j⟩,mem,eq⟩ := List.mem_map.mp h
    have a : i=u := Fin.ext (congrArg Prod.fst eq)
    have b : j=v := Fin.ext (congrArg Prod.snd eq)
    exact ⟨(i,j),mem,by simp [a,b,p,q]⟩
def target (x : Fin 14 → Bool) : Bool := (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def lowEdges : List (Fin 14 × Fin 14) := [(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
theorem lowSpec (x : Fin 14 → Bool) : target x = true ↔
    ∃ u v : Fin 14, (u.val,v.val) ∈ ([(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
  have same : target x = lowEdges.any (fun p => x p.1 && x p.2) := by
    simp [target,lowEdges,Bool.or_assoc]
  have mapEq : lowEdges.map (fun p => (p.1.val,p.2.val)) = [(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] := by decide
  rw [same,List.any_eq_true,← mapEq]
  constructor
  · rintro ⟨⟨u,v⟩,h,p⟩
    exact ⟨u,v,List.mem_map.mpr ⟨(u,v),h,rfl⟩,by simpa using p⟩
  · rintro ⟨u,v,h,p,q⟩
    obtain ⟨⟨i,j⟩,mem,eq⟩ := List.mem_map.mp h
    have a : i=u := Fin.ext (congrArg Prod.fst eq)
    have b : j=v := Fin.ext (congrArg Prod.snd eq)
    exact ⟨(i,j),mem,by simp [a,b,p,q]⟩
theorem step0 (s : ℕ) (h : MSize 25 f0 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f1 t := by
  apply pin f0 f1 1 (fun j => decide (j = 13)) (fun j => decide (j = 13 ∨ j = 1))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f0,f1,Function.update, Bool.or_assoc]
theorem step1 (s : ℕ) (h : MSize 25 f1 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f2 t := by
  apply pin f1 f2 5 (fun j => decide (j = 16)) (fun j => decide (j = 16 ∨ j = 5))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f1,f2,Function.update, Bool.or_assoc]
theorem step2 (s : ℕ) (h : MSize 25 f2 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f3 t := by
  apply pin f2 f3 8 (fun j => decide (j = 19)) (fun j => decide (j = 19 ∨ j = 8))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f2,f3,Function.update, Bool.or_assoc]
theorem step3 (s : ℕ) (h : MSize 25 f3 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f4 t := by
  apply pin f3 f4 9 (fun j => decide (j = 18)) (fun j => decide (j = 18 ∨ j = 9))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f3,f4,Function.update, Bool.or_assoc]
theorem step4 (s : ℕ) (h : MSize 25 f4 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f5 t := by
  apply pin f4 f5 11 (fun j => decide (j = 22)) (fun j => decide (j = 22 ∨ j = 11))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f4,f5,Function.update, Bool.or_assoc]
theorem step5 (s : ℕ) (h : MSize 25 f5 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f6 t := by
  apply pin f5 f6 12 (fun j => decide (j = 15)) (fun j => decide (j = 15 ∨ j = 12))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f5,f6,Function.update, Bool.or_assoc]
theorem step6 (s : ℕ) (h : MSize 25 f6 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f7 t := by
  apply pin f6 f7 14 (fun j => decide (j = 2)) (fun j => decide (j = 2 ∨ j = 14))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f6,f7,Function.update, Bool.or_assoc]
theorem step7 (s : ℕ) (h : MSize 25 f7 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f8 t := by
  apply pin f7 f8 17 (fun j => decide (j = 6)) (fun j => decide (j = 6 ∨ j = 17))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f7,f8,Function.update, Bool.or_assoc]
theorem step8 (s : ℕ) (h : MSize 25 f8 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f9 t := by
  apply pin f8 f9 20 (fun j => decide (j = 4)) (fun j => decide (j = 4 ∨ j = 20))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f8,f9,Function.update, Bool.or_assoc]
theorem step9 (s : ℕ) (h : MSize 25 f9 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f10 t := by
  apply pin f9 f10 21 (fun j => decide (j = 10)) (fun j => decide (j = 10 ∨ j = 21))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f9,f10,Function.update, Bool.or_assoc]
theorem step10 (s : ℕ) (h : MSize 25 f10 s) : ∃ t, t+1 ≤ s ∧ MSize 25 f11 t := by
  apply pin f10 f11 23 (fun j => decide (j = 7)) (fun j => decide (j = 7 ∨ j = 23))
    (fun _ => false) (fun j => decide (j = 0 ∨ j = 16)) _ _ _ _ h
  · intro j hj; simp [hj]
  · decide
  · decide
  · intro y; simp [f10,f11,Function.update, Bool.or_assoc]
def renameV (i : Fin 25) : Fin 14 := (![1,0,3,0,6,0,2,5,0,0,4,0,0,11,0,8,9,0,12,10,0,0,13,0,7] : Fin 25 → Fin 14) i
theorem renameOK (x : Fin 14 → Bool) : f11 (x ∘ renameV) = target x := by
  change ((x 1 && x 9) || (x 1 && x 13) || (x 1 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 3 && x 7) || (x 0 && x 8) || (x 0 && x 10) || (x 6 && x 11) || (x 6 && x 8) || (x 6 && x 9) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 5 && x 9) || (x 5 && x 12) || (x 5 && x 10) || (x 4 && x 11) || (x 4 && x 10) || (x 4 && x 13)) = _
  simp only [target,Bool.or_assoc]
  all_goals ac_rfl
theorem transfer (known : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 25 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))))) : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 36 ∧ (∀ x : Fin 25 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 25, (u.val, v.val) ∈ ([(0, 16), (0, 22), (0, 24), (1, 13), (1, 17), (1, 23), (2, 13), (2, 14), (2, 18), (2, 24), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 17), (8, 19), (8, 20), (8, 24), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23), (12, 15), (12, 21), (12, 23), (12, 24)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)))) := by
  rintro ⟨C,mono,size,ev⟩
  have h0 : MSize 25 f0 C.size := ⟨C,mono,le_rfl,fun x => Bool.eq_iff_iff.mpr ((ev x).trans (hostSpec x).symm)⟩
  obtain ⟨s1,size1,h1⟩ := step0 _ h0
  obtain ⟨s2,size2,h2⟩ := step1 _ h1
  obtain ⟨s3,size3,h3⟩ := step2 _ h2
  obtain ⟨s4,size4,h4⟩ := step3 _ h3
  obtain ⟨s5,size5,h5⟩ := step4 _ h4
  obtain ⟨s6,size6,h6⟩ := step5 _ h5
  obtain ⟨s7,size7,h7⟩ := step6 _ h6
  obtain ⟨s8,size8,h8⟩ := step7 _ h7
  obtain ⟨s9,size9,h9⟩ := step8 _ h8
  obtain ⟨s10,size10,h10⟩ := step9 _ h9
  obtain ⟨s11,size11,h11⟩ := step10 _ h10
  obtain ⟨D,hm,hs,he⟩ := relabel_size renameV f11 s11 h11
  apply known
  exact ⟨D,hm,by omega,fun x => by rw [he]; exact (show f11 (x ∘ renameV) = true ↔ _ by rw [renameOK,lowSpec])⟩
end PEqualNP.Outside.Lower9738
#print axioms PEqualNP.Outside.Lower9738.transfer
