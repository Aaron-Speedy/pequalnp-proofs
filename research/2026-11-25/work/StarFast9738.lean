import MonoPin9738
import PEqualNP.Defs
open PEqualNP.Outside.MonoPin9738
namespace PEqualNP.Outside.Graph9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def edges : List (Fin 25 × Fin 25) := [(0,16),(0,22),(0,24),(1,13),(1,17),(1,23),(2,13),(2,14),(2,18),(2,24),(3,14),(3,15),(3,19),(4,13),(4,15),(4,16),(4,20),(5,14),(5,16),(5,17),(5,21),(6,15),(6,17),(6,18),(6,22),(7,16),(7,18),(7,19),(7,23),(8,17),(8,19),(8,20),(8,24),(9,18),(9,20),(9,21),(10,13),(10,19),(10,21),(10,22),(11,14),(11,20),(11,22),(11,23),(12,15),(12,21),(12,23),(12,24)]
def original : List (ℕ × ℕ) := [(0,16),(0,22),(0,24),(1,13),(1,17),(1,23),(2,13),(2,14),(2,18),(2,24),(3,14),(3,15),(3,19),(4,13),(4,15),(4,16),(4,20),(5,14),(5,16),(5,17),(5,21),(6,15),(6,17),(6,18),(6,22),(7,16),(7,18),(7,19),(7,23),(8,17),(8,19),(8,20),(8,24),(9,18),(9,20),(9,21),(10,13),(10,19),(10,21),(10,22),(11,14),(11,20),(11,22),(11,23),(12,15),(12,21),(12,23),(12,24)]
def C : Circuit := ⟨[⟨.or,[1,2]⟩,
⟨.or,[4,10]⟩,
⟨.or,[25,26]⟩,
⟨.and,[13,27]⟩,
⟨.or,[2,3]⟩,
⟨.or,[5,11]⟩,
⟨.or,[29,30]⟩,
⟨.and,[14,31]⟩,
⟨.or,[3,4]⟩,
⟨.or,[6,12]⟩,
⟨.or,[33,34]⟩,
⟨.and,[15,35]⟩,
⟨.or,[0,4]⟩,
⟨.or,[5,7]⟩,
⟨.or,[37,38]⟩,
⟨.and,[16,39]⟩,
⟨.or,[1,5]⟩,
⟨.or,[6,8]⟩,
⟨.or,[41,42]⟩,
⟨.and,[17,43]⟩,
⟨.or,[2,6]⟩,
⟨.or,[7,9]⟩,
⟨.or,[45,46]⟩,
⟨.and,[18,47]⟩,
⟨.or,[3,7]⟩,
⟨.or,[8,10]⟩,
⟨.or,[49,50]⟩,
⟨.and,[19,51]⟩,
⟨.or,[4,8]⟩,
⟨.or,[9,11]⟩,
⟨.or,[53,54]⟩,
⟨.and,[20,55]⟩,
⟨.or,[5,9]⟩,
⟨.or,[10,12]⟩,
⟨.or,[57,58]⟩,
⟨.and,[21,59]⟩,
⟨.or,[0,6]⟩,
⟨.or,[10,11]⟩,
⟨.or,[61,62]⟩,
⟨.and,[22,63]⟩,
⟨.or,[1,7]⟩,
⟨.or,[11,12]⟩,
⟨.or,[65,66]⟩,
⟨.and,[23,67]⟩,
⟨.or,[0,2]⟩,
⟨.or,[8,12]⟩,
⟨.or,[69,70]⟩,
⟨.and,[24,71]⟩,
⟨.or,[28,32]⟩,
⟨.or,[36,40]⟩,
⟨.or,[44,48]⟩,
⟨.or,[52,56]⟩,
⟨.or,[60,64]⟩,
⟨.or,[68,72]⟩,
⟨.or,[73,74]⟩,
⟨.or,[75,76]⟩,
⟨.or,[77,78]⟩,
⟨.or,[79,80]⟩,
⟨.or,[82,81]⟩],83⟩
theorem size : C.size = 59 := by decide
theorem mono : Monotone2 C := by simp [Monotone2,C]
def val (x : Fin 25 → Bool) (w : ℕ) := (run C.gates (List.ofFn x)).getD w false
theorem val_input (x : Fin 25 → Bool) (i : Fin 25) : val x i = x i := by
  unfold val
  rw [run_input _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
theorem step_or (x : Fin 25 → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (h : C.gates[j] = ⟨.or,[a,b]⟩) (ha : a < 25+j) (hb : b < 25+j) :
    val x (25+j) = (val x a || val x b) := by
  have z := run_gate C.gates (List.ofFn x) j hj
  simpa [val,h,GateOp.eval,ha,hb] using z
theorem step_and (x : Fin 25 → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (h : C.gates[j] = ⟨.and,[a,b]⟩) (ha : a < 25+j) (hb : b < 25+j) :
    val x (25+j) = (val x a && val x b) := by
  have z := run_gate C.gates (List.ofFn x) j hj
  simpa [val,h,GateOp.eval,ha,hb] using z
set_option maxRecDepth 18000 in
set_option maxHeartbeats 3000000 in
theorem evalStars (x : Fin 25 → Bool) : C.eval (List.ofFn x) = edges.any (fun p => x p.1 && x p.2) := by
  have h0 : val x 0 = x 0 := val_input x (0 : Fin 25)
  have h1 : val x 1 = x 1 := val_input x (1 : Fin 25)
  have h2 : val x 2 = x 2 := val_input x (2 : Fin 25)
  have h3 : val x 3 = x 3 := val_input x (3 : Fin 25)
  have h4 : val x 4 = x 4 := val_input x (4 : Fin 25)
  have h5 : val x 5 = x 5 := val_input x (5 : Fin 25)
  have h6 : val x 6 = x 6 := val_input x (6 : Fin 25)
  have h7 : val x 7 = x 7 := val_input x (7 : Fin 25)
  have h8 : val x 8 = x 8 := val_input x (8 : Fin 25)
  have h9 : val x 9 = x 9 := val_input x (9 : Fin 25)
  have h10 : val x 10 = x 10 := val_input x (10 : Fin 25)
  have h11 : val x 11 = x 11 := val_input x (11 : Fin 25)
  have h12 : val x 12 = x 12 := val_input x (12 : Fin 25)
  have h13 : val x 13 = x 13 := val_input x (13 : Fin 25)
  have h14 : val x 14 = x 14 := val_input x (14 : Fin 25)
  have h15 : val x 15 = x 15 := val_input x (15 : Fin 25)
  have h16 : val x 16 = x 16 := val_input x (16 : Fin 25)
  have h17 : val x 17 = x 17 := val_input x (17 : Fin 25)
  have h18 : val x 18 = x 18 := val_input x (18 : Fin 25)
  have h19 : val x 19 = x 19 := val_input x (19 : Fin 25)
  have h20 : val x 20 = x 20 := val_input x (20 : Fin 25)
  have h21 : val x 21 = x 21 := val_input x (21 : Fin 25)
  have h22 : val x 22 = x 22 := val_input x (22 : Fin 25)
  have h23 : val x 23 = x 23 := val_input x (23 : Fin 25)
  have h24 : val x 24 = x 24 := val_input x (24 : Fin 25)
  have h25 := step_or x 0 1 2 (by decide) rfl (by decide) (by decide)
  change val x 25 = _ at h25
  have h26 := step_or x 1 4 10 (by decide) rfl (by decide) (by decide)
  change val x 26 = _ at h26
  have h27 := step_or x 2 25 26 (by decide) rfl (by decide) (by decide)
  change val x 27 = _ at h27
  have h28 := step_and x 3 13 27 (by decide) rfl (by decide) (by decide)
  change val x 28 = _ at h28
  have h29 := step_or x 4 2 3 (by decide) rfl (by decide) (by decide)
  change val x 29 = _ at h29
  have h30 := step_or x 5 5 11 (by decide) rfl (by decide) (by decide)
  change val x 30 = _ at h30
  have h31 := step_or x 6 29 30 (by decide) rfl (by decide) (by decide)
  change val x 31 = _ at h31
  have h32 := step_and x 7 14 31 (by decide) rfl (by decide) (by decide)
  change val x 32 = _ at h32
  have h33 := step_or x 8 3 4 (by decide) rfl (by decide) (by decide)
  change val x 33 = _ at h33
  have h34 := step_or x 9 6 12 (by decide) rfl (by decide) (by decide)
  change val x 34 = _ at h34
  have h35 := step_or x 10 33 34 (by decide) rfl (by decide) (by decide)
  change val x 35 = _ at h35
  have h36 := step_and x 11 15 35 (by decide) rfl (by decide) (by decide)
  change val x 36 = _ at h36
  have h37 := step_or x 12 0 4 (by decide) rfl (by decide) (by decide)
  change val x 37 = _ at h37
  have h38 := step_or x 13 5 7 (by decide) rfl (by decide) (by decide)
  change val x 38 = _ at h38
  have h39 := step_or x 14 37 38 (by decide) rfl (by decide) (by decide)
  change val x 39 = _ at h39
  have h40 := step_and x 15 16 39 (by decide) rfl (by decide) (by decide)
  change val x 40 = _ at h40
  have h41 := step_or x 16 1 5 (by decide) rfl (by decide) (by decide)
  change val x 41 = _ at h41
  have h42 := step_or x 17 6 8 (by decide) rfl (by decide) (by decide)
  change val x 42 = _ at h42
  have h43 := step_or x 18 41 42 (by decide) rfl (by decide) (by decide)
  change val x 43 = _ at h43
  have h44 := step_and x 19 17 43 (by decide) rfl (by decide) (by decide)
  change val x 44 = _ at h44
  have h45 := step_or x 20 2 6 (by decide) rfl (by decide) (by decide)
  change val x 45 = _ at h45
  have h46 := step_or x 21 7 9 (by decide) rfl (by decide) (by decide)
  change val x 46 = _ at h46
  have h47 := step_or x 22 45 46 (by decide) rfl (by decide) (by decide)
  change val x 47 = _ at h47
  have h48 := step_and x 23 18 47 (by decide) rfl (by decide) (by decide)
  change val x 48 = _ at h48
  have h49 := step_or x 24 3 7 (by decide) rfl (by decide) (by decide)
  change val x 49 = _ at h49
  have h50 := step_or x 25 8 10 (by decide) rfl (by decide) (by decide)
  change val x 50 = _ at h50
  have h51 := step_or x 26 49 50 (by decide) rfl (by decide) (by decide)
  change val x 51 = _ at h51
  have h52 := step_and x 27 19 51 (by decide) rfl (by decide) (by decide)
  change val x 52 = _ at h52
  have h53 := step_or x 28 4 8 (by decide) rfl (by decide) (by decide)
  change val x 53 = _ at h53
  have h54 := step_or x 29 9 11 (by decide) rfl (by decide) (by decide)
  change val x 54 = _ at h54
  have h55 := step_or x 30 53 54 (by decide) rfl (by decide) (by decide)
  change val x 55 = _ at h55
  have h56 := step_and x 31 20 55 (by decide) rfl (by decide) (by decide)
  change val x 56 = _ at h56
  have h57 := step_or x 32 5 9 (by decide) rfl (by decide) (by decide)
  change val x 57 = _ at h57
  have h58 := step_or x 33 10 12 (by decide) rfl (by decide) (by decide)
  change val x 58 = _ at h58
  have h59 := step_or x 34 57 58 (by decide) rfl (by decide) (by decide)
  change val x 59 = _ at h59
  have h60 := step_and x 35 21 59 (by decide) rfl (by decide) (by decide)
  change val x 60 = _ at h60
  have h61 := step_or x 36 0 6 (by decide) rfl (by decide) (by decide)
  change val x 61 = _ at h61
  have h62 := step_or x 37 10 11 (by decide) rfl (by decide) (by decide)
  change val x 62 = _ at h62
  have h63 := step_or x 38 61 62 (by decide) rfl (by decide) (by decide)
  change val x 63 = _ at h63
  have h64 := step_and x 39 22 63 (by decide) rfl (by decide) (by decide)
  change val x 64 = _ at h64
  have h65 := step_or x 40 1 7 (by decide) rfl (by decide) (by decide)
  change val x 65 = _ at h65
  have h66 := step_or x 41 11 12 (by decide) rfl (by decide) (by decide)
  change val x 66 = _ at h66
  have h67 := step_or x 42 65 66 (by decide) rfl (by decide) (by decide)
  change val x 67 = _ at h67
  have h68 := step_and x 43 23 67 (by decide) rfl (by decide) (by decide)
  change val x 68 = _ at h68
  have h69 := step_or x 44 0 2 (by decide) rfl (by decide) (by decide)
  change val x 69 = _ at h69
  have h70 := step_or x 45 8 12 (by decide) rfl (by decide) (by decide)
  change val x 70 = _ at h70
  have h71 := step_or x 46 69 70 (by decide) rfl (by decide) (by decide)
  change val x 71 = _ at h71
  have h72 := step_and x 47 24 71 (by decide) rfl (by decide) (by decide)
  change val x 72 = _ at h72
  have h73 := step_or x 48 28 32 (by decide) rfl (by decide) (by decide)
  change val x 73 = _ at h73
  have h74 := step_or x 49 36 40 (by decide) rfl (by decide) (by decide)
  change val x 74 = _ at h74
  have h75 := step_or x 50 44 48 (by decide) rfl (by decide) (by decide)
  change val x 75 = _ at h75
  have h76 := step_or x 51 52 56 (by decide) rfl (by decide) (by decide)
  change val x 76 = _ at h76
  have h77 := step_or x 52 60 64 (by decide) rfl (by decide) (by decide)
  change val x 77 = _ at h77
  have h78 := step_or x 53 68 72 (by decide) rfl (by decide) (by decide)
  change val x 78 = _ at h78
  have h79 := step_or x 54 73 74 (by decide) rfl (by decide) (by decide)
  change val x 79 = _ at h79
  have h80 := step_or x 55 75 76 (by decide) rfl (by decide) (by decide)
  change val x 80 = _ at h80
  have h81 := step_or x 56 77 78 (by decide) rfl (by decide) (by decide)
  change val x 81 = _ at h81
  have h82 := step_or x 57 79 80 (by decide) rfl (by decide) (by decide)
  change val x 82 = _ at h82
  have h83 := step_or x 58 82 81 (by decide) rfl (by decide) (by decide)
  change val x 83 = _ at h83
  change val x 83 = _
  simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53,h54,h55,h56,h57,h58,h59,h60,h61,h62,h63,h64,h65,h66,h67,h68,h69,h70,h71,h72,h73,h74,h75,h76,h77,h78,h79,h80,h81,h82,h83]
  simp [edges,Bool.and_or_distrib_left,Bool.or_assoc]
  all_goals ac_rfl
theorem exactEdges (x : Fin 25 → Bool) : C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 25, (u.val,v.val) ∈ original ∧ x u = true ∧ x v = true := by
  have mapEq : edges.map (fun p => (p.1.val,p.2.val)) = original := by decide
  rw [evalStars,List.any_eq_true]
  constructor
  · rintro ⟨⟨u,v⟩,h,p⟩
    exact ⟨u,v,mapEq ▸ List.mem_map.mpr ⟨(u,v),h,rfl⟩,by simpa using p⟩
  · rintro ⟨u,v,h,p,q⟩
    rw [← mapEq] at h
    obtain ⟨⟨i,j⟩,mem,eq⟩ := List.mem_map.mp h
    have a : i = u := Fin.ext (congrArg Prod.fst eq)
    have b : j = v := Fin.ext (congrArg Prod.snd eq)
    exact ⟨(i,j),mem,by simp [a,b,p,q]⟩
theorem sideDegrees : C.lineDeg 25 (Finset.range 13) = 1 ∧ C.lineDeg 25 (Finset.Ico 13 25) = 1 := by decide +kernel
end PEqualNP.Outside.Graph9738
#print axioms PEqualNP.Outside.Graph9738.exactEdges
