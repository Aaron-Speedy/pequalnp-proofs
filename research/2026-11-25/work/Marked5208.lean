import MonoPin9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.MonoPin9738 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
namespace Marked5208
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def D : Finset (Fin 13) := {0,1,3,9}
def edges : List (Fin 13 × Fin 13) := [(0,0),(0,4),(0,10),(0,12),(1,0),(1,1),(1,5),(1,11),(2,1),(2,2),(2,6),(2,12),(3,0),(3,2),(3,3),(3,7),(4,1),(4,3),(4,4),(4,8),(5,2),(5,4),(5,5),(5,9),(6,3),(6,5),(6,6),(6,10),(7,4),(7,6),(7,7),(7,11),(8,5),(8,7),(8,8),(8,12),(9,0),(9,6),(9,8),(9,9),(10,1),(10,7),(10,9),(10,10),(11,2),(11,8),(11,10),(11,11),(12,3),(12,9),(12,11),(12,12)]
def C : Circuit := ⟨[⟨.or,[13,14]⟩,
⟨.or,[18,24]⟩,
⟨.or,[26,27]⟩,
⟨.and,[1,28]⟩,
⟨.and,[13,26]⟩,
⟨.or,[30,17]⟩,
⟨.or,[23,25]⟩,
⟨.or,[31,32]⟩,
⟨.and,[0,33]⟩,
⟨.and,[0,34]⟩,
⟨.or,[14,15]⟩,
⟨.or,[19,25]⟩,
⟨.or,[36,37]⟩,
⟨.and,[2,38]⟩,
⟨.or,[13,15]⟩,
⟨.or,[16,20]⟩,
⟨.or,[40,41]⟩,
⟨.and,[3,42]⟩,
⟨.or,[14,16]⟩,
⟨.or,[17,21]⟩,
⟨.or,[44,45]⟩,
⟨.and,[4,46]⟩,
⟨.or,[15,17]⟩,
⟨.or,[18,22]⟩,
⟨.or,[48,49]⟩,
⟨.and,[5,50]⟩,
⟨.or,[16,18]⟩,
⟨.or,[19,23]⟩,
⟨.or,[52,53]⟩,
⟨.and,[6,54]⟩,
⟨.or,[17,19]⟩,
⟨.or,[20,24]⟩,
⟨.or,[56,57]⟩,
⟨.and,[7,58]⟩,
⟨.or,[18,20]⟩,
⟨.or,[21,25]⟩,
⟨.or,[60,61]⟩,
⟨.and,[8,62]⟩,
⟨.or,[13,19]⟩,
⟨.or,[21,22]⟩,
⟨.or,[64,65]⟩,
⟨.and,[9,66]⟩,
⟨.or,[14,20]⟩,
⟨.or,[22,23]⟩,
⟨.or,[68,69]⟩,
⟨.and,[10,70]⟩,
⟨.or,[15,21]⟩,
⟨.or,[23,24]⟩,
⟨.or,[72,73]⟩,
⟨.and,[11,74]⟩,
⟨.or,[16,22]⟩,
⟨.or,[24,25]⟩,
⟨.or,[76,77]⟩,
⟨.and,[12,78]⟩,
⟨.or,[35,29]⟩,
⟨.or,[80,39]⟩,
⟨.or,[81,43]⟩,
⟨.or,[82,47]⟩,
⟨.or,[83,51]⟩,
⟨.or,[84,55]⟩,
⟨.or,[85,59]⟩,
⟨.or,[86,63]⟩,
⟨.or,[87,67]⟩,
⟨.or,[88,71]⟩,
⟨.or,[89,75]⟩,
⟨.or,[90,79]⟩],91⟩
def val (x : Fin 26 → Bool) (w : ℕ) := (run C.gates (List.ofFn x)).getD w false
theorem val_input (x : Fin 26 → Bool) (i : Fin 26) : val x i = x i := by
  unfold val
  rw [run_input _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
theorem step_or (x : Fin 26 → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (h : C.gates[j] = ⟨.or,[a,b]⟩) (ha : a < 26+j) (hb : b < 26+j) :
    val x (26+j) = (val x a || val x b) := by
  have z := run_gate C.gates (List.ofFn x) j hj
  simpa [val,h,GateOp.eval,ha,hb] using z
theorem step_and (x : Fin 26 → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (h : C.gates[j] = ⟨.and,[a,b]⟩) (ha : a < 26+j) (hb : b < 26+j) :
    val x (26+j) = (val x a && val x b) := by
  have z := run_gate C.gates (List.ofFn x) j hj
  simpa [val,h,GateOp.eval,ha,hb] using z
theorem evalu (x : Fin 26 → Bool) : val x 91 = edges.any (fun e => x (Fin.castAdd 13 e.1) && x (Fin.natAdd 13 e.2)) := by
  have h0 : val x 0 = x 0 := val_input x (0 : Fin 26)
  have h1 : val x 1 = x 1 := val_input x (1 : Fin 26)
  have h2 : val x 2 = x 2 := val_input x (2 : Fin 26)
  have h3 : val x 3 = x 3 := val_input x (3 : Fin 26)
  have h4 : val x 4 = x 4 := val_input x (4 : Fin 26)
  have h5 : val x 5 = x 5 := val_input x (5 : Fin 26)
  have h6 : val x 6 = x 6 := val_input x (6 : Fin 26)
  have h7 : val x 7 = x 7 := val_input x (7 : Fin 26)
  have h8 : val x 8 = x 8 := val_input x (8 : Fin 26)
  have h9 : val x 9 = x 9 := val_input x (9 : Fin 26)
  have h10 : val x 10 = x 10 := val_input x (10 : Fin 26)
  have h11 : val x 11 = x 11 := val_input x (11 : Fin 26)
  have h12 : val x 12 = x 12 := val_input x (12 : Fin 26)
  have h13 : val x 13 = x 13 := val_input x (13 : Fin 26)
  have h14 : val x 14 = x 14 := val_input x (14 : Fin 26)
  have h15 : val x 15 = x 15 := val_input x (15 : Fin 26)
  have h16 : val x 16 = x 16 := val_input x (16 : Fin 26)
  have h17 : val x 17 = x 17 := val_input x (17 : Fin 26)
  have h18 : val x 18 = x 18 := val_input x (18 : Fin 26)
  have h19 : val x 19 = x 19 := val_input x (19 : Fin 26)
  have h20 : val x 20 = x 20 := val_input x (20 : Fin 26)
  have h21 : val x 21 = x 21 := val_input x (21 : Fin 26)
  have h22 : val x 22 = x 22 := val_input x (22 : Fin 26)
  have h23 : val x 23 = x 23 := val_input x (23 : Fin 26)
  have h24 : val x 24 = x 24 := val_input x (24 : Fin 26)
  have h25 : val x 25 = x 25 := val_input x (25 : Fin 26)
  have h26 := step_or x 0 13 14 (by decide) rfl (by decide) (by decide)
  change val x 26 = _ at h26
  have h27 := step_or x 1 18 24 (by decide) rfl (by decide) (by decide)
  change val x 27 = _ at h27
  have h28 := step_or x 2 26 27 (by decide) rfl (by decide) (by decide)
  change val x 28 = _ at h28
  have h29 := step_and x 3 1 28 (by decide) rfl (by decide) (by decide)
  change val x 29 = _ at h29
  have h30 := step_and x 4 13 26 (by decide) rfl (by decide) (by decide)
  change val x 30 = _ at h30
  have first : val x 30 = x 13 := by rw [h30,h26,h13,h14]; cases x 13 <;> rfl
  have h31 := step_or x 5 30 17 (by decide) rfl (by decide) (by decide)
  change val x 31 = _ at h31
  have h32 := step_or x 6 23 25 (by decide) rfl (by decide) (by decide)
  change val x 32 = _ at h32
  have h33 := step_or x 7 31 32 (by decide) rfl (by decide) (by decide)
  change val x 33 = _ at h33
  have h34 := step_and x 8 0 33 (by decide) rfl (by decide) (by decide)
  change val x 34 = _ at h34
  have h35 := step_and x 9 0 34 (by decide) rfl (by decide) (by decide)
  change val x 35 = _ at h35
  have second : val x 35 = val x 34 := by rw [h35,h34,h0]; cases x 0 <;> rfl
  have h36 := step_or x 10 14 15 (by decide) rfl (by decide) (by decide)
  change val x 36 = _ at h36
  have h37 := step_or x 11 19 25 (by decide) rfl (by decide) (by decide)
  change val x 37 = _ at h37
  have h38 := step_or x 12 36 37 (by decide) rfl (by decide) (by decide)
  change val x 38 = _ at h38
  have h39 := step_and x 13 2 38 (by decide) rfl (by decide) (by decide)
  change val x 39 = _ at h39
  have h40 := step_or x 14 13 15 (by decide) rfl (by decide) (by decide)
  change val x 40 = _ at h40
  have h41 := step_or x 15 16 20 (by decide) rfl (by decide) (by decide)
  change val x 41 = _ at h41
  have h42 := step_or x 16 40 41 (by decide) rfl (by decide) (by decide)
  change val x 42 = _ at h42
  have h43 := step_and x 17 3 42 (by decide) rfl (by decide) (by decide)
  change val x 43 = _ at h43
  have h44 := step_or x 18 14 16 (by decide) rfl (by decide) (by decide)
  change val x 44 = _ at h44
  have h45 := step_or x 19 17 21 (by decide) rfl (by decide) (by decide)
  change val x 45 = _ at h45
  have h46 := step_or x 20 44 45 (by decide) rfl (by decide) (by decide)
  change val x 46 = _ at h46
  have h47 := step_and x 21 4 46 (by decide) rfl (by decide) (by decide)
  change val x 47 = _ at h47
  have h48 := step_or x 22 15 17 (by decide) rfl (by decide) (by decide)
  change val x 48 = _ at h48
  have h49 := step_or x 23 18 22 (by decide) rfl (by decide) (by decide)
  change val x 49 = _ at h49
  have h50 := step_or x 24 48 49 (by decide) rfl (by decide) (by decide)
  change val x 50 = _ at h50
  have h51 := step_and x 25 5 50 (by decide) rfl (by decide) (by decide)
  change val x 51 = _ at h51
  have h52 := step_or x 26 16 18 (by decide) rfl (by decide) (by decide)
  change val x 52 = _ at h52
  have h53 := step_or x 27 19 23 (by decide) rfl (by decide) (by decide)
  change val x 53 = _ at h53
  have h54 := step_or x 28 52 53 (by decide) rfl (by decide) (by decide)
  change val x 54 = _ at h54
  have h55 := step_and x 29 6 54 (by decide) rfl (by decide) (by decide)
  change val x 55 = _ at h55
  have h56 := step_or x 30 17 19 (by decide) rfl (by decide) (by decide)
  change val x 56 = _ at h56
  have h57 := step_or x 31 20 24 (by decide) rfl (by decide) (by decide)
  change val x 57 = _ at h57
  have h58 := step_or x 32 56 57 (by decide) rfl (by decide) (by decide)
  change val x 58 = _ at h58
  have h59 := step_and x 33 7 58 (by decide) rfl (by decide) (by decide)
  change val x 59 = _ at h59
  have h60 := step_or x 34 18 20 (by decide) rfl (by decide) (by decide)
  change val x 60 = _ at h60
  have h61 := step_or x 35 21 25 (by decide) rfl (by decide) (by decide)
  change val x 61 = _ at h61
  have h62 := step_or x 36 60 61 (by decide) rfl (by decide) (by decide)
  change val x 62 = _ at h62
  have h63 := step_and x 37 8 62 (by decide) rfl (by decide) (by decide)
  change val x 63 = _ at h63
  have h64 := step_or x 38 13 19 (by decide) rfl (by decide) (by decide)
  change val x 64 = _ at h64
  have h65 := step_or x 39 21 22 (by decide) rfl (by decide) (by decide)
  change val x 65 = _ at h65
  have h66 := step_or x 40 64 65 (by decide) rfl (by decide) (by decide)
  change val x 66 = _ at h66
  have h67 := step_and x 41 9 66 (by decide) rfl (by decide) (by decide)
  change val x 67 = _ at h67
  have h68 := step_or x 42 14 20 (by decide) rfl (by decide) (by decide)
  change val x 68 = _ at h68
  have h69 := step_or x 43 22 23 (by decide) rfl (by decide) (by decide)
  change val x 69 = _ at h69
  have h70 := step_or x 44 68 69 (by decide) rfl (by decide) (by decide)
  change val x 70 = _ at h70
  have h71 := step_and x 45 10 70 (by decide) rfl (by decide) (by decide)
  change val x 71 = _ at h71
  have h72 := step_or x 46 15 21 (by decide) rfl (by decide) (by decide)
  change val x 72 = _ at h72
  have h73 := step_or x 47 23 24 (by decide) rfl (by decide) (by decide)
  change val x 73 = _ at h73
  have h74 := step_or x 48 72 73 (by decide) rfl (by decide) (by decide)
  change val x 74 = _ at h74
  have h75 := step_and x 49 11 74 (by decide) rfl (by decide) (by decide)
  change val x 75 = _ at h75
  have h76 := step_or x 50 16 22 (by decide) rfl (by decide) (by decide)
  change val x 76 = _ at h76
  have h77 := step_or x 51 24 25 (by decide) rfl (by decide) (by decide)
  change val x 77 = _ at h77
  have h78 := step_or x 52 76 77 (by decide) rfl (by decide) (by decide)
  change val x 78 = _ at h78
  have h79 := step_and x 53 12 78 (by decide) rfl (by decide) (by decide)
  change val x 79 = _ at h79
  have h80 := step_or x 54 35 29 (by decide) rfl (by decide) (by decide)
  change val x 80 = _ at h80
  have h81 := step_or x 55 80 39 (by decide) rfl (by decide) (by decide)
  change val x 81 = _ at h81
  have h82 := step_or x 56 81 43 (by decide) rfl (by decide) (by decide)
  change val x 82 = _ at h82
  have h83 := step_or x 57 82 47 (by decide) rfl (by decide) (by decide)
  change val x 83 = _ at h83
  have h84 := step_or x 58 83 51 (by decide) rfl (by decide) (by decide)
  change val x 84 = _ at h84
  have h85 := step_or x 59 84 55 (by decide) rfl (by decide) (by decide)
  change val x 85 = _ at h85
  have h86 := step_or x 60 85 59 (by decide) rfl (by decide) (by decide)
  change val x 86 = _ at h86
  have h87 := step_or x 61 86 63 (by decide) rfl (by decide) (by decide)
  change val x 87 = _ at h87
  have h88 := step_or x 62 87 67 (by decide) rfl (by decide) (by decide)
  change val x 88 = _ at h88
  have h89 := step_or x 63 88 71 (by decide) rfl (by decide) (by decide)
  change val x 89 = _ at h89
  have h90 := step_or x 64 89 75 (by decide) rfl (by decide) (by decide)
  change val x 90 = _ at h90
  have h91 := step_or x 65 90 79 (by decide) rfl (by decide) (by decide)
  change val x 91 = _ at h91
  simp only [first,second,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h31,h32,h33,h34,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53,h54,h55,h56,h57,h58,h59,h60,h61,h62,h63,h64,h65,h66,h67,h68,h69,h70,h71,h72,h73,h74,h75,h76,h77,h78,h79,h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90,h91]
  simp [edges,Bool.and_or_distrib_left,Bool.or_assoc,Fin.natAdd,Fin.castAdd]
theorem semantic (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 13, p-l ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  change val x 91 = true ↔ _
  rw [evalu,List.any_eq_true]
  have inc : ∀ p l : Fin 13, (p,l) ∈ edges ↔ p-l ∈ D := by decide +kernel
  constructor
  · rintro ⟨⟨p,l⟩,e,h⟩
    exact ⟨p,l,(inc p l).mp e,Bool.and_eq_true_iff.mp h⟩
  · rintro ⟨p,l,e,h⟩
    exact ⟨(p,l),(inc p l).mpr e,Bool.and_eq_true_iff.mpr h⟩

end Marked5208
#print axioms Marked5208.semantic
