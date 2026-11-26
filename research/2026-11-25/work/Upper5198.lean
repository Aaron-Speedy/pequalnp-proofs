import Join5198
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.MonoPin9738 PEqualNP.Outside.Join5198
open PEqualNP.HeptadCover PEqualNP.GenericRejection
namespace PEqualNP.Outside.Upper5198
def left : List (Fin 13 × Fin 13) := [(0,0),(0,4),(0,10),(0,12)]
def right : List (Fin 13 × Fin 13) := [(1,0),(1,1),(1,5),(1,11),(2,1),(2,2),(2,6),(2,12),(3,0),(3,2),(3,3),(3,7),(4,1),(4,3),(4,4),(4,8),(5,2),(5,4),(5,5),(5,9),(6,3),(6,5),(6,6),(6,10),(7,4),(7,6),(7,7),(7,11),(8,5),(8,7),(8,8),(8,12),(9,0),(9,6),(9,8),(9,9),(10,1),(10,7),(10,9),(10,10),(11,2),(11,8),(11,10),(11,11),(12,3),(12,9),(12,11),(12,12)]
def C : Circuit := ⟨[⟨.or,[13,17]⟩,
⟨.or,[23,25]⟩,
⟨.or,[26,27]⟩,
⟨.and,[0,28]⟩,
⟨.or,[13,14]⟩,
⟨.or,[18,24]⟩,
⟨.or,[30,31]⟩,
⟨.and,[1,32]⟩,
⟨.or,[14,15]⟩,
⟨.or,[19,25]⟩,
⟨.or,[34,35]⟩,
⟨.and,[2,36]⟩,
⟨.or,[13,15]⟩,
⟨.or,[16,20]⟩,
⟨.or,[38,39]⟩,
⟨.and,[3,40]⟩,
⟨.or,[14,16]⟩,
⟨.or,[17,21]⟩,
⟨.or,[42,43]⟩,
⟨.and,[4,44]⟩,
⟨.or,[15,17]⟩,
⟨.or,[18,22]⟩,
⟨.or,[46,47]⟩,
⟨.and,[5,48]⟩,
⟨.or,[16,18]⟩,
⟨.or,[19,23]⟩,
⟨.or,[50,51]⟩,
⟨.and,[6,52]⟩,
⟨.or,[17,19]⟩,
⟨.or,[20,24]⟩,
⟨.or,[54,55]⟩,
⟨.and,[7,56]⟩,
⟨.or,[18,20]⟩,
⟨.or,[21,25]⟩,
⟨.or,[58,59]⟩,
⟨.and,[8,60]⟩,
⟨.or,[13,19]⟩,
⟨.or,[21,22]⟩,
⟨.or,[62,63]⟩,
⟨.and,[9,64]⟩,
⟨.or,[14,20]⟩,
⟨.or,[22,23]⟩,
⟨.or,[66,67]⟩,
⟨.and,[10,68]⟩,
⟨.or,[15,21]⟩,
⟨.or,[23,24]⟩,
⟨.or,[70,71]⟩,
⟨.and,[11,72]⟩,
⟨.or,[16,22]⟩,
⟨.or,[24,25]⟩,
⟨.or,[74,75]⟩,
⟨.and,[12,76]⟩,
⟨.or,[33,37]⟩,
⟨.or,[78,41]⟩,
⟨.or,[79,45]⟩,
⟨.or,[80,49]⟩,
⟨.or,[81,53]⟩,
⟨.or,[82,57]⟩,
⟨.or,[83,61]⟩,
⟨.or,[84,65]⟩,
⟨.or,[85,69]⟩,
⟨.or,[86,73]⟩,
⟨.or,[87,77]⟩],88⟩
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
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem both (x : Fin 26 → Bool) :
    val x 29 = left.any (fun e => x (Fin.castAdd 13 e.1) && x (Fin.natAdd 13 e.2)) ∧
    val x 88 = right.any (fun e => x (Fin.castAdd 13 e.1) && x (Fin.natAdd 13 e.2)) := by
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
  have h26 := step_or x 0 13 17 (by decide) rfl (by decide) (by decide)
  change val x 26 = _ at h26
  have h27 := step_or x 1 23 25 (by decide) rfl (by decide) (by decide)
  change val x 27 = _ at h27
  have h28 := step_or x 2 26 27 (by decide) rfl (by decide) (by decide)
  change val x 28 = _ at h28
  have h29 := step_and x 3 0 28 (by decide) rfl (by decide) (by decide)
  change val x 29 = _ at h29
  have h30 := step_or x 4 13 14 (by decide) rfl (by decide) (by decide)
  change val x 30 = _ at h30
  have h31 := step_or x 5 18 24 (by decide) rfl (by decide) (by decide)
  change val x 31 = _ at h31
  have h32 := step_or x 6 30 31 (by decide) rfl (by decide) (by decide)
  change val x 32 = _ at h32
  have h33 := step_and x 7 1 32 (by decide) rfl (by decide) (by decide)
  change val x 33 = _ at h33
  have h34 := step_or x 8 14 15 (by decide) rfl (by decide) (by decide)
  change val x 34 = _ at h34
  have h35 := step_or x 9 19 25 (by decide) rfl (by decide) (by decide)
  change val x 35 = _ at h35
  have h36 := step_or x 10 34 35 (by decide) rfl (by decide) (by decide)
  change val x 36 = _ at h36
  have h37 := step_and x 11 2 36 (by decide) rfl (by decide) (by decide)
  change val x 37 = _ at h37
  have h38 := step_or x 12 13 15 (by decide) rfl (by decide) (by decide)
  change val x 38 = _ at h38
  have h39 := step_or x 13 16 20 (by decide) rfl (by decide) (by decide)
  change val x 39 = _ at h39
  have h40 := step_or x 14 38 39 (by decide) rfl (by decide) (by decide)
  change val x 40 = _ at h40
  have h41 := step_and x 15 3 40 (by decide) rfl (by decide) (by decide)
  change val x 41 = _ at h41
  have h42 := step_or x 16 14 16 (by decide) rfl (by decide) (by decide)
  change val x 42 = _ at h42
  have h43 := step_or x 17 17 21 (by decide) rfl (by decide) (by decide)
  change val x 43 = _ at h43
  have h44 := step_or x 18 42 43 (by decide) rfl (by decide) (by decide)
  change val x 44 = _ at h44
  have h45 := step_and x 19 4 44 (by decide) rfl (by decide) (by decide)
  change val x 45 = _ at h45
  have h46 := step_or x 20 15 17 (by decide) rfl (by decide) (by decide)
  change val x 46 = _ at h46
  have h47 := step_or x 21 18 22 (by decide) rfl (by decide) (by decide)
  change val x 47 = _ at h47
  have h48 := step_or x 22 46 47 (by decide) rfl (by decide) (by decide)
  change val x 48 = _ at h48
  have h49 := step_and x 23 5 48 (by decide) rfl (by decide) (by decide)
  change val x 49 = _ at h49
  have h50 := step_or x 24 16 18 (by decide) rfl (by decide) (by decide)
  change val x 50 = _ at h50
  have h51 := step_or x 25 19 23 (by decide) rfl (by decide) (by decide)
  change val x 51 = _ at h51
  have h52 := step_or x 26 50 51 (by decide) rfl (by decide) (by decide)
  change val x 52 = _ at h52
  have h53 := step_and x 27 6 52 (by decide) rfl (by decide) (by decide)
  change val x 53 = _ at h53
  have h54 := step_or x 28 17 19 (by decide) rfl (by decide) (by decide)
  change val x 54 = _ at h54
  have h55 := step_or x 29 20 24 (by decide) rfl (by decide) (by decide)
  change val x 55 = _ at h55
  have h56 := step_or x 30 54 55 (by decide) rfl (by decide) (by decide)
  change val x 56 = _ at h56
  have h57 := step_and x 31 7 56 (by decide) rfl (by decide) (by decide)
  change val x 57 = _ at h57
  have h58 := step_or x 32 18 20 (by decide) rfl (by decide) (by decide)
  change val x 58 = _ at h58
  have h59 := step_or x 33 21 25 (by decide) rfl (by decide) (by decide)
  change val x 59 = _ at h59
  have h60 := step_or x 34 58 59 (by decide) rfl (by decide) (by decide)
  change val x 60 = _ at h60
  have h61 := step_and x 35 8 60 (by decide) rfl (by decide) (by decide)
  change val x 61 = _ at h61
  have h62 := step_or x 36 13 19 (by decide) rfl (by decide) (by decide)
  change val x 62 = _ at h62
  have h63 := step_or x 37 21 22 (by decide) rfl (by decide) (by decide)
  change val x 63 = _ at h63
  have h64 := step_or x 38 62 63 (by decide) rfl (by decide) (by decide)
  change val x 64 = _ at h64
  have h65 := step_and x 39 9 64 (by decide) rfl (by decide) (by decide)
  change val x 65 = _ at h65
  have h66 := step_or x 40 14 20 (by decide) rfl (by decide) (by decide)
  change val x 66 = _ at h66
  have h67 := step_or x 41 22 23 (by decide) rfl (by decide) (by decide)
  change val x 67 = _ at h67
  have h68 := step_or x 42 66 67 (by decide) rfl (by decide) (by decide)
  change val x 68 = _ at h68
  have h69 := step_and x 43 10 68 (by decide) rfl (by decide) (by decide)
  change val x 69 = _ at h69
  have h70 := step_or x 44 15 21 (by decide) rfl (by decide) (by decide)
  change val x 70 = _ at h70
  have h71 := step_or x 45 23 24 (by decide) rfl (by decide) (by decide)
  change val x 71 = _ at h71
  have h72 := step_or x 46 70 71 (by decide) rfl (by decide) (by decide)
  change val x 72 = _ at h72
  have h73 := step_and x 47 11 72 (by decide) rfl (by decide) (by decide)
  change val x 73 = _ at h73
  have h74 := step_or x 48 16 22 (by decide) rfl (by decide) (by decide)
  change val x 74 = _ at h74
  have h75 := step_or x 49 24 25 (by decide) rfl (by decide) (by decide)
  change val x 75 = _ at h75
  have h76 := step_or x 50 74 75 (by decide) rfl (by decide) (by decide)
  change val x 76 = _ at h76
  have h77 := step_and x 51 12 76 (by decide) rfl (by decide) (by decide)
  change val x 77 = _ at h77
  have h78 := step_or x 52 33 37 (by decide) rfl (by decide) (by decide)
  change val x 78 = _ at h78
  have h79 := step_or x 53 78 41 (by decide) rfl (by decide) (by decide)
  change val x 79 = _ at h79
  have h80 := step_or x 54 79 45 (by decide) rfl (by decide) (by decide)
  change val x 80 = _ at h80
  have h81 := step_or x 55 80 49 (by decide) rfl (by decide) (by decide)
  change val x 81 = _ at h81
  have h82 := step_or x 56 81 53 (by decide) rfl (by decide) (by decide)
  change val x 82 = _ at h82
  have h83 := step_or x 57 82 57 (by decide) rfl (by decide) (by decide)
  change val x 83 = _ at h83
  have h84 := step_or x 58 83 61 (by decide) rfl (by decide) (by decide)
  change val x 84 = _ at h84
  have h85 := step_or x 59 84 65 (by decide) rfl (by decide) (by decide)
  change val x 85 = _ at h85
  have h86 := step_or x 60 85 69 (by decide) rfl (by decide) (by decide)
  change val x 86 = _ at h86
  have h87 := step_or x 61 86 73 (by decide) rfl (by decide) (by decide)
  change val x 87 = _ at h87
  have h88 := step_or x 62 87 77 (by decide) rfl (by decide) (by decide)
  change val x 88 = _ at h88
  constructor <;> simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53,h54,h55,h56,h57,h58,h59,h60,h61,h62,h63,h64,h65,h66,h67,h68,h69,h70,h71,h72,h73,h74,h75,h76,h77,h78,h79,h80,h81,h82,h83,h84,h85,h86,h87,h88]
  all_goals simp [left,right,Bool.and_or_distrib_left,Bool.or_assoc,Fin.natAdd,Fin.castAdd]
  all_goals ac_rfl

theorem rows (P L : Finset (Fin 13)) :
    W C 29 P L = left.any (fun e => decide (e.1 ∈ P ∧ e.2 ∈ L)) ∧
    W C 88 P L = right.any (fun e => decide (e.1 ∈ P ∧ e.2 ∈ L)) := by
  let x : Fin 26 → Bool := Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
  have eq : List.ofFn x = incidenceInput P L := by simp [x,incidenceInput, List.ofFn_fin_append]
  have h := both x
  unfold val at h
  rw [eq] at h
  simpa [W,run,Circuit.wires,x,decide_and] using h

theorem negative (P : Finset (Fin 13)) :
    W C 29 P (missLines singerLines3 P) = false ∧ W C 88 P (missLines singerLines3 P) = false := by
  have prop (l : List (Fin 13 × Fin 13)) (valid : ∀ e ∈ l, e.1 ∈ singerLines3 e.2) :
      l.any (fun e => decide (e.1 ∈ P ∧ e.2 ∈ missLines singerLines3 P)) = false := by
    apply List.any_eq_false.mpr
    intro e he
    simp only [decide_eq_false_iff_not]
    rintro ⟨p,m⟩
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp m).2 p (valid e he)
  have h := rows P (missLines singerLines3 P)
  exact ⟨h.1.trans (prop _ (by decide)), h.2.trans (prop _ (by decide))⟩

theorem positive : ∀ p l : Fin 13, p ∈ singerLines3 l → W C 29 {p} {l} = true ∨ W C 88 {p} {l} = true := by
  intro p l hp
  have h := rows {p} {l}
  rw [h.1,h.2]
  revert hp l p
  decide +kernel

theorem structure_ok : Monotone2 C ∧ ReadsBack 26 C ∧ C.size=63 ∧
    (∀ j ∈ Finset.range C.size, (gateAt C j).op = GateOp.and →
      ∀ i ∈ (gateAt C j).inputs, 26 ≤ i → (gateAt C (i-26)).op ≠ GateOp.and) := by decide +kernel
theorem exclusive : (W C 29 {0} {0} = true ∧ W C 88 {0} {0} = false) ∧
    (W C 29 {1} {1} = false ∧ W C 88 {1} {1} = true) := by decide +kernel
end PEqualNP.Outside.Upper5198
#print axioms PEqualNP.Outside.Upper5198.negative
