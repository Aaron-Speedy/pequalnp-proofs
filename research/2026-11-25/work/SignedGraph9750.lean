import Signed9750
namespace PEqualNP.Outside.Signed9750
def bits (r : ℕ) (i : Fin 12) := r.testBit i
theorem weaken {f : Fn Assignment} {a b : ℕ} (le : a ≤ b) (h : LB f b) : LB f a :=
  fun k p => le.trans (h k p)

theorem edgeCost (a b : Fin 12) (ne : a ≠ b) : LB (fun x => x a && x b) 1 := by
  intro k h
  cases k with
  | succ k => omega
  | zero =>
    change primary (fun x => x a && x b) at h
    rcases h with ⟨c,eq⟩ | ⟨j,eq|eq⟩
    · have h0 := congrFun eq (fun _ => false)
      have h1 := congrFun eq (fun _ => true)
      simp_all
    · have d := congrFun eq (fun i => decide (i = j))
      simp at d
      exact False.elim (ne (d.1.trans d.2.symm))
    · have d := congrFun eq (fun _ => false)
      simp [inv] at d

def table2049_0 (x : Assignment) : Bool := (x 0 && x 11)
theorem lowtable2049_0 : LB table2049_0 1 := by
  exact edgeCost 0 11 (by decide)

def table2051_0 (x : Assignment) : Bool := (x 0 && x 11) || (x 1 && x 11)
theorem lowtable2051_0 : LB table2051_0 2 := by
  apply lbOne (g := table2049_0) 1 false (bits 2048) (bits 0) (bits 2049)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table2051_0,table2049_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable2049_0

def table2049_2 (x : Assignment) : Bool := x 1 || (x 0 && x 11)
theorem lowtable2049_2 : LB table2049_2 2 := by
  apply lbOne (g := table2049_0) 1 false (bits 0) (bits 0) (bits 2049)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table2049_2,table2049_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable2049_0

def table3075_0 (x : Assignment) : Bool := (x 0 && x 11) || (x 1 && x 10) || (x 1 && x 11)
theorem lowtable3075_0 : LB table3075_0 4 := by
  apply lbBoth (g := table2051_0) (h := table2049_2) 10 (bits 2) (bits 0) (bits 2049) (bits 0) (bits 2)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3075_0,table2051_0,co,slice,pairAt,Function.update] <;> grind
  · funext x; simp [table3075_0,table2049_2,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable2051_0
  · exact weaken (by decide) lowtable2049_2

def table3139_0 (x : Assignment) : Bool := (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11)
theorem lowtable3139_0 : LB table3139_0 5 := by
  apply lbOne (g := table3075_0) 6 false (bits 2) (bits 0) (bits 1026)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3139_0,table3075_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3075_0

def table2115_0 (x : Assignment) : Bool := (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 11)
theorem lowtable2115_0 : LB table2115_0 4 := by
  apply lbBoth (g := table2051_0) (h := table2049_2) 6 (bits 2) (bits 0) (bits 2049) (bits 0) (bits 2)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · funext x; simp [table2115_0,table2051_0,co,slice,pairAt,Function.update] <;> grind
  · funext x; simp [table2115_0,table2049_2,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable2051_0
  · exact weaken (by decide) lowtable2049_2

def table2115_1024 (x : Assignment) : Bool := x 10 || (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 11)
theorem lowtable2115_1024 : LB table2115_1024 5 := by
  apply lbOne (g := table2115_0) 10 false (bits 0) (bits 0) (bits 66)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table2115_1024,table2115_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable2115_0

def table3143_0 (x : Assignment) : Bool := (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 10)
theorem lowtable3143_0 : LB table3143_0 7 := by
  apply lbBoth (g := table3139_0) (h := table2115_1024) 2 (bits 1024) (bits 0) (bits 66) (bits 0) (bits 66)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3143_0,table3139_0,co,slice,pairAt,Function.update] <;> grind
  · funext x; simp [table3143_0,table2115_1024,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3139_0
  · exact weaken (by decide) lowtable2115_1024

def table3151_0 (x : Assignment) : Bool := (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 10) || (x 3 && x 11)
theorem lowtable3151_0 : LB table3151_0 8 := by
  apply lbOne (g := table3143_0) 3 false (bits 2048) (bits 0) (bits 66)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3151_0,table3143_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3143_0

def table1026_0 (x : Assignment) : Bool := (x 1 && x 10)
theorem lowtable1026_0 : LB table1026_0 1 := by
  exact edgeCost 1 10 (by decide)

def table3074_0 (x : Assignment) : Bool := (x 1 && x 10) || (x 1 && x 11)
theorem lowtable3074_0 : LB table3074_0 2 := by
  apply lbOne (g := table1026_0) 11 false (bits 2) (bits 0) (bits 1026)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3074_0,table1026_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable1026_0

def table2050_0 (x : Assignment) : Bool := (x 1 && x 11)
theorem lowtable2050_0 : LB table2050_0 1 := by
  exact edgeCost 1 11 (by decide)

def table2050_1024 (x : Assignment) : Bool := x 10 || (x 1 && x 11)
theorem lowtable2050_1024 : LB table2050_1024 2 := by
  apply lbOne (g := table2050_0) 10 false (bits 0) (bits 0) (bits 2050)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table2050_1024,table2050_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable2050_0

def table3078_0 (x : Assignment) : Bool := (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 10)
theorem lowtable3078_0 : LB table3078_0 4 := by
  apply lbBoth (g := table3074_0) (h := table2050_1024) 2 (bits 1024) (bits 0) (bits 1026) (bits 0) (bits 1024)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3078_0,table3074_0,co,slice,pairAt,Function.update] <;> grind
  · funext x; simp [table3078_0,table2050_1024,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3074_0
  · exact weaken (by decide) lowtable2050_1024

def table3142_0 (x : Assignment) : Bool := (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 10)
theorem lowtable3142_0 : LB table3142_0 5 := by
  apply lbOne (g := table3078_0) 6 false (bits 2) (bits 0) (bits 1026)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3142_0,table3078_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3078_0

def table1030_0 (x : Assignment) : Bool := (x 1 && x 10) || (x 2 && x 10)
theorem lowtable1030_0 : LB table1030_0 2 := by
  apply lbOne (g := table1026_0) 2 false (bits 1024) (bits 0) (bits 1026)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table1030_0,table1026_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable1026_0

def table1028_0 (x : Assignment) : Bool := (x 2 && x 10)
theorem lowtable1028_0 : LB table1028_0 1 := by
  exact edgeCost 2 10 (by decide)

def table1028_2 (x : Assignment) : Bool := x 1 || (x 2 && x 10)
theorem lowtable1028_2 : LB table1028_2 2 := by
  apply lbOne (g := table1028_0) 1 false (bits 0) (bits 0) (bits 1028)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table1028_2,table1028_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable1028_0

def table1094_0 (x : Assignment) : Bool := (x 1 && x 6) || (x 1 && x 10) || (x 2 && x 10)
theorem lowtable1094_0 : LB table1094_0 4 := by
  apply lbBoth (g := table1030_0) (h := table1028_2) 6 (bits 2) (bits 0) (bits 1026) (bits 0) (bits 2)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · funext x; simp [table1094_0,table1030_0,co,slice,pairAt,Function.update] <;> grind
  · funext x; simp [table1094_0,table1028_2,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable1030_0
  · exact weaken (by decide) lowtable1028_2

def table1094_2048 (x : Assignment) : Bool := x 11 || (x 1 && x 6) || (x 1 && x 10) || (x 2 && x 10)
theorem lowtable1094_2048 : LB table1094_2048 5 := by
  apply lbOne (g := table1094_0) 11 false (bits 0) (bits 0) (bits 66)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table1094_2048,table1094_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable1094_0

def table3150_0 (x : Assignment) : Bool := (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 10) || (x 3 && x 11)
theorem lowtable3150_0 : LB table3150_0 7 := by
  apply lbBoth (g := table3142_0) (h := table1094_2048) 3 (bits 2048) (bits 0) (bits 66) (bits 0) (bits 66)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3150_0,table3142_0,co,slice,pairAt,Function.update] <;> grind
  · funext x; simp [table3150_0,table1094_2048,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3142_0
  · exact weaken (by decide) lowtable1094_2048

def table3150_1 (x : Assignment) : Bool := x 0 || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 10) || (x 3 && x 11)
theorem lowtable3150_1 : LB table3150_1 8 := by
  apply lbOne (g := table3150_0) 0 false (bits 0) (bits 0) (bits 66)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3150_1,table3150_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3150_0

def table3279_0 (x : Assignment) : Bool := (x 0 && x 7) || (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 10) || (x 3 && x 11)
theorem lowtable3279_0 : LB table3279_0 10 := by
  apply lbBoth (g := table3151_0) (h := table3150_1) 7 (bits 1) (bits 0) (bits 66) (bits 0) (bits 1)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3279_0,table3151_0,co,slice,pairAt,Function.update] <;> grind
  · funext x; simp [table3279_0,table3150_1,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3151_0
  · exact weaken (by decide) lowtable3150_1

def table3295_0 (x : Assignment) : Bool := (x 0 && x 7) || (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 10) || (x 3 && x 11) || (x 4 && x 7) || (x 4 && x 10)
theorem lowtable3295_0 : LB table3295_0 11 := by
  apply lbOne (g := table3279_0) 4 false (bits 128) (bits 0) (bits 66)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3295_0,table3279_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3279_0

def table3327_0 (x : Assignment) : Bool := (x 0 && x 7) || (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 10) || (x 3 && x 11) || (x 4 && x 7) || (x 4 && x 10) || (x 5 && x 6) || (x 5 && x 7)
theorem lowtable3327_0 : LB table3327_0 12 := by
  apply lbOne (g := table3295_0) 5 false (bits 64) (bits 0) (bits 66)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3327_0,table3295_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3295_0

def table3583_0 (x : Assignment) : Bool := (x 0 && x 7) || (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 10) || (x 3 && x 8) || (x 3 && x 11) || (x 4 && x 7) || (x 4 && x 8) || (x 4 && x 10) || (x 5 && x 6) || (x 5 && x 7)
theorem lowtable3583_0 : LB table3583_0 13 := by
  apply lbOne (g := table3327_0) 8 false (bits 8) (bits 0) (bits 66)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table3583_0,table3327_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3327_0

def table4095_0 (x : Assignment) : Bool := (x 0 && x 7) || (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 9) || (x 2 && x 10) || (x 3 && x 8) || (x 3 && x 9) || (x 3 && x 11) || (x 4 && x 7) || (x 4 && x 8) || (x 4 && x 10) || (x 5 && x 6) || (x 5 && x 7) || (x 5 && x 9)
theorem lowtable4095_0 : LB table4095_0 14 := by
  apply lbOne (g := table3583_0) 9 false (bits 4) (bits 0) (bits 66)
  · decide +kernel
  · decide +kernel
  · funext x; simp [table4095_0,table3583_0,co,slice,pairAt,Function.update] <;> grind
  · exact weaken (by decide) lowtable3583_0

end PEqualNP.Outside.Signed9750
#print axioms PEqualNP.Outside.Signed9750.lowtable4095_0
