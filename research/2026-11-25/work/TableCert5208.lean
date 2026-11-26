import Reflect5208
open PEqualNP.CircuitLowerBounds
namespace Marked5208
open Reflection
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000
def partialDNF (i : ℕ) := (C.gates.take i).foldl sym init
theorem advance (i : ℕ) (hi : i < C.gates.length) :
    partialDNF (i+1) = sym (partialDNF i) C.gates[i] := by
  unfold partialDNF
  rw [List.take_succ_eq_append_getElem hi,List.foldl_append]
  rfl
def t0 := init
theorem r0 : partialDNF 0 = t0 := rfl
def z1 : DNF := {{13},{14}}
def t1 := t0 ++ [z1]
theorem r1 : partialDNF 1 = t1 := by
  rw [advance 0 (by decide),r0]
  apply congrArg (fun m : DNF => t0 ++ [m])
  decide +kernel
def z2 : DNF := {{18},{24}}
def t2 := t1 ++ [z2]
theorem r2 : partialDNF 2 = t2 := by
  rw [advance 1 (by decide),r1]
  apply congrArg (fun m : DNF => t1 ++ [m])
  decide +kernel
def z3 : DNF := {{13},{14},{18},{24}}
def t3 := t2 ++ [z3]
theorem r3 : partialDNF 3 = t3 := by
  rw [advance 2 (by decide),r2]
  apply congrArg (fun m : DNF => t2 ++ [m])
  decide +kernel
def z4 : DNF := {{1,13},{1,14},{1,18},{1,24}}
def t4 := t3 ++ [z4]
theorem r4 : partialDNF 4 = t4 := by
  rw [advance 3 (by decide),r3]
  apply congrArg (fun m : DNF => t3 ++ [m])
  decide +kernel
def z5 : DNF := {{13},{13,14}}
def t5 := t4 ++ [z5]
theorem r5 : partialDNF 5 = t5 := by
  rw [advance 4 (by decide),r4]
  apply congrArg (fun m : DNF => t4 ++ [m])
  decide +kernel
def z6 : DNF := {{13},{13,14},{17}}
def t6 := t5 ++ [z6]
theorem r6 : partialDNF 6 = t6 := by
  rw [advance 5 (by decide),r5]
  apply congrArg (fun m : DNF => t5 ++ [m])
  decide +kernel
def z7 : DNF := {{23},{25}}
def t7 := t6 ++ [z7]
theorem r7 : partialDNF 7 = t7 := by
  rw [advance 6 (by decide),r6]
  apply congrArg (fun m : DNF => t6 ++ [m])
  decide +kernel
def z8 : DNF := {{13},{13,14},{17},{23},{25}}
def t8 := t7 ++ [z8]
theorem r8 : partialDNF 8 = t8 := by
  rw [advance 7 (by decide),r7]
  apply congrArg (fun m : DNF => t7 ++ [m])
  decide +kernel
def z9 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25}}
def t9 := t8 ++ [z9]
theorem r9 : partialDNF 9 = t9 := by
  rw [advance 8 (by decide),r8]
  apply congrArg (fun m : DNF => t8 ++ [m])
  decide +kernel
def z10 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25}}
def t10 := t9 ++ [z10]
theorem r10 : partialDNF 10 = t10 := by
  rw [advance 9 (by decide),r9]
  apply congrArg (fun m : DNF => t9 ++ [m])
  decide +kernel
def z11 : DNF := {{14},{15}}
def t11 := t10 ++ [z11]
theorem r11 : partialDNF 11 = t11 := by
  rw [advance 10 (by decide),r10]
  apply congrArg (fun m : DNF => t10 ++ [m])
  decide +kernel
def z12 : DNF := {{19},{25}}
def t12 := t11 ++ [z12]
theorem r12 : partialDNF 12 = t12 := by
  rw [advance 11 (by decide),r11]
  apply congrArg (fun m : DNF => t11 ++ [m])
  decide +kernel
def z13 : DNF := {{14},{15},{19},{25}}
def t13 := t12 ++ [z13]
theorem r13 : partialDNF 13 = t13 := by
  rw [advance 12 (by decide),r12]
  apply congrArg (fun m : DNF => t12 ++ [m])
  decide +kernel
def z14 : DNF := {{2,14},{2,15},{2,19},{2,25}}
def t14 := t13 ++ [z14]
theorem r14 : partialDNF 14 = t14 := by
  rw [advance 13 (by decide),r13]
  apply congrArg (fun m : DNF => t13 ++ [m])
  decide +kernel
def z15 : DNF := {{13},{15}}
def t15 := t14 ++ [z15]
theorem r15 : partialDNF 15 = t15 := by
  rw [advance 14 (by decide),r14]
  apply congrArg (fun m : DNF => t14 ++ [m])
  decide +kernel
def z16 : DNF := {{16},{20}}
def t16 := t15 ++ [z16]
theorem r16 : partialDNF 16 = t16 := by
  rw [advance 15 (by decide),r15]
  apply congrArg (fun m : DNF => t15 ++ [m])
  decide +kernel
def z17 : DNF := {{13},{15},{16},{20}}
def t17 := t16 ++ [z17]
theorem r17 : partialDNF 17 = t17 := by
  rw [advance 16 (by decide),r16]
  apply congrArg (fun m : DNF => t16 ++ [m])
  decide +kernel
def z18 : DNF := {{3,13},{3,15},{3,16},{3,20}}
def t18 := t17 ++ [z18]
theorem r18 : partialDNF 18 = t18 := by
  rw [advance 17 (by decide),r17]
  apply congrArg (fun m : DNF => t17 ++ [m])
  decide +kernel
def z19 : DNF := {{14},{16}}
def t19 := t18 ++ [z19]
theorem r19 : partialDNF 19 = t19 := by
  rw [advance 18 (by decide),r18]
  apply congrArg (fun m : DNF => t18 ++ [m])
  decide +kernel
def z20 : DNF := {{17},{21}}
def t20 := t19 ++ [z20]
theorem r20 : partialDNF 20 = t20 := by
  rw [advance 19 (by decide),r19]
  apply congrArg (fun m : DNF => t19 ++ [m])
  decide +kernel
def z21 : DNF := {{14},{16},{17},{21}}
def t21 := t20 ++ [z21]
theorem r21 : partialDNF 21 = t21 := by
  rw [advance 20 (by decide),r20]
  apply congrArg (fun m : DNF => t20 ++ [m])
  decide +kernel
def z22 : DNF := {{4,14},{4,16},{4,17},{4,21}}
def t22 := t21 ++ [z22]
theorem r22 : partialDNF 22 = t22 := by
  rw [advance 21 (by decide),r21]
  apply congrArg (fun m : DNF => t21 ++ [m])
  decide +kernel
def z23 : DNF := {{15},{17}}
def t23 := t22 ++ [z23]
theorem r23 : partialDNF 23 = t23 := by
  rw [advance 22 (by decide),r22]
  apply congrArg (fun m : DNF => t22 ++ [m])
  decide +kernel
def z24 : DNF := {{18},{22}}
def t24 := t23 ++ [z24]
theorem r24 : partialDNF 24 = t24 := by
  rw [advance 23 (by decide),r23]
  apply congrArg (fun m : DNF => t23 ++ [m])
  decide +kernel
def z25 : DNF := {{15},{17},{18},{22}}
def t25 := t24 ++ [z25]
theorem r25 : partialDNF 25 = t25 := by
  rw [advance 24 (by decide),r24]
  apply congrArg (fun m : DNF => t24 ++ [m])
  decide +kernel
def z26 : DNF := {{5,15},{5,17},{5,18},{5,22}}
def t26 := t25 ++ [z26]
theorem r26 : partialDNF 26 = t26 := by
  rw [advance 25 (by decide),r25]
  apply congrArg (fun m : DNF => t25 ++ [m])
  decide +kernel
def z27 : DNF := {{16},{18}}
def t27 := t26 ++ [z27]
theorem r27 : partialDNF 27 = t27 := by
  rw [advance 26 (by decide),r26]
  apply congrArg (fun m : DNF => t26 ++ [m])
  decide +kernel
def z28 : DNF := {{19},{23}}
def t28 := t27 ++ [z28]
theorem r28 : partialDNF 28 = t28 := by
  rw [advance 27 (by decide),r27]
  apply congrArg (fun m : DNF => t27 ++ [m])
  decide +kernel
def z29 : DNF := {{16},{18},{19},{23}}
def t29 := t28 ++ [z29]
theorem r29 : partialDNF 29 = t29 := by
  rw [advance 28 (by decide),r28]
  apply congrArg (fun m : DNF => t28 ++ [m])
  decide +kernel
def z30 : DNF := {{6,16},{6,18},{6,19},{6,23}}
def t30 := t29 ++ [z30]
theorem r30 : partialDNF 30 = t30 := by
  rw [advance 29 (by decide),r29]
  apply congrArg (fun m : DNF => t29 ++ [m])
  decide +kernel
def z31 : DNF := {{17},{19}}
def t31 := t30 ++ [z31]
theorem r31 : partialDNF 31 = t31 := by
  rw [advance 30 (by decide),r30]
  apply congrArg (fun m : DNF => t30 ++ [m])
  decide +kernel
def z32 : DNF := {{20},{24}}
def t32 := t31 ++ [z32]
theorem r32 : partialDNF 32 = t32 := by
  rw [advance 31 (by decide),r31]
  apply congrArg (fun m : DNF => t31 ++ [m])
  decide +kernel
def z33 : DNF := {{17},{19},{20},{24}}
def t33 := t32 ++ [z33]
theorem r33 : partialDNF 33 = t33 := by
  rw [advance 32 (by decide),r32]
  apply congrArg (fun m : DNF => t32 ++ [m])
  decide +kernel
def z34 : DNF := {{7,17},{7,19},{7,20},{7,24}}
def t34 := t33 ++ [z34]
theorem r34 : partialDNF 34 = t34 := by
  rw [advance 33 (by decide),r33]
  apply congrArg (fun m : DNF => t33 ++ [m])
  decide +kernel
def z35 : DNF := {{18},{20}}
def t35 := t34 ++ [z35]
theorem r35 : partialDNF 35 = t35 := by
  rw [advance 34 (by decide),r34]
  apply congrArg (fun m : DNF => t34 ++ [m])
  decide +kernel
def z36 : DNF := {{21},{25}}
def t36 := t35 ++ [z36]
theorem r36 : partialDNF 36 = t36 := by
  rw [advance 35 (by decide),r35]
  apply congrArg (fun m : DNF => t35 ++ [m])
  decide +kernel
def z37 : DNF := {{18},{20},{21},{25}}
def t37 := t36 ++ [z37]
theorem r37 : partialDNF 37 = t37 := by
  rw [advance 36 (by decide),r36]
  apply congrArg (fun m : DNF => t36 ++ [m])
  decide +kernel
def z38 : DNF := {{8,18},{8,20},{8,21},{8,25}}
def t38 := t37 ++ [z38]
theorem r38 : partialDNF 38 = t38 := by
  rw [advance 37 (by decide),r37]
  apply congrArg (fun m : DNF => t37 ++ [m])
  decide +kernel
def z39 : DNF := {{13},{19}}
def t39 := t38 ++ [z39]
theorem r39 : partialDNF 39 = t39 := by
  rw [advance 38 (by decide),r38]
  apply congrArg (fun m : DNF => t38 ++ [m])
  decide +kernel
def z40 : DNF := {{21},{22}}
def t40 := t39 ++ [z40]
theorem r40 : partialDNF 40 = t40 := by
  rw [advance 39 (by decide),r39]
  apply congrArg (fun m : DNF => t39 ++ [m])
  decide +kernel
def z41 : DNF := {{13},{19},{21},{22}}
def t41 := t40 ++ [z41]
theorem r41 : partialDNF 41 = t41 := by
  rw [advance 40 (by decide),r40]
  apply congrArg (fun m : DNF => t40 ++ [m])
  decide +kernel
def z42 : DNF := {{9,13},{9,19},{9,21},{9,22}}
def t42 := t41 ++ [z42]
theorem r42 : partialDNF 42 = t42 := by
  rw [advance 41 (by decide),r41]
  apply congrArg (fun m : DNF => t41 ++ [m])
  decide +kernel
def z43 : DNF := {{14},{20}}
def t43 := t42 ++ [z43]
theorem r43 : partialDNF 43 = t43 := by
  rw [advance 42 (by decide),r42]
  apply congrArg (fun m : DNF => t42 ++ [m])
  decide +kernel
def z44 : DNF := {{22},{23}}
def t44 := t43 ++ [z44]
theorem r44 : partialDNF 44 = t44 := by
  rw [advance 43 (by decide),r43]
  apply congrArg (fun m : DNF => t43 ++ [m])
  decide +kernel
def z45 : DNF := {{14},{20},{22},{23}}
def t45 := t44 ++ [z45]
theorem r45 : partialDNF 45 = t45 := by
  rw [advance 44 (by decide),r44]
  apply congrArg (fun m : DNF => t44 ++ [m])
  decide +kernel
def z46 : DNF := {{10,14},{10,20},{10,22},{10,23}}
def t46 := t45 ++ [z46]
theorem r46 : partialDNF 46 = t46 := by
  rw [advance 45 (by decide),r45]
  apply congrArg (fun m : DNF => t45 ++ [m])
  decide +kernel
def z47 : DNF := {{15},{21}}
def t47 := t46 ++ [z47]
theorem r47 : partialDNF 47 = t47 := by
  rw [advance 46 (by decide),r46]
  apply congrArg (fun m : DNF => t46 ++ [m])
  decide +kernel
def z48 : DNF := {{23},{24}}
def t48 := t47 ++ [z48]
theorem r48 : partialDNF 48 = t48 := by
  rw [advance 47 (by decide),r47]
  apply congrArg (fun m : DNF => t47 ++ [m])
  decide +kernel
def z49 : DNF := {{15},{21},{23},{24}}
def t49 := t48 ++ [z49]
theorem r49 : partialDNF 49 = t49 := by
  rw [advance 48 (by decide),r48]
  apply congrArg (fun m : DNF => t48 ++ [m])
  decide +kernel
def z50 : DNF := {{11,15},{11,21},{11,23},{11,24}}
def t50 := t49 ++ [z50]
theorem r50 : partialDNF 50 = t50 := by
  rw [advance 49 (by decide),r49]
  apply congrArg (fun m : DNF => t49 ++ [m])
  decide +kernel
def z51 : DNF := {{16},{22}}
def t51 := t50 ++ [z51]
theorem r51 : partialDNF 51 = t51 := by
  rw [advance 50 (by decide),r50]
  apply congrArg (fun m : DNF => t50 ++ [m])
  decide +kernel
def z52 : DNF := {{24},{25}}
def t52 := t51 ++ [z52]
theorem r52 : partialDNF 52 = t52 := by
  rw [advance 51 (by decide),r51]
  apply congrArg (fun m : DNF => t51 ++ [m])
  decide +kernel
def z53 : DNF := {{16},{22},{24},{25}}
def t53 := t52 ++ [z53]
theorem r53 : partialDNF 53 = t53 := by
  rw [advance 52 (by decide),r52]
  apply congrArg (fun m : DNF => t52 ++ [m])
  decide +kernel
def z54 : DNF := {{12,16},{12,22},{12,24},{12,25}}
def t54 := t53 ++ [z54]
theorem r54 : partialDNF 54 = t54 := by
  rw [advance 53 (by decide),r53]
  apply congrArg (fun m : DNF => t53 ++ [m])
  decide +kernel
def z55 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24}}
def t55 := t54 ++ [z55]
theorem r55 : partialDNF 55 = t55 := by
  rw [advance 54 (by decide),r54]
  apply congrArg (fun m : DNF => t54 ++ [m])
  decide +kernel
def z56 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25}}
def t56 := t55 ++ [z56]
theorem r56 : partialDNF 56 = t56 := by
  rw [advance 55 (by decide),r55]
  apply congrArg (fun m : DNF => t55 ++ [m])
  decide +kernel
def z57 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25},{3,13},{3,15},{3,16},{3,20}}
def t57 := t56 ++ [z57]
theorem r57 : partialDNF 57 = t57 := by
  rw [advance 56 (by decide),r56]
  apply congrArg (fun m : DNF => t56 ++ [m])
  decide +kernel
def z58 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25},{3,13},{3,15},{3,16},{3,20},{4,14},{4,16},{4,17},{4,21}}
def t58 := t57 ++ [z58]
theorem r58 : partialDNF 58 = t58 := by
  rw [advance 57 (by decide),r57]
  apply congrArg (fun m : DNF => t57 ++ [m])
  decide +kernel
def z59 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25},{3,13},{3,15},{3,16},{3,20},{4,14},{4,16},{4,17},{4,21},{5,15},{5,17},{5,18},{5,22}}
def t59 := t58 ++ [z59]
theorem r59 : partialDNF 59 = t59 := by
  rw [advance 58 (by decide),r58]
  apply congrArg (fun m : DNF => t58 ++ [m])
  decide +kernel
def z60 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25},{3,13},{3,15},{3,16},{3,20},{4,14},{4,16},{4,17},{4,21},{5,15},{5,17},{5,18},{5,22},{6,16},{6,18},{6,19},{6,23}}
def t60 := t59 ++ [z60]
theorem r60 : partialDNF 60 = t60 := by
  rw [advance 59 (by decide),r59]
  apply congrArg (fun m : DNF => t59 ++ [m])
  decide +kernel
def z61 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25},{3,13},{3,15},{3,16},{3,20},{4,14},{4,16},{4,17},{4,21},{5,15},{5,17},{5,18},{5,22},{6,16},{6,18},{6,19},{6,23},{7,17},{7,19},{7,20},{7,24}}
def t61 := t60 ++ [z61]
theorem r61 : partialDNF 61 = t61 := by
  rw [advance 60 (by decide),r60]
  apply congrArg (fun m : DNF => t60 ++ [m])
  decide +kernel
def z62 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25},{3,13},{3,15},{3,16},{3,20},{4,14},{4,16},{4,17},{4,21},{5,15},{5,17},{5,18},{5,22},{6,16},{6,18},{6,19},{6,23},{7,17},{7,19},{7,20},{7,24},{8,18},{8,20},{8,21},{8,25}}
def t62 := t61 ++ [z62]
theorem r62 : partialDNF 62 = t62 := by
  rw [advance 61 (by decide),r61]
  apply congrArg (fun m : DNF => t61 ++ [m])
  decide +kernel
def z63 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25},{3,13},{3,15},{3,16},{3,20},{4,14},{4,16},{4,17},{4,21},{5,15},{5,17},{5,18},{5,22},{6,16},{6,18},{6,19},{6,23},{7,17},{7,19},{7,20},{7,24},{8,18},{8,20},{8,21},{8,25},{9,13},{9,19},{9,21},{9,22}}
def t63 := t62 ++ [z63]
theorem r63 : partialDNF 63 = t63 := by
  rw [advance 62 (by decide),r62]
  apply congrArg (fun m : DNF => t62 ++ [m])
  decide +kernel
def z64 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25},{3,13},{3,15},{3,16},{3,20},{4,14},{4,16},{4,17},{4,21},{5,15},{5,17},{5,18},{5,22},{6,16},{6,18},{6,19},{6,23},{7,17},{7,19},{7,20},{7,24},{8,18},{8,20},{8,21},{8,25},{9,13},{9,19},{9,21},{9,22},{10,14},{10,20},{10,22},{10,23}}
def t64 := t63 ++ [z64]
theorem r64 : partialDNF 64 = t64 := by
  rw [advance 63 (by decide),r63]
  apply congrArg (fun m : DNF => t63 ++ [m])
  decide +kernel
def z65 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25},{3,13},{3,15},{3,16},{3,20},{4,14},{4,16},{4,17},{4,21},{5,15},{5,17},{5,18},{5,22},{6,16},{6,18},{6,19},{6,23},{7,17},{7,19},{7,20},{7,24},{8,18},{8,20},{8,21},{8,25},{9,13},{9,19},{9,21},{9,22},{10,14},{10,20},{10,22},{10,23},{11,15},{11,21},{11,23},{11,24}}
def t65 := t64 ++ [z65]
theorem r65 : partialDNF 65 = t65 := by
  rw [advance 64 (by decide),r64]
  apply congrArg (fun m : DNF => t64 ++ [m])
  decide +kernel
def z66 : DNF := {{0,13},{0,13,14},{0,17},{0,23},{0,25},{1,13},{1,14},{1,18},{1,24},{2,14},{2,15},{2,19},{2,25},{3,13},{3,15},{3,16},{3,20},{4,14},{4,16},{4,17},{4,21},{5,15},{5,17},{5,18},{5,22},{6,16},{6,18},{6,19},{6,23},{7,17},{7,19},{7,20},{7,24},{8,18},{8,20},{8,21},{8,25},{9,13},{9,19},{9,21},{9,22},{10,14},{10,20},{10,22},{10,23},{11,15},{11,21},{11,23},{11,24},{12,16},{12,22},{12,24},{12,25}}
def t66 := t65 ++ [z66]
theorem r66 : partialDNF 66 = t66 := by
  rw [advance 65 (by decide),r65]
  apply congrArg (fun m : DNF => t65 ++ [m])
  decide +kernel
theorem allTerms : result = z66 := by
  have eq : C.gates.take 66 = C.gates := List.take_of_length_le (by decide)
  have h := r66
  unfold partialDNF at h
  rw [eq] at h
  unfold result
  rw [h]
  rfl
end Marked5208
#print axioms Marked5208.allTerms
