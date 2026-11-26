import CircuitAPart9
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_16977_aux
namespace S_13
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (2, 6), (3, 7), (3, 19), (4, 5), (4, 6), (4, 12), (8, 12), (9, 13), (9, 25), (10, 14), (10, 26), (11, 15), (11, 27), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 4, 4, 4, 8, 9, 9, 10, 10, 11, 11, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [5, 17, 6, 7, 19, 5, 6, 12, 12, 13, 25, 14, 26, 15, 27, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_13.map (· &&& dom_13)
def goalM : Nat := goal_13 &&& dom_13
def NN : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xe1c2916
  | 5, 0 => 0xfd575aab93c0f7228c616cec5299e96d30706e42
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000fcfcfcfc00000000f0f0f0f000000000cccccccc00000000aaaaaaaa000000000f0f0f0f000000000f0f00000000000000ff00ff
  | 0, 1 => 0xffff000000000000ffccffcc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x754315
  | 5, 0, 0 => 0x97543269765436095430509743259875436
  | 6, 0, 0 => 0x975435
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe03f800fde3f07001c007781c00330df1ffc7f8f00003f80ff
  | 0, 1 => 0x3ff0001c77f1c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf23fc06fdeff67457da97785c24f31db1750498ba8241b807f
  | 0, 1 => 0x3ffa825f77fdc
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 10 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 10 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 10 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 10 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 4
  | 5 => 20
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xac05225e81ea162e5e1d4aa81f7c8e90
  | 5, 0 => 0xf27aa6a5d051f507c5159104ba7741d8ac05225eaa294541a0508cfd818360617ecfa1837702c5a955ccd233554c825e3a6b8d412b0e7274276bea4325303d37206585ea1b8a7ef1126b25b70241d3e1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x200000c00002
  | 5, 0 => 0x400001000000000000000000000100000400000000008000000000040000000000400000000000000030000040000000000800000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 1 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 2 => checkCutEntry dom_11 roots_11 4 s ws hint
  | 3 => checkCutEntry dom_12 roots_12 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_13 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_13 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_13 == dom_13) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_13 goalM u ys) : RunD dom_13 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_13 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

end S_13

end PEqualNP.Outside.L_meta_16977_aux
