import CircuitAPart3
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_16977_aux
namespace S_9
def pairsG : List (Nat × Nat) := [(2, 6), (4, 6), (4, 12), (8, 12), (10, 14), (10, 26), (10, 42), (18, 22), (18, 26), (18, 50), (20, 22), (20, 28), (24, 26), (24, 28), (34, 38), (34, 42), (34, 50), (36, 38), (36, 44), (40, 42), (40, 44), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 4, 4, 8, 10, 10, 10, 18, 18, 18, 20, 20, 24, 24, 34, 34, 34, 36, 36, 40, 40, 48, 52, 52, 56, 56]
def r2sG : List Nat := [6, 6, 12, 12, 14, 26, 42, 22, 26, 50, 22, 28, 26, 28, 38, 42, 50, 38, 44, 42, 44, 50, 54, 60, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 5 => 15
  | 6 => 10
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xe77511a6d11bbdccb197e02ea8a49cec8920bf4e7f1654644d896a013fd9525d26c253012278734a1cbfaf881901fc09186b1a11174662b60925d246
  | 6, 0 => 0xdeee3556c894e17cb197e02eabf0fefda91103de929bbc978920bf4e45028db10ebf8666009ef5f6
  | 7, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x11551155115511551111111111111111050505050505050500550055005500550044004400440044000500050005000500005555000055550000000055555555
  | 0, 1 => 0x55550000555500005550555055505550550055005500550050555055505550555050505050505050444444444444444444444444000000004400440044004400
  | 0, 2 => 0x555555555050505055555555000000005555505055555050
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x117acc4503d6a4914117ad4457b56a491a2f6ad44603daa2814117a8a458bdab51da2f6b16a68c1ab511a2f6ad43603dab30162f6ad4260456a2054127ad445
  | 6, 0, 0 => 0x45ed59940f6ad495045eb51162f6ad486045ed5a962f7356a68bdab5118117b5455045ab5054127b56a5
  | 7, 0, 0 => 0x117b56a5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffffe3ffe3c0ece7cfe4e7cf870070e0421c38107f01fc003fff
  | 0, 1 => 0xf80fe03de3c7ec60c1e0e7cf87318301801c3f10070000000070
  | 0, 2 => 0x3ffcc06fff0003e63f86
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xbddba3e94280c4a64d8063468318d1a0c21020007b017c003dbf
  | 0, 1 => 0xf84fe83defdffe72e5f2f76e9fb59b27d6bd7f35af0901089170
  | 0, 2 => 0x3ffeedffff0903f77fbf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 19 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 19 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 19 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 19 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 5 0) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 5 0) :: stateWiresS n (ids >>> 5)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 3
  | 5 => 106
  | 6 => 15
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xc894e17ca91103de009ef5f6
  | 5, 0 => 0x6e6b15296da08be96775c469664d787e64866b4f61b810305d1d00a55c81a6f059b0f7305975714e58d74d1351611c384e5c1d1d48d34d1946ecb51545028db143c04d4042c02137423432924231bff2418260a83f2991103ef79fa83de578bc3d5d2b1839f193b038fdad373771174237272296367c276e35c2b3aa3149fbb430f9b38330602c332f6bafef2df959362caa0b3b2bf37093297eb424276abb79264621db2512ec2b24982a05247a692822ade254220f8ca01d8eff491c6a746a1b12df04176a2f3714447d23129b33ee100e14170fe7d2510ebf86660bb638c60a97920e07215e2206ed8b2e05cc22e2058f0e8d037ef11501ea44f4009ef5f6
  | 5, 1 => 0xfeb66bbae4605ff0deee3556da6eec38cd5dd687cb74dc9bc894e17cbea9733ebcf336a4ba39e421b40f9908b2d634ddb2cded72b21f9a35b1f7cb58b12b6c36abf0fefda91103dea55430d8a1e8f17ea127b8309ff7eb879c96fa119c907fc99b7d27a899f6a9f2939387ca9352573f929bbc97917f85c890c3bbb090a07422902700288a0e0c5f8341b7ab7ec014a87c05848e7adfbf297a3bd46c7535b93672a0d11c713fde12
  | 6, 0 => 0xcd5dd687b2cded729b7d27a89352573f713fde125c81a6f046ecb51539f193b0276abb79247a692822ade2541b12df040fe7d25105cc22e2058f0e8d
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0xc1100
  | 5, 0 => 0x30040800000300404c01020000040000100001400004000018c01040000140000200000000000000008c5104000004c01020000040000400000c000010000100000020440000002300410000020000100000700001000001
  | 5, 1 => 0x10c51020000040000600001c0000331441000000000010000000000000000120040400006000000000010000180000100000c00000304400000073144100000420040400000000008c51033144080000700000cc1100
  | 5, 2 => 0x304400c01010000000000700000400005000000000000000040000000001c0000500000000001000004000010000040000100000400001000000000000000140000010440000002000000000073044000000000000400000
  | 5, 3 => 0x1c0000000000000001000008000000000004010100001000007
  | 6, 0 => 0x200000c00001000004000000000000000000000400005000008000000000140000100000c00004
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 3 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 4 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 5 => checkCutEntry dom_8 roots_8 5 s ws hint
  | 6 => checkCutEntry dom_3 roots_3 4 s ws hint
  | 7 => checkCutEntry dom_0 roots_0 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_9 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_9 == dom_9) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_9 goalM u ys) : RunD dom_9 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_9 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

end S_9

end PEqualNP.Outside.L_meta_16977_aux
