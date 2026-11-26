import PEqualNP.Defs
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
def allowed (w : Word) : Bool := (if w < 61440 then (if w < 52424 then (if w < 43656 then (if w < 41120 then (if w < 34944 then (if w < 32896 then (w == 32768) else (if w < 34816 then (w == 32896) else (w == 34816))) else (if w < 40960 then (if w < 34952 then (w == 34944) else (w == 34952)) else (if w < 41088 then (w == 40960) else (w == 41088)))) else (if w < 43168 then (if w < 43008 then (w == 41120) else (if w < 43144 then (w == 43008) else (w == 43144))) else (if w < 43520 then (if w < 43176 then (w == 43168) else (w == 43176)) else (if w < 43648 then (w == 43520) else (w == 43648))))) else (if w < 51200 then (if w < 43690 then (if w < 43680 then (w == 43656) else (if w < 43688 then (w == 43680) else (w == 43688))) else (if w < 49280 then (if w < 49152 then (w == 43690) else (w == 49152)) else (if w < 49344 then (w == 49280) else (w == 49344)))) else (if w < 52224 then (if w < 51392 then (if w < 51336 then (w == 51200) else (w == 51336)) else (if w < 51400 then (w == 51392) else (w == 51400))) else (if w < 52360 then (if w < 52352 then (w == 52224) else (w == 52352)) else (if w < 52416 then (w == 52360) else (w == 52416)))))) else (if w < 60576 then (if w < 59904 then (if w < 57504 then (if w < 52428 then (w == 52424) else (if w < 57344 then (w == 52428) else (w == 57344))) else (if w < 57568 then (if w < 57536 then (w == 57504) else (w == 57536)) else (if w < 59624 then (w == 57568) else (w == 59624)))) else (if w < 60104 then (if w < 60074 then (w == 59904) else (if w < 60096 then (w == 60074) else (w == 60096))) else (if w < 60138 then (if w < 60128 then (w == 60104) else (w == 60128)) else (if w < 60416 then (w == 60138) else (w == 60416))))) else (if w < 61088 then (if w < 60640 then (if w < 60584 then (w == 60576) else (if w < 60620 then (w == 60584) else (w == 60620))) else (if w < 60928 then (if w < 60652 then (w == 60640) else (w == 60652)) else (if w < 61064 then (w == 60928) else (w == 61064)))) else (if w < 61152 then (if w < 61120 then (if w < 61098 then (w == 61088) else (w == 61098)) else (if w < 61132 then (w == 61120) else (w == 61132))) else (if w < 61164 then (if w < 61162 then (w == 61152) else (w == 61162)) else (if w < 61166 then (w == 61164) else (w == 61166))))))) else (if w < 64752 then (if w < 64160 then (if w < 63624 then (if w < 61632 then (if w < 61568 then (w == 61440) else (if w < 61600 then (w == 61568) else (w == 61600))) else (if w < 61680 then (if w < 61664 then (w == 61632) else (w == 61664)) else (if w < 63488 then (w == 61680) else (w == 63488)))) else (if w < 63728 then (if w < 63656 then (w == 63624) else (if w < 63688 then (w == 63656) else (w == 63688))) else (if w < 64000 then (if w < 63736 then (w == 63728) else (w == 63736)) else (if w < 64136 then (w == 64000) else (w == 64136))))) else (if w < 64250 then (if w < 64200 then (if w < 64170 then (w == 64160) else (if w < 64192 then (w == 64170) else (w == 64192))) else (if w < 64240 then (if w < 64234 then (w == 64200) else (w == 64234)) else (if w < 64248 then (w == 64240) else (w == 64248)))) else (if w < 64680 then (if w < 64648 then (if w < 64512 then (w == 64250) else (w == 64512)) else (if w < 64672 then (w == 64648) else (w == 64672))) else (if w < 64716 then (if w < 64704 then (w == 64680) else (w == 64704)) else (if w < 64748 then (w == 64716) else (w == 64748)))))) else (if w < 65440 then (if w < 65264 then (if w < 65024 then (if w < 64760 then (w == 64752) else (if w < 64764 then (w == 64760) else (w == 64764))) else (if w < 65228 then (if w < 65194 then (w == 65024) else (w == 65194)) else (if w < 65262 then (w == 65228) else (w == 65262)))) else (if w < 65278 then (if w < 65274 then (w == 65264) else (if w < 65276 then (w == 65274) else (w == 65276))) else (if w < 65408 then (if w < 65280 then (w == 65278) else (w == 65280)) else (if w < 65416 then (w == 65408) else (w == 65416))))) else (if w < 65514 then (if w < 65472 then (if w < 65448 then (w == 65440) else (if w < 65450 then (w == 65448) else (w == 65450))) else (if w < 65484 then (if w < 65480 then (w == 65472) else (w == 65480)) else (if w < 65504 then (w == 65484) else (w == 65504)))) else (if w < 65528 then (if w < 65518 then (if w < 65516 then (w == 65514) else (w == 65516)) else (if w < 65520 then (w == 65518) else (w == 65520))) else (if w < 65532 then (if w < 65530 then (w == 65528) else (w == 65530)) else (if w < 65534 then (w == 65532) else (w == 65534))))))))
def catalog : List (Word × Formula) := [(32768,(.conj (.conj (.var 3) (.var 2)) (.conj (.var 1) (.var 0)))),
(32896,(.conj (.var 2) (.conj (.var 1) (.var 0)))),
(34816,(.conj (.var 3) (.conj (.var 1) (.var 0)))),
(34944,(.conj (.disj (.var 3) (.var 2)) (.conj (.var 1) (.var 0)))),
(34952,(.conj (.var 1) (.var 0))),
(40960,(.conj (.var 3) (.conj (.var 2) (.var 0)))),
(41088,(.conj (.disj (.var 3) (.var 1)) (.conj (.var 2) (.var 0)))),
(41120,(.conj (.var 2) (.var 0))),
(43008,(.conj (.disj (.var 2) (.var 1)) (.conj (.var 3) (.var 0)))),
(43144,(.conj (.var 0) (.disj (.var 1) (.conj (.var 3) (.var 2))))),
(43168,(.conj (.var 0) (.disj (.var 2) (.conj (.var 3) (.var 1))))),
(43176,(.conj (.var 0) (.disj (.var 2) (.var 1)))),
(43520,(.conj (.var 3) (.var 0))),
(43648,(.conj (.var 0) (.disj (.var 3) (.conj (.var 2) (.var 1))))),
(43656,(.conj (.var 0) (.disj (.var 3) (.var 1)))),
(43680,(.conj (.var 0) (.disj (.var 3) (.var 2)))),
(43688,(.conj (.var 0) (.disj (.var 3) (.disj (.var 2) (.var 1))))),
(43690,(.var 0)),
(49152,(.conj (.var 3) (.conj (.var 2) (.var 1)))),
(49280,(.conj (.conj (.var 2) (.var 1)) (.disj (.var 3) (.var 0)))),
(49344,(.conj (.var 2) (.var 1))),
(51200,(.conj (.conj (.var 3) (.var 1)) (.disj (.var 2) (.var 0)))),
(51336,(.conj (.var 1) (.disj (.var 0) (.conj (.var 3) (.var 2))))),
(51392,(.conj (.var 1) (.disj (.var 2) (.conj (.var 3) (.var 0))))),
(51400,(.conj (.var 1) (.disj (.var 2) (.var 0)))),
(52224,(.conj (.var 3) (.var 1))),
(52352,(.conj (.var 1) (.disj (.var 3) (.conj (.var 2) (.var 0))))),
(52360,(.conj (.var 1) (.disj (.var 3) (.var 0)))),
(52416,(.conj (.var 1) (.disj (.var 3) (.var 2)))),
(52424,(.conj (.var 1) (.disj (.var 3) (.disj (.var 2) (.var 0))))),
(52428,(.var 1)),
(57344,(.conj (.conj (.var 3) (.var 2)) (.disj (.var 1) (.var 0)))),
(57504,(.conj (.var 2) (.disj (.var 0) (.conj (.var 3) (.var 1))))),
(57536,(.conj (.var 2) (.disj (.var 1) (.conj (.var 3) (.var 0))))),
(57568,(.conj (.var 2) (.disj (.var 1) (.var 0)))),
(59624,(.conj (.disj (.var 2) (.var 1)) (.disj (.var 0) (.conj (.var 2) (.var 1))))),
(59904,(.conj (.var 3) (.disj (.var 0) (.conj (.var 2) (.var 1))))),
(60074,(.disj (.var 0) (.conj (.var 3) (.conj (.var 2) (.var 1))))),
(60096,(.disj (.conj (.var 2) (.var 1)) (.conj (.var 3) (.var 0)))),
(60104,(.conj (.disj (.var 3) (.var 1)) (.disj (.var 0) (.conj (.var 2) (.var 1))))),
(60128,(.conj (.disj (.var 3) (.var 2)) (.disj (.var 0) (.conj (.var 2) (.var 1))))),
(60138,(.disj (.var 0) (.conj (.var 2) (.var 1)))),
(60416,(.conj (.var 3) (.disj (.var 1) (.conj (.var 2) (.var 0))))),
(60576,(.disj (.conj (.var 3) (.var 1)) (.conj (.var 2) (.var 0)))),
(60584,(.disj (.conj (.var 3) (.var 1)) (.conj (.var 0) (.disj (.var 2) (.var 1))))),
(60620,(.disj (.var 1) (.conj (.var 3) (.conj (.var 2) (.var 0))))),
(60640,(.conj (.disj (.var 3) (.var 2)) (.disj (.var 1) (.conj (.var 2) (.var 0))))),
(60652,(.disj (.var 1) (.conj (.var 2) (.var 0)))),
(60928,(.conj (.var 3) (.disj (.var 1) (.var 0)))),
(61064,(.conj (.disj (.var 3) (.var 1)) (.disj (.var 0) (.conj (.var 3) (.var 1))))),
(61088,(.conj (.disj (.var 3) (.var 2)) (.disj (.var 0) (.conj (.var 3) (.var 1))))),
(61098,(.disj (.var 0) (.conj (.var 3) (.var 1)))),
(61120,(.conj (.disj (.var 3) (.var 2)) (.disj (.var 1) (.conj (.var 3) (.var 0))))),
(61132,(.disj (.var 1) (.conj (.var 3) (.var 0)))),
(61152,(.conj (.disj (.var 3) (.var 2)) (.disj (.var 1) (.var 0)))),
(61162,(.disj (.var 0) (.conj (.var 1) (.disj (.var 3) (.var 2))))),
(61164,(.disj (.var 1) (.conj (.var 0) (.disj (.var 3) (.var 2))))),
(61166,(.disj (.var 1) (.var 0))),
(61440,(.conj (.var 3) (.var 2))),
(61568,(.conj (.var 2) (.disj (.var 3) (.conj (.var 1) (.var 0))))),
(61600,(.conj (.var 2) (.disj (.var 3) (.var 0)))),
(61632,(.conj (.var 2) (.disj (.var 3) (.var 1)))),
(61664,(.conj (.var 2) (.disj (.var 3) (.disj (.var 1) (.var 0))))),
(61680,(.var 2)),
(63488,(.conj (.var 3) (.disj (.var 2) (.conj (.var 1) (.var 0))))),
(63624,(.disj (.conj (.var 3) (.var 2)) (.conj (.var 1) (.var 0)))),
(63656,(.disj (.conj (.var 3) (.var 2)) (.conj (.var 0) (.disj (.var 2) (.var 1))))),
(63688,(.disj (.conj (.var 3) (.var 2)) (.conj (.var 1) (.disj (.var 2) (.var 0))))),
(63728,(.disj (.var 2) (.conj (.var 3) (.conj (.var 1) (.var 0))))),
(63736,(.disj (.var 2) (.conj (.var 1) (.var 0)))),
(64000,(.conj (.var 3) (.disj (.var 2) (.var 0)))),
(64136,(.disj (.conj (.var 3) (.var 2)) (.conj (.var 0) (.disj (.var 3) (.var 1))))),
(64160,(.conj (.disj (.var 3) (.var 2)) (.disj (.var 0) (.conj (.var 3) (.var 2))))),
(64170,(.disj (.var 0) (.conj (.var 3) (.var 2)))),
(64192,(.conj (.disj (.var 3) (.var 1)) (.disj (.var 2) (.conj (.var 3) (.var 0))))),
(64200,(.conj (.disj (.var 3) (.var 1)) (.disj (.var 2) (.var 0)))),
(64234,(.disj (.var 0) (.conj (.var 2) (.disj (.var 3) (.var 1))))),
(64240,(.disj (.var 2) (.conj (.var 3) (.var 0)))),
(64248,(.disj (.var 2) (.conj (.var 0) (.disj (.var 3) (.var 1))))),
(64250,(.disj (.var 2) (.var 0))),
(64512,(.conj (.var 3) (.disj (.var 2) (.var 1)))),
(64648,(.disj (.conj (.var 3) (.var 2)) (.conj (.var 1) (.disj (.var 3) (.var 0))))),
(64672,(.disj (.conj (.var 3) (.var 1)) (.conj (.var 2) (.disj (.var 3) (.var 0))))),
(64680,(.conj (.disj (.var 2) (.var 1)) (.disj (.var 3) (.var 0)))),
(64704,(.conj (.disj (.var 3) (.var 2)) (.disj (.var 1) (.conj (.var 3) (.var 2))))),
(64716,(.disj (.var 1) (.conj (.var 3) (.var 2)))),
(64748,(.disj (.var 1) (.conj (.var 2) (.disj (.var 3) (.var 0))))),
(64752,(.disj (.var 2) (.conj (.var 3) (.var 1)))),
(64760,(.disj (.var 2) (.conj (.var 1) (.disj (.var 3) (.var 0))))),
(64764,(.disj (.var 2) (.var 1))),
(65024,(.conj (.var 3) (.disj (.var 2) (.disj (.var 1) (.var 0))))),
(65194,(.disj (.var 0) (.conj (.var 3) (.disj (.var 2) (.var 1))))),
(65228,(.disj (.var 1) (.conj (.var 3) (.disj (.var 2) (.var 0))))),
(65262,(.disj (.conj (.var 3) (.var 2)) (.disj (.var 1) (.var 0)))),
(65264,(.disj (.var 2) (.conj (.var 3) (.disj (.var 1) (.var 0))))),
(65274,(.disj (.conj (.var 3) (.var 1)) (.disj (.var 2) (.var 0)))),
(65276,(.disj (.disj (.var 2) (.var 1)) (.conj (.var 3) (.var 0)))),
(65278,(.disj (.var 2) (.disj (.var 1) (.var 0)))),
(65280,(.var 3)),
(65408,(.disj (.var 3) (.conj (.var 2) (.conj (.var 1) (.var 0))))),
(65416,(.disj (.var 3) (.conj (.var 1) (.var 0)))),
(65440,(.disj (.var 3) (.conj (.var 2) (.var 0)))),
(65448,(.disj (.var 3) (.conj (.var 0) (.disj (.var 2) (.var 1))))),
(65450,(.disj (.var 3) (.var 0))),
(65472,(.disj (.var 3) (.conj (.var 2) (.var 1)))),
(65480,(.disj (.var 3) (.conj (.var 1) (.disj (.var 2) (.var 0))))),
(65484,(.disj (.var 3) (.var 1))),
(65504,(.disj (.var 3) (.conj (.var 2) (.disj (.var 1) (.var 0))))),
(65514,(.disj (.conj (.var 2) (.var 1)) (.disj (.var 3) (.var 0)))),
(65516,(.disj (.disj (.var 3) (.var 1)) (.conj (.var 2) (.var 0)))),
(65518,(.disj (.var 3) (.disj (.var 1) (.var 0)))),
(65520,(.disj (.var 3) (.var 2))),
(65528,(.disj (.disj (.var 3) (.var 2)) (.conj (.var 1) (.var 0)))),
(65530,(.disj (.var 3) (.disj (.var 2) (.var 0)))),
(65532,(.disj (.var 3) (.disj (.var 2) (.var 1)))),
(65534,(.disj (.disj (.var 3) (.var 2)) (.disj (.var 1) (.var 0))))]
theorem validCatalog : ∀ pair ∈ catalog, truth pair.2 = pair.1 ∧ gates pair.2 ≤ 4 := by decide +kernel
theorem lookup (w : Word) (h : allowed w = true) : ∃ f : Formula, truth f = w ∧ gates f ≤ 4 := by
  have finite : ∀ v : Word, allowed v = true → v ∈ catalog.map Prod.fst := by
    intro v hv
    simp only [allowed] at hv
    repeat' split at hv
    all_goals simp only [beq_iff_eq] at hv; subst v; decide +kernel
  obtain ⟨⟨v,f⟩,mem,eq⟩ := List.mem_map.mp (finite w h)
  subst w
  exact ⟨f,validCatalog _ mem⟩
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block0 : ok 3 (34952::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block1 : ok 3 (41120::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block2 : ok 3 (43520::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block3 : ok 3 (49344::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block4 : ok 3 (52224::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block5 : ok 3 (61166::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block6 : ok 3 (61440::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block7 : ok 3 (64250::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block8 : ok 3 (64764::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block9 : ok 3 (65450::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block10 : ok 3 (65484::vars) allowed = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem block11 : ok 3 (65520::vars) allowed = true := by decide +kernel
theorem small : ∀ w, Reached 4 vars w → ∃ f : Formula, truth f = w ∧ gates f ≤ 4 := by
  intro w hw
  apply lookup w
  apply ok_sound hw
  change vars.all allowed && (trace vars).all _ = true
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel,List.all_eq_true.mpr ?_⟩
  intro v hv
  by_cases fresh : v ∈ vars
  · simp [fresh]
  · have casesV : ∀ a ∈ trace vars, a ∉ vars → a = 34952 ∨ a = 41120 ∨ a = 43520 ∨ a = 49344 ∨ a = 52224 ∨ a = 61166 ∨ a = 61440 ∨ a = 64250 ∨ a = 64764 ∨ a = 65450 ∨ a = 65484 ∨ a = 65520 := by decide +kernel
    rcases casesV v hv fresh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp [block0]
    · simp [block1]
    · simp [block2]
    · simp [block3]
    · simp [block4]
    · simp [block5]
    · simp [block6]
    · simp [block7]
    · simp [block8]
    · simp [block9]
    · simp [block10]
    · simp [block11]
end PEqualNP.Outside.Small2056
#print axioms PEqualNP.Outside.Small2056.small
