import Cap4126
namespace CapCase1
open SignedRect4126
open PEqualNP.MetaComplexity
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def signals : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 288160007407550752, 270286071508633728, 229736628138025984, 183565875465490436, 218994303132270608, 155696362464477250, 9]
def positive (i : Fin 15) : Finset (Fin 21) := Finset.univ.filter fun j => ((signals.getD i.val 0).testBit (j.val + 0))
def negative (i : Fin 15) : Finset (Fin 37) := Finset.univ.filter fun j => !((signals.getD i.val 0).testBit (j.val + 21))
def words : List ℕ := [63907011022258387020186531401078530542791165291480352961133818018960981953359582939086976, 63918667124540065928870886257821988142903332963826014037050172651327322350394022614696064, 63918667035613098333157797971684591628715974798846814014648740423277512734502381204177024, 63907011022258387020186531401078530542791165291480352961133818018960981953359582939086976, 63907011022258387020186531391474565174992457635165756085877003221818305063121660137209984, 63907011022258387020186533879014657400566507388741230546948357160873864604455710845075584, 63901182926653385298715566803824386147725289516820433339521829232800325560833899715657856, 63912839028935064207398657913067821061597065046646270340117979092377028034136455969276544, 63912839117863388741658759745832697624097416081949806915603951853648862495633794096201856, 61917733253951545143548001362455350344673434312740921291420869338095983071314878365140096, 65896288761154490584805809154067275154394079202393559611954239762388270774743046662683776, 65896303997308271942238422638614506730070808179480689617148885248411726265110938175700096, 63901183015580352935838501296955154043409747230670034672147417159373164039202452479049856, 63912839028935064165988811706074449680858473429568388054138559031653576318396746459808384, 63912839028936421187355517666688672491394055332021955575397269921492905241412417869611136, 63912839028935064207399289796421797772520344715254269474305036960469954177611170851094656, 63901183015583066771519522814542011551096498081855690794112662788293445463069952997490816, 63912839029167100698723137317803359042015006065824384291380834994772943476170841879773824, 63901183104510034367232611100679407777949711344827388976330875227974811619101801646686336, 63912839028935064207399289796421798347201788035573272380976316821036451601573037788397696, 63912854235678559607071080454291534446072321586309769279314535516150800557291982989329024]
def packed (i : Fin 21) := words.getD i.val 0
def W (i : Fin 21) (j : Fin 37) : ℤ := (((packed i >>> (8*j.val)) % 256 : ℕ) : ℤ) - 128
def X (p : Fin 21) (i : Fin 15) := decide (p ∈ positive i)
def Y (q : Fin 37) (i : Fin 15) := !decide (q ∈ negative i)
theorem test0 : ∀ A ∈ (positive 0).powerset, (∑ j ∈ negative 0, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 0).powerset, (∑ j ∈ negative 0, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test1 : ∀ A ∈ (positive 1).powerset, (∑ j ∈ negative 1, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 1).powerset, (∑ j ∈ negative 1, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test2 : ∀ A ∈ (positive 2).powerset, (∑ j ∈ negative 2, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 2).powerset, (∑ j ∈ negative 2, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test3 : ∀ A ∈ (positive 3).powerset, (∑ j ∈ negative 3, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 3).powerset, (∑ j ∈ negative 3, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test4 : ∀ A ∈ (positive 4).powerset, (∑ j ∈ negative 4, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 4).powerset, (∑ j ∈ negative 4, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test5 : ∀ A ∈ (positive 5).powerset, (∑ j ∈ negative 5, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 5).powerset, (∑ j ∈ negative 5, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test6 : ∀ A ∈ (positive 6).powerset, (∑ j ∈ negative 6, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 6).powerset, (∑ j ∈ negative 6, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test7 : ∀ A ∈ (positive 7).powerset, (∑ j ∈ negative 7, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 7).powerset, (∑ j ∈ negative 7, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test8 : ∀ A ∈ (positive 8).powerset, (∑ j ∈ negative 8, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 8).powerset, (∑ j ∈ negative 8, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test9 : ∀ A ∈ (positive 9).powerset, (∑ j ∈ negative 9, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 9).powerset, (∑ j ∈ negative 9, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test10 : ∀ A ∈ (positive 10).powerset, (∑ j ∈ negative 10, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 10).powerset, (∑ j ∈ negative 10, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test11 : ∀ A ∈ (positive 11).powerset, (∑ j ∈ negative 11, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 11).powerset, (∑ j ∈ negative 11, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test12 : ∀ A ∈ (positive 12).powerset, (∑ j ∈ negative 12, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 12).powerset, (∑ j ∈ negative 12, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test13 : ∀ A ∈ (positive 13).powerset, (∑ j ∈ negative 13, max 0 (∑ a ∈ A, W a j)) ≤ 12 := by
  letI : Decidable (∀ A ∈ (positive 13).powerset, (∑ j ∈ negative 13, max 0 (∑ a ∈ A, W a j)) ≤ 12) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem test14 : ∀ A ∈ (positive 14).powerset, (∑ j ∈ negative 14, max 0 (∑ a ∈ A, W a j)) ≤ 0 := by
  letI : Decidable (∀ A ∈ (positive 14).powerset, (∑ j ∈ negative 14, max 0 (∑ a ∈ A, W a j)) ≤ 0) := Finset.decidableDforallFinset
  exact of_decide_eq_true rfl
theorem cap (i : Fin 15) (A : Finset (Fin 21)) (B : Finset (Fin 37))
    (hA : ∀ p ∈ A, X p i = true) (hB : ∀ q ∈ B, Y q i = false) :
    mass W A B ≤ if i = 14 then 0 else 12 := by
  refine (cap_iff W (positive i) (negative i) _).mpr ?_ A (by simpa [X,Finset.subset_iff] using hA) B (by simpa [Y,Finset.subset_iff] using hB)
  fin_cases i
  · exact test0
  · exact test1
  · exact test2
  · exact test3
  · exact test4
  · exact test5
  · exact test6
  · exact test7
  · exact test8
  · exact test9
  · exact test10
  · exact test11
  · exact test12
  · exact test13
  · exact test14
theorem excludes (f : DMFormula 15) (pf : pos f) (sz : 2 + f.leaves ≤ 28)
    (used : 2 ≤ occurrences 14 f) (yes : ∀ p, f.eval (X p) = true)
    (no : ∀ q, f.eval (Y q) = false) : False := by
  apply exclude W X Y 14 Finset.univ Finset.univ 12 0 2 (by decide) (by decide) cap _ f pf sz used (fun p _ => yes p) (fun q _ => no q)
  decide +kernel
end CapCase1
#print axioms CapCase1.excludes
