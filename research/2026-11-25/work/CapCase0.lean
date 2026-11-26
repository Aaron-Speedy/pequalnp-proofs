import Cap4126
namespace CapCase0
open SignedRect4126
open PEqualNP.MetaComplexity
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def signals : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 288160007407550752, 270286071508633728, 229736628138025984, 183565875465490436, 218994303132270608, 155696362464477250, 98933359855537727]
def positive (i : Fin 15) : Finset (Fin 21) := Finset.univ.filter fun j => ((signals.getD i.val 0).testBit (j.val + 0))
def negative (i : Fin 15) : Finset (Fin 37) := Finset.univ.filter fun j => !((signals.getD i.val 0).testBit (j.val + 21))
def words : List ℕ := [63907011022258387020159571457625231471585824973429748353453592786913343793589148247228544, 63907011140829486399252340720441238068320928298864778502263211666086745021650387945881216, 63907011022260196278536530706756938042100140951602471073844970446033430313961014488104576, 63907011022258387020267411236259143809469541656068016414442328351973602008956068645994624, 63907011022258387020186531391436951700219878064781593371970098184299456841107331121970816, 63907011051901614184689912366231923723467176142562520720061917538578933991094250060676736, 63907010903687287641148208588234402918659251012867878918875446300608989380752121327157632, 63907011140829486399170934317374505318744464515069876188332168056057867096091460334748032, 63907011140829486399252656660530046268613012496325591388578322534611343457332823815324032, 63907011022258387020159571457625329551300440389881121858004527626024037683011452672311424, 63907011022258839360696019947963460296279712957379873487013144094520010739412846124236416, 63907011051901161864993818572013678309133833919558184354291089271621181237835537466818176, 63907011022256577796372223774413179191912962853813973185377176938103145885714965258928512, 63907011022260196243946919131195729045496553009182510985500636818903592808864105516597632, 63907011022260196299241769750342431837349633052235082091303693360467105147772604162081152, 63907011022258387020240451302447497140628757635132465686869898573307682838260029256204672, 63907011022260196271553904521571787107085634656109547724741491821856787849573573518000512, 63907011022258387020159992705185041598989319155685260344758581430122154596253027830694272, 63907011140829486399171355569754982076223252339549138252108548789964627839049234695487872, 63907011022258387020240451302447497906870682061701795846841045435929031689378873082872192, 63907011022258387047766556843180622136851819709922426150219767100388400435432674207695232]
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
end CapCase0
#print axioms CapCase0.excludes
