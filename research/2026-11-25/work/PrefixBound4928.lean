import Suffix4928
open Features4928 LocalFano4126 PEqualNP.CircuitLowerBounds
namespace Local4928
def inputs (P U : Finset V) (i : Fin 14) : Bool :=
  if h : i.val < 7 then decide ((⟨i.val,h⟩ : V) ∈ P)
  else decide ((⟨i.val-7,by have := i.isLt; omega⟩ : V) ∈ U)
theorem inputCorrect (P U : Finset V) : F (inputs P U) ↔ edgeOn P U := by
  have left (p : V) : inputs P U (Fin.castAdd 7 p) = decide (p ∈ P) := by simp [inputs,p.isLt]
  have right (l : V) : inputs P U (Fin.natAdd 7 l) = decide (l ∈ U) := by simp [inputs,Fin.natAdd]
  constructor
  · rintro ⟨p,l,inc,hp,hl⟩
    exact ⟨p,of_decide_eq_true (left p ▸ hp),l,by simpa [linesAt] using inc,of_decide_eq_true (right l ▸ hl)⟩
  · rintro ⟨p,hp,l,inc,hl⟩
    exact ⟨p,l,by simpa [linesAt] using inc,(left p).trans (decide_eq_true hp),(right l).trans (decide_eq_true hl)⟩

def Observed (pre post : List Gate) (out : ℕ) (labels : ℕ → Token) :=
  ∀ i ∈ external pre post out, ∀ P U,
    valAt pre (inputs P U) i = true ↔ observe P U (labels i)

theorem suffixEnough (pre post : List Gate) (out : ℕ) (val : Valid ⟨pre ++ post,out⟩)
    (labels : ℕ → Token) (obs : Observed pre post out labels) :
    enough ((external pre post out).map labels) := by
  intro P U Q W same
  let C : Circuit := ⟨pre ++ post,out⟩
  have runs : C.eval (List.ofFn (inputs P U)) = C.eval (List.ofFn (inputs Q W)) := by
    change ((pre ++ post).foldl wireStep _).getD out false = ((pre ++ post).foldl wireStep _).getD out false
    simp only [List.foldl_append]
    apply readSupport post out
    · simp [lengthRun]
    · intro i hi lt
      have hmem : i ∈ external pre post out := List.mem_filter.mpr ⟨hi,by simpa [lengthRun] using lt⟩
      have eqv := (obs i hmem P U).trans ((same (labels i) (List.mem_map.mpr ⟨i,hmem,rfl⟩)).trans (obs i hmem Q W).symm)
      exact Bool.eq_iff_iff.mpr eqv
  exact (inputCorrect P U).symm.trans ((val.2.2 _).symm.trans
    ((iff_of_eq (congrArg (· = true) runs)).trans ((val.2.2 _).trans (inputCorrect Q W))))

theorem suffixMinimum (pre post : List Gate) (out : ℕ) (val : Valid ⟨pre ++ post,out⟩)
    (labels : ℕ → Token) (obs : Observed pre post out labels) : 13 ≤ post.length ∧
    (post.length = 13 → ((external pre post out).map labels).Nodup) := by
  obtain ⟨le,tight⟩ := interfaceClassification _ (suffixEnough pre post out val labels obs)
  have high := externalBound pre post out val
  rw [List.length_map] at le
  refine ⟨by omega,fun h => (tight ?_).1⟩
  rw [List.length_map]; omega
end Local4928
#print axioms Local4928.suffixMinimum
