import Join5198
import PEqualNP.Outside.L_meta_5254
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover PEqualNP.GenericRejection
open PEqualNP.Outside.Join5198
namespace PEqualNP.Outside.Linear5198
def D : Finset (Fin 13) := {0,1,3,9}
theorem geom : ∀ p l : Fin 13, p-l ∈ D ↔ p ∈ singerLines3 l := by decide +kernel

theorem linearLower (C : Circuit) (hm : Monotone2 C) (a b : ℕ)
    (pos : ∀ p l : Fin 13, p ∈ singerLines3 l → W C a {p} {l} = true ∨ W C b {p} {l} = true)
    (neg : ∀ Q, IsQuadrangle singerLines3 Q → W C a Q (missLines singerLines3 Q) = false ∧ W C b Q (missLines singerLines3 Q) = false)
    (deg : ∀ k ∈ [a,b], (C.lineDegrees 26 (Finset.Ico 13 26)).getD k 0 ≤ 1) : 63 ≤ C.size := by
  let J := join C a b
  have bound : HasLineDegree 26 (Finset.Ico 13 26) J 1 := by
    change (join C a b).lineDeg 26 _ ≤ 1
    rw [degree,max_le_iff]
    exact ⟨deg a (by simp),deg b (by simp)⟩
  have big : 64 ≤ J.size := by
    apply PEqualNP.Outside.L_meta_5254 J (mono hm a b) _ bound
    intro truth x test
    cases truth with
    | true =>
      obtain ⟨p,l,h,rfl⟩ := test
      have eq := eval C a b {p} {l}
      simp only [incidenceInput,Finset.mem_singleton] at eq
      rw [eq]
      exact Bool.or_eq_true_iff.mpr (pos p l ((geom p l).mp h))
    | false =>
      obtain ⟨Q,sz,arc,rfl⟩ := test
      have sq : IsQuadrangle singerLines3 Q := by
        refine ⟨sz,fun l => ?_⟩
        have e : Q ∩ singerLines3 l = Q.filter (fun p => p-l ∈ D) := by
          ext p; simp [geom]
        rw [e]; exact arc l
      have off (l : Fin 13) : l ∈ missLines singerLines3 Q ↔ ∀ p ∈ Q, p-l ∉ D := by
        simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and,Finset.disjoint_left,geom]
        constructor
        · intro h p hp hq; exact h hq hp
        · intro h p hp hq; exact h p hq hp
      have eq := eval C a b Q (missLines singerLines3 Q)
      rw [(neg Q sq).1,(neg Q sq).2] at eq
      calc
        _ = J.eval (incidenceInput Q (missLines singerLines3 Q)) := by
          apply congrArg J.eval
          unfold incidenceInput
          apply congrArg (fun r : List Bool => List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++ r)
          apply congrArg List.ofFn
          funext l
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          exact (off l).symm
        _ = false := eq
  change 64 ≤ (join C a b).size at big
  rw [size] at big; omega
end PEqualNP.Outside.Linear5198
#print axioms PEqualNP.Outside.Linear5198.linearLower
