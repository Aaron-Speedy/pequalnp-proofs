import SharedOr2056
import FreeInput2056
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.MonoPin9738
open PEqualNP.Outside.TwoPoints2056
namespace PEqualNP.Outside.ClassOr2056
def ext (a b : Fin 9) (x : Fin 9 → Bool) : Fin 10 → Bool :=
  Fin.snoc (α := fun _ => Bool) x (x a || x b)
def Paid (a b : Fin 9) (s : ℕ) := ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
  ∀ x, C.eval (List.ofFn (ext a b x)) = f0 x

theorem payForOr {a b s} (hp : Paid a b s) : 8 ≤ s := by
  have full := FreeInput2056.pay (f := f0) (a := a) (b := b) (s := s) hp
  have := (TwoPoints2056.exactMinimum _).mp full
  omega

theorem ignore (a b : Fin 9) {s : ℕ} (hs : 9 ≤ s) : Paid a b s := by
  obtain ⟨D,hm,sz,ev⟩ := relabel_size (fun t : Fin 9 => t.castSucc) f0 _ ((TwoPoints2056.exactMinimum s).mpr hs)
  exact ⟨D,hm,sz,fun x => (ev (ext a b x)).trans (by simp [Function.comp_def,ext])⟩

theorem move {a b : Fin 9} {s : ℕ} (σ : Fin 9 → Fin 9)
    (symm : ∀ x, f0 (x ∘ σ) = f0 x) (hp : Paid a b s) : Paid (σ a) (σ b) s := by
  obtain ⟨C,m,sz,ev⟩ := hp
  let ρ : Fin 10 → Fin 10 := Fin.snoc (α := fun _ => Fin 10) (fun j => (σ j).castSucc) (Fin.last 9)
  obtain ⟨D,dm,ds,de⟩ := relabel_size ρ (fun y => C.eval (List.ofFn y)) s ⟨C,m,sz,fun _ => rfl⟩
  refine ⟨D,dm,ds,fun x => (de _).trans ?_⟩
  have eq : ext (σ a) (σ b) x ∘ ρ = ext a b (x ∘ σ) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [ρ,ext,Function.comp_apply,Fin.snoc_last,Fin.snoc_castSucc]
  change C.eval (List.ofFn (ext (σ a) (σ b) x ∘ ρ)) = f0 x
  rw [eq,ev,symm]

def samePrivate : Circuit := ⟨[⟨.or,[4,8]⟩,⟨.or,[9,10]⟩,⟨.and,[0,11]⟩,
   ⟨.or,[5,6]⟩,⟨.or,[7,8]⟩,⟨.or,[13,14]⟩,⟨.and,[1,15]⟩,⟨.or,[12,16]⟩],17⟩
def withCommon : Circuit := ⟨[⟨.or,[2,3]⟩,⟨.or,[9,10]⟩,⟨.and,[0,11]⟩,
   ⟨.or,[5,6]⟩,⟨.or,[7,8]⟩,⟨.or,[13,14]⟩,⟨.and,[1,15]⟩,⟨.or,[12,16]⟩],17⟩

theorem privateMin (s : ℕ) : Paid 2 3 s ↔ 8 ≤ s :=
  ⟨payForOr,fun hs => ⟨samePrivate,by simp [samePrivate,Monotone2],hs,by decide +kernel⟩⟩
theorem commonMin (s : ℕ) : Paid 4 8 s ↔ 8 ≤ s :=
  ⟨payForOr,fun hs => ⟨withCommon,by simp [withCommon,Monotone2],hs,by decide +kernel⟩⟩
theorem crossMin (s : ℕ) : Paid 4 7 s ↔ 9 ≤ s := by
  refine ⟨?_,ignore _ _⟩
  rintro ⟨C,hm,sz,ev⟩
  exact (SharedOr2056.crossLower C hm ev).trans sz

theorem moveIff {a b c d : Fin 9} {s : ℕ} (σ τ : Fin 9 → Fin 9)
    (pres : ∀ x, f0 (x ∘ σ) = f0 x) (left : ∀ i, τ (σ i) = i)
    (ac : σ a = c) (bd : σ b = d) : Paid c d s ↔ Paid a b s := by
  subst c; subst d
  refine ⟨fun h => ?_, move σ pres⟩
  have inv (x : Fin 9 → Bool) : f0 (x ∘ τ) = f0 x := by
    have h := pres (x ∘ τ)
    have eq : (x ∘ τ) ∘ σ = x := funext (fun i => congrArg x (left i))
    rw [eq] at h; exact h.symm
  simpa only [left] using move τ inv h

def cost (a b : Fin 9) : ℕ := if a.val < 5 && 5 ≤ b.val && b.val < 8 then 9 else 8
theorem case23 (s : ℕ) : Paid 2 3 s ↔ cost 2 3 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 2) (b := 3) σ τ symm (by decide) rfl rfl).trans (privateMin s)
theorem case24 (s : ℕ) : Paid 2 4 s ↔ cost 2 4 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 2, 4, 3, 5, 6, 7, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 2, 4, 3, 5, 6, 7, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 2 || x 4 || x 3 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 2) (b := 3) σ τ symm (by decide) rfl rfl).trans (privateMin s)
theorem case25 (s : ℕ) : Paid 2 5 s ↔ cost 2 5 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 3, 4, 2, 6, 7, 5, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 4, 2, 3, 7, 5, 6, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 3 || x 4 || x 2 || x 8)) || (x 1 && (x 6 || x 7 || x 5 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 7) σ τ symm (by decide) rfl rfl).trans (crossMin s)
theorem case26 (s : ℕ) : Paid 2 6 s ↔ cost 2 6 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 3, 4, 2, 5, 7, 6, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 4, 2, 3, 5, 7, 6, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 3 || x 4 || x 2 || x 8)) || (x 1 && (x 5 || x 7 || x 6 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 7) σ τ symm (by decide) rfl rfl).trans (crossMin s)
theorem case27 (s : ℕ) : Paid 2 7 s ↔ cost 2 7 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 3, 4, 2, 5, 6, 7, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 4, 2, 3, 5, 6, 7, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 3 || x 4 || x 2 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 7) σ τ symm (by decide) rfl rfl).trans (crossMin s)
theorem case28 (s : ℕ) : Paid 2 8 s ↔ cost 2 8 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 3, 4, 2, 5, 6, 7, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 4, 2, 3, 5, 6, 7, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 3 || x 4 || x 2 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 8) σ τ symm (by decide) rfl rfl).trans (commonMin s)
theorem case34 (s : ℕ) : Paid 3 4 s ↔ cost 3 4 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 3, 4, 2, 5, 6, 7, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 4, 2, 3, 5, 6, 7, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 3 || x 4 || x 2 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 2) (b := 3) σ τ symm (by decide) rfl rfl).trans (privateMin s)
theorem case35 (s : ℕ) : Paid 3 5 s ↔ cost 3 5 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 2, 4, 3, 6, 7, 5, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 2, 4, 3, 7, 5, 6, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 2 || x 4 || x 3 || x 8)) || (x 1 && (x 6 || x 7 || x 5 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 7) σ τ symm (by decide) rfl rfl).trans (crossMin s)
theorem case36 (s : ℕ) : Paid 3 6 s ↔ cost 3 6 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 2, 4, 3, 5, 7, 6, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 2, 4, 3, 5, 7, 6, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 2 || x 4 || x 3 || x 8)) || (x 1 && (x 5 || x 7 || x 6 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 7) σ τ symm (by decide) rfl rfl).trans (crossMin s)
theorem case37 (s : ℕ) : Paid 3 7 s ↔ cost 3 7 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 2, 4, 3, 5, 6, 7, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 2, 4, 3, 5, 6, 7, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 2 || x 4 || x 3 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 7) σ τ symm (by decide) rfl rfl).trans (crossMin s)
theorem case38 (s : ℕ) : Paid 3 8 s ↔ cost 3 8 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 2, 4, 3, 5, 6, 7, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 2, 4, 3, 5, 6, 7, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 2 || x 4 || x 3 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 8) σ τ symm (by decide) rfl rfl).trans (commonMin s)
theorem case45 (s : ℕ) : Paid 4 5 s ↔ cost 4 5 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 6, 7, 5, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 7, 5, 6, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 6 || x 7 || x 5 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 7) σ τ symm (by decide) rfl rfl).trans (crossMin s)
theorem case46 (s : ℕ) : Paid 4 6 s ↔ cost 4 6 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 7, 6, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 7, 6, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 7 || x 6 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 7) σ τ symm (by decide) rfl rfl).trans (crossMin s)
theorem case47 (s : ℕ) : Paid 4 7 s ↔ cost 4 7 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 7) σ τ symm (by decide) rfl rfl).trans (crossMin s)
theorem case48 (s : ℕ) : Paid 4 8 s ↔ cost 4 8 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]
  let τ : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 8) σ τ symm (by decide) rfl rfl).trans (commonMin s)
theorem case56 (s : ℕ) : Paid 5 6 s ↔ cost 5 6 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![1, 0, 5, 6, 7, 2, 3, 4, 8]
  let τ : Fin 9 → Fin 9 := ![1, 0, 5, 6, 7, 2, 3, 4, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 1 && (x 5 || x 6 || x 7 || x 8)) || (x 0 && (x 2 || x 3 || x 4 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 2) (b := 3) σ τ symm (by decide) rfl rfl).trans (privateMin s)
theorem case57 (s : ℕ) : Paid 5 7 s ↔ cost 5 7 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![1, 0, 5, 7, 6, 2, 3, 4, 8]
  let τ : Fin 9 → Fin 9 := ![1, 0, 5, 6, 7, 2, 4, 3, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 1 && (x 5 || x 7 || x 6 || x 8)) || (x 0 && (x 2 || x 3 || x 4 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 2) (b := 3) σ τ symm (by decide) rfl rfl).trans (privateMin s)
theorem case58 (s : ℕ) : Paid 5 8 s ↔ cost 5 8 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![1, 0, 6, 7, 5, 2, 3, 4, 8]
  let τ : Fin 9 → Fin 9 := ![1, 0, 5, 6, 7, 4, 2, 3, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 1 && (x 6 || x 7 || x 5 || x 8)) || (x 0 && (x 2 || x 3 || x 4 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 8) σ τ symm (by decide) rfl rfl).trans (commonMin s)
theorem case67 (s : ℕ) : Paid 6 7 s ↔ cost 6 7 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![1, 0, 6, 7, 5, 2, 3, 4, 8]
  let τ : Fin 9 → Fin 9 := ![1, 0, 5, 6, 7, 4, 2, 3, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 1 && (x 6 || x 7 || x 5 || x 8)) || (x 0 && (x 2 || x 3 || x 4 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 2) (b := 3) σ τ symm (by decide) rfl rfl).trans (privateMin s)
theorem case68 (s : ℕ) : Paid 6 8 s ↔ cost 6 8 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![1, 0, 5, 7, 6, 2, 3, 4, 8]
  let τ : Fin 9 → Fin 9 := ![1, 0, 5, 6, 7, 2, 4, 3, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 1 && (x 5 || x 7 || x 6 || x 8)) || (x 0 && (x 2 || x 3 || x 4 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 8) σ τ symm (by decide) rfl rfl).trans (commonMin s)
theorem case78 (s : ℕ) : Paid 7 8 s ↔ cost 7 8 ≤ s := by
  let σ : Fin 9 → Fin 9 := ![1, 0, 5, 6, 7, 2, 3, 4, 8]
  let τ : Fin 9 → Fin 9 := ![1, 0, 5, 6, 7, 2, 3, 4, 8]
  have symm (x : Fin 9 → Bool) : f0 (x ∘ σ) = f0 x := by
    change ((x 1 && (x 5 || x 6 || x 7 || x 8)) || (x 0 && (x 2 || x 3 || x 4 || x 8))) = ((x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8)))
    ac_rfl
  exact (moveIff (a := 4) (b := 8) σ τ symm (by decide) rfl rfl).trans (commonMin s)
theorem classification (a b : Fin 9) (lines : 2 ≤ a.val) (ord : a < b) (s : ℕ) :
    Paid a b s ↔ cost a b ≤ s := by
  let pairs : List (Fin 9 × Fin 9) := [(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,4),(3,5),(3,6),(3,7),(3,8),(4,5),(4,6),(4,7),(4,8),(5,6),(5,7),(5,8),(6,7),(6,8),(7,8)]
  have cover : ∀ i j : Fin 9, 2 ≤ i.val → i < j → (i,j) ∈ pairs := by decide
  have table (k : Fin 9 × Fin 9) (mem : k ∈ pairs) : Paid k.1 k.2 s ↔ cost k.1 k.2 ≤ s := by
    simp only [pairs,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact case23 s
    · exact case24 s
    · exact case25 s
    · exact case26 s
    · exact case27 s
    · exact case28 s
    · exact case34 s
    · exact case35 s
    · exact case36 s
    · exact case37 s
    · exact case38 s
    · exact case45 s
    · exact case46 s
    · exact case47 s
    · exact case48 s
    · exact case56 s
    · exact case57 s
    · exact case58 s
    · exact case67 s
    · exact case68 s
    · exact case78 s
  exact table _ (cover a b lines ord)
end PEqualNP.Outside.ClassOr2056
#print axioms PEqualNP.Outside.ClassOr2056.classification
