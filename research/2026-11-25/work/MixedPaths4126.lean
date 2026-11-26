import ForkPaths4126
open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3793
namespace LocalFano4126
theorem ctxAppend (a b : Ctx) (x v) :
    evalCtx (a ++ b) x v = evalCtx b x (evalCtx a x v) := by simp [evalCtx,List.foldl_append]
theorem chargeAppend (a b : Ctx) : added (a++b) = added a + added b := by simp [added]
theorem moveRight (c : Ctx) (op : Bool) (u : Uniform c op) (x a b) :
    evalCtx c x (bval op a b) = bval op a (evalCtx c x b) := by
  calc
    _ = evalCtx c x (bval op b a) := congrArg (evalCtx c x) (commB op a b)
    _ = _ := (moveAlong c op u x b a).trans (commB op _ _)
theorem pullTails (out L R l r : Ctx) (op : Bool) (h : Form)
    (pl : Uniform l op) (pr : Uniform r op) (x) :
    RunFork out (L++l) (R++r) op h x = RunFork (l++r++out) L R op h x := by
  unfold RunFork
  simp only [ctxAppend,moveAlong l op pl,moveRight r op pr]
theorem pulledFloor (out L R l r : Ctx) (op oL oR : Bool) (h : Form) (ph : Positive h)
    (po : ∀ p ∈ out, Positive p.2) (pL : ∀ p ∈ L++l, Positive p.2)
    (pR : ∀ p ∈ R++r, Positive p.2) (ul : Uniform l op) (ur : Uniform r op)
    (uL : Uniform L oL) (uR : Uniform R oR)
    (ok : ∀ x, RunFork out (L++l) (R++r) op h x = true ↔ F x) :
    28 ≤ h.leaves + added (L++l) + added (R++r) + added out := by
  have po' (p) (hp : p ∈ l++r++out) : Positive p.2 := by
    rcases List.mem_append.mp hp with hr | ho
    · rcases List.mem_append.mp hr with hl | hr
      · exact pL p (List.mem_append_right _ hl)
      · exact pR p (List.mem_append_right _ hr)
    · exact po p ho
  have big := uniformForkFloor (l++r++out) L R op oL oR h ph po'
    (fun p hp => pL p (List.mem_append_left _ hp))
    (fun p hp => pR p (List.mem_append_left _ hp)) uL uR
    (fun x => (pullTails out L R l r op h ul ur x) ▸ ok x)
  simp only [chargeAppend] at big ⊢
  omega

/-- A path has an AND/OR matching the join followed later by a gate of the other type. -/
def switchBack (op : Bool) (c : Ctx) : Prop :=
  ∃ a b d p q, c = a ++ p :: (b ++ q :: d) ∧ p.1 = op ∧ q.1 = !op

theorem splitPath (op : Bool) (c : Ctx) (no : ¬ switchBack op c) :
    ∃ a b, c = a++b ∧ Uniform a (!op) ∧ Uniform b op := by
  induction c with
  | nil => exact ⟨[],[],rfl,by simp [Uniform],by simp [Uniform]⟩
  | cons p c ih =>
    have tail : ¬ switchBack op c := by
      rintro ⟨a,b,d,s,t,eq,e,f⟩
      exact no ⟨p::a,b,d,s,t,by simp [eq],e,f⟩
    obtain ⟨a,b,e,ua,ub⟩ := ih tail
    by_cases hp : p.1 = op
    · refine ⟨[],p::c,rfl,by simp [Uniform],?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · by_contra bad
        have opp : q.1 = !op := by cases q with | mk f g => cases f <;> cases op <;> simp_all
        obtain ⟨before,after,eq⟩ := List.append_of_mem hq
        exact no ⟨[],before,after,p,q,by simp [eq],hp,opp⟩
    · have opp : p.1 = !op := by cases p with | mk f g => cases f <;> cases op <;> simp_all
      refine ⟨p::a,b,by simp [e],?_,ub⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact opp
      · exact ua q hq

theorem necessarySwitch (out L R : Ctx) (op : Bool) (h : Form) (ph : Positive h)
    (po : ∀ p ∈ out, Positive p.2) (pl : ∀ p ∈ L, Positive p.2) (pr : ∀ p ∈ R, Positive p.2)
    (ok : ∀ x, RunFork out L R op h x = true ↔ F x)
    (small : h.leaves + added L + added R + added out ≤ 27) : switchBack op L ∨ switchBack op R := by
  by_contra! bad
  obtain ⟨a,b,rfl,u,v⟩ := splitPath op L bad.1
  obtain ⟨c,d,rfl,w,z⟩ := splitPath op R bad.2
  have big := pulledFloor out a c b d op (!op) (!op) h ph po pl pr v z u w ok
  omega
end LocalFano4126
#print axioms LocalFano4126.necessarySwitch
