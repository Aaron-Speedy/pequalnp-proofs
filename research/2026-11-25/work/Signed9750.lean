import PEqualNP.Defs
namespace PEqualNP.Outside.Signed9750
abbrev Fn (X : Type) := X → Bool
abbrev Pool (X : Type) := Fn X → Prop
def inv {X : Type} (f : Fn X) : Fn X := fun x => !(f x)
def both {X : Type} (f g : Fn X) : Fn X := fun x => f x && g x
def extend {X : Type} (R : Pool X) (f : Fn X) : Pool X := fun g => R g ∨ g=f ∨ g=inv f
def Stable {X : Type} (R : Pool X) : Prop :=
  (∀ b : Bool, R (fun _ => b)) ∧ ∀ g, R g → R (inv g)
theorem doubleInv {X : Type} (g : Fn X) : inv (inv g) = g := by funext x; simp [inv]
theorem stableExt {X : Type} {R : Pool X} (st : Stable R) (f : Fn X) : Stable (extend R f) := by
  refine ⟨fun b => Or.inl (st.1 b),?_⟩
  intro g h
  rcases h with h|rfl|rfl
  · exact Or.inl (st.2 g h)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (doubleInv f))
def Can {X : Type} (f : Fn X) : ℕ → Pool X → Prop
  | 0, R => R f
  | k+1, R => Can f k R ∨ ∃ a b, R a ∧ R b ∧ Can f k (extend R (both a b))
theorem Can.ready {X : Type} {f : Fn X} {R : Pool X} (h : R f) : Can f 0 R := h
theorem Can.skip {X : Type} {f : Fn X} {R : Pool X} {k : ℕ} (h : Can f k R) : Can f (k+1) R :=
  Or.inl h
theorem Can.gate {X : Type} {f : Fn X} {k : ℕ} {R : Pool X} (a b : Fn X) (ha : R a) (hb : R b)
    (h : Can f k (extend R (both a b))) : Can f (k+1) R := Or.inr ⟨a,b,ha,hb,h⟩
theorem Can.ind {X : Type} {f : Fn X} {motive : ∀ k R, Can f k R → Prop}
    (ready : ∀ {R : Pool X} (hf : R f), motive 0 R (Can.ready hf))
    (skip : ∀ {k : ℕ} {R : Pool X} (h : Can f k R), motive k R h → motive (k+1) R (Can.skip h))
    (gate : ∀ {k : ℕ} {R : Pool X} (a b : Fn X) (ha : R a) (hb : R b)
      (h : Can f k (extend R (both a b))), motive k (extend R (both a b)) h →
      motive (k+1) R (Can.gate a b ha hb h))
    {k : ℕ} {R : Pool X} (h : Can f k R) : motive k R h := by
  induction k generalizing R with
  | zero => exact ready h
  | succ k ih =>
    rcases h with old|⟨a,b,ha,hb,tail⟩
    · exact skip old (ih old)
    · exact gate a b ha hb tail (ih tail)

def liftF {X : Type} (f : Fn X) : Fn (X × Bool) := fun y => f y.1
def slice {X : Type} (b : Bool) (f : Fn (X × Bool)) : Fn X := fun x => f (x,b)
def bitInput {X : Type} : Fn (X × Bool) := fun y => y.2

theorem mapRestrict {X : Type} {f : Fn (X × Bool)} {k : ℕ} {S : Pool (X × Bool)}
    (h : Can f k S) (v : Bool) (R : Pool X) (st : Stable R)
    (hr : ∀ z, S z → R (slice v z)) : Can (slice v f) k R := by
  induction h using Can.ind generalizing R with
  | ready hf => exact .ready (hr _ hf)
  | skip _ ih => exact .skip (ih R st hr)
  | gate a b ha hb _ ih =>
    apply Can.gate (slice v a) (slice v b) (hr a ha) (hr b hb)
    apply ih _ (stableExt st _)
    intro z hz
    rcases hz with hz|rfl|rfl
    · exact Or.inl (hr _ hz)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

def lifted {X : Type} (R : Pool X) (z : Fn (X × Bool)) := ∃ g, R g ∧ z=liftF g
def fixedAt {X : Type} (v : Bool) (z : Fn (X × Bool)) := ∃ c : Bool, slice v z=fun _ => c

theorem dropOne {X : Type} {f : Fn (X × Bool)} {S : Pool (X × Bool)} {k : ℕ}
    (h : Can f k S) (v : Bool) (dep : ∀ g, f ≠ liftF g) (nc : ¬ fixedAt v f)
    (R : Pool X) (st : Stable R) (hs : ∀ z, S z → lifted R z ∨ fixedAt v z) :
    ∃ t, t+1 ≤ k ∧ Can (slice v f) t R := by
  have value {Q : Pool X} (sq : Stable Q) {z : Fn (X × Bool)}
      (hz : lifted Q z ∨ fixedAt v z) : Q (slice v z) := by
    rcases hz with ⟨g,hg,rfl⟩|⟨c,hc⟩
    · exact hg
    · rw [hc]; exact sq.1 c
  induction h using Can.ind generalizing R with
  | ready hf =>
    rcases hs _ hf with ⟨g,_,e⟩|hconst
    · exact (dep g e).elim
    · exact (nc hconst).elim
  | skip _ ih =>
    obtain ⟨t,sz,pr⟩ := ih R st hs
    exact ⟨t,by omega,pr⟩
  | @gate k S a b ha hb rest ih =>
    have aa := hs a ha
    have bb := hs b hb
    have save (ok : R (slice v (both a b))) : ∃ t, t+1 ≤ k+1 ∧ Can (slice v f) t R := by
      refine ⟨k,le_rfl,mapRestrict rest v R st ?_⟩
      intro z hz
      rcases hz with hz|rfl|rfl
      · exact value st (hs _ hz)
      · exact ok
      · exact st.2 _ ok
    rcases aa with ⟨u,hu,rfl⟩|⟨c,hc⟩
    · rcases bb with ⟨w,hw,rfl⟩|⟨d,hd⟩
      · let T := extend R (both u w)
        obtain ⟨t,sz,pr⟩ := ih T (stableExt st _) (by
          intro z hz
          rcases hz with hz|rfl|rfl
          · rcases hs _ hz with ⟨g,hg,rfl⟩|c
            · exact Or.inl ⟨g,Or.inl hg,rfl⟩
            · exact Or.inr c
          · exact Or.inl ⟨both u w,Or.inr (Or.inl rfl),rfl⟩
          · exact Or.inl ⟨inv (both u w),Or.inr (Or.inr rfl),rfl⟩)
        exact ⟨t+1,by omega,Can.gate u w hu hw pr⟩
      · apply save
        change R (both u (slice v b))
        rw [hd]
        cases d
        · have e : both u (fun _ => false) = (fun _ => false) := by funext x; simp [both]
          rw [e]; exact st.1 false
        · have e : both u (fun _ => true) = u := by funext x; simp [both]
          rw [e]; exact hu
    · apply save
      change R (both (slice v a) (slice v b))
      rw [hc]
      cases c
      · exact st.1 false
      · exact value st bb

theorem dropTwo {X : Type} {f : Fn (X × Bool)} {S : Pool (X × Bool)} {k : ℕ}
    (h : Can f k S) (dep : ∀ g, f ≠ liftF g) (nc : ∀ v, ¬ fixedAt v f)
    (R : Pool X) (st : Stable R)
    (hs : ∀ z, S z → lifted R z ∨ z=bitInput ∨ z=inv bitInput) :
    ∃ v t, t+2 ≤ k ∧ Can (slice v f) t R := by
  induction h using Can.ind generalizing R with
  | ready hf =>
    rcases hs _ hf with ⟨g,_,e⟩|e|e
    · exact (dep g e).elim
    · exact (nc false ⟨false, by rw [e]; rfl⟩).elim
    · exact (nc false ⟨true, by rw [e]; rfl⟩).elim
  | skip _ ih =>
    obtain ⟨v,t,sz,pr⟩ := ih R st hs
    exact ⟨v,t,by omega,pr⟩
  | @gate k S a b ha hb rest ih =>
    have save (v : Bool) (zero : slice v (both a b) = fun _ => false) :
        ∃ v t, t+2 ≤ k+1 ∧ Can (slice v f) t R := by
      have extra : ∀ z, extend S (both a b) z → lifted R z ∨ fixedAt v z := by
        intro z hz
        rcases hz with hz|rfl|rfl
        · rcases hs _ hz with old|rfl|rfl
          · exact Or.inl old
          · exact Or.inr ⟨v,rfl⟩
          · exact Or.inr ⟨!v,rfl⟩
        · exact Or.inr ⟨false,zero⟩
        · refine Or.inr ⟨true,?_⟩
          change inv (slice v (both a b)) = _
          rw [zero]; rfl
      obtain ⟨t,sz,pr⟩ := dropOne rest v dep (nc v) R st extra
      exact ⟨v,t,by omega,pr⟩
    rcases hs a ha with ⟨u,hu,rfl⟩|rfl|rfl
    · rcases hs b hb with ⟨w,hw,rfl⟩|rfl|rfl
      · obtain ⟨v,t,sz,pr⟩ := ih (extend R (both u w)) (stableExt st _) (by
          intro z hz
          rcases hz with hz|rfl|rfl
          · rcases hs _ hz with ⟨g,hg,rfl⟩|e
            · exact Or.inl ⟨g,Or.inl hg,rfl⟩
            · exact Or.inr e
          · exact Or.inl ⟨both u w,Or.inr (Or.inl rfl),rfl⟩
          · exact Or.inl ⟨inv (both u w),Or.inr (Or.inr rfl),rfl⟩)
        exact ⟨v,t+1,by omega,Can.gate u w hu hw pr⟩
      · apply save false; funext x; simp [slice,both,bitInput]
      · apply save true; funext x; simp [slice,both,inv,bitInput]
    · exact save false rfl
    · exact save true rfl

open PEqualNP.CircuitLowerBounds

def useBinary (g : Gate) := match g.op with | .not => false | _ => true
def cost (gs : List Gate) := (gs.filter useBinary).length
def readF {X : Type} (w : List (Fn X)) (i : ℕ) : Fn X := w.getD i (fun _ => false)
def outF {X : Type} (w : List (Fn X)) (g : Gate) : Fn X :=
  fun x => g.op.eval (g.inputs.map (fun i => readF w i x))
def traceF {X : Type} (gs : List Gate) (w : List (Fn X)) : List (Fn X) :=
  gs.foldl (fun old g => old ++ [outF old g]) w
def fan (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem readIn {X : Type} {w : List (Fn X)} {R : Pool X} (st : Stable R)
    (hw : ∀ u ∈ w, R u) (i : ℕ) : R (readF w i) := by
  by_cases h : i < w.length
  · rw [readF,List.getD_eq_getElem _ _ h]; exact hw _ (List.getElem_mem _)
  · rw [readF,List.getD_eq_default _ _ (by omega)]; exact st.1 false

theorem gateClass {X : Type} (w : List (Fn X)) (g : Gate) (hg : fan g) (R : Pool X)
    (st : Stable R) (hw : ∀ u ∈ w, R u) :
    if useBinary g then R (outF w g) ∨
      ∃ a b, R a ∧ R b ∧ (outF w g = both a b ∨ outF w g = inv (both a b))
    else R (outF w g) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,len⟩ := hg
  change (op = .and ∨ op = .or ∨ op = .not) at hop
  change ins.length ≤ 2 at len
  rcases hop with rfl|rfl|rfl
  · change R _ ∨ _
    cases ins with
    | nil => exact Or.inl (st.1 true)
    | cons i t =>
      cases t with
      | nil =>
        apply Or.inl
        convert readIn st hw i using 1
        funext x
        simp [outF,GateOp.eval]
      | cons j t =>
        have hnil : t=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst t
        exact Or.inr ⟨readF w i,readF w j,readIn st hw i,readIn st hw j,Or.inl (by funext x; simp [outF,GateOp.eval,both])⟩
  · change R _ ∨ _
    cases ins with
    | nil => exact Or.inl (st.1 false)
    | cons i t =>
      cases t with
      | nil =>
        apply Or.inl
        convert readIn st hw i using 1
        funext x
        simp [outF,GateOp.eval]
      | cons j t =>
        have hnil : t=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst t
        refine Or.inr ⟨inv (readF w i),inv (readF w j),st.2 _ (readIn st hw i),
          st.2 _ (readIn st hw j),Or.inr ?_⟩
        funext x
        simp [outF,GateOp.eval,inv,both]
  · cases ins with
    | nil => exact st.1 true
    | cons i t => exact st.2 _ (readIn st hw i)

theorem comp {X : Type} (gs : List Gate) (o : ℕ) (legal : ∀ g ∈ gs, fan g)
    (w : List (Fn X)) (R : Pool X) (st : Stable R) (hw : ∀ u ∈ w, R u) :
    Can (readF (traceF gs w) o) (cost gs) R := by
  induction gs generalizing w R with
  | nil => exact Can.ready (readIn st hw o)
  | cons g gs ih =>
    have cont := ih (fun u hu => legal u (List.mem_cons_of_mem _ hu))
    have cl := gateClass w g (legal g List.mem_cons_self) R st hw
    change Can (readF (traceF gs (w ++ [outF w g])) o) _ R
    have same (h : R (outF w g)) : Can (readF (traceF gs (w ++ [outF w g])) o) (cost gs) R := by
      apply cont _ R st
      intro z hz
      rcases List.mem_append.mp hz with hz|hz
      · exact hw z hz
      · obtain rfl := List.mem_singleton.mp hz
        exact h
    cases hb : useBinary g with
    | false =>
      simp only [hb, Bool.false_eq_true, ite_false] at cl
      simpa [cost,hb] using same cl
    | true =>
      simp only [hb,ite_true] at cl
      have len : cost (g::gs)=cost gs+1 := by simp [cost,hb]
      rw [len]
      rcases cl with h|⟨a,b,ha,hb',eq⟩
      · exact Can.skip (same h)
      · apply Can.gate a b ha hb'
        apply cont _ _ (stableExt st _)
        intro z hz
        rcases List.mem_append.mp hz with hz|hz
        · exact Or.inl (hw z hz)
        · obtain rfl := List.mem_singleton.mp hz
          exact Or.inr eq

theorem readAt {X : Type} (w : List (Fn X)) (i : ℕ) (x : X) :
    (w.map (fun z => z x)).getD i false = readF w i x := by
  by_cases h : i < w.length
  · simp [readF,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
  · simp [readF,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_none (by omega : w.length ≤ i)]

theorem traceAt {X : Type} (gs : List Gate) (w : List (Fn X)) (x : X) :
    (traceF gs w).map (fun z => z x) =
      gs.foldl (fun old g => old ++ [g.op.eval (g.inputs.map (fun i => old.getD i false))])
        (w.map (fun z => z x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (traceF gs (w ++ [outF w g])).map _ = _
    rw [ih,List.foldl_cons]
    simp only [List.map_append,List.map_cons,List.map_nil,outF,readAt]


def extendInput {X : Type} (R : Pool X) : Pool (X × Bool) :=
  fun z => lifted R z ∨ z=bitInput ∨ z=inv bitInput
theorem stableInput {X : Type} {R : Pool X} (st : Stable R) : Stable (extendInput R) := by
  refine ⟨fun b => Or.inl ⟨fun _ => b,st.1 b,rfl⟩,?_⟩
  intro z h
  rcases h with ⟨g,hg,rfl⟩|rfl|rfl
  · exact Or.inl ⟨inv g,st.2 _ hg,rfl⟩
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (doubleInv _))
theorem genuine {X : Type} {f : Fn (X × Bool)} (x : X) (h : f (x,false) ≠ f (x,true)) :
    ∀ g, f ≠ liftF g := by
  intro g he
  exact h (he ▸ rfl)
theorem varying {X : Type} {f : Fn (X × Bool)} (v : Bool) (x y : X)
    (h : f (x,v) ≠ f (y,v)) : ¬ fixedAt v f := by
  rintro ⟨c,eq⟩
  exact h ((congrFun eq x).trans (congrFun eq y).symm)

abbrev Assignment := Fin 12 → Bool
def primary (z : Fn Assignment) := (∃ b : Bool, z = fun _ => b) ∨
  ∃ i : Fin 12, z = (fun x => x i) ∨ z = inv (fun x => x i)
theorem stablePrimary : Stable primary := by
  refine ⟨fun b => Or.inl ⟨b,rfl⟩,?_⟩
  rintro z (⟨b,rfl⟩|⟨i,rfl|rfl⟩)
  · exact Or.inl ⟨!b,rfl⟩
  · exact Or.inr ⟨i,Or.inr rfl⟩
  · exact Or.inr ⟨i,Or.inl (doubleInv _)⟩

theorem pullCan {X Y : Type} {f : Fn X} {R : Pool X} {k : ℕ}
    (h : Can f k R) (φ : Y → X) (T : Pool Y) (ht : ∀ z, R z → T (z ∘ φ)) :
    Can (f ∘ φ) k T := by
  induction h using Can.ind generalizing T with
  | ready hf => exact .ready (ht _ hf)
  | skip _ ih => exact .skip (ih _ ht)
  | gate a b ha hb _ ih =>
    apply Can.gate (a ∘ φ) (b ∘ φ) (ht _ ha) (ht _ hb)
    apply ih
    rintro z (h|rfl|rfl)
    · exact Or.inl (ht _ h)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

def pairAt (i : Fin 12) (y : Assignment × Bool) := Function.update y.1 i y.2
theorem pullPrimary (i : Fin 12) (z : Fn Assignment) (h : primary z) :
    extendInput primary (z ∘ pairAt i) := by
  rcases h with ⟨b,rfl⟩ | ⟨j,rfl|rfl⟩
  · exact Or.inl ⟨_,Or.inl ⟨b,rfl⟩,rfl⟩
  · by_cases eq : j = i
    · subst j
      exact Or.inr (Or.inl (by funext y; simp [pairAt,bitInput]))
    · exact Or.inl ⟨fun x => x j,Or.inr ⟨j,Or.inl rfl⟩,
        by funext y; simp [pairAt,liftF,eq]⟩
  · by_cases eq : j = i
    · subst j
      exact Or.inr (Or.inr (by funext y; simp [pairAt,inv,bitInput]))
    · exact Or.inl ⟨inv (fun x => x j),Or.inr ⟨j,Or.inr rfl⟩,
        by funext y; simp [pairAt,liftF,inv,eq]⟩

def LB (f : Fn Assignment) (v : ℕ) := ∀ k, Can f k primary → v ≤ k
def co (f : Fn Assignment) (i : Fin 12) (b : Bool) := slice b (f ∘ pairAt i)
theorem lbOne {f g : Fn Assignment} {v : ℕ} (i : Fin 12) (b : Bool)
    (x y z : Assignment) (dep : co f i false x ≠ co f i true x)
    (nc : co f i b y ≠ co f i b z) (eq : co f i b = g) (low : LB g v) : LB f (v+1) := by
  intro k h
  have test := pullCan h (pairAt i) _ (pullPrimary i)
  obtain ⟨s,bd,run⟩ := dropOne test b (genuine x dep) (varying b y z nc) primary stablePrimary (by
    intro w hw
    rcases hw with lifted|rfl|rfl
    · exact Or.inl lifted
    · exact Or.inr ⟨b,rfl⟩
    · exact Or.inr ⟨!b,rfl⟩)
  change Can (co f i b) s primary at run
  rw [eq] at run
  have := low _ run
  omega

theorem lbBoth {f g h : Fn Assignment} {v : ℕ} (i : Fin 12) (x y z u w : Assignment)
    (dep : co f i false x ≠ co f i true x)
    (nc0 : co f i false y ≠ co f i false z) (nc1 : co f i true u ≠ co f i true w)
    (eq0 : co f i false = g) (eq1 : co f i true = h)
    (lo0 : LB g v) (lo1 : LB h v) : LB f (v+2) := by
  intro k hk
  have test := pullCan hk (pairAt i) _ (pullPrimary i)
  obtain ⟨b,s,bd,run⟩ := dropTwo test (genuine x dep)
    (fun b => by cases b; exact varying false y z nc0; exact varying true u w nc1)
    primary stablePrimary (fun _ hz => hz)
  change Can (co f i b) s primary at run
  cases b
  · rw [eq0] at run
    have := lo0 _ run
    omega
  · rw [eq1] at run
    have := lo1 _ run
    omega

end PEqualNP.Outside.Signed9750
