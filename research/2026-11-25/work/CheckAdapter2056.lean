import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.BlockProof2056
def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

abbrev Word := BitVec 16
def available (S : List Word) := (S.flatMap fun a => S.flatMap fun b => [a &&& b,a ||| b]).eraseDups
def safe (goal : Word) : ℕ → List Word → Bool
  | 0,S => !S.contains goal
  | n+1,S => safe goal n S && (available S).all (fun v => S.contains v || safe goal n (v::S))

theorem one {S : List Word} {a b : Word} (ha : a ∈ S) (hb : b ∈ S) :
    a &&& b ∈ available S ∧ a ||| b ∈ available S := by
  constructor <;> simp only [available,List.mem_eraseDups,List.mem_flatMap] <;>
    exact ⟨a,ha,b,hb,by simp⟩

theorem wordMem {B S : List Word} (inc : ∀ v ∈ B, v ∈ S) (z : (0 : Word) ∈ S)
    (o : BitVec.allOnes 16 ∈ S) (g : Gate)
    (hg : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    hcsGateVal B g ∈ S ∨ hcsGateVal B g ∈ available S := by
  have atB (i : ℕ) : B.getD i 0 ∈ S := by
    rw [List.getD_eq_getElem?_getD]
    cases h : B[i]? with
    | none => exact z
    | some a => exact inc a (List.mem_of_getElem? h)
  have zeroW (x : Word) : x ||| (0 : Word) = x := BitVec.or_zero
  obtain ⟨op,ins⟩ := g
  rcases hg with ⟨hop,len⟩
  change op ∈ ({GateOp.and,GateOp.or} : Set GateOp) at hop
  change ins.length ≤ 2 at len
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with rfl|rfl <;> cases ins with
  | nil => first | exact Or.inl o | exact Or.inl z
  | cons a rest =>
    cases rest with
    | nil =>
      apply Or.inl
      first
      | change B.getD a 0 &&& BitVec.allOnes 16 ∈ S
        rw [BitVec.and_allOnes]
        exact atB a
      | change B.getD a 0 ||| 0 ∈ S
        rw [zeroW (B.getD a 0)]
        exact atB a
    | cons b rest =>
      cases rest with
      | nil =>
        apply Or.inr
        first
        | change B.getD a 0 &&& (B.getD b 0 &&& BitVec.allOnes 16) ∈ available S
          rw [BitVec.and_allOnes]
          exact (one (atB a) (atB b)).1
        | change B.getD a 0 ||| (B.getD b 0 ||| 0) ∈ available S
          rw [zeroW (B.getD b 0)]
          exact (one (atB a) (atB b)).2
      | cons c rem => simp at len

theorem sound (target : Word) (gs : List Gate) (B S : List Word) (k : ℕ)
    (small : gs.length ≤ k) (cert : safe target k S = true)
    (inc : ∀ v ∈ B, v ∈ S) (z : (0 : Word) ∈ S) (o : BitVec.allOnes 16 ∈ S)
    (mono : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    target ∉ gs.foldl hcsStep B := by
  induction k generalizing gs S B with
  | zero =>
    obtain rfl : gs = [] := List.length_eq_zero_iff.mp (by omega)
    intro h
    have mem := inc target h
    simpa [safe,mem] using cert
  | succ k ih =>
    have ⟨old,new⟩ := Bool.and_eq_true_iff.mp cert
    cases gs with
    | nil => exact ih [] B S (by simp) old inc z o mono
    | cons g gs =>
      have sub : gs.length ≤ k := by simpa using small
      have tail := fun h m => mono h (List.mem_cons_of_mem g m)
      let v := hcsGateVal B g
      change target ∉ gs.foldl hcsStep (B ++ [v])
      by_cases hv : v ∈ S
      · apply ih gs _ S sub old _ z o tail
        simpa [List.mem_append] using fun a (h : a ∈ B ∨ a=v) => h.elim (inc a) (fun e => e ▸ hv)
      · have av := (wordMem inc z o g (mono _ List.mem_cons_self)).resolve_left hv
        have next := List.all_eq_true.mp new v av
        apply ih gs _ (v::S) sub (by simpa [hv] using next) _ (List.mem_cons_of_mem _ z) (List.mem_cons_of_mem _ o) tail
        intro a ha
        simp only [List.mem_append,List.mem_singleton] at ha
        exact ha.elim (fun h => List.mem_cons_of_mem _ (inc a h)) (fun h => h ▸ List.mem_cons_self)

theorem exclude {n k : ℕ} (raw : List Word) (goal : Word) (nz : goal ≠ 0)
    (row : Fin 16 → Fin n → Bool) (f : (Fin n → Bool) → Bool)
    (data : ∀ j : Fin 16, raw.map (fun v => v.getLsbD j.val) = List.ofFn (row j))
    (want : ∀ j : Fin 16, goal.getLsbD j.val = f (row j))
    (cert : safe goal k (0 :: BitVec.allOnes 16 :: raw) = true)
    (C : Circuit) (mono : Monotone2 C) (ev : ∀ x, C.eval (List.ofFn x) = f x) : k < C.size := by
  by_contra! small
  have fan : FanInTwo C := fun g hg => ⟨by
    rcases (mono g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h), (mono g hg).2⟩
  have eq : (C.gates.foldl hcsStep raw).getD C.output 0 = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have bits := hcsFoldBits raw ⟨j,hj⟩ C.gates fan
    have h : (C.wires (List.ofFn (row ⟨j,hj⟩))).getD C.output false = f (row ⟨j,hj⟩) := ev _
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
      (List.ofFn (row ⟨j,hj⟩))).getD C.output false = _ at h
    rw [← data ⟨j,hj⟩,← bits,← hcsGetDBit] at h
    exact h.trans (want ⟨j,hj⟩).symm
  have out := sound goal C.gates raw _ k small cert (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
    List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) mono
  rw [List.getD_eq_getElem?_getD] at eq
  cases h : (C.gates.foldl hcsStep raw)[C.output]? with
  | none => simp [h] at eq; exact nz eq.symm
  | some a =>
    have e : a = goal := by simpa [h] using eq
    exact out (e ▸ List.mem_of_getElem? h)

def raw : List Word := [42405, 51914, 20817, 12850, 7196]
def goal : Word := 3855
def block := fun x : Fin 5 → Bool => (x 0 && (x 2 || x 4)) || (x 1 && (x 3 || x 4))
def row (r : Fin 16) (i : Fin 5) := (([5, 10, 17, 18, 28, 9, 6, 3, 5, 10, 17, 18, 28, 9, 6, 3] : List ℕ).getD r.val 0).testBit i.val
end PEqualNP.Outside.BlockProof2056
