import Leader.L4.ReportPulseRecode

namespace L4.ReportPulseOverwrite
open ReportPulseRecode
universe u
variable {G : Type u} [DecidableEq G] {n : Nat}

/-- A fixed key describes only the replacement gate/bit at each raw
index. The index advances even at an outside or unchanged mark. -/
def overwriteFrom (put : G × Bool → Fin n) (key : Nat → Option (G × Bool))
    (i : Nat) : List (Fin n) → List (Fin n)
  | [] => []
  | e::w => ((key i).map put).getD e :: overwriteFrom put key (i+1) w

def LegalAt (put : G × Bool → Fin n) (s : Armed G) (e : Fin n)
    (edit : Option (G × Bool)) : Prop :=
  match edit with
  | none => True
  | some (g,_) => s g=false ∧ ∃ a : Bool,e=put (g,a)

/-- Test the edit key against the *unedited* chronological prefix. -/
noncomputable def LegalFrom (put : G × Bool → Fin n) (key : Nat → Option (G × Bool))
    (s : Armed G) (i : Nat) : List (Fin n) → Prop
  | [] => True
  | e::w =>
    LegalAt put s e (key i) ∧
      LegalFrom put key (skeletonStep s (readLabel put e)).1 (i+1) w

theorem local_same (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Armed G) (e : Fin n) (edit : Option (G × Bool))
    (H : LegalAt put s e edit) :
    skeletonStep s (readLabel put (((edit.map put).getD e))) =
      skeletonStep s (readLabel put e) := by
  cases edit with
  | none => rfl
  | some edit =>
    obtain ⟨g,b⟩ := edit
    obtain ⟨A,a,E⟩ := H
    subst e
    change skeletonStep s (readLabel put (put (g,b))) =
      skeletonStep s (readLabel put (put (g,a)))
    have W (bit : Bool) : readLabel put (put (g,bit))=.inl (g,bit) :=
      read_write put inj (.inl (g,bit))
    rw [W b,W a]
    simp only [skeletonStep,A]
    rfl

theorem overwrite_skeleton (put : G × Bool → Fin n) (inj : Function.Injective put)
    (key : Nat → Option (G × Bool)) (s : Armed G) (i : Nat) (w : List (Fin n))
    (H : LegalFrom put key s i w) :
    skeleton s ((overwriteFrom put key i w).map (readLabel put)) =
      skeleton s (w.map (readLabel put)) ∧
    skeletonState s ((overwriteFrom put key i w).map (readLabel put)) =
      skeletonState s (w.map (readLabel put)) := by
  induction w generalizing s i with
  | nil => exact ⟨rfl,rfl⟩
  | cons e w IH =>
    have Same := local_same put inj s e (key i) H.1
    obtain ⟨Events,State⟩ := IH _ _ H.2
    simp only [overwriteFrom,List.map_cons,skeleton,skeletonState,Same,Events,State, and_self]

omit [DecidableEq G] in
theorem overwrite_length (put : G × Bool → Fin n)
    (key : Nat → Option (G × Bool)) (i : Nat) (w : List (Fin n)) :
    (overwriteFrom put key i w).length=w.length := by
  induction w generalizing i with
  | nil => rfl
  | cons e w IH => simp only [overwriteFrom,List.length_cons,IH]

omit [DecidableEq G] in
theorem overwrite_extract (put : G × Bool → Fin n)
    (key : Nat → Option (G × Bool)) (i j : Nat) (w : List (Fin n)) :
    (overwriteFrom put key i w)[j]? =
      (w[j]?).map (fun e => ((key (i+j)).map put).getD e) := by
  induction w generalizing i j with
  | nil => simp [overwriteFrom]
  | cons e w IH =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [overwriteFrom,List.getElem?_cons_succ,IH]
      rw [show i+1+j=i+(j+1) by omega]

/-- Full chronological skeleton equality implies *every* extracted
schedule of starts and completions is preserved, including cuts at
specified completion indices. -/
theorem extract_schedule (put : G × Bool → Fin n) (inj : Function.Injective put)
    (key : Nat → Option (G × Bool)) (s : Armed G) (i : Nat) (w : List (Fin n))
    (H : LegalFrom put key s i w) {A : Type}
    (schedule : List (Option (Event G)) → A) :
    schedule (skeleton s ((overwriteFrom put key i w).map (readLabel put))) =
      schedule (skeleton s (w.map (readLabel put))) :=
  congrArg schedule (overwrite_skeleton put inj key s i w H).1

#print axioms overwrite_skeleton
#print axioms overwrite_length
#print axioms overwrite_extract
#print axioms extract_schedule

theorem start_iff (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Armed G) (e : Fin n) (g : G) :
    (skeletonStep s (readLabel put e)).2=some (.start g) ↔
      s g=false ∧ ∃ a : Bool,e=put (g,a) := by
  constructor
  · cases E : readLabel put e with
    | inr z => simp [skeletonStep]
    | inl ib =>
      obtain ⟨j,bit⟩ := ib
      have W := write_read put e
      rw [E] at W
      change put (j,bit)=e at W
      cases A : s j <;> cases bit <;> simp [skeletonStep,A]
      · intro Eq
        subst j
        exact ⟨A,.inl W.symm⟩
      · intro Eq
        subst j
        exact ⟨A,.inr W.symm⟩
  · rintro ⟨A,a,rfl⟩
    have W : readLabel put (put (g,a))=.inl (g,a) := read_write put inj (.inl (g,a))
    simp [W,skeletonStep,A]

theorem skeleton_append {Z : Type} (s : Armed G) (pre post : List (Label G Z)) :
    skeleton s (pre++post)=skeleton s pre++skeleton (skeletonState s pre) post := by
  induction pre generalizing s with
  | nil => rfl
  | cons e pre IH => simp only [List.cons_append,skeleton,skeletonState,IH]

theorem skeleton_length {Z : Type} (s : Armed G) (w : List (Label G Z)) :
    (skeleton s w).length=w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons e w IH => simp only [skeleton,List.length_cons,IH]

theorem split_skeleton_at (put : G × Bool → Fin n) (s : Armed G)
    (pre post : List (Fin n)) (e : Fin n) :
    (skeleton s ((pre++e::post).map (readLabel put)))[pre.length]? =
      some (skeletonStep (skeletonState s (pre.map (readLabel put))) (readLabel put e)).2 := by
  induction pre generalizing s with
  | nil => rfl
  | cons a pre IH =>
    simp only [List.cons_append,List.map_cons,skeleton,skeletonState,List.length_cons,List.getElem?_cons_succ]
    exact IH _

/-- An arbitrary map of edits is legal if the original skeleton really
has the named round start at each changed coordinate. This proof uses
the original marks, not a hypothesized skeleton of the edited tape. -/
theorem legal_of_starts (put : G × Bool → Fin n) (inj : Function.Injective put)
    (key : Nat → Option (G × Bool)) (s : Armed G) (i : Nat) (w : List (Fin n))
    (H : ∀ j g b, j<w.length → key (i+j)=some (g,b) →
      (skeleton s (w.map (readLabel put)))[j]?=some (some (.start g))) :
    LegalFrom put key s i w := by
  induction w generalizing s i with
  | nil => trivial
  | cons e w IH =>
    constructor
    · cases E : key i with
      | none => trivial
      | some ib =>
        obtain ⟨g,b⟩ := ib
        have S := H 0 g b (by simp) (by simpa using E)
        change some (skeletonStep s (readLabel put e)).2=some (some (.start g)) at S
        exact (start_iff put inj s e g).mp (Option.some.inj S)
    · apply IH
      intro j g b J Edit
      have E : i+(j+1)=i+1+j := by omega
      have P := H (j+1) g b (by simp; omega) (by rw [E]; exact Edit)
      exact P

theorem overwrite_skeleton_of_starts (put : G × Bool → Fin n) (inj : Function.Injective put)
    (key : Nat → Option (G × Bool)) (s : Armed G) (i : Nat) (w : List (Fin n))
    (H : ∀ j g b, j<w.length → key (i+j)=some (g,b) →
      (skeleton s (w.map (readLabel put)))[j]?=some (some (.start g))) :
    skeleton s ((overwriteFrom put key i w).map (readLabel put)) =
      skeleton s (w.map (readLabel put)) :=
  (overwrite_skeleton put inj key s i w (legal_of_starts put inj key s i w H)).1

#print axioms start_iff
#print axioms split_skeleton_at
#print axioms legal_of_starts
#print axioms overwrite_skeleton_of_starts
end L4.ReportPulseOverwrite
