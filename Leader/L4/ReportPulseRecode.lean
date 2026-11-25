import Lean

/-! Pure chronologically reversible relabeling of disjoint pulse pairs.
    A physical partition presents its labels as gate/side or outside. -/
namespace L4.ReportPulseRecode
universe u v
variable {G : Type u} {Z : Type v}
abbrev Label (G : Type u) (Z : Type v) := Sum (G × Bool) Z
abbrev Phase (G : Type u) := G → Option Bool

def flip (p : Option Bool) (b : Bool) : Bool :=
  match p with
  | none => b
  | some a => if a then !b else b

theorem flip_twice (p : Option Bool) (b : Bool) : flip p (flip p b)=b := by
  cases p with
  | none => rfl
  | some a => cases a <;> cases b <;> rfl

def relabel (s : Phase G) : Label G Z → Label G Z
  | .inl (i,b) => .inl (i,flip (s i) b)
  | .inr z => .inr z

theorem relabel_twice (s : Phase G) (e : Label G Z) : relabel s (relabel s e)=e := by
  cases e with
  | inl ib => obtain ⟨i,b⟩ := ib; simp [relabel,flip_twice]
  | inr _ => rfl

variable [DecidableEq G]

def phaseNext : Option Bool → Bool → Option Bool
  | none,b => some b
  | some a,b => if a=b then some a else none

def physicalStep (s : Phase G) : Label G Z → Phase G
  | .inr _ => s
  | .inl (i,b) => fun j => if j=i then phaseNext (s i) b else s j

def encode (s : Phase G) : List (Label G Z) → List (Label G Z)
  | [] => []
  | e::w => relabel s e::encode (physicalStep s e) w

def decode (s : Phase G) : List (Label G Z) → List (Label G Z)
  | [] => []
  | e::w =>
    let b := relabel s e
    b::decode (physicalStep s b) w

theorem decode_encode (s : Phase G) (w : List (Label G Z)) :
    decode s (encode s w)=w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w IH => simp only [encode,decode,relabel_twice,IH]

theorem encode_decode (s : Phase G) (w : List (Label G Z)) :
    encode s (decode s w)=w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w IH => simp only [decode,encode,relabel_twice,IH]

theorem encode_length (s : Phase G) (w : List (Label G Z)) :
    (encode s w).length=w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons e w IH => simp only [encode,List.length_cons,IH]

def Armed (G : Type u) := G → Bool
def armed (s : Phase G) : Armed G := fun i => (s i).isSome

inductive Event (G : Type u)
  | start (i : G)
  | complete (i : G)

/-- A pair label written in recoded coordinates: on an empty pair either
letter starts a round, whereas on an armed pair true closes the round. -/
def advance : Bool → Bool → Bool
  | false,_ => true
  | true,b => !b

def skeletonStep (s : Armed G) : Label G Z → Armed G × Option (Event G)
  | .inr _ => (s,none)
  | .inl (i,b) =>
    (fun j => if j=i then advance (s i) b else s j,
     if s i then (if b then some (.complete i) else none)
     else some (.start i))

def physicalEvent (s : Phase G) : Label G Z → Option (Event G)
  | .inr _ => none
  | .inl (i,b) =>
    match s i with
    | none => some (.start i)
    | some a => if a=b then none else some (.complete i)

theorem step_fusion (s : Phase G) (e : Label G Z) :
    skeletonStep (armed s) (relabel s e)=(armed (physicalStep s e),physicalEvent s e) := by
  cases e with
  | inr _ => rfl
  | inl ib =>
    obtain ⟨i,b⟩ := ib
    apply Prod.ext
    · funext j
      by_cases H : j=i
      · subst j
        cases E : s i with
        | none => simp [armed,skeletonStep,relabel,physicalStep,E,flip,phaseNext,advance]
        | some a => cases a <;> cases b <;> simp [armed,skeletonStep,relabel,physicalStep,E,flip,phaseNext,advance]
      · simp [armed,skeletonStep,relabel,physicalStep,H]
    · cases E : s i with
      | none => simp [armed,skeletonStep,relabel,physicalEvent,E,flip]
      | some a => cases a <;> cases b <;> simp [armed,skeletonStep,relabel,physicalEvent,E,flip]

def skeleton (s : Armed G) : List (Label G Z) → List (Option (Event G))
  | [] => []
  | e::w => (skeletonStep s e).2::skeleton (skeletonStep s e).1 w

def physicalEvents (s : Phase G) : List (Label G Z) → List (Option (Event G))
  | [] => []
  | e::w => physicalEvent s e::physicalEvents (physicalStep s e) w

theorem skeleton_encode (s : Phase G) (w : List (Label G Z)) :
    skeleton (armed s) (encode s w)=physicalEvents s w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w IH => simp only [encode,skeleton,physicalEvents,step_fusion,IH]

theorem empty_start_flip (s : Armed G) (i : G) (H : s i=false)
    (a b : Bool) (w : List (Label G Z)) :
    skeleton s (.inl (i,a)::w)=skeleton s (.inl (i,b)::w) := by
  simp only [skeleton,skeletonStep,H]
  rfl

def skeletonState (s : Armed G) : List (Label G Z) → Armed G
  | [] => s
  | e::w => skeletonState (skeletonStep s e).1 w

theorem flip_after_prefix (s : Armed G) (pre post : List (Label G Z))
    (i : G) (H : skeletonState s pre i=false) (a b : Bool) :
    skeleton s (pre++(.inl (i,a)::post))=skeleton s (pre++(.inl (i,b)::post)) := by
  induction pre generalizing s with
  | nil => exact empty_start_flip s i H a b post
  | cons e pre IH =>
    simp only [List.cons_append,skeleton]
    exact congrArg (List.cons (skeletonStep s e).2) (IH _ H)

section Finite
variable {n : Nat}

/-- Disjoint actual pulse pairs specified as an injective side-to-edge map.
Unused physical edges exist as the literal complement; no counts or
choices are needed for them. -/
def Outside (put : G × Bool → Fin n) : Type :=
  {e : Fin n // ¬∃ ib,put ib=e}

def writeLabel (put : G × Bool → Fin n) : Label G (Outside put) → Fin n
  | .inl ib => put ib
  | .inr e => e.val

noncomputable def readLabel (put : G × Bool → Fin n) (e : Fin n) :
    Label G (Outside put) := by
  classical
  exact if H : ∃ ib,put ib=e then .inl (Classical.choose H) else .inr ⟨e,H⟩

omit [DecidableEq G] in
theorem write_read (put : G × Bool → Fin n) (e : Fin n) :
    writeLabel put (readLabel put e)=e := by
  classical
  unfold readLabel
  split
  · exact Classical.choose_spec ‹∃ ib,put ib=e›
  · rfl

omit [DecidableEq G] in
theorem read_write (put : G × Bool → Fin n) (inj : Function.Injective put)
    (e : Label G (Outside put)) :
    readLabel put (writeLabel put e)=e := by
  classical
  cases e with
  | inl ib =>
    change readLabel put (put ib)=.inl ib
    unfold readLabel
    rw [dif_pos (show ∃ a,put a=put ib from ⟨ib,rfl⟩)]
    exact congrArg Sum.inl (inj (Classical.choose_spec (show ∃ a,put a=put ib from ⟨ib,rfl⟩)))
  | inr e =>
    change readLabel put e.val=.inr e
    unfold readLabel
    rw [dif_neg e.property]
    exact congrArg Sum.inr (Subtype.ext rfl)

omit [DecidableEq G] in
theorem read_write_word (put : G × Bool → Fin n) (inj : Function.Injective put)
    (w : List (Label G (Outside put))) :
    (w.map (writeLabel put)).map (readLabel put)=w := by
  induction w with
  | nil => rfl
  | cons e w IH => simp only [List.map_cons,read_write put inj,IH]

omit [DecidableEq G] in
theorem write_read_word (put : G × Bool → Fin n) (w : List (Fin n)) :
    (w.map (readLabel put)).map (writeLabel put)=w := by
  induction w with
  | nil => rfl
  | cons e w IH => simp only [List.map_cons,write_read,IH]

noncomputable def encodeFin (put : G × Bool → Fin n) (s : Phase G)
    (w : List (Fin n)) : List (Fin n) :=
  (encode s (w.map (readLabel put))).map (writeLabel put)

noncomputable def decodeFin (put : G × Bool → Fin n) (s : Phase G)
    (w : List (Fin n)) : List (Fin n) :=
  (decode s (w.map (readLabel put))).map (writeLabel put)

theorem decode_encodeFin (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Phase G) (w : List (Fin n)) : decodeFin put s (encodeFin put s w)=w := by
  unfold decodeFin encodeFin
  rw [read_write_word put inj,decode_encode,write_read_word]

theorem encode_decodeFin (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Phase G) (w : List (Fin n)) : encodeFin put s (decodeFin put s w)=w := by
  unfold decodeFin encodeFin
  rw [read_write_word put inj,encode_decode,write_read_word]

theorem encodeFin_length (put : G × Bool → Fin n) (s : Phase G) (w : List (Fin n)) :
    (encodeFin put s w).length=w.length := by
  simp [encodeFin,encode_length]

theorem skeleton_encodeFin (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Phase G) (w : List (Fin n)) :
    skeleton (armed s) ((encodeFin put s w).map (readLabel put)) =
      physicalEvents s (w.map (readLabel put)) := by
  unfold encodeFin
  rw [read_write_word put inj,skeleton_encode]

theorem flip_after_prefixFin (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Armed G) (pre post : List (Fin n))
    (i : G) (H : skeletonState s (pre.map (readLabel put)) i=false) (a b : Bool) :
    skeleton s ((pre++(put (i,a)::post)).map (readLabel put)) =
      skeleton s ((pre++(put (i,b)::post)).map (readLabel put)) := by
  have E (bit : Bool) : readLabel put (put (i,bit))=.inl (i,bit) :=
    read_write put inj (.inl (i,bit))
  simp only [List.map_append,List.map_cons,E]
  exact flip_after_prefix s _ _ i H a b

/-- Completion at a given recoded mark pins its physical-label coordinate
in the *recoded* word; it need not pin the original physical edge. -/
theorem completion_pinsFin (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Armed G) (e : Fin n) (i : G) :
    (skeletonStep s (readLabel put e)).2=some (.complete i) ↔
      e=put (i,true) ∧ s i=true := by
  constructor
  · cases E : readLabel put e with
    | inr z => simp [skeletonStep]
    | inl ib =>
      obtain ⟨j,bit⟩ := ib
      have W := write_read put e
      rw [E] at W
      change put (j,bit)=e at W
      cases A : s j <;> cases bit <;> simp [skeletonStep,A]
      intro Q
      subst j
      exact ⟨W.symm,A⟩
  · rintro ⟨rfl,H⟩
    rw [show readLabel put (put (i,true))=.inl (i,true) from read_write put inj (.inl (i,true))]
    simp [skeletonStep,H]

end Finite
end L4.ReportPulseRecode
