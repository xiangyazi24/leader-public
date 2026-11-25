import Leader.L4.BStarBitSegment

namespace L4.BStarBitGateCover
open BStarLongClaims BStarClearanceRaceMark BStarBitSegment

def absorbing {n : Nat} (i : Fin n) (state : Option Phase) (e : Fin n) : Option Phase :=
  state.bind (fun p => nextPhase i p e)

def leftSeen (p : Option Phase) : Prop :=
  p=none ∨ p=some (.first .left) ∨ ∃ s, p=some (.complete s)

def bothSeen (p : Option Phase) : Prop :=
  p=none ∨ ∃ s, p=some (.complete s)

variable {n : Nat} (i : Fin n)
local notation "L" => incident i Side.left
local notation "R" => incident i Side.right

theorem left_hits (z : Option Phase) :
    leftSeen (absorbing i z L) := by
  cases z with
  | none => simp [absorbing,leftSeen]
  | some p =>
    cases p with
    | fresh => simp [absorbing,nextPhase,leftSeen]
    | first s => cases s <;> simp [absorbing,nextPhase,leftSeen]
    | complete s => simp [absorbing,nextPhase,leftSeen]

theorem left_stays (z : Option Phase) (Z : leftSeen z) (e : Fin n) :
    leftSeen (absorbing i z e) := by
  rcases Z with rfl|rfl|⟨s,rfl⟩
  · simp [absorbing,leftSeen]
  · by_cases A : e=L <;> by_cases T : e=R <;> simp_all [absorbing,nextPhase,leftSeen]
  · by_cases A : e=L <;> by_cases T : e=R <;> simp_all [absorbing,nextPhase,leftSeen]

theorem right_hits (distinct : L≠R) (z : Option Phase) (Z : leftSeen z) :
    bothSeen (absorbing i z R) := by
  have D := Ne.symm distinct
  rcases Z with rfl|rfl|⟨s,rfl⟩
  · simp [absorbing,bothSeen]
  · simp [absorbing,nextPhase,D,bothSeen]
  · simp [absorbing,nextPhase,D,bothSeen]

theorem both_stays (z : Option Phase) (Z : bothSeen z) (e : Fin n) :
    bothSeen (absorbing i z e) := by
  rcases Z with rfl|⟨s,rfl⟩
  · simp [absorbing,bothSeen]
  · by_cases A : e=L <;> by_cases T : e=R <;> simp_all [absorbing,nextPhase,bothSeen]

theorem last_hits (z : Option Phase) (Z : bothSeen z) : absorbing i z L=none := by
  rcases Z with rfl|⟨s,rfl⟩
  · rfl
  · simp [absorbing,nextPhase]

private theorem word_invariant {A B : Type} (f : A→B→A) (P : A→Prop)
    (keep : ∀ a e,P a→P (f a e)) (w : List B) (x : A) (init : P x) :
    P (w.foldl f x) := by
  induction w generalizing x with
  | nil => exact init
  | cons e w ih => exact ih _ (keep _ _ init)

private theorem service {A B : Type} (f : A→B→A) (P Q : A→Prop)
    (preserveP : ∀ a e,P a→P (f a e)) (preserveQ : ∀ a e,Q a→Q (f a e))
    (e : B) (hit : ∀ a,P a→Q (f a e)) (w : List B) (haveMark : e∈w)
    (x : A) (init : P x) : Q (w.foldl f x) := by
  obtain ⟨u,v,W,_⟩ := List.eq_append_cons_of_mem haveMark
  rw [W,List.foldl_append,List.foldl_cons]
  exact word_invariant f Q preserveQ v _ (hit _ (word_invariant f P preserveP u x init))

/-- Left-right-left is a fixed subsequence cover for all five pending
gate phases. Extra labels cannot undo progress. This says nothing
about which side was first; earlier labels may choose either side. -/
theorem left_right_left (distinct : L≠R) (p : Phase) (w : List (Fin n))
    (cover : [L,R,L].Sublist w) : w.foldl (absorbing i) (some p)=none := by
  obtain ⟨a,bc,W,A,Rl⟩ := List.cons_sublist_iff.mp cover
  obtain ⟨b,c,V,B,F⟩ := List.cons_sublist_iff.mp Rl
  have C : L∈c := List.mem_of_cons_sublist F
  have P := service (absorbing i) (fun _=>True) leftSeen (fun _ _ _=>True.intro)
    (fun z e H=>left_stays i z H e) L (fun z _=>left_hits i z) a A (some p) trivial
  have Q := service (absorbing i) leftSeen bothSeen (fun z e H=>left_stays i z H e)
    (fun z e H=>both_stays i z H e) R (right_hits i distinct) b B _ P
  rw [W,V,List.foldl_append,List.foldl_append]
  exact service (absorbing i) bothSeen (fun z=>z=none) (fun z e H=>both_stays i z H e)
    (fun _ _ H=>by rw [H]; rfl) L (last_hits i) c C _ Q

private theorem completes_only (p : Phase) (e : Fin n)
    (nonePhase : nextPhase i p e=none) : ∃ s,p=.complete s := by
  cases p with
  | fresh =>
    by_cases A : e=L <;> by_cases T : e=R <;> simp_all [nextPhase]
  | first s =>
    cases s <;> by_cases A : e=L <;> by_cases T : e=R <;> simp_all [nextPhase]
  | complete s => exact ⟨s,rfl⟩

/-- The exact scanner is checked only on the prefix ending at its
first departure, not on the entire extended word. -/
theorem first_departure (w : List (Fin n)) (p : Phase)
    (exit : w.foldl (absorbing i) (some p)=none) :
    ∃ pre post s,w=pre++post ∧ readSegment i p pre=some s := by
  induction w generalizing p with
  | nil => contradiction
  | cons e es ih =>
    cases h : nextPhase i p e with
    | none =>
      obtain ⟨s,rfl⟩ := completes_only i p e h
      exact ⟨[e],es,s,rfl,by simp [readSegment,h]⟩
    | some q =>
      have exit' : es.foldl (absorbing i) (some q)=none := by
        change es.foldl (absorbing i) (nextPhase i p e)=none at exit
        rwa [h] at exit
      obtain ⟨pre,post,s,E,read⟩ := ih q exit'
      exact ⟨e::pre,post,s,congrArg (List.cons e) E,by simp [readSegment,h,read]⟩

end L4.BStarBitGateCover
