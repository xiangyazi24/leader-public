import Leader.L4.ShortFiveRenewal
import Leader.L4.ShortTwoPublicationClock
import Leader.L4.ReportAdaptiveRank
import Leader.L4.ShortFiveFailurePotential

namespace L4.ShortPrefixTrial
open Classical

variable {X : Type} {n : Nat}

structure State (X : Type) (n : Nat) where
  real : X×Bool
  remain : Option (List (Fin n))

def filterWord (watch : Fin n→Bool) (w : List (Fin n)) := w.filter watch

def start (x : X×Bool) (word : List (Fin n)) : State X n := ⟨x,some word⟩

def cursor (watch : Fin n→Bool) (p : Option (List (Fin n))) (e : Fin n) :
    Option (List (Fin n)) :=
  match p with
  | some (a::w) => if e=a then some w else if watch e then none else p
  | _ => p

/-- Even an abort mark is executed first on the original raw tape.
Only a true event from the checked real phase can latch success. -/
def next (step : (X×Bool)→Fin n→(X×Bool)) (watch : Fin n→Bool)
    (y : State X n) (e : Fin n) : State X n :=
  let z:=step y.real e
  ⟨z,if z.2 then y.remain else cursor watch y.remain e⟩

def ready (y : State X n) : Prop := y.real.2=true ∨ y.remain=none ∨ y.remain=some []

def reach (step : (X×Bool)→Fin n→(X×Bool)) (Good : X→Prop) (watch : Fin n→Bool)
    (x : X×Bool) (word : List (Fin n)) (y : State X n) : Prop :=
  Good y.real.1 ∧ ∀ rem, y.real.2≠true → y.remain=some rem →
    ∃ w, y.real=Height.runWord step x w ∧ filterWord watch w++rem=word

def Replay (step : (X×Bool)→Fin n→(X×Bool)) (watch : Fin n→Bool)
    (x : X×Bool) (word : List (Fin n)) : Prop :=
  ∀ w, filterWord watch w=word → (Height.runWord step x w).2=true

theorem reach_start (step : (X×Bool)→Fin n→(X×Bool)) (Good : X→Prop) (watch : Fin n→Bool)
    (x : X×Bool) (word : List (Fin n)) (G : Good x.1) :
    reach step Good watch x word (start x word) := by
  refine ⟨G,?_⟩
  intro rem _ W
  have E : word=rem := Option.some.inj W
  subst rem
  exact ⟨[],rfl,rfl⟩

theorem exhausted_true {step : (X×Bool)→Fin n→(X×Bool)} {Good : X→Prop} {watch : Fin n→Bool}
    {x : X×Bool} {word : List (Fin n)}
    (S : Replay step watch x word)
    (y : State X n) (Y : reach step Good watch x word y) (E : y.remain=some []) :
    y.real.2=true := by
  by_cases F : y.real.2=true
  · exact F
  · obtain ⟨w,W,R⟩ := Y.2 [] F E
    rw [W]
    exact S w (by simpa using R)

theorem reach_next (step : (X×Bool)→Fin n→(X×Bool)) (Good : X→Prop)
    (closed : ∀ z e, Good z.1→Good (step z e).1)
    (sticky : ∀ z e, z.2=true→(step z e).2=true)
    (watch : Fin n→Bool) (x : X×Bool) (word : List (Fin n))
    (H : ∀ e∈word,watch e=true) (S : Replay step watch x word)
    (y : State X n) (e : Fin n) (Y : reach step Good watch x word y) :
    reach step Good watch x word (next step watch y e) := by
  refine ⟨closed y.real e Y.1,?_⟩
  intro rem F R
  change (step y.real e).2≠true at F
  have A : y.real.2≠true := fun I=>F (sticky y.real e I)
  have M : cursor watch y.remain e=some rem := by simpa only [next,if_neg F] using R
  cases old : y.remain with
  | none => simp [old,cursor] at M
  | some p =>
    cases p with
    | nil => exact False.elim (A (exhausted_true S y Y old))
    | cons a u =>
      obtain ⟨w,W,P⟩ := Y.2 (a::u) A old
      refine ⟨w++[e],?_,?_⟩
      · change step y.real e=_
        rw [Height.runWord_append,←W]
        rfl
      · simp only [old,cursor] at M
        change (w++[e]).filter watch++rem=word
        rw [List.filter_append,List.append_assoc]
        by_cases E : e=a
        · subst e
          have B : watch a=true := H a (by rw [←P]; exact List.mem_append_right _ (by simp))
          simp only [if_true,Option.some.injEq] at M
          subst rem
          simpa only [filterWord,List.filter_cons,B,if_true,List.filter_nil,List.cons_append,List.nil_append] using P
        · simp only [if_neg E] at M
          cases V : watch e with
          | true => simp [V] at M
          | false =>
            simp only [V,Bool.false_eq_true,if_false,Option.some.injEq] at M
            subst rem
            simpa only [filterWord,List.filter_cons,V,Bool.false_eq_true,if_false,List.filter_nil,List.nil_append] using P

theorem remain_in_word {step : (X×Bool)→Fin n→(X×Bool)} {Good : X→Prop} {watch : Fin n→Bool}
    {x : X×Bool} {word : List (Fin n)} {y : State X n} {rem : List (Fin n)}
    (Y : reach step Good watch x word y) (F : y.real.2≠true) (R : y.remain=some rem)
    (e : Fin n) (E : e∈rem) : e∈word := by
  obtain ⟨w,_,W⟩ := Y.2 rem F R
  rw [←W]
  exact List.mem_append_right _ E

theorem real_next (step : (X×Bool)→Fin n→(X×Bool)) (watch : Fin n→Bool)
    (y : State X n) (e : Fin n) : (next step watch y e).real=step y.real e := rfl

/-- On a live trial, in the absence of a real event on this mark, the
first wrong watched mark makes a terminal failure. A spectator mark
cannot do so, including when it changes other raw bytes. -/
theorem wrong_mark_stops (step : (X×Bool)→Fin n→(X×Bool)) (watch : Fin n→Bool)
    (y : State X n) (e a : Fin n) (u : List (Fin n))
    (R : y.remain=some (a::u)) (N : (step y.real e).2≠true) :
    (next step watch y e).remain=none ↔ e≠a ∧ watch e=true := by
  unfold next
  dsimp only
  simp only [if_neg N,R,cursor]
  by_cases E : e=a
  · simp [E]
  · cases W : watch e <;> simp [E]

theorem terminal_bad_iff_wrong {step : (X×Bool)→Fin n→(X×Bool)} {Good : X→Prop}
    {watch : Fin n→Bool} {x : X×Bool} {word : List (Fin n)}
    (S : Replay step watch x word) {y : State X n} (Y : reach step Good watch x word y)
    (R : ready y) (F : y.real.2≠true) : y.remain=none := by
  rcases R with H|H|H
  · exact False.elim (F H)
  · exact H
  · exact False.elim (F (exhausted_true S y Y H))

def stage (step : (X×Bool)→Fin n→(X×Bool)) (Good : X→Prop)
    (closed : ∀ z e, Good z.1→Good (step z e).1)
    (sticky : ∀ z e, z.2=true→(step z e).2=true)
    (watch : Fin n→Bool) (x : X×Bool) (word : List (Fin n))
    (H : ∀ e∈word,watch e=true) (S : Replay step watch x word) (G : Good x.1) :
    TripleRenewal.Stage step x :=
  ⟨State X n,start x word,next step watch,State.real,ready,reach step Good watch x word,
   rfl,real_next step watch,reach_start step Good watch x word G,reach_next step Good closed sticky watch x word H S⟩

def rank (y : State X n) : Nat :=
  if y.real.2 then 0 else (y.remain.map List.length).getD 0

theorem trans_mean {Y : Type} (step : Y→Fin n→Y) (hit : Y→Prop)
    (t : Nat) (x : Y) :
    iidHitCost step hit t x=Height.iidHitCost step hit t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases H : hit x
    · simp [iidHitCost,Height.iidHitCost,H]
    · simp only [iidHitCost,Height.iidHitCost,if_neg H]
      congr 2
      apply congrArg List.ofFn
      funext e
      exact ih _

theorem trial_mean {step : (X×Bool)→Fin n→(X×Bool)} {Good : X→Prop} {watch : Fin n→Bool}
    {x : X×Bool} {word : List (Fin n)}
    (closed : ∀ z e, Good z.1→Good (step z e).1)
    (sticky : ∀ z e, z.2=true→(step z e).2=true)
    (H : ∀ e∈word,watch e=true) (S : Replay step watch x word)
    (y : State X n) (Y : reach step Good watch x word y) :
    IIDExpectedHittingTimeAtMost (next step watch) ready y (n*rank y) := by
  let Q := reach step Good watch x word
  have F : ReportAdaptiveFibre.Nomination (next step watch) Q ready rank := by
    refine ⟨reach_next step Good closed sticky watch x word H S,?_,?_⟩
    · intro z e _ D
      have Z : z.real.2≠true := fun G=>D (.inl G)
      cases E : z.remain with
      | none => exact False.elim (D (.inr (.inl E)))
      | some rem =>
        cases rem with
        | nil => exact False.elim (D (.inr (.inr E)))
        | cons a rem =>
          unfold rank next
          dsimp only
          split
          · exact Nat.zero_le _
          · simp only [E,cursor]
            split
            · simp
            · split <;> simp
    · intro z _ D
      have Z : z.real.2≠true := fun G=>D (.inl G)
      cases E : z.remain with
      | none => exact False.elim (D (.inr (.inl E)))
      | some rem =>
        cases rem with
        | nil => exact False.elim (D (.inr (.inr E)))
        | cons a rem =>
          refine ⟨a,?_⟩
          unfold rank next
          dsimp only
          simp only [if_neg Z,E,cursor,if_true,Option.map_some,Option.getD_some,List.length_cons]
          split <;> simp <;> omega
  intro t
  rw [trans_mean]
  exact ReportAdaptiveFibre.nominated_mean (next step watch) Q ready rank F y Y t

#print axioms stage
#print axioms wrong_mark_stops
#print axioms exhausted_true
#print axioms trial_mean
end L4.ShortPrefixTrial
