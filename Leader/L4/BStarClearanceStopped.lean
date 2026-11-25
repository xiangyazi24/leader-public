import Leader.L4.BStarResetSchedule

/-! Stopped finite-word clearance. Local rank accounting may give
stutters on ordinary marks. A separate service lemma supplies a short
word with a strict decrease or an access event. -/
namespace L4.BStarClearanceStopped
open BStarResetSchedule

structure Certificate {X : Type} {n : Nat} (step : X → Fin n → X)
    (Inv Ready : X → Prop) (rank : X → Nat) (budget : Nat) : Prop where
  closed : ∀ x e, Inv x → ¬ Ready x → Inv (step x e)
  nonincrease : ∀ x e, Inv x → ¬ Ready x → rank (step x e)≤rank x
  serve : ∀ x, Inv x → ¬ Ready x → ∃ w : List (Fin n), w.length≤budget ∧
    (Ready (BStarResetSchedule.run step x w) ∨ rank (BStarResetSchedule.run step x w)<rank x)

def Before {X : Type} {n : Nat} (step : X → Fin n → X) (Ready : X → Prop)
    (x : X) (w : List (Fin n)) : Prop :=
  ∀ u e v, w=u++e::v → ¬ Ready (BStarResetSchedule.run step x u)

private theorem truncate_closed {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv Ready : X → Prop}
    (closed : ∀ x e, Inv x → ¬ Ready x → Inv (step x e))
    (x : X) (w : List (Fin n)) (I : Inv x) :
    ∃ u v, w=u++v ∧ Before step Ready x u ∧ Inv (BStarResetSchedule.run step x u) ∧
      (Ready (BStarResetSchedule.run step x u) ∨ v=[]) := by
  classical
  induction w generalizing x with
  | nil =>
    exact ⟨[],[],rfl,fun _ _ _ h => by have Z := congrArg List.length h; simp only [List.length_nil,List.length_append,List.length_cons] at Z; omega,I,.inr rfl⟩
  | cons e w ih =>
    by_cases R : Ready x
    · exact ⟨[],e::w,rfl,fun _ _ _ h => by have Z := congrArg List.length h; simp only [List.length_nil,List.length_append,List.length_cons] at Z; omega,I,.inl R⟩
    · obtain ⟨u,v,E,B,J,G⟩ := ih (step x e) (closed x e I R)
      refine ⟨e::u,v,congrArg (List.cons e) E,?_,J,G⟩
      intro p f q H
      cases p with
      | nil => exact R
      | cons a p =>
        obtain ⟨EA,EB⟩ := List.cons.inj H
        subst a
        exact B p f q EB

theorem truncate {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv Ready : X → Prop} {rank : X → Nat} {budget : Nat}
    (C : Certificate step Inv Ready rank budget) (x : X) (w : List (Fin n)) (I : Inv x) :
    ∃ u v, w=u++v ∧ Before step Ready x u ∧ Inv (BStarResetSchedule.run step x u) ∧
      (Ready (BStarResetSchedule.run step x u) ∨ v=[]) :=
  truncate_closed C.closed x w I

/-- A deterministic forcing word needs a strict decrease only at the
end of a nominated service block. There is no rank condition on the
other marks (or on intermediate marks of the block). Use the stronger
Certificate only for arbitrary-schedule accounting. -/
theorem ready_word_of_service {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv Ready : X → Prop} {rank : X → Nat} {budget : Nat}
    (closed : ∀ x e, Inv x → ¬ Ready x → Inv (step x e))
    (serve : ∀ x, Inv x → ¬ Ready x → ∃ w : List (Fin n), w.length≤budget ∧
      (Ready (BStarResetSchedule.run step x w) ∨ rank (BStarResetSchedule.run step x w)<rank x))
    (x : X) (I : Inv x) :
    ∃ w : List (Fin n), w.length≤budget*(rank x+1) ∧
      Before step Ready x w ∧ Inv (BStarResetSchedule.run step x w) ∧ Ready (BStarResetSchedule.run step x w) := by
  classical
  have go (k : Nat) : ∀ x, rank x=k → Inv x →
    ∃ w : List (Fin n), w.length≤budget*(k+1) ∧
      Before step Ready x w ∧ Inv (BStarResetSchedule.run step x w) ∧ Ready (BStarResetSchedule.run step x w) := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro x E I
      by_cases R : Ready x
      · exact ⟨[],Nat.zero_le _,fun _ _ _ h => by have Z := congrArg List.length h; simp only [List.length_nil,List.length_append,List.length_cons] at Z; omega,I,R⟩
      obtain ⟨w,L,H⟩ := serve x I R
      obtain ⟨u,v,W,B,J,Q⟩ := truncate_closed closed x w I
      have U : u.length≤budget := by rw [W,List.length_append] at L; omega
      have M : budget≤budget*(k+1) := by rw [Nat.mul_succ]; omega
      rcases Q with QQ|rfl
      · exact ⟨u,Nat.le_trans U M,B,J,QQ⟩
      rw [List.append_nil] at W
      subst w
      rcases H with H|H
      · exact ⟨u,Nat.le_trans U M,B,J,H⟩
      · have P : rank (BStarResetSchedule.run step x u)<k := E ▸ H
        obtain ⟨v,V,_,_,T⟩ := ih _ P _ rfl J
        obtain ⟨a,b,A,AB,AI,AR⟩ := truncate_closed closed x (u++v) I
        have RR : Ready (BStarResetSchedule.run step x a) := by
          rcases AR with h|rfl
          · exact h
          · rw [List.append_nil] at A
            rw [←A,BStarResetSchedule.run_append]
            exact T
        have S : budget*(rank (BStarResetSchedule.run step x u)+1)≤budget*k :=
          Nat.mul_le_mul_left _ (by omega)
        refine ⟨a,?_,AB,AI,RR⟩
        have AL := congrArg List.length A
        simp only [List.length_append] at AL
        rw [Nat.mul_succ]
        omega
  exact go _ x rfl I

theorem ready_word {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv Ready : X → Prop} {rank : X → Nat} {budget : Nat}
    (C : Certificate step Inv Ready rank budget) (x : X) (I : Inv x) :
    ∃ w : List (Fin n), w.length≤budget*(rank x+1) ∧
      Before step Ready x w ∧ Inv (BStarResetSchedule.run step x w) ∧ Ready (BStarResetSchedule.run step x w) :=
  ready_word_of_service C.closed C.serve x I

/-- Selection happens by a separate old-state edge after clearance,
not by assuming that the last clearing edge also has access. -/
theorem selectable_word {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv Ready : X → Prop} {rank : X → Nat} {budget : Nat}
    (C : Certificate step Inv Ready rank budget) (x : X) (I : Inv x)
    {Event : X → Fin n → X → Prop}
    (selectable : ∀ y, Inv y → Ready y → ∃ e, Event y e (step y e)) :
    ∃ w : List (Fin n), ∃ e : Fin n, (w++[e]).length≤budget*(rank x+1)+1 ∧
      Before step Ready x w ∧ Event (BStarResetSchedule.run step x w) e (BStarResetSchedule.run step x (w++[e])) := by
  obtain ⟨w,L,B,J,R⟩ := ready_word C x I
  obtain ⟨e,H⟩ := selectable _ J R
  refine ⟨w,e,?_,B,?_⟩
  · simp; omega
  · rw [BStarResetSchedule.run_append]
    exact H

theorem rank_along {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv Ready : X → Prop} {rank : X → Nat} {budget : Nat}
    (C : Certificate step Inv Ready rank budget) (x : X) (I : Inv x)
    (w : List (Fin n)) (B : Before step Ready x w) :
    rank (BStarResetSchedule.run step x w)≤rank x ∧ Inv (BStarResetSchedule.run step x w) := by
  induction w generalizing x with
  | nil => exact ⟨Nat.le_refl _,I⟩
  | cons e w ih =>
    have R := B [] e w rfl
    have H : Before step Ready (step x e) w := by
      intro u f v E
      exact B (e::u) f v (congrArg (List.cons e) E)
    obtain ⟨A,J⟩ := ih (step x e) (C.closed x e I R) H
    exact ⟨Nat.le_trans A (C.nonincrease x e I R),J⟩

end L4.BStarClearanceStopped
