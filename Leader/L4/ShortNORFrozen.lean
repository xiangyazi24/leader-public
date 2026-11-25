import Leader.L4.CustodyMonitorTargets
import Leader.L4.SelectedMISLayers

namespace L4.ShortNORFrozen
open ShortNORCover CustodyMonitorTargets

theorem update_eq_of_maximal {J : Type} [DecidableEq J]
    (r : Ring J) (z : J→Bool) (I : Independent r z)
    (D : ∀ j,Dominates r z j) (e : J) : update r z e=z := by
  funext j
  by_cases E : j=e
  · subst j
    cases B : z e with
    | true => exact chosen_step r z e e I B
    | false =>
      have H := D e
      rcases H with L|M|R
      · simp [update,selectedNeighbors,L]
      · rw [B] at M
        cases M
      · simp [update,selectedNeighbors,R]
  · simp [update,E]

theorem raw_observe_frozen {X J : Type} {n : Nat} [DecidableEq J]
    (step : X→Fin n→X) (classify : X→Fin n→Option J)
    (r : Ring J) (observe : X→J→Bool) (Good : X→Prop)
    (closed : ∀ x e,Good x→Good (step x e))
    (auth : ∀ x e,Good x→observe (step x e)=
      match classify x e with
      | none => observe x
      | some j => update r (observe x) j)
    (x : X) (w : List (Fin n)) (M : RawMaximal r observe Good x) :
    RawMaximal r observe Good (w.foldl step x) ∧
      observe (w.foldl step x)=observe x := by
  induction w generalizing x with
  | nil => exact ⟨M,rfl⟩
  | cons e w IH =>
    have R := raw_maximal_closed step classify r observe Good closed auth x e M
    have E : observe (step x e)=observe x := by
      rw [auth x e M.1]
      cases classify x e with
      | none => rfl
      | some j => exact update_eq_of_maximal r _ M.2.1 M.2.2 j
    obtain ⟨A,B⟩ := IH _ R
    exact ⟨A,B.trans E⟩

#print axioms update_eq_of_maximal
#print axioms raw_observe_frozen
end L4.ShortNORFrozen
