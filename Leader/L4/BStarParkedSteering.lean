import Leader.L4.BStarSteeredLikelihood

namespace L4.BStarParkedSteering
open BStarSteeringSupport BStarSteeredLikelihood BStarAdmitIncidentGeometry
open BStarClearanceRaceMark BStarLongClaims BStarH6Ordinal

/-- No non-first phase is eligible to be prescribed under the paper's
mask. The caller still constructs the mask and its generated history. -/
def FreshOnly {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (fresh : Word n → Fin n → Prop)
    (redirect : Word n → Fin n → Option (Fin n)) : Prop :=
  ∀ a e f, redirect a e=some f → ∃ i s, ordinal h hh i=gateOrdinal false ∧
    fresh a i ∧ e=incident i s ∧ f=incident i (opposite s)

theorem support_of_fresh {n : Nat} {h : Fin n→Bool} {hh : ∃ i,h i=true}
    {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (H : FreshOnly h hh fresh redirect) (a : Word n) : Supported h hh (redirect a) := by
  intro e f E
  obtain ⟨i,s,I,_,S,T⟩ := H a e f E
  exact ⟨i,s,I,S,T⟩

/-- Once an ADMIT is in OTHER, no fresh gate can redirect either of
its two physical candidate edges: equal source labels force the same gate. -/
theorem parked_candidate_unchanged {n : Nat} {h : Fin n→Bool} {hh : ∃ i,h i=true}
    {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (mask : FreshOnly h hh fresh redirect)
    (a : Word n) (i : Fin n) (I : ordinal h hh i=gateOrdinal false)
    (parked : ¬fresh a i) (s : Side) :
    chooseBy redirect a (incident i s) = incident i s := by
  unfold chooseBy
  cases E : redirect a (incident i s) with
  | none => rfl
  | some f =>
    obtain ⟨j,t,J,F,L,_⟩ := mask a _ f E
    obtain ⟨eq,_,_⟩ := incident_gate_injective h hh i j false false I J s t L
    exact (parked (eq.symm ▸ F)).elim

/-- After a suppression, a parked ADMIT cannot suffer a second
suppression on its nominated side. The condition on a skipped
prefix is exactly residence of the same nonfresh gate up to payment,
not a claim of independence of the next candidate mark. -/
theorem parked_fiber {n : Nat} {h : Fin n→Bool} {hh : ∃ i,h i=true}
    {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (mask : FreshOnly h hh fresh redirect)
    (a : Word n) (i : Fin n) (I : ordinal h hh i=gateOrdinal false)
    (parked : ¬fresh a i) (s : Side) (e : Fin n) :
    chooseBy redirect a e = incident i s ↔ e = incident i s := by
  constructor
  · intro H
    unfold chooseBy at H
    cases E : redirect a e with
    | none => simpa only [E,Option.getD_none] using H
    | some f =>
      change (redirect a e).getD e = incident i s at H
      rw [E] at H
      obtain ⟨j,t,J,F,_,out⟩ := mask a e f E
      have K : incident i s = incident j (opposite t) := H.symm.trans out
      obtain ⟨eq,_,_⟩ := incident_gate_injective h hh i j false false I J s _ K
      exact (parked (eq.symm ▸ F)).elim
  · rintro rfl
    exact parked_candidate_unchanged mask a i I parked s

#print axioms parked_fiber

theorem parked_first_candidate {n : Nat} {h : Fin n→Bool} {hh : ∃ i,h i=true}
    {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (mask : FreshOnly h hh fresh redirect)
    (a skipped suffix : Word n) (i : Fin n) (I : ordinal h hh i=gateOrdinal false) (s : Side)
    (still : ¬fresh (a++emit (chooseBy redirect) a skipped) i) :
    emit (chooseBy redirect) a (skipped++incident i s::suffix) =
      emit (chooseBy redirect) a skipped ++
        incident i s :: emit (chooseBy redirect)
          ((a++emit (chooseBy redirect) a skipped)++[incident i s]) suffix := by
  have split (a u w : Word n) :
      emit (chooseBy redirect) a (u++w) =
        emit (chooseBy redirect) a u ++
          emit (chooseBy redirect) (a++emit (chooseBy redirect) a u) w := by
    induction u generalizing a with
    | nil => simp [emit]
    | cons e u ih =>
      rw [List.cons_append,emit,emit,ih]
      simp only [List.cons_append,List.append_assoc,List.nil_append]
  rw [split,emit,parked_candidate_unchanged mask _ i I still s]

/-- Canonical predictable steering: for each currently eligible fresh
ADMIT, send its unchosen candidate to the selected mate. Only the
distinct physical labels are examined; no erased event clock is used. -/
noncomputable def redirectTo {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (fresh : Word n → Fin n → Prop) (pick : Word n → Fin n → Side)
    (a : Word n) (e : Fin n) : Option (Fin n) :=
  open Classical in
  if H : ∃ i, ordinal h hh i=gateOrdinal false ∧ fresh a i ∧
      e=incident i (opposite (pick a i)) then
    some (incident (Classical.choose H) (pick a (Classical.choose H)))
  else none

theorem opposite_opposite (s : Side) : opposite (opposite s)=s := by cases s <;> rfl

theorem redirectTo_isFresh {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (fresh : Word n → Fin n → Prop) (pick : Word n → Fin n → Side) :
    FreshOnly h hh fresh (redirectTo h hh fresh pick) := by
  intro a e f E
  classical
  unfold redirectTo at E
  split at E
  · rename_i H
    obtain ⟨I,F,S⟩ := Classical.choose_spec H
    refine ⟨Classical.choose H, opposite (pick a (Classical.choose H)),I,F,S,?_⟩
    rw [opposite_opposite]
    exact (Option.some.inj E).symm
  · contradiction

theorem redirectTo_fresh_hit {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (fresh : Word n → Fin n → Prop) (pick : Word n → Fin n → Side)
    (a : Word n) (i : Fin n) (I : ordinal h hh i=gateOrdinal false)
    (new : fresh a i) (s : Side) :
    chooseBy (redirectTo h hh fresh pick) a (incident i s) =
      incident i (pick a i) := by
  classical
  unfold chooseBy redirectTo
  by_cases P : s=pick a i
  · rw [P]
    split
    · rename_i H
      obtain ⟨J,_,S⟩ := Classical.choose_spec H
      obtain ⟨E,_,K⟩ := incident_gate_injective h hh i (Classical.choose H)
        false false I J _ _ S
      rw [←E] at K
      have N (t : Side) : t ≠ opposite t := by cases t <;> decide
      exact (N _ K).elim
    · rfl
  · have O : s=opposite (pick a i) := by
      cases Ps : pick a i <;> cases s <;> simp_all [opposite]
    let e := incident i s
    have H : ∃ j, ordinal h hh j=gateOrdinal false ∧ fresh a j ∧
        e=incident j (opposite (pick a j)) := ⟨i,I,new,congrArg (incident i) O⟩
    change ((if J : ∃ j, ordinal h hh j=gateOrdinal false ∧ fresh a j ∧
        e=incident j (opposite (pick a j)) then
          some (incident (Classical.choose J) (pick a (Classical.choose J))) else none).getD e) = _
    rw [dif_pos H]
    obtain ⟨J,_,S⟩ := Classical.choose_spec H
    obtain ⟨E,_,_⟩ := incident_gate_injective h hh i (Classical.choose H) false false I J _ _ S
    rw [←E]
    rfl

/-- The loss ledger charges exactly one decision when the nominated
gate is prescribed, regardless of which of its two candidates arrived. -/
theorem redirectTo_charges_fresh {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (fresh : Word n → Fin n → Prop) (pick : Word n → Fin n → Side)
    (a : Word n) (i : Fin n) (I : ordinal h hh i=gateOrdinal false)
    (new : fresh a i) (s : Side) :
    prescribed (redirectTo h hh fresh pick) a
      (chooseBy (redirectTo h hh fresh pick) a (incident i s)) = 1 := by
  classical
  rw [redirectTo_fresh_hit h hh fresh pick a i I new s]
  unfold prescribed
  have P : ∃ e, redirectTo h hh fresh pick a e=some (incident i (pick a i)) := by
    refine ⟨incident i (opposite (pick a i)),?_⟩
    unfold redirectTo
    let e := incident i (opposite (pick a i))
    have Z : ∃ j, ordinal h hh j=gateOrdinal false ∧ fresh a j ∧
        e=incident j (opposite (pick a j)) := ⟨i,I,new,rfl⟩
    change (if H : ∃ j, ordinal h hh j=gateOrdinal false ∧ fresh a j ∧
        e=incident j (opposite (pick a j)) then
        some (incident (Classical.choose H) (pick a (Classical.choose H))) else none)=_
    rw [dif_pos Z]
    obtain ⟨J,_,U⟩ := Classical.choose_spec Z
    obtain ⟨E,_,_⟩ := incident_gate_injective h hh i (Classical.choose Z) false false I J _ _ U
    rw [←E]
  rw [if_pos P]

#print axioms redirectTo_charges_fresh
#print axioms redirectTo_isFresh
#print axioms redirectTo_fresh_hit
#print axioms parked_candidate_unchanged
#print axioms parked_first_candidate
end L4.BStarParkedSteering
