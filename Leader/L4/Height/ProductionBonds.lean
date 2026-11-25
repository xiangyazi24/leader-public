import Leader.L4.Height.CandidatePolicy
import Leader.L4.Height.OpenFenceLine

namespace L4.Height.CandidateResidence
open PhysicalCustody ProductionCustody BStarAcquireLiteralChain BStarH6WordChart
open BStarSteeredLikelihood BStarParkedSteering BStarSteeringSupport
open Classical
noncomputable section

private theorem first {α : Type} [DecidableEq α] (e : α) (w : List α) (hit : e∈w) :
    ∃ u v, w=u++e::v ∧ ∀ f∈u,f≠e := by
  induction w with
  | nil => exact (List.not_mem_nil hit).elim
  | cons a w ih =>
    by_cases same : a=e
    · subst a
      exact ⟨[],w,rfl,by simp⟩
    · obtain ⟨u,v,eq,avoid⟩ := ih ((List.mem_cons.mp hit).resolve_left (Ne.symm same))
      refine ⟨a::u,v,congrArg (List.cons a) eq,?_⟩
      intro f mem
      rcases List.mem_cons.mp mem with rfl|rest
      · exact same
      · exact avoid _ rest

private theorem join {n : Nat} (c : Word n → Fin n → Fin n) (a u v : Word n) :
    emit c a (u++v)=emit c a u++emit c (a++emit c a u) v := by
  induction u generalizing a with
  | nil => simp [emit]
  | cons e u ih => simp only [List.cons_append,emit,ih,List.append_assoc,List.nil_append]

theorem twice_of_residence {n : Nat} (R : Word n → Fin n → Option (Fin n))
    (res : ∀ a e f skipped, R a e=some f → (∀ j∈skipped,j≠e) →
      chooseBy R ((a++[f])++emit (chooseBy R) (a++[f]) skipped) e=e) :
    OpenFenceLine.Twice (fun a => chooseBy R (emit (chooseBy R) [] a)) := by
  intro a e mid
  let c := chooseBy R
  let b := emit c [] a
  cases firstMark : R b e with
  | none =>
    refine ⟨[],e,mid++[e],rfl,?_⟩
    simp only [List.append_nil]
    exact (show (R b e).getD e=e by rw [firstMark]; rfl)
  | some f =>
    obtain ⟨u,v,eq,avoid⟩ := first e (mid++[e]) (by simp)
    refine ⟨e::u,e,v,congrArg (List.cons e) eq,?_⟩
    have head : c b e=f := by change (R b e).getD e=f; rw [firstMark]; rfl
    have tape : emit c [] (a++e::u)=(b++[f])++emit c (b++[f]) u := by
      rw [join]
      change b ++ (c b e :: emit c (b++[c b e]) u)=_
      simp only [head,List.append_assoc,List.singleton_append]
    change chooseBy R (emit c [] (a++e::u)) e=e
    rw [tape]
    exact res b e f u firstMark avoid

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (P : Production g)
    (o : Owners (oldH6 (rows s) g.base))
local notation "hp" => (show 0<2 by decide)

include P in
/-- On the actual five-client production mask, two occurrences of any
candidate supply that physical bond somewhere on the intervening tape. -/
theorem candidates_supply_bonds (phase : Fin 5 → Word n → Prop) :
    let R := ProductionClients.redirect g o (live (g:=g) o phase)
    OpenFenceLine.Twice (fun a => chooseBy R (emit (chooseBy R) [] a)) := by
  let l := live (g:=g) o phase
  let gate := ProductionClients.gate g o
  let issue := ProductionClients.issue g o
  let fresh (a : Word n) (i : Fin n) := ∃ j, i=gate j ∧ l j a ∧
    AdmissionMask.credit (issue j) (AdmissionMask.hitAt (gate j) (l j)) a=true
  let R := ProductionClients.redirect g o l
  have mask : FreshOnly _ g.hh fresh R := redirectTo_isFresh _ _ _ _
  have old (a : Word n) (i : Fin n) (F : fresh a i) :
      firstAdmission hp (base:=g.base) (hh:=g.hh) (rawRun x a) i := by
    obtain ⟨j,rfl,age,_⟩ := F
    exact age.2.2
  apply twice_of_residence R
  intro a e f skipped firstMark avoid
  exact submask_redirect_two_hits hp x mask old (Ready g) (fun y q j => g.fiber y q.1 j)
    (fun _ q e => ready_next P q e) (fun _ q => q.2) (separation P) a skipped e f
    (ready_run P a) firstMark avoid

end
end L4.Height.CandidateResidence
