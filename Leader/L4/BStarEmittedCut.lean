import Leader.L4.BStarSteeredLikelihood
import Leader.L4.BStarGatePolicySplice

/-! Convert a located physical mark into its actual raw candidate.
Candidate rewrites change labels, not positions or prefix lengths. -/
namespace L4.BStarEmittedCut
open BStarSteeredLikelihood

theorem marked_cut {n : Nat} (choose : Word n→Fin n→Fin n)
    (a w pre post : Word n) (e : Fin n)
    (E : emit choose a w=pre++e::post) :
    ∃ lead c tail, w=lead++c::tail ∧ emit choose a lead=pre ∧
      choose (a++pre) c=e ∧ emit choose (a++pre++[e]) tail=post := by
  induction pre generalizing a w with
  | nil =>
    cases w with
    | nil => cases E
    | cons c tail =>
      obtain ⟨one,rest⟩ := List.cons.inj E
      exact ⟨[],c,tail,rfl,rfl,by simpa using one,by simpa only [List.append_nil,one] using rest⟩
  | cons b pre ih =>
    cases w with
    | nil => cases E
    | cons c w =>
      obtain ⟨one,rest⟩ := List.cons.inj E
      change choose a c=b at one
      rw [one] at rest
      obtain ⟨lead,d,tail,W,F,G,H⟩ := ih (a++[b]) w rest
      refine ⟨c::lead,d,tail,congrArg (List.cons c) W,?_,?_,?_⟩
      · rw [emit,one,F]
      · simpa only [List.append_assoc,List.singleton_append] using G
      · simpa only [List.append_assoc,List.singleton_append] using H

open BStarClearanceRaceMark BStarLongClaims BStarH6Ordinal BStarAdmitIncidentGeometry
open BStarParkedSteering BStarSteeringSupport

/-- An observed FIRST label on the physical word identifies the actual
candidate cut and the prescribed side at precisely that old prefix.
Freshness is supplied by the owner-specific launch/phase predicate. -/
theorem first_side {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (fresh : Word n→Fin n→Prop) (pick : Word n→Fin n→Side)
    (a w pre post : Word n) (i : Fin n) (ord : ordinal h hh i=gateOrdinal false)
    (side : Side) (F : fresh (a++pre) i)
    (E : emit (chooseBy (redirectTo h hh fresh pick)) a w=pre++incident i side::post) :
    side=pick (a++pre) i := by
  let r := redirectTo h hh fresh pick
  obtain ⟨_,c,_,_,_,C,_⟩ := marked_cut (chooseBy r) a w pre post (incident i side) E
  have S := support_of_fresh (redirectTo_isFresh h hh fresh pick)
  obtain ⟨t,T⟩ := BStarGatePolicySplice.incident_preimage (S (a++pre)) i ord c side C
  rw [T,redirectTo_fresh_hit h hh fresh pick (a++pre) i ord F t] at C
  exact (incident_gate_injective h hh i i false false ord ord _ _ C).2.2.symm

#print axioms marked_cut
#print axioms first_side
end L4.BStarEmittedCut
