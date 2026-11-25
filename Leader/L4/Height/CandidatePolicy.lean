import Leader.L4.Height.AdmissionAge
import Leader.L4.Height.ProductionGates
import Leader.L4.Height.GateResidence

namespace L4.Height.CandidateResidence
open PhysicalCustody ProductionCustody BStarAcquireLiteralChain BStarH6WordChart
open BStarSteeredLikelihood BStarParkedSteering BStarSteeringSupport
open Classical
noncomputable section

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (P : Production g)
    (o : Owners (oldH6 (rows s) g.base))
local notation "hp" => (show 0<2 by decide)

def live (phase : Fin 5 → Word n → Prop) (j : Fin 5) (a : Word n) : Prop :=
  (phase j a ∧ ¬RawServiceCore.publishes x (endpoint (oldH6 (rows s) g.base) g.hh o 1).1 a) ∧
    newAdmission x
    (endpoint (oldH6 (rows s) g.base) g.hh (ProductionClients.client _ g.hh o j) 0).1 a ∧
    firstAdmission hp (base:=g.base) (hh:=g.hh) (rawRun x a) (ProductionClients.gate g o j)

theorem identity_after_service (i : BStarAcquireAnchors.Header (oldH6 (rows s) g.base))
    (phase : Fin 5 → Word n → Prop) (a : Word n) (pub : RawServiceCore.publishes x i.val a)
    (e : Fin n) :
    let target := ProductionClients.serviceOwner g i
    let R := ProductionClients.redirect g target (live (g:=g) target phase)
    chooseBy R a e=e := by
  let target := ProductionClients.serviceOwner g i
  let l := live (g:=g) target phase
  let gate := ProductionClients.gate g target
  let issue := ProductionClients.issue g target
  let old (a : Word n) (v : Fin n) := ∃ j, v=gate j ∧ l j a ∧
    AdmissionMask.credit (issue j) (AdmissionMask.hitAt (gate j) (l j)) a=true
  let R := ProductionClients.redirect g target l
  have mask : FreshOnly _ g.hh old R := redirectTo_isFresh _ _ _ _
  change (R a e).getD e=e
  cases E : R a e with
  | none => rfl
  | some f =>
    obtain ⟨_,_,_,⟨j,_,ready,_⟩,_,_⟩ := mask a e f E
    exact False.elim (ready.1.2 (by simpa only [target,ProductionClients.service_header] using pub))

#print axioms identity_after_service
end
end L4.Height.CandidateResidence

