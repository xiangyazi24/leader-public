import Leader.L4.Height.AdmissionPolicyCore
import Leader.L4.BStarGatePolicySplice

namespace L4.Height.AdmissionActualFirst
open PhysicalCustody AdmissionPolicyCore BStarSteeredLikelihood
open BStarH6WordChart BStarAcquireAnchors BStarAcquireVisitOrder BStarLongClaims
open BStarParkedSteering BStarClearanceRaceMark BStarAdmitIncidentGeometry BStarH6Ordinal
open AllSizeProtocol BStarOwnerLaunchOrigin BStarResetChartTouch
open BStarAcquireLiteralChain BStarFenceReceiverChart BStarGeneratedOwner BStarLongCommand BStarLongToken BStarLongWork BStarTrace
variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 (rows s) g.base

theorem actual_hit (o : Owners h) (large : 6≤s)
    (phase : Fin 5→Word n→Prop) (j : Fin 5) (b : Word n)
    (candidate : Fin n) (seen : Side)
    (E : chooseBy (redirect g o (live g o phase)) b candidate=incident (gate g o j) seen)
    (L : live g o phase j b)
    (A : AdmissionMask.credit (issue g o j) (AdmissionMask.hitAt (gate g o j)
      (live g o phase j)) b=true) :
    ∃ side, candidate=incident (gate g o j) side ∧
      incident (gate g o j) seen=
        incident (gate g o j) (if (client h g.hh o j).val=o.val then .left else .right) := by
  obtain ⟨ord,_⟩ := gate_address g large o j
  have S := support_of_fresh (redirectTo_isFresh h g.hh
    (fun a i => ∃ j, i=gate g o j ∧ live g o phase j a ∧
      AdmissionMask.credit (issue g o j) (AdmissionMask.hitAt (gate g o j) (live g o phase j)) a=true)
    (fun _ i => if commandOwner h i 1=o.val then .left else .right))
  obtain ⟨side,H⟩ := BStarGatePolicySplice.incident_preimage (S b) (gate g o j) ord candidate seen E
  refine ⟨side,H,?_⟩
  rw [H] at E
  exact E.symm.trans (selected_live g o large phase j b side L A)

local notation "hp" => (show 0<2 by decide)

/-- Literal old FIRST, generated since the query cut, supplies all eligibility
except the phase/release-cut condition and absence of target publication. -/
theorem live_of_first (o : Owners h) (phase : Fin 5→Word n→Prop) (j : Fin 5)
    (b : Word n) (S : List (Pos n)) (len : Nat) (fall : Pos n) (k : Nat)
    (m : Mode)
    (chart : Chart hp g.base g.hh (client h g.hh o j) S len fall)
    (source : (S.getD 0 fall).1=(endpoint h g.hh (client h g.hh o j) 0).1)
    (gateAt : S.getD k fall=(gate g o j,1))
    (G : GeneratedOwner hp g.base (fun z=>S.getD z fall) len x m b (.busy admit (.out k)))
    (noInherited : ∀ z, m≠.busy admit z)
    (C : Current hp g.base (fun z=>S.getD z fall) len (rawRun x b) (.busy admit (.out k)))
    (v : Payload)
    (R : bind (longGeometry (rows s) (rawRun x b (gate g o j))) 1
      (atSite (rawRun x b (gate g o j)).long 1)=.forward v)
    (op : v.opcode.toNat=gateOpcode false) (healthy : v.fault=0) (first : v.race=1)
    (phaseAt : phase j b)
    (noPublish : ¬RawServiceCore.publishes x (endpoint h g.hh o 1).1 b) :
    live g o phase j b := by
  refine ⟨⟨phaseAt,noPublish⟩,?_,⟨_,S,len,fall,k,v,chart,gateAt,C,R,op,healthy,first⟩⟩
  rcases admission_age G with ⟨age,_⟩ | ⟨_,z,hm,_⟩
  · rw [source] at age
    exact age
  · exact (noInherited z hm).elim

end L4.Height.AdmissionActualFirst
