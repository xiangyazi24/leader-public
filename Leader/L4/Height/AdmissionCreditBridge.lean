import Leader.L4.Height.AdmissionMask
import Leader.L4.Height.GateResidence
import Leader.L4.BStarAdmissionCreditPhysical

namespace L4.Height.AdmissionCreditBridge
open AllSizeProtocol BStarTrace BStarSteeredLikelihood BStarLongClaims
open BStarLongWork BStarLongToken BStarLongCommand BStarAcquireLiteralChain
open BStarAcquireVisitOrder BStarClearanceRaceMark BStarAdmissionCreditFlight
open BStarH6WordChart BStarAcquireForwardTrace BStarCommitNoPrior BStarGeneratedOwner
open BStarOwnerControlHistory BStarOwnerLaunchOrigin

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- A live admission predicate may add age, window and publication guards;
only its exact generated gate test is needed for the physical flight. -/
theorem armed {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {addr : Nat→Pos n} {len k j : Nat}
    (a u quiet : Word n) (launch arrival : Fin n) (gate : Fin n)
    (K1 : addr k=(gate,1))
    (I : genuineIssue hp x (addr 0).1 a launch)
    (P : BusyOnly hp base addr len admit (step (run x a) launch) (.out 0) u (.out j))
    (J : j<k) (K : k≤len)
    (live : Word n→Prop)
    (sound : ∀ b, live b → firstAdmission hp (hh:=hh) (run x b) gate)
    (offsite : ∀ e∈quiet,∀ s,e≠incident gate s) :
    AdmissionMask.credit (genuineIssue hp x (addr 0).1) (AdmissionMask.hitAt gate live)
      ((a++[launch])++(u++arrival::quiet))=true := by
  classical
  apply BStarAdmissionCreditPhysical.bound_credit hp a u quiet launch arrival gate K1 I P J K live
    _ _ _ _ offsite
  · intro b L
    obtain ⟨_,_,_,_,_,v,_,_,_,H,_⟩ := sound b L
    exact ⟨v,H⟩
  · intro H
    simp [AdmissionMask.credit_snoc,AdmissionMask.advanceCredit,H]
  · intro b e C H
    change ¬AdmissionMask.hitAt gate live b e at H
    rw [AdmissionMask.credit_snoc]
    by_cases T : genuineIssue hp x (addr 0).1 b e <;>
      simp [AdmissionMask.advanceCredit,T,H,C]

/-- On the actual old emitted prefix, the mask steers either
candidate incidence to its prescribed side once the genuine credit is armed. -/
theorem selected {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (gates : Fin 5→Fin n) (issue : Fin 5→Word n→Fin n→Prop)
    (live : Fin 5→Word n→Prop) (pick : Word n→Fin n→Side)
    (b : Word n) (j : Fin 5) (s : Side)
    (ord : BStarH6Ordinal.ordinal h hh (gates j)=BStarAdmitIncidentGeometry.gateOrdinal false)
    (L : live j b)
    (A : AdmissionMask.credit (issue j) (AdmissionMask.hitAt (gates j) (live j)) b=true) :
    chooseBy (AdmissionMask.mask h hh gates issue live pick) b (incident (gates j) s)=
      incident (gates j) (pick b (gates j)) := by
  exact BStarParkedSteering.redirectTo_fresh_hit h hh _ pick b (gates j) ord ⟨j,rfl,L,A⟩ s

end L4.Height.AdmissionCreditBridge
