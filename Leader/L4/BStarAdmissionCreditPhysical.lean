import Leader.L4.BStarAdmissionCreditFlight

namespace L4.BStarAdmissionCreditPhysical
open AllSizeProtocol BStarTrace BStarLongWork BStarLongCommand BStarLongToken
open BStarAcquireVisitOrder BStarH6WordChart BStarResetMarkAdapter BStarOwnerLaunchOrigin
open BStarSeparatingRail BStarAcquireForwardTrace BStarSteeredLikelihood
open BStarAdmitIncidentGeometry BStarClearanceRaceMark BStarLongClaims BStarH6Ordinal
open BStarAdmissionCreditFlight BStarParkedSteering

theorem raw_of_bound_forward (g : LongGeometry) (j : Fin 11) (t : Token) (v : Payload)
    (H : bind g j t=.forward v) : ∃ q,t=.forward q := by
  cases t with
  | empty => contradiction
  | trail => contradiction
  | forward q => exact ⟨q,rfl⟩
  | reply q =>
    simp only [BStarLongCommand.bind] at H
    split at H
    · contradiction
    · split at H <;> contradiction

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- For the actual fresh predicate a live gate implies a raw forward
at its fixed chart address; binding does not create one from another
token variant. Thus the prior flight cannot consume the credit. -/
theorem bound_credit {base x : X} {addr : Nat→Pos n} {len k j : Nat}
    (a u quiet : Word n) (launch arrival : Fin n) (gate : Fin n)
    (K1 : addr k=(gate,1))
    (I : genuineIssue hp x (addr 0).1 a launch)
    (P : BusyOnly hp base addr len admit (step (run x a) launch) (.out 0) u (.out j))
    (J : j<k) (K : k≤len)
    (live : Word n→Prop)
    (sound : ∀ b,live b → ∃ v,
      bind (longGeometry B (run x b gate)) 1 (atSite (run x b gate).long 1)=.forward v)
    (credit : Word n → Bool)
    (sets : genuineIssue hp x (addr 0).1 a launch → credit (a++[launch])=true)
    (preserve : ∀ b e, credit b=true → ¬physicalHit gate live b e →
      credit (b++[e])=true)
    (offsite : ∀ e∈quiet,∀ s,e≠incident gate s) :
    credit ((a++[launch])++(u++arrival::quiet))=true := by
  apply credit_through_arrival hp a u quiet launch arrival gate I P J K live _ credit sets preserve offsite
  intro b A
  obtain ⟨v,V⟩ := sound b A
  obtain ⟨q,R⟩ := raw_of_bound_forward _ _ _ _ V
  refine ⟨q,?_⟩
  change atCursor (run x b) (addr k)=_
  rw [K1]
  exact R

end L4.BStarAdmissionCreditPhysical
