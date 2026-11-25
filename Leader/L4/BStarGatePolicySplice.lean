import Leader.L4.BStarGateStutter
import Leader.L4.BStarParkedSteering
import Leader.L4.BStarFenceTwoCandidates

namespace L4.BStarGatePolicySplice
open BStarSteeringSupport BStarSteeredLikelihood BStarAdmitIncidentGeometry
open BStarClearanceRaceMark BStarLongClaims BStarH6Ordinal BStarParkedSteering

/-- No outsider candidate is mapped into the two incident gate labels,
even when other owners have a simultaneous fresh prescription. -/
theorem incident_preimage {n : Nat} {h : Fin n→Bool} {hh : ∃ i,h i=true}
    {redirect : Fin n→Option (Fin n)} (P : Supported h hh redirect)
    (i : Fin n) (I : ordinal h hh i=gateOrdinal false) (e : Fin n) (s : Side)
    (H : (redirect e).getD e=incident i s) :
    ∃ t,e=incident i t := by
  cases E : redirect e with
  | none => exact ⟨s,by simpa only [E,Option.getD_none] using H⟩
  | some f =>
    obtain ⟨j,t,J,L,R⟩ := P e f E
    have T : f=incident i s := by simpa only [E,Option.getD_some] using H
    obtain ⟨K,_,_⟩ := incident_gate_injective h hh i j false false I J _ _ (T.symm.trans R)
    exact ⟨t,by simpa only [←K] using L⟩

theorem no_incident_prefix {n : Nat} {h : Fin n→Bool} {hh : ∃ i,h i=true}
    {redirect : Word n→Fin n→Option (Fin n)}
    (P : ∀ a,Supported h hh (redirect a)) (i : Fin n) (I : ordinal h hh i=gateOrdinal false)
    (a u : Word n) (N : ∀ e∈u,∀ s,e≠incident i s) :
    ∀ e∈emit (chooseBy redirect) a u,∀ s,e≠incident i s := by
  induction u generalizing a with
  | nil => intro e H; cases H
  | cons e u ih =>
    intro f H s
    simp only [emit,List.mem_cons] at H
    rcases H with H|H
    · subst f
      intro K
      obtain ⟨t,T⟩ := incident_preimage (P a) i I e s K
      exact N e List.mem_cons_self t T
    · exact ih _ (fun g H=>N g (List.mem_cons_of_mem _ H)) _ H s

/-- If the actual old emitted prefix has the tracked ADMIT enabled and
fresh, the first candidate incident label produces the prescribed
first emitted incident label on this very tape. No earlier outsider
hit can have supplied an incidence, irrespective of its policy. -/
theorem first_emitted {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (fresh : Word n→Fin n→Prop) (pick : Word n→Fin n→Side)
    (a u tail : Word n) (i : Fin n) (I : ordinal h hh i=gateOrdinal false) (s : Side)
    (N : ∀ e∈u,∀ t,e≠incident i t)
    (F : fresh (a++emit (chooseBy (redirectTo h hh fresh pick)) a u) i) :
    let choose := chooseBy (redirectTo h hh fresh pick)
    let emitted := emit choose a u
    let old := a++emitted
    let k := incident i (pick old i)
    (∀ e∈emitted,∀ t,e≠incident i t) ∧
      emit choose a (u++incident i s::tail) =
        emitted++k::emit choose (old++[k]) tail ∧
      prescribed (redirectTo h hh fresh pick) old k=1 := by
  dsimp only
  let r := redirectTo h hh fresh pick
  let c := chooseBy r
  have mask : FreshOnly h hh fresh r := redirectTo_isFresh h hh fresh pick
  have hit := redirectTo_fresh_hit h hh fresh pick (a++emit c a u) i I F s
  refine ⟨no_incident_prefix (support_of_fresh mask) i I a u N,?_,?_⟩
  · rw [BStarFenceTwoCandidates.emit_append,emit,hit]
  · have K := redirectTo_charges_fresh h hh fresh pick (a++emit c a u) i I F s
    rwa [hit] at K

open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongCommand BStarLongLayout
open BStarAcquireVisitOrder BStarResetChartTouch BStarAcquireLiteralChain BStarH6WordChart
open BStarGeneratedOwner BStarBitParity BStarGateStutter BStarClearanceOffset

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- The prescribed first incident has the literal FIRST observer
effect. The generated cursor is still parked at the same K1. -/
theorem prescribed_physical_first {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (q : Q x) (atGate : S.getD k fall=(i,1))
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy admit (.out k)))
    (v : Payload)
    (read : bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v)
    (op : v.opcode.toNat=admit) (fault : v.fault=0) (race : v.race=1)
    (ready : correct (oldH6 B base) hh 5 x)
    (readyAll : ∀ e,correct (oldH6 B base) hh 5 (step x e))
    (I : ordinal (oldH6 B base) hh i=gateOrdinal false)
    (fresh : Word n→Fin n→Prop) (pick : Word n→Fin n→Side) (a : Word n)
    (F : fresh a i) (s : Side) :
    let e := chooseBy (redirectTo (oldH6 B base) hh fresh pick) a (incident i s)
    e=incident i (pick a i) ∧
    (kField 1).read (step x e i).long=encode (.forward {v with race:=firstCode (pick a i)}) ∧
    Event hp (fun j=>S.getD j fall) len x e (.busy admit (.out k)) (.busy admit (.out k)) ∧
    Current hp base (fun j=>S.getD j fall) len (step x e) (.busy admit (.out k)) := by
  dsimp only
  let side := pick a i
  have hit := redirectTo_fresh_hit (oldH6 B base) hh fresh pick a i I F s
  refine ⟨hit,?_⟩
  rw [hit]
  have fixed : ∀ j,oldH6 B x j=oldH6 B base j :=
    fun j=>(congrArg Prod.fst (fiber x q j)).symm
  have G : gate admit 1 (longGeometry B (x i))=true :=
    (selected_gate_iff hp hh fixed ready i 1 false).mpr ⟨rfl,I⟩
  have E : BStarAcquireDoorHistory.siteOf (incident i side) side=i := by
    cases side <;> first | rfl | exact RearTrace.right_predecessor _
  obtain ⟨R,Z,K,_⟩ := observed_race_step hp C Q fiber closed distinct i (incident i side) false k q
    atGate cur v read op fault ready (readyAll _) G side E (firstCode side) (.inl ⟨race,rfl⟩)
  exact ⟨R,Z,K⟩

#print axioms first_emitted
#print axioms prescribed_physical_first
end L4.BStarGatePolicySplice
