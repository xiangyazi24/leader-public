import Leader.L4.BStarResetChartTouch
import Leader.L4.BStarResetQuietAdapter
import Leader.L4.BStarResetWaitRing
import Leader.L4.BStarResetSchedule

/-! Assemble the real old-mark service interface on a fixed literal
chart. The live source is stopped just before consumption of its D. -/
namespace L4.BStarResetChartService
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongTransport BStarLongCommand BStarLongDoor BStarLongEvents
open BStarH6WordChart BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarAcquireVisitOrder BStarAcquireAnchors BStarLongFixedRouting
open BStarResetRailRing BStarSeparatingRail BStarSeparatingProgress BStarResetMarkAdapter
open BStarResetQuietAdapter BStarResetQuietTable BStarResetQuiet BStarResetIdleRing
open BStarResetChartTouch

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem frames {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i) (e : Fin n)
    (op : Nat) (ho : op<3) (z : Cursor) (live : z≠.back 0)
    (G : Good (resetTag op) len (project (fun j => S.getD j fallback) x) z)
    (waitV : LongDoorGuard.valid manifest (x (S.getD 0 fallback).1).long=true)
    (waitP : (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=2) :
    MarkFrames hp x e (fun j => S.getD j fallback) len := by
  let addr := fun j => S.getD j fallback
  refine ⟨?_,?_⟩
  · intro j hj a hit
    refine ⟨not_discarded hp C same e j hj a hit,?_⟩
    have Rt (h : a=R 0) (hhx : oldH6 B x (rightNeighbor e)=true) : j=0 := by
      subst a
      have hOld : oldH6 B base (rightNeighbor e)=true :=
        (congrArg Prod.fst (same (rightNeighbor e))).trans hhx
      have M : addr j∈S := by
        have L := C.length
        change S.getD j fallback∈S
        rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
        exact List.getElem_mem _
      have Own := (C.entries _ M).2
      change addr j=address e (R 0) at hit
      rw [hit] at Own
      have atRoot := (endpoint_spec _ hh o 0).2.2 (rightNeighbor e) hOld Own
      have eq : addr j=addr 0 := hit.trans (atRoot.trans C.root.symm)
      have L := C.length
      exact (List.getD_inj (by omega) (by omega) C.nodup).mp eq
    apply pair_door_safe hp x e addr a j len op ho z G live hit Rt
    · intro h hhx
      have eq := hit
      rw [Rt h hhx,h] at eq
      exact congrArg (fun i : Pos n => LongDoorGuard.valid manifest (x i.1).long) eq ▸ waitV
    · intro h hhx
      have eq := hit
      rw [Rt h hhx,h] at eq
      exact congrArg (fun i : Pos n => (ctrlPhase.read (x i.1).long).toNat) eq ▸ waitP
  · intro j hj a hit noSucc noPred noTerm
    apply middle_avoids_of_chart
    rintro ⟨K,act⟩ hk hSlot w hw _
    have P : K∈orderedCommands (oldPair B x e) := by
      rw [←actualOffers_claims _ ((x e).long,(x (rightNeighbor e)).long)]
      exact List.mem_map.mpr ⟨(K,act),hk,rfl⟩
    rcases touches hp C same e j hj K a P hSlot hit with D|T|L|⟨i,J,L⟩
    · skip
      have hG : BStarLongLiteral.gatedAt (oldPair B x e)
          ((x e).long,(x (rightNeighbor e)).long) K =
          .door (bound (oldPair B x e) (readK ((x e).long,(x (rightNeighbor e)).long)) K.source) := by
        unfold BStarLongLiteral.gatedAt BStarLongLiteral.classifyOld
        simp [D.2.1,classify,BStarLongCommandData.checkOffer,bound,BStarLongCommandData.oldTokens,readK]
      have H := BStarAcquireNonRouting.actual_door _ _ (K,act) hk _ hG
      dsimp only at H
      subst act
      unfold selected at hw
      dsimp only at hw
      split at hw <;> cases hw
    · exact noTerm T.1 T.2
    · exact noSucc L
    · exact noPred i J L

noncomputable def service {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i) (e : Fin n) (he : e≠rightNeighbor e)
    (op : Nat) (ho : op<3) (z : Cursor) (live : z≠.back 0)
    (G : Good (resetTag op) len (project (fun j => S.getD j fallback) x) z)
    (waitV : LongDoorGuard.valid manifest (x (S.getD 0 fallback).1).long=true)
    (waitP : (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=2) :
    Service (resetTag op) len
      (project (fun j => S.getD j fallback) x)
      (project (fun j => S.getD j fallback) (AllSizeS1Geometry.step B x e)) :=
  actualService hp x e he _ len op ho
    (quiet_of_frames hp x e he _ len op ho (frames hp C same e op ho z live G waitV waitP))

open BStarResetSchedule BStarAcquireWaitControl

/-- Fixed lower geometry plus old right source WAIT for this reset.
The invariant intentionally also holds at the pre-consumption cut. -/
def Waiting (base : XX) (root : Fin n) (op : Nat) (x : XX) : Prop :=
  (∀ i, Layout B base i=Layout B x i) ∧
  LongDoorGuard.valid manifest (x root).long=true ∧
  (ctrlPhase.read (x root).long).toNat=2 ∧ (ctrlOp.read (x root).long).toNat=op

theorem sane (op : Nat) (ho : op<3) : Sane (resetTag op) := by
  constructor
  · rintro ⟨p,h,k⟩
    cases k
  · rintro ⟨p,h,k⟩
    obtain ⟨d,E⟩ := (BStarResetTaggedRows.bind_finish
      ⟨⟨false,false,false,false,false,false⟩,false,false,0,false⟩ 0 p (reset_of_holds op ho p h)).2
    rw [E] at k
    cases k
  · intro t D F
    obtain ⟨p,h,Z⟩ := D
    obtain ⟨q,_,Q⟩ := F
    obtain ⟨d,E⟩ := (BStarResetTaggedRows.bind_finish
      ⟨⟨false,false,false,false,false,false⟩,false,false,0,false⟩ 0 p (reset_of_holds op ho p h)).2
    rw [E,Q] at Z
    cases Z

theorem root_header {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i) :
    oldH6 B x (S.getD 0 fallback).1=true ∧ (S.getD 0 fallback).2=0 := by
  have K : (endpoint (oldH6 B base) hh o 0).2=0 := rfl
  refine ⟨?_,C.root ▸ K⟩
  have O := (endpoint_spec (oldH6 B base) hh o 0).1
  have baseH : oldH6 B base (S.getD 0 fallback).1=true := by
    rw [C.root]
    exact O
  exact (congrArg Prod.fst (same _)).symm.trans baseH

theorem waiting_closed_at {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (e : Fin n) (op : Nat) (ho : op<3)
    (nextLayout : ∀ i, Layout B base i=Layout B (AllSizeS1Geometry.step B x e) i)
    (z : Cursor) (live : z≠.back 0)
    (G : Good (resetTag op) len (project (fun j => S.getD j fallback) x) z)
    (W : Waiting hp base (S.getD 0 fallback).1 op x) :
    Waiting hp base (S.getD 0 fallback).1 op (AllSizeS1Geometry.step B x e) := by
  let i := (S.getD 0 fallback).1
  obtain ⟨H,K⟩ := root_header hp C W.1
  have roots := root_before_reply G live
  have L : atSite (x i).long 0=.trail ∨
      ∃ v, atSite (x i).long 0=.forward v ∧ BStarResetTaggedRows.ResetF v := by
    have R : project (fun j => S.getD j fallback) x 0=atSite (x i).long 0 := by
      change atSite (x i).long (S.getD 0 fallback).2=_
      rw [K]
    rw [R] at roots
    rcases roots with T|⟨pay,p,e⟩
    · exact .inl T
    · exact .inr ⟨pay,e,reset_of_holds op ho pay p⟩
  have P := BStarResetWaitRing.step_control k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x e i H W.2.1 W.2.2.1 L
  refine ⟨nextLayout,?_,?_,?_⟩
  · exact (BStarResetWaitRing.valid_of_control_eq _ _ P).trans W.2.1
  · exact (congrArg (fun q : BitVec 2 × BitVec 9 => q.1.toNat) P).trans W.2.2.1
  · exact (congrArg (fun q : BitVec 2 × BitVec 9 => q.2.toNat) P).trans W.2.2.2

theorem waiting_closed {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (geo : ∀ x : XX, (∀ i, Layout B base i=Layout B x i) →
       ∀ e i, Layout B base i=Layout B (AllSizeS1Geometry.step B x e) i)
    (e : Fin n) (op : Nat) (ho : op<3)
    (z : Cursor) (live : z≠.back 0)
    (G : Good (resetTag op) len (project (fun j => S.getD j fallback) x) z)
    (W : Waiting hp base (S.getD 0 fallback).1 op x) :
    Waiting hp base (S.getD 0 fallback).1 op (AllSizeS1Geometry.step B x e) :=
  waiting_closed_at hp C e op ho (geo x W.1 e) z live G W

/-- After a genuine issue, every live mark satisfies Service on the
same fixed owner chart. The two remaining geometric inputs explicitly
state layout closure and nominate a real mark for each index. -/
theorem adapter {base : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (geo : ∀ x : XX, (∀ i, Layout B base i=Layout B x i) →
       ∀ e i, Layout B base i=Layout B (AllSizeS1Geometry.step B x e) i)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (ho : op<3) (edgeOf : Label → Fin n)
    (linkN : ∀ x : XX, (∀ i, Layout B base i=Layout B x i) → ∀ j<len,
      onLink hp x (edgeOf (.link j)) (fun j => S.getD j fallback) j)
    (termN : ∀ x : XX, (∀ i, Layout B base i=Layout B x i) →
      onTerminal hp x (edgeOf .terminal) (fun j => S.getD j fallback) len) :
    Adapter (AllSizeS1Geometry.step B) (project (fun j => S.getD j fallback))
      (resetTag op) len (Waiting hp base (S.getD 0 fallback).1 op) edgeOf := by
  refine ⟨sane op ho,fun x e z W L G => waiting_closed hp C geo e op ho z L G W,?_⟩
  intro x e z W L G
  refine ⟨service hp C W.1 e (distinct _) op ho z L G W.2.1 W.2.2.1,?_⟩
  intro H
  subst e
  change nomination len z ∈ labels hp x (edgeOf (nomination len z)) _ len
  cases z with
  | out j =>
    by_cases T : j=len
    · have P := (mem_terminal hp x (edgeOf .terminal) _ len).mpr (termN x W.1)
      simpa [nomination,T] using P
    · have J : j≤len := G.1
      have J' : j<len := by omega
      have P := (mem_link hp x (edgeOf (.link j)) _ len j).mpr ⟨J',linkN x W.1 j J'⟩
      simpa [nomination,T] using P
  | back j =>
    cases j with
    | zero => exact (L rfl).elim
    | succ j =>
      have J : j+1≤len := G.1
      have J' : j<len := by omega
      exact (mem_link hp x (edgeOf (.link j)) _ len j).mpr ⟨J',linkN x W.1 j J'⟩

theorem adapter_on {base : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (Q : XX → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (ho : op<3) (edgeOf : Label → Fin n)
    (linkN : ∀ x : XX, (∀ i, Layout B base i=Layout B x i) → ∀ j<len,
      onLink hp x (edgeOf (.link j)) (fun j => S.getD j fallback) j)
    (termN : ∀ x : XX, (∀ i, Layout B base i=Layout B x i) →
      onTerminal hp x (edgeOf .terminal) (fun j => S.getD j fallback) len) :
    Adapter (AllSizeS1Geometry.step B) (project (fun j => S.getD j fallback))
      (resetTag op) len (fun x => Q x ∧ Waiting hp base (S.getD 0 fallback).1 op x) edgeOf := by
  refine ⟨sane op ho,?_,?_⟩
  · intro x e z ⟨Qx,W⟩ L G
    have yQ := closed x Qx e
    exact ⟨yQ,waiting_closed_at hp C e op ho (fiber _ yQ) z L G W⟩
  intro x e z ⟨_,W⟩ L G
  refine ⟨service hp C W.1 e (distinct _) op ho z L G W.2.1 W.2.2.1,?_⟩
  intro H
  subst e
  change nomination len z ∈ labels hp x (edgeOf (nomination len z)) _ len
  cases z with
  | out j =>
    by_cases T : j=len
    · have P := (mem_terminal hp x (edgeOf .terminal) _ len).mpr (termN x W.1)
      simpa [nomination,T] using P
    · have J : j≤len := G.1
      have J' : j<len := by omega
      have P := (mem_link hp x (edgeOf (.link j)) _ len j).mpr ⟨J',linkN x W.1 j J'⟩
      simpa [nomination,T] using P
  | back j =>
    cases j with
    | zero => exact (L rfl).elim
    | succ j =>
      have J : j+1≤len := G.1
      have J' : j<len := by omega
      exact (mem_link hp x (edgeOf (.link j)) _ len j).mpr ⟨J',linkN x W.1 j J'⟩

end L4.BStarResetChartService
