import Leader.L4.BStarBitFirstRing
import Leader.L4.BStarClearanceObserveJoined
import Leader.L4.BStarLongKOne
import Leader.L4.BStarResetQuietTable

namespace L4.BStarBitFollowRing
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongRouting BStarLongWork BStarLongEvents
open BStarClearanceObserveJoined BStarResetQuiet BStarResetQuietTable BStarLongLiteral BStarLongKOne
open BStarBitParity
set_option maxRecDepth 4096

private theorem norm_frame (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (p : Payload) (B : bound g (readK raw) ⟨s,1⟩=.forward p)
    (F : p.fault=0) : avoids ⟨s,1⟩ (normalization g (readK raw)) := by
  intro w hw E
  rcases List.mem_append.mp hw with hw|hw
  · obtain ⟨a,_,h⟩ := List.mem_filterMap.mp hw
    dsimp only at h
    split at h
    · rename_i guard
      have eq : a=(⟨s,1⟩ : AtK) := (congrArg Prod.fst (Option.some.inj h)).trans E
      subst a
      simp [B,isFault,F] at guard
    · contradiction
  · obtain ⟨a,ha,h⟩ := List.mem_map.mp hw
    have eq : a=(⟨s,1⟩ : AtK) := (congrArg Prod.fst h).trans E
    subst a
    cases s <;> cases X : g.1.inside <;> cases Y : g.2.inside <;>
      simp [discarded,X,Y,L,R] at ha

private theorem actual_hold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (hc : c∈orderedCommands g)
    (hv : classify c (geometry g c.source.side) (bound g (readK x) c.source)
        ((c.destination.map (bound g (readK x))).getD .empty)=.hold) :
    (c,.hold)∈actualOffers g x := by
  have C : (c,.hold)∈offersOn g (readK x) := List.mem_map.mpr
    ⟨c,hc,congrArg (Prod.mk c) hv⟩
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round BStarLongCommandData.gated
  simp only [List.mem_map]
  refine ⟨(c,.hold),⟨(c,.hold),⟨(c,.hold),C,rfl⟩,rfl⟩,?_⟩
  unfold BStarLongGrant.update
  dsimp only
  split <;> rfl

/-- Exact old-pair protection for either nominated first observation.
The incoming side needs a nonheader receiving BIT and a preceding
bound T; the outgoing side does not inspect destination contents. -/
theorem pending_avoids (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (p : Payload)
    (B : bound g (readK raw) ⟨s,1⟩=.forward p)
    (F : p.fault=0) (P : p.opcode.toNat=bitOp) (K : p.race.toNat < 4)
    (G : gate bitOp 1 (geometry g s)=true)
    (incoming : s=.right → g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail) :
    avoids ⟨s,1⟩ (normalization g (readK raw) ++ middle g raw) := by
  have mid : avoids ⟨s,1⟩ (middle g raw) := by
    cases s with
    | left =>
      let c := centerLink g
      have src : c.source=L 1 := rfl
      have shape : c.kind=.link := rfl
      have h : (c,.hold)∈actualOffers g raw := by
        apply actual_hold g raw c (center_mem g)
        change bound g (readK raw) (L 1)=.forward p at B
        rw [src,B]
        change classify c (geometry g .left) (.forward p) _=.hold
        simp [classify,shape,depart,F,P,K,show c.source.occurrence=(1:Fin 11) from rfl,G]
      exact hold_avoids g raw c h _ (by simp only [Claim.slots,src,List.mem_cons]; exact .inl rfl)
    | right =>
      change bound g (readK raw) (R 1)=.forward p at B
      obtain ⟨body,trail⟩ := incoming rfl
      have hc : advance∈orderedCommands g := by
        apply (one_mem g advance (by decide)).mpr
        simp [body]
      exact (link_avoids g raw advance (R 1) hc rfl rfl
        (show LinkHold (bound g (readK raw) (L 1)) (bound g (readK raw) (R 1)) by
          rw [trail,B]; exact .tf p)).2
  intro w hw E
  exact (List.mem_append.mp hw).elim
    (fun N => norm_frame g raw s p B F w N E) (fun M => mid w M E)


private theorem fold_hold (a : AtK) (ws : List KWrite) (raw : BitVec 52)
    (H : avoids a ws) : ws.foldl (fun k w => putRaw k a w) raw=raw := by
  induction ws generalizing raw with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons,ih _ (fun q hm => H q (List.mem_cons_of_mem _ hm))]
    simp [putRaw,Ne.symm (H w List.mem_cons_self)]

private theorem silent_avoids (g : Pair LongGeometry) (old : ReadK) (pre : List KWrite)
    (a : AtK) (p : Payload) (B : bound g old a=.forward p)
    (S : observe a (geometry g a.side) p=none) :
    avoids a (observations g old pre) := by
  intro w hw E
  obtain ⟨j,_,J⟩ := List.mem_filterMap.mp hw
  split at J
  · contradiction
  · split at J <;> try contradiction
    rename_i P _
    cases Z : observe j (geometry g j.side) P with
    | none => simp [Z] at J
    | some Q =>
      have H := (congrArg Prod.fst (Option.some.inj (by simpa [Z] using J))).trans E
      change j=a at H
      subst j
      simp_all

theorem joined_follow (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s first : Side)
    (v : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let a : AtK := ⟨s,1⟩
    bound g (readK raw) a=.forward v →
    v.fault=0 → v.opcode.toNat=bitOp → v.race=firstCode first →
    gate bitOp 1 (geometry g s)=true →
    (s=.right → g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail) →
    readRaw (Pair.map LargeSite.long (largePair b x)) a=
      if s=first then readRaw raw a else encode (.forward {v with race:=finalCode first}) := by
  dsimp only
  intro B F P K G incoming
  have small : v.race.toNat<4 := by rw [K]; cases first <;> decide
  have H := pending_avoids _ _ s v B F P small G incoming
  have O := observe_follow _ v first s G F P K
  by_cases E : s=first
  · rw [if_pos E] at O ⊢
    rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x ⟨s,1⟩
      (fun ea _ => (by have T := congrArg (fun z : AtK => z.occurrence.val) ea; change (1 : Nat) = 0 at T; omega)),
      raw_transit _ _ _ (by change (1:Nat)≠0; decide),routing_parts,List.foldl_append,
      fold_hold _ _ _ H]
    exact fold_hold _ _ _ (silent_avoids _ _ _ _ v B O)
  · rw [if_neg E] at O ⊢
    exact (observed_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x ⟨s,1⟩ (by change (1:Nat)≠0; decide)
      v _ 0 H B O).1

open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarResetChartTouch BStarResetChartIndex BStarAcquireLiteralChain
open BStarAcquireAnchors BStarLongFiberOwner BStarLongKOne BStarClearanceRaceMark
open BStarResetMarkAdapter BStarGeneratedOwner BStarSeparatingRail BStarAcquireForwardTrace
open BStarClearanceOffset BStarBitGateGeometry BStarBitParity BStarBitFirstRing
open BStarBankTrace (sideFlag)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- On the actual generated cursor, the first label repeating leaves its old token unchanged,
and the opposite label records the completed code, and every nonincident raw label
frames the exact old wire. No extra per-mark mask premise. -/
theorem follow_mark {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (ready : correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (idx : S.getD k fall=(i,1))
    (O : oldOrdinal B base hh i=4)
    (now : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k)))
    (v : Payload) (old : bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v)
    (F : v.fault=0) (op : v.opcode.toNat=bitOp) (first : Side) (R1 : v.race=firstCode first) :
    (∀ s, atSite (step x (incident i s) i).long 1=
      if s=first then atSite (x i).long 1 else .forward {v with race:=finalCode first}) ∧
    (∀ e, e≠incident i .left → e≠incident i .right →
      (step x e i).long=(x i).long) := by
  constructor
  · intro s
    let e := incident i s
    let pair := (x e,x (rightNeighbor e))
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long pair
    have I : site e s=i := incident_site i s
    have geo : geometry g s=longGeometry B (x i) := by
      rw [←I]
      cases s <;> rfl
    have read : readK raw (⟨s,1⟩ : AtK)=atSite (x i).long 1 := by
      rw [←I]
      cases s <;> rfl
    have starts : bound g (readK raw) ⟨s,1⟩=.forward v := by
      change bind (geometry g s) 1 (readK raw ⟨s,1⟩)=.forward v
      rwa [geo,read]
    have gateOn : gate bitOp 1 (geometry g s)=true := by
      rw [geo]
      exact (bit_gate_iff hp hh fixed ready i 1).mpr ⟨rfl,O⟩
    have right : s=.right → g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail := by
      intro E
      subst s
      have bd : oldH6 B base i=false := Bool.eq_false_iff.mpr (fun H => by
        have Z := (ordinal_zero _ hh i).mpr H
        change ordinal _ hh i=4 at O
        omega)
      constructor
      · change oldH6 B x (rightNeighbor e)=false
        rw [show rightNeighbor e=i from RearTrace.right_predecessor i,fixed,bd]
      · have T := predecessor_trail hp C i k idx O now
        change bind (geometry g .left) 1 (atSite (x (RearTrace.predecessor i)).long 1)=.trail
        rw [T]
        rfl
    have out := joined_follow k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair s first v starts F op R1 gateOn right
    have pairStep : step x e i=lane (sideFlag s) (largePair B pair) := by
      rw [←I]
      cases s with
      | left => simp only [site,AllSizeS1Geometry.step,if_true]; rfl
      | right => simp only [site,AllSizeS1Geometry.step,if_neg (Ne.symm (sep e)),if_true]; rfl
    change atSite (step x e i).long 1=_
    rw [pairStep]
    unfold atSite
    have V : (kField 1).read (lane (sideFlag s) (largePair B pair)).long =
      readRaw (Pair.map LargeSite.long (largePair B pair)) ⟨s,1⟩ := by cases s <;> rfl
    rw [V,out]
    by_cases h : s=first
    · rw [if_pos h,if_pos h]
      change decode (readRaw raw ⟨s,1⟩)=atSite (x i).long 1
      exact read
    · rw [if_neg h,if_neg h,BStarLongToken.decode_encode]
  · intro e left right
    have L : i≠e := Ne.symm left
    have U : i≠rightNeighbor e := fun E => right (by change e=RearTrace.predecessor i; rw [E,RearTrace.predecessor_right])
    simp [AllSizeS1Geometry.step,L,U]


#print axioms joined_follow
#print axioms follow_mark
end L4.BStarBitFollowRing
