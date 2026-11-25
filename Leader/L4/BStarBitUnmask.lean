import Leader.L4.BStarBitParity
import Leader.L4.BStarClearanceObserveJoined
import Leader.L4.BStarLongKOne
import Leader.L4.BStarResetQuietTable

namespace L4.BStarBitUnmask
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongRouting BStarLongWork BStarLongEvents
open BStarClearanceObserveJoined BStarResetQuiet BStarResetQuietTable BStarLongLiteral BStarLongKOne
open BStarBitParity

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
theorem first_avoids (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (p : Payload)
    (B : bound g (readK raw) ⟨s,1⟩=.forward p)
    (F : p.fault=0) (P : p.opcode.toNat=bitOp) (K : p.race=1)
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

/-- The real simultaneous joined mark writes the first side exactly,
not just a lower race rank. No probabilistic assertion is made. -/
theorem joined_first (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : Side)
    (v : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let a : AtK := ⟨s,1⟩
    bound g (readK raw) a=.forward v →
    v.fault=0 → v.opcode.toNat=bitOp → v.race=1 →
    gate bitOp 1 (geometry g s)=true →
    (s=.right → g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail) →
    readRaw (Pair.map LargeSite.long (largePair b x)) a=encode (.forward {v with race:=firstCode s}) := by
  dsimp only
  intro B F P K G incoming
  have H := first_avoids _ _ s v B F P K G incoming
  exact (observed_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x ⟨s,1⟩ (by change (1:Nat)≠0; decide)
    v {v with race:=firstCode s} 0 H B (observe_first _ v s G F P K)).1

#print axioms joined_first
end L4.BStarBitUnmask
