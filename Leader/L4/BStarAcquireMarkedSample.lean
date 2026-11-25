import Leader.L4.BStarAcquireDepart
import Leader.L4.BStarAcquireHealthy

/-! Exact capture observations are determined by the literal old pair.
In particular neither a visited selector nor its win is inferred from a
later receipt. -/
namespace L4.BStarAcquireMarkedSample
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongTransport
open BStarLongCommand BStarLongWork BStarAcquireLatch BStarAcquireHop

/-- Only an old H6 incidence among K0–K2 records an observation. -/
def event (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) : Option Visit :=
  if h : C.source.occurrence.val < 3 then
    if (geometry g C.source.side).axes.h6 then
      let old := BStarLongGrant.atOld x C.source.side
      some ⟨BStarLongPublication.readSel old, BStarLongGrant.headerBits old, ⟨_,h⟩,
        won g x (BStarLongCommandData.round g x).offered C ⟨_,h⟩⟩
    else none
  else none

theorem event_apply (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (pay : Payload) :
    ((event g x C).toList.foldl (fun q v => v.apply q) pay) =
      argUpdate g x (BStarLongCommandData.round g x).offered C pay := by
  unfold event argUpdate
  split
  · split <;> rfl
  · rfl

theorem event_incidence (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (v : Visit) (h : event g x C=some v) :
    v.incidence.val=C.source.occurrence.val ∧ (geometry g C.source.side).axes.h6=true := by
  unfold event at h
  split at h
  · split at h
    · cases h
      exact ⟨rfl,by assumption⟩
    · cases h
  · cases h

theorem event_count (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (k : Nat) (hk : k<3) :
    ((event g x C).toList.filter (fun v => v.incidence.val==k)).length =
      if C.source.occurrence.val==k && (geometry g C.source.side).axes.h6 then 1 else 0 := by
  by_cases J : C.source.occurrence.val<3
  · cases H : (geometry g C.source.side).axes.h6 <;>
      by_cases E : C.source.occurrence.val=k <;> simp [event,J,H,E,hk]
  · have NE : C.source.occurrence.val≠k := by omega
    simp [event,J,NE]

/-- The exact postmark payload is the old token with this observed
capture applied (the identity when there was no capture). At its old
address the same mark installs Trail. -/
theorem capture_link (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (a : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    let q := (event g raw C).toList.foldl (fun q v => v.apply q) pay
    C∈orderedCommands g → C.destination=some a →
    readK raw C.source=.forward pay → Healthy pay →
    readK y C.source=.trail ∧ readK y a=.forward q ∧ Healthy q := by
  dsimp only
  intro hc hd hs hpay
  rw [event_apply]
  have shape := BStarAcquireReturn.link_shape _ C a hc hd
  exact ⟨BStarAcquireDepart.joined_departs k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C a pay hc hd hs hpay,
    BStarAcquireJoinedHop.joined_acquire_lands k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C a pay hc hd
      (by rw [shape.2.1]; decide) hs hpay,
    BStarAcquireHealthy.actual_hop_healthy _ _ _ _ _ hpay⟩

/-- The destination's old payload is not a vacancy guard. An
incoming inherited ACQUIRE may overwrite a different healthy forward
cursor on an idle mark for that cursor. Protecting an issue against
this case is an additional history invariant, not a row property. -/
theorem capture_overwrites (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (a : AtK) (pay other : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let q := (event g raw C).toList.foldl (fun z v => v.apply z) pay
    C∈orderedCommands g → C.destination=some a →
    readK raw C.source=.forward pay → Healthy pay →
    readK raw a=.forward other → q≠other →
    readK (Pair.map LargeSite.long (largePair b x)) a≠readK raw a := by
  dsimp only
  intro hc hd hf hh old different
  have upd := (capture_link k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C a pay hc hd hf hh).2.1
  intro eq
  exact different (Token.forward.inj (upd.symm.trans (eq.trans old)))

end L4.BStarAcquireMarkedSample
