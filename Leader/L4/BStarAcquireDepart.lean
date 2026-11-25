import Leader.L4.BStarAcquireReturn

namespace L4.BStarAcquireDepart
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongTransport
open BStarLongRouting BStarLongLayout BStarLongWork BStarLongRoutingFrame
open BStarAcquireJoinedHop

/-- On a selected real ACQUIRE link, the old F cursor is replaced by
Trail. The right K0 door override cannot erase this Trail: right K0
is never the source of a selected link. -/
theorem joined_departs (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (a : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.destination=some a →
    readK raw C.source=.forward pay → BStarAcquireHop.Healthy pay →
    readK (Pair.map LargeSite.long (largePair b x)) C.source=.trail := by
  dsimp only
  intro hc hd hread hpay
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  have S := BStarAcquireReturn.link_shape g C a hc hd
  have depart := BStarAcquireLandingHop.raw_acquire_departs g raw C a pay hc hd
    (Ne.symm S.1) (by rw [S.2.1]; decide) hread hpay
  suffices E : readRaw (Pair.map LargeSite.long (largePair b x)) C.source =
      readRaw (patchPair w raw) C.source by
    change decode (readRaw (Pair.map LargeSite.long (largePair b x)) C.source)=_
    rw [E]
    exact depart
  cases H : C.source.side
  · change (kField C.source.occurrence).read _=_
    unfold readRaw
    rw [H]
    change (kField C.source.occurrence).read ((w.1.compose q.1).apply raw.1)=
      (kField C.source.occurrence).read (w.1.apply raw.1)
    rw [Patch.compose_apply]
    exact field_kframe _ _ _ (scratch_kframe g raw false)
  · unfold readRaw
    rw [H]
    let j := C.source.occurrence
    change (kField j).read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      (w.2.compose q.2)).apply raw.2)=(kField j).read (w.2.apply raw.2)
    have Q : (kField j).read ((w.2.compose q.2).apply raw.2)=(kField j).read (w.2.apply raw.2) := by
      rw [Patch.compose_apply]
      exact field_kframe _ _ _ (scratch_kframe g raw true)
    cases K : g.2.axes.h6
    · rw [LongDoorGuard.no_authority]; exact Q
    · cases V : LongDoorGuard.valid manifest raw.2
      · rw [LongDoorGuard.invalid_override _ _ _ V,Patch.compose_apply]
        have F := read_frame (raw.1,(w.2.compose q.2).apply raw.2) (R j) (S.2.2 H)
          (true,LongDoorGuard.repair manifest) guard_frame
        exact F.trans Q
      · rw [LongDoorGuard.valid_no_override _ _ _ V]; exact Q

end L4.BStarAcquireDepart
