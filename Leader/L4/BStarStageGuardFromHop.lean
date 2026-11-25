import Leader.L4.BStarStageHopExtract

namespace L4.BStarStageGuardFromHop
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongEvents BStarLongWork BStarLongLiteral BStarLongCommandData
open BStarClearanceForward BStarLongRouting BStarStageProvenance BStarLongPublication
open BStarLongOutgoing
open BStarResetQuiet BStarResetQuietTable

/-- A healthy destination of the actual selected center STAGE hop
forces the old writer guard. Otherwise the outgoing row emits a fault. -/
theorem authorized (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (c : CommandClaim) (a : AtK) (offer after : Payload) (d : Descriptor) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c.destination=some a → c.source=L 1 →
    (c,.advance offer)∈actualOffers g raw →
    readK y a=.forward after → Stage offer → Stage after →
    decode (descriptorBits offer)=some d → g.1.axes.h6=true → actual raw.1 d=true := by
  dsimp only
  intro dst source sel land offered healthy desc head
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  have hm : c∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have ne := (BStarAcquireReturn.link_shape g c a hm dst).1
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have H := (BStarAcquireJoinedHop.k0_dest g c a hm dst J).2
    simp [Z] at H
  have A := (move_lands g raw c offer a dst sel (Ne.symm ne)).2
  have Arr : arrive (geometry g a.side) a.occurrence (carried g raw c offer)=.forward after := by
    change BStarLongToken.decode (readRaw y a)=.forward after at land
    erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,decode_encode] at land
    exact land
  cases auth : actual raw.1 d
  · have row : BStarLongArithmetic.visit g.1 1 raw.1 offer=(.empty _,offer) := by
      unfold BStarLongArithmetic.visit
      split
      · rfl
      · rw [offered.2,show BStarLongArithmetic.nodeOf stageOp=none by decide +kernel]
    have faulted : carried g raw c offer=⟨1,0,0,0,0⟩ := by
      unfold carried
      rw [source]
      change (match (execute g.1 1 raw.1 (BStarLongArithmetic.visit g.1 1 raw.1 offer).2).carried with
        | .forward q => q
        | _ => ⟨1,0,0,0,0⟩)=_
      have DD : BStarLongPublication.decode (BitVec.ofNat 7 (offer.argument.toNat/2^18))=some d := desc
      rw [row,stage_rejection _ _ _ _ offered.2 head DD offered.1 auth]
      rfl
    rw [faulted] at Arr
    unfold arrive at Arr
    split at Arr <;> injection Arr with H
    all_goals
      have E := congrArg Payload.fault H
      exact False.elim ((by decide : (1 : BitVec 1)≠0) (E.trans healthy.1))
  · rfl

#print axioms authorized
end L4.BStarStageGuardFromHop
