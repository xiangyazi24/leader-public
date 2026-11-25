import Leader.L4.BStarCommitHealthyOffer

namespace L4.BStarCommitHealthyHop
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongCommand BStarLongEvents BStarLongCommandData BStarLongTransport
open BStarLongLiteral BStarLongRouting BStarResetQuiet BStarClearanceForward
open BStarCommitHealthyOffer

/-- Exact raw wire invariant. Width constrains the effective descriptor
and branch; the final field excludes noncanonical ignored padding. -/
structure Well (p : Payload) : Prop where
  fault : p.fault=0
  opcode : p.opcode.toNat=commitOp
  race : p.race=0
  outcome : p.outcome=0
  width : forwardWidth commitOp p.argument.toNat=some 9
  small : p.argument.toNat<2^9

theorem crop_self (p : Payload) (H : Well p) : cropped p 9=p := by
  have argEq : BitVec.ofNat 34 (low p.argument.toNat 9)=p.argument := by
    rw [show low p.argument.toNat 9=p.argument.toNat from Nat.mod_eq_of_lt H.small]
    simp
  cases p
  simp_all [cropped]

theorem selected_well (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (M : C∈orderedCommands g)
    (nd : C.kind≠.door) (H : Well p) (old : readK raw C.source=.forward p) :
    (C,.advance p)∈actualOffers g raw := by
  have so := raw_commit_selected g raw C p M nd H.fault H.opcode H.race H.outcome H.width old
  rwa [crop_self p H] at so

private theorem carried_before_center (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (H : Well p)
    (away : C.source.occurrence.val≠1 ∨ (geometry g C.source.side).axes.h6=false) :
    carried g raw C p=p := by
  have N : BStarLongArithmetic.nodeOf 411=none := by decide
  rcases away with n|head
  · simp [carried,BStarLongArithmetic.visit,n,BStarLongOutgoing.noncenter_hold,BStarLongOutgoing.hold]
  · simp [carried,BStarLongArithmetic.visit,H.opcode,N,commitOp,BStarLongOutgoing.execute,
      head,stageOp,sealOp,BStarLongOutgoing.hold]

/-- An actual selected owner link strictly before the center carries a
well-formed COMMIT bit-for-bit into its physical joined destination. -/
theorem joined_before_center (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (C : CommandClaim) (a : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    C∈orderedCommands g → C.destination=some a →
    (C.source.occurrence.val≠1 ∨ (geometry g C.source.side).axes.h6=false) →
    readK raw C.source=.forward pay → Well pay → readK y a=.forward pay := by
  dsimp only
  intro cm dst away front H
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have shape := BStarAcquireReturn.link_shape g C a cm dst
  have sel := selected_well g raw C pay cm (by rw [shape.2.1]; decide) H front
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have W := (BStarAcquireJoinedHop.k0_dest g C a cm dst J).2
    simp [Z] at W
  have A := (move_lands g raw C pay a dst sel (Ne.symm shape.1)).2
  change decode (readRaw _ a)=_
  rw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,decode_encode,
    carried_before_center g raw C pay H away]
  simp [arrive,H.opcode,gate,commitOp,bitOp,admit]

end L4.BStarCommitHealthyHop
