import Leader.L4.BStarSealHealthyHop
import Leader.L4.BStarStageIssue
import Leader.L4.BStarStageCandidateWrite

namespace L4.Height.StageHealthyHop
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongCommand BStarLongEvents BStarLongCommandData BStarLongTransport
open BStarLongLiteral BStarLongRouting

private theorem prep_fault_origin (g : Pair LongGeometry) (x : Pair (BitVec LW)) (j : AtK)
    (h : j∈(round g x).faults) :
    ∃ c q, c.source=j ∧ (c,.advance q)∈gated g x ∧
      ∃ op, prepOf q.opcode.toNat=some op := by
  let L := preparedBy g x (gated g x)
  have hf : j∈BStarLongPrep.prepFaults (BStarLongPrep.view x) L := h
  unfold BStarLongPrep.prepFaults at hf
  have selected_mem (o : BStarLongPrep.Offer)
      (h : o∈(BStarLongPrep.arbitration L).1) : o∈L := by
    have H : o∈(offers BStarLongPrep.offerPriority L) := by
      unfold BStarLongPrep.arbitration at h
      rw [BStarLongPrep.arbitrate_winners] at h
      exact (select_sublist _ _ _).subset h
    have general (xs : List BStarLongPrep.Offer) (h : o∈offers BStarLongPrep.offerPriority xs) : o∈xs := by
      induction xs with
      | nil => exact h
      | cons b rest ih =>
        change o∈insert BStarLongPrep.offerPriority b (offers BStarLongPrep.offerPriority rest) at h
        rcases (mem_insert BStarLongPrep.offerPriority b o _).mp h with h|h
        · exact List.mem_cons.mpr (.inl h)
        · exact List.mem_cons_of_mem _ (ih h)
    exact general L H
  have loser_mem (o : BStarLongPrep.Offer) (h : o∈(BStarLongPrep.arbitration L).2) :
      o∈L := by
    have H := (BStarLongPrep.arbitrate_losers [] (offers BStarLongPrep.offerPriority L)).subset h
    have general (xs : List BStarLongPrep.Offer) (h : o∈offers BStarLongPrep.offerPriority xs) : o∈xs := by
      induction xs with
      | nil => exact h
      | cons b rest ih =>
        change o∈insert BStarLongPrep.offerPriority b (offers BStarLongPrep.offerPriority rest) at h
        rcases (mem_insert BStarLongPrep.offerPriority b o _).mp h with h|h
        · exact List.mem_cons.mpr (.inl h)
        · exact List.mem_cons_of_mem _ (ih h)
    exact general L H
  have witness : ∃ o∈L, o.claim.origin=j := by
    rcases List.mem_append.mp hf with H|H
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,loser_mem o ho,rfl⟩
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,selected_mem o (List.mem_filter.mp ho).1,rfl⟩
  obtain ⟨o,ho,he⟩ := witness
  unfold L preparedBy at ho
  obtain ⟨⟨c,s⟩,hc,hO⟩ := List.mem_flatMap.mp ho
  cases s <;> simp only at hO
  all_goals try cases hO
  rename_i q
  unfold fieldOffers at hO
  split at hO
  · cases hO
  · split at hO
    · cases hO
    · rename_i op hOp
      obtain ⟨cl,hcl,rfl⟩ := List.mem_map.mp hO
      obtain ⟨sh,hsh,rfl⟩ := List.mem_map.mp hcl
      exact ⟨c,q,he,hc,op,hOp⟩

/-- Each actual non-door claim whose bound old forward token is STAGE
selects that very payload, independent of other commands, the
destination's token, and the authorization at the body. -/
theorem bound_stage_selected (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (M : C∈orderedCommands g) (nd : C.kind≠.door)
    (B : bound g (readK x) C.source=.forward p) (op : p.opcode.toNat=stageOp) :
    (C,.advance p)∈actualOffers g x := by
  have D : depart (geometry g C.source.side) C.source.occurrence p=some p := by
    simp [depart,gate,op,stageOp,bitOp,admit]
  have cl : classifyOld g x C=.advance p := by
    change classify C _ (bound g (readK x) C.source) _=_
    simp [classify,nd,B,D]
  have gateEq : gatedAt g x C=.advance p := by
    unfold gatedAt
    rw [cl]
    simp [checkOffer,checkFence,op,stageOp]
  have cg : (C,.advance p)∈gated g x := (gated_mem g x C _).mpr ⟨M,gateEq.symm⟩
  have keep : C.source∉(round g x).faults := by
    intro bad
    obtain ⟨b,q,eq,hq,k,P⟩ := prep_fault_origin g x C.source bad
    obtain ⟨mb,Q⟩ := (gated_mem g x b _).mp hq
    have E := BStarAcquireIncidence.same_claim g b C b.source mb M
      (by simp [Claim.slots]) (by simp [Claim.slots,eq])
    subst b
    have eq := Offer.advance.inj (Q.trans gateEq)
    subst q
    simp [op,stageOp,prepOf] at P
  have pre : (C,.advance p)∈(round g x).offered :=
    List.mem_map.mpr ⟨(C,.advance p),cg,by
      change (if C.source∈(round g x).faults then (C,Offer.advance failedPayload) else (C,Offer.advance p))=_
      rw [if_neg keep]⟩
  exact List.mem_map.mpr ⟨(C,.advance p),pre,by
    by_cases h : C.source.occurrence.val<3
    · simp [BStarLongGrant.update,h,op,stageOp,acquire]
    · simp [BStarLongGrant.update,h]⟩

open BStarResetQuiet BStarClearanceForward BStarLongLayout

private theorem carried_stage (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (source : BitVec LW) (d : BStarLongPublication.Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (auth : (geometry g C.source.side).axes.h6=true → C.source.occurrence.val=1 →
      BStarLongOutgoing.actual (atOld raw C.source) d=true) :
    carried g raw C (BStarStageIssue.payload source)=BStarStageIssue.payload source := by
  have N : BStarLongArithmetic.nodeOf 408=none := by decide +kernel
  have num : BStarLongArithmetic.visit (geometry g C.source.side) C.source.occurrence
      (atOld raw C.source) (BStarStageIssue.payload source)=(.empty _, BStarStageIssue.payload source) := by
    unfold BStarLongArithmetic.visit
    split
    · rfl
    · rw [show (BStarStageIssue.payload source).opcode.toNat=408 from rfl,N]
  unfold carried
  dsimp only
  rw [num]
  by_cases one : C.source.occurrence.val=1
  · have dec := (BStarStageIssue.issued_descriptor source).trans D
    have E := BStarStageCandidateWrite.execute_stage (geometry g C.source.side) (atOld raw C.source)
      C.source.occurrence (BStarStageIssue.payload source) d one rfl rfl dec (fun h=>auth h one)
    rw [E]
  · rw [BStarLongOutgoing.noncenter_hold _ _ _ _ one]
    rfl

/-- Every real selected link on the issued STAGE word, including its
authorized center departure, preserves its canonical payload exactly. -/
theorem joined_stage (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (C : CommandClaim) (a : AtK) (source : BitVec LW) (d : BStarLongPublication.Descriptor) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    C∈orderedCommands g → C.destination=some a →
    BStarLongPublication.decode (sourceDescriptor.read source)=some d →
    ((geometry g C.source.side).axes.h6=true → C.source.occurrence.val=1 →
      BStarLongOutgoing.actual (atOld raw C.source) d=true) →
    readK raw C.source=.forward (BStarStageIssue.payload source) →
    readK y a=.forward (BStarStageIssue.payload source) := by
  dsimp only
  intro cm dst D auth front
  let pay := BStarStageIssue.payload source
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have shape := BStarAcquireReturn.link_shape g C a cm dst
  have sel : (C,.advance pay)∈actualOffers g raw := by
    apply bound_stage_selected g raw C pay cm (by rw [shape.2.1]; decide) _ rfl
    unfold bound
    rw [front]
    exact BStarStageIssue.bound_forward_exact _ _ source d D
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have W := (BStarAcquireJoinedHop.k0_dest g C a cm dst J).2
    simp [Z] at W
  have A := (move_lands g raw C pay a dst sel (Ne.symm shape.1)).2
  change decode (readRaw _ a)=_
  rw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,decode_encode,
    carried_stage g raw C source d D auth]
  simp [arrive,BStarStageIssue.payload,gate,stageOp,bitOp,admit]

end L4.Height.StageHealthyHop
