import Leader.L4.BStarCommitOwnerOrigin

namespace L4.BStarCommitHealthyOffer
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

/-- Each actual non-door claim whose bound old forward token is COMMIT
selects that very payload, independent of other commands, the
destination's token, and the authorization at the body. -/
theorem bound_commit_selected (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (M : C∈orderedCommands g) (nd : C.kind≠.door)
    (B : bound g (readK x) C.source=.forward p) (op : p.opcode.toNat=commitOp) :
    (C,.advance p)∈actualOffers g x := by
  have D : depart (geometry g C.source.side) C.source.occurrence p=some p := by
    simp [depart,gate,op,commitOp,bitOp,admit]
  have cl : classifyOld g x C=.advance p := by
    change classify C _ (bound g (readK x) C.source) _=_
    simp [classify,nd,B,D]
  have gateEq : gatedAt g x C=.advance p := by
    unfold gatedAt
    rw [cl]
    simp [checkOffer,checkFence,op,commitOp]
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
    simp [op,commitOp,prepOf] at P
  have pre : (C,.advance p)∈(round g x).offered :=
    List.mem_map.mpr ⟨(C,.advance p),cg,by
      change (if C.source∈(round g x).faults then (C,Offer.advance failedPayload) else (C,Offer.advance p))=_
      rw [if_neg keep]⟩
  exact List.mem_map.mpr ⟨(C,.advance p),pre,by
    by_cases h : C.source.occurrence.val<3
    · simp [BStarLongGrant.update,h,op,commitOp,acquire]
    · simp [BStarLongGrant.update,h]⟩

/-- Raw invariants needed to get a healthy bound COMMIT. Healthy opcode
and fault alone are insufficient: outcome, race, and packed descriptor
and bank shape must pass the actual binder. -/
theorem bind_commit (g : LongGeometry) (k : Fin 11) (p : Payload)
    (F : p.fault=0) (O : p.opcode.toNat=commitOp) (R : p.race=0) (T : p.outcome=0)
    (W : forwardWidth commitOp p.argument.toNat=some 9) :
    BStarLongCommand.bind g k (.forward p)=.forward (cropped p 9) := by
  have W' : forwardWidth 411 p.argument.toNat=some 9 := W
  simp [BStarLongCommand.bind,F,O,R,T,W',gate,commitOp,bitOp,admit]

/-- No successful publication is assumed. A well-formed literal old
COMMIT at any selected non-door claim yields a healthy actual offer. -/
theorem raw_commit_selected (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (M : C∈orderedCommands g) (nd : C.kind≠.door)
    (F : p.fault=0) (O : p.opcode.toNat=commitOp) (R : p.race=0) (T : p.outcome=0)
    (W : forwardWidth commitOp p.argument.toNat=some 9)
    (H : readK x C.source=.forward p) :
    (C,.advance (cropped p 9))∈actualOffers g x := by
  apply bound_commit_selected g x C (cropped p 9) M nd _ O
  change BStarLongCommand.bind _ _ (readK x C.source)=_
  rw [H]
  exact bind_commit _ _ p F O R T W

/-- Fault zero and opcode 411 alone do not imply bindability. A stale
forward token with a nonzero outcome is canonicalized to fault. -/
theorem raw_healthy_is_not_enough (g : LongGeometry) (k : Fin 11) (p : Payload)
    (F : p.fault=0) (O : p.opcode.toNat=commitOp) :
    let bad := {p with outcome:=1}
    BStarCommitPayload.Commit bad ∧
      BStarLongCommand.bind g k (.forward bad)=fault false := by
  dsimp only
  exact ⟨⟨F,O⟩,by simp [BStarLongCommand.bind]⟩

end L4.BStarCommitHealthyOffer
