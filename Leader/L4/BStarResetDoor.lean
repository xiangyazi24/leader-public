import Leader.L4.BStarAcquireJoinedIssue
import Leader.L4.BStarAcquireWaitControl

namespace L4.BStarResetDoor
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongWork
open BStarLongCommand BStarLongDoor BStarAcquireJoinedIssue

private theorem phase_token (x : BitVec LW) (t : Token) :
    ctrlPhase.read ((setToken 0 t).apply x)=ctrlPhase.read x := by
  unfold setToken
  exact Field.read_other_assign _ _ _ _ (.inr (by decide))

theorem issue_view (o a : Nat) (x : BitVec LW) :
    view ((issued o a).apply x)=(forward o a,2) := by
  unfold issued
  split <;> simp only [view,Patch.compose_apply,atSite_after,phase_token,Field.read_assign]

theorem schedule_view (o : Nat) (x : BitVec LW) :
    view ((schedule o).apply x)=(.empty,1) := by
  simp only [view,schedule,Patch.compose_apply,atSite_after,phase_token]
  rw [Field.read_other_assign _ _ _ _ (.inr (by decide)),Field.read_assign]

theorem restart_view (x : BitVec LW) :
    view (faultRestart.apply x)=(.empty,1) := by
  obtain ⟨ph,_,_,k⟩ := LongDoorGuard.repair_values manifest x
  change ctrlPhase.read (faultRestart.apply x)=1 at ph
  change (kField 0).read (faultRestart.apply x)=0 at k
  unfold view at *
  rw [ph]
  change (decode ((kField 0).read (faultRestart.apply x)),1)=(.empty,1)
  rw [k]
  rfl

theorem valid_of (x : BitVec LW) {o q : Nat}
    (ph : (ctrlPhase.read x).toNat=q) (op : (ctrlOp.read x).toNat=o)
    (hq : q=1 ∨ q=2) (ho : o<3) : LongDoorGuard.valid manifest x=true := by
  change ((((ctrlPhase.read x).toNat==1) || ((ctrlPhase.read x).toNat==2)) &&
      decide ((ctrlOp.read x).toNat<manifest.opcodes))=true
  have E : manifest.opcodes=413 := rfl
  rw [ph,op,E]
  rcases hq with rfl|rfl <;> simp <;> omega

theorem reset_initial (x : BitVec LW) (o : Nat) (ho : o<3) : initial o x=some 0 := by
  have T : o=0 ∨ o=1 ∨ o=2 := by omega
  rcases T with rfl|rfl|rfl <;> rfl

/-- Every genuine reset ISSUE writes a fresh F(0/1/2,0) and enters
WAIT, independent of inherited K0 bytes and dormant flags. -/
theorem joined_reset_issue (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (o : Nat) (ho : o<3) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (oldHeaders b x.2).h6=true →
    (ctrlPhase.read x.2.long).toNat=1 →
    (ctrlOp.read x.2.long).toNat=o →
    view (largePair b x).2.long=(forward o 0,2) := by
  dsimp only
  intro hh ph op
  have V := valid_of x.2.long ph op (.inl rfl) ho
  apply joined_door_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x (issued o 0) _ hh V
  · simp only [oldDoor,V,ph,op,Bool.not_true,Bool.false_eq_true,if_false,BEq.rfl,if_true]
    let old : BitVec LW := x.2.long
    change (match initial o old with | none => Decision.write faultRestart | some n => Decision.write (issued o n))=Decision.write (issued o 0)
    rw [reset_initial old o ho]
  · exact issue_view o 0

/-- A tagged fault returning to the old door is rejected, but the
same reset action empties K0 and leaves a legal ISSUE for the next
attempt. This statement does not infer a tag from byte equality. -/
theorem joined_fault_consumed (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (f : Payload) (bad : f.fault≠0) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    (oldHeaders b x.2).h6=true →
    LongDoorGuard.valid manifest x.2.long=true →
    (ctrlPhase.read x.2.long).toNat=2 →
    bind g.2 0 (atSite x.2.long 0)=.reply f →
    view (largePair b x).2.long=(.empty,1) := by
  dsimp only
  intro hh V ph B
  apply joined_door_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x faultRestart _ hh V
  · rw [B]
    have E : (f.fault != 0)=true := bne_iff_ne.mpr bad
    simp only [oldDoor,V,ph,Bool.not_true,Bool.false_eq_true,if_false,E,Bool.true_or,if_true]
    rfl
  · exact restart_view

open BStarAcquireWaitControl

theorem phase_control_write (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (w : Patch LW) (f : (BitVec 2 × BitVec 9) → (BitVec 2 × BitVec 9)) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true →
    oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))=.write w →
    (∀ old, control (w.apply old)=f (control old)) →
    control (largePair b x).2.long=f (control raw.2) := by
  dsimp only
  intro hh hv eq W
  rw [joined_control k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x hv]
  refine door_projection _ _ hh [(true,w)] ?_ f ?_
  · simp only [selected,BStarCommitIssue.doorClaim,BStarLongClaims.R,atOld,lane]
    change (match oldDoor (Pair.map LargeSite.long x).2 _ with
      | .hold => (⟨[],[],[]⟩ : Selected)
      | .write q => ⟨[],[(true,q)],[]⟩
      | .acceptTour o p => ⟨[],[(true,BStarLongArithmetic.acceptFile (Pair.map LargeSite.long x).2 o p)],[]⟩).work=_
    erw [eq]
  · intro y
    exact W y.2

private theorem control_schedule (o : Nat) (x : BitVec LW) :
    control ((schedule o).apply x)=(1,BitVec.ofNat 9 o) := by
  have F : (kField 0).offset+52≤ctrlOp.offset := by decide
  unfold BStarAcquireWaitControl.control schedule setToken
  rw [Patch.compose_apply,Patch.compose_apply,Field.read_other_assign _ _ _ _ (.inr (by decide)),
    Field.read_other_assign _ _ _ _ (.inr (by decide)),Field.read_assign,
    Field.read_other_assign _ _ _ _ (.inr F),Field.read_assign]
  rfl

private def clearResetDescriptor : Patch LW :=
  (((sourceDescriptor.assign 0).compose (choice.assign 0)).compose (candidateHeaders.assign 0))

private theorem clear_descriptor_view (x : BitVec LW) :
    view (clearResetDescriptor.apply x)=view x := by
  unfold clearResetDescriptor view atSite
  simp only [Patch.compose_apply]
  rw [Field.read_other_assign _ _ _ _ (.inl (by decide)),
    Field.read_other_assign _ _ _ _ (.inl (by decide)),Field.read_other_assign _ _ _ _ (.inl (by decide)),
    Field.read_other_assign _ _ _ _ (.inr (by decide)),
    Field.read_other_assign _ _ _ _ (.inr (by decide)),Field.read_other_assign _ _ _ _ (.inr (by decide))]

private theorem clear_descriptor_control (x : BitVec LW) :
    control (clearResetDescriptor.apply x)=control x := by
  unfold clearResetDescriptor BStarAcquireWaitControl.control
  simp only [Patch.compose_apply]
  rw [Field.read_other_assign _ _ _ _ (.inr (by decide)),
    Field.read_other_assign _ _ _ _ (.inr (by decide)),Field.read_other_assign _ _ _ _ (.inr (by decide)),
    Field.read_other_assign _ _ _ _ (.inr (by decide)),
    Field.read_other_assign _ _ _ _ (.inr (by decide)),Field.read_other_assign _ _ _ _ (.inr (by decide))]

/-- Exact K0 and source-control result of an old bound matching reset
receipt. Whether it was generated must come from the tagged history. -/
theorem joined_reset_advance (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (o : Nat) (f : Payload) (ho : o<3) (hf : f.fault=0) (hm : f.opcode.toNat=o) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    (oldHeaders b x.2).h6=true →
    (ctrlPhase.read x.2.long).toNat=2 →
    (ctrlOp.read x.2.long).toNat=o →
    bind g.2 0 (atSite x.2.long 0)=.reply f →
    let y := (largePair b x).2.long
    atSite y 0=.empty ∧ control y=(1,BitVec.ofNat 9 (o+1)) := by
  dsimp only
  intro hh ph op bound
  have V := valid_of x.2.long ph op (.inr rfl) ho
  let w := if o=1 then (schedule (o+1)).compose clearResetDescriptor else schedule (o+1)
  have D : oldDoor x.2.long (.reply f)=.write w := by
    obtain ⟨_,r0,r1,r2⟩ := BStarCommitIssue.reset_receipt _ f o V ph op hf hm
    have S : o=0 ∨ o=1 ∨ o=2 := by omega
    rcases S with rfl|rfl|rfl
    · exact r0 rfl
    · exact r1 rfl
    · exact r2 rfl
  have H := D
  have WW (z : BitVec LW) : view (w.apply z)=(.empty,1) := by
    unfold w
    split
    · rw [Patch.compose_apply,clear_descriptor_view,schedule_view]
    · exact schedule_view _ _
  have WC (z : BitVec LW) : control (w.apply z)=(1,BitVec.ofNat 9 (o+1)) := by
    unfold w
    split
    · rw [Patch.compose_apply,clear_descriptor_control,control_schedule]
    · exact control_schedule _ _
  have before : oldDoor x.2.long
      (bind (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x).2 0
        (atSite x.2.long 0))=.write w := congrArg (oldDoor x.2.long) bound |>.trans H
  exact ⟨congrArg Prod.fst (joined_door_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x w _ hh V before WW),
    phase_control_write k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x w (fun _ => _) hh V before WC⟩

#print axioms joined_reset_advance
#print axioms joined_reset_issue
#print axioms joined_fault_consumed
end L4.BStarResetDoor
