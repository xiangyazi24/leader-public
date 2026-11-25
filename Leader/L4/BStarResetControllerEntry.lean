import Leader.L4.BStarResetDoor

namespace L4.BStarResetControllerEntry
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongWork
open BStarLongCommand BStarLongDoor BStarAcquireJoinedIssue BStarAcquireWaitControl BStarResetDoor

def snapshot (x : BitVec LW) : (Token × BitVec 2) × BitVec 9 :=
  (view x,ctrlOp.read x)

theorem restart_control (x : BitVec LW) : control (faultRestart.apply x)=(1,0) := by
  obtain ⟨h₁,h₂,_,_⟩ := LongDoorGuard.repair_values manifest x
  exact Prod.ext h₁ h₂

theorem issued_control (op a : Nat) (x : BitVec LW) :
    control ((issued op a).apply x)=(2,ctrlOp.read x) := by
  have H (y : BitVec LW) :
      control (((ctrlPhase.assign 2).compose (setToken 0 (forward op a))).apply y) =
        (2,ctrlOp.read y) := by
    unfold BStarAcquireWaitControl.control setToken
    rw [Patch.compose_apply,
      Field.read_other_assign _ _ _ _ (.inr (by decide)),
      Field.read_assign,Field.read_other_assign _ _ _ _ (.inr (by decide)),
      Field.read_other_assign _ _ _ _ (.inl (by decide))]
  unfold issued
  split
  · rw [Patch.compose_apply,H]
    unfold clearFile
    rw [Field.read_other_assign _ _ _ _ (.inr (by decide))]
  · exact H x

theorem selected_restart (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest x.2.long=true →
    oldDoor x.2.long (bind g.2 0 (atSite x.2.long 0))=.write faultRestart →
    snapshot (largePair b x).2.long=((.empty,1),0) := by
  dsimp only
  intro hh hv E
  have v := joined_door_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x faultRestart _ hh hv E restart_view
  have q := phase_control_write k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x faultRestart
    (fun _ => (1,0)) hh hv E restart_control
  exact Prod.ext v (congrArg (fun q : BitVec 2 × BitVec 9 => q.2) q)

theorem guard_restart (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest x.2.long=false →
    snapshot (largePair b x).2.long=((.empty,1),0) := by
  dsimp only
  intro hh hv
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let g := Pair.map (longGeometry b) x
  change snapshot ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
    ((longWork g raw).2.compose (longScratch g raw).2)).apply raw.2)=_
  rw [show g.2.axes.h6=true from hh,LongDoorGuard.invalid_override _ _ _ (show LongDoorGuard.valid manifest raw.2=false from hv),Patch.compose_apply]
  exact Prod.ext (restart_view _) (congrArg (fun q : BitVec 2 × BitVec 9 => q.2) (restart_control _))

theorem exact_empty_entry (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let v : BitVec LW := x.2.long
    let op := (ctrlOp.read v).toNat
    let y := (largePair b x).2.long
    (oldHeaders b x.2).h6=true → atSite v 0=.empty →
    (LongDoorGuard.valid manifest v=false ∨ (ctrlPhase.read v).toNat≠1 ∨ initial op v=none) ∧
       snapshot y=((.empty,1),0)
      ∨ ∃ a, LongDoorGuard.valid manifest v=true ∧ (ctrlPhase.read v).toNat=1 ∧
        initial op v=some a ∧ snapshot y=((forward op a,2),ctrlOp.read v) := by
  dsimp only
  intro hh empty
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let v : BitVec LW := x.2.long
  let g := Pair.map (longGeometry b) x
  let op := (ctrlOp.read v).toNat
  have bound : bind g.2 0 (atSite v 0)=.empty := by rw [show atSite v 0=.empty from empty]; rfl
  cases V : LongDoorGuard.valid manifest v with
  | false => exact .inl ⟨.inl rfl,guard_restart k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x hh V⟩
  | true =>
    by_cases phase : (ctrlPhase.read v).toNat=1
    · have D : oldDoor v (bind g.2 0 (atSite v 0))=
          (match initial op v with
          | none => Decision.write faultRestart
          | some a => Decision.write (issued op a)) := by
        rw [bound]
        simp [oldDoor,V,phase,op] <;> rfl
      cases H : initial op v with
      | none =>
        rw [H] at D
        exact .inl ⟨.inr (.inr rfl),selected_restart k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x hh V D⟩
      | some a =>
        rw [H] at D
        refine .inr ⟨a,rfl,phase,rfl,?_⟩
        have w := joined_door_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x (issued op a) _ hh V D (issue_view op a)
        have q := phase_control_write k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x (issued op a)
          (fun old => (2,old.2)) hh V D (issued_control op a)
        exact Prod.ext w (congrArg (fun q : BitVec 2 × BitVec 9 => q.2) q)
    · have D : oldDoor v (bind g.2 0 (atSite v 0))=.write faultRestart := by
        rw [bound]
        simp [oldDoor,V,phase]
      exact .inl ⟨.inr (.inl phase),selected_restart k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x hh V D⟩


theorem issue_ignores_token (v : BitVec LW) (t : Token)
    (V : LongDoorGuard.valid manifest v=true) (phase : (ctrlPhase.read v).toNat=1) :
    oldDoor v t =
      match initial (ctrlOp.read v).toNat v with
      | none => .write faultRestart
      | some a => .write (issued (ctrlOp.read v).toNat a) := by
  simp [oldDoor,V,phase] <;> rfl

/-- Arbitrary old K0, including inherited F/T/D. Only valid old ISSUE
matters; every valid initial argument gets genuinely issued. -/
theorem exact_issue_any_token (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let v : BitVec LW := x.2.long
    let op := (ctrlOp.read v).toNat
    let y := (largePair b x).2.long
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest v=true →
    (ctrlPhase.read v).toNat=1 →
    snapshot y =
      match initial op v with
      | none => ((.empty,1),0)
      | some a => ((forward op a,2),ctrlOp.read v) := by
  dsimp only
  intro hh V phase
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let v : BitVec LW := x.2.long
  let g := Pair.map (longGeometry b) x
  let op := (ctrlOp.read v).toNat
  have D := issue_ignores_token v (bind g.2 0 (atSite v 0)) V phase
  cases H : initial op v with
  | none =>
    rw [H] at D
    exact selected_restart k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x hh V D
  | some a =>
    rw [H] at D
    have w := joined_door_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x (issued op a) _ hh V D (issue_view op a)
    have q := phase_control_write k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x (issued op a)
      (fun old => (2,old.2)) hh V D (issued_control op a)
    exact Prod.ext w (congrArg (fun q : BitVec 2 × BitVec 9 => q.2) q)

open BStarLongEvents BStarLongClaims BStarCommitIssue in
/-- The uniquely selected old source door consumes a bound old reply.
There is no ISSUE alternative at this mark; ordinary and arithmetic
replies use different patches. An old byte match gives no provenance. -/
theorem wait_reply_selected (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (f : Payload)
    (hh : g.2.axes.h6=true) (V : LongDoorGuard.valid manifest raw.2=true)
    (phase : (ctrlPhase.read raw.2).toNat=2)
    (bound : bind g.2 0 (atSite raw.2 0)=.reply f) :
    let op := (ctrlOp.read raw.2).toNat
    let claim : CmdOffer := (doorClaim,.door (.reply f))
    (actualOffers g raw).filter BStarDoorUnique.doorAction=[claim] ∧
      (selected g raw claim).k=[] ∧
      (selected g raw claim).work=[(true,
        if f.fault != 0 || f.opcode.toNat != op then faultRestart
        else if (arithKind op).isSome then BStarLongArithmetic.acceptFile raw.2 op f
        else afterReply op f raw.2)] := by
  dsimp only
  have E := BStarDoorUnique.actual_door_singleton g raw hh
  rw [bound] at E
  refine ⟨E,?_⟩
  change
    (match oldDoor raw.2 (.reply f) with
     | .hold => (⟨[],[],[]⟩ : Selected)
     | .write q => ⟨[],[(true,q)],[]⟩
     | .acceptTour op p => ⟨[],[(true,BStarLongArithmetic.acceptFile raw.2 op p)],[]⟩).k=[] ∧ _
  have D : oldDoor raw.2 (.reply f) =
      (if f.fault != 0 || f.opcode.toNat != (ctrlOp.read raw.2).toNat then .write faultRestart
       else if (arithKind (ctrlOp.read raw.2).toNat).isSome then .acceptTour (ctrlOp.read raw.2).toNat f
       else .write (afterReply (ctrlOp.read raw.2).toNat f raw.2)) := by
    simp only [oldDoor,V,phase] <;> rfl
  change
    (match oldDoor raw.2 (.reply f) with
     | .hold => (⟨[],[],[]⟩ : Selected)
     | .write q => ⟨[],[(true,q)],[]⟩
     | .acceptTour op p => ⟨[],[(true,BStarLongArithmetic.acceptFile raw.2 op p)],[]⟩).k=[] ∧
    (match oldDoor raw.2 (.reply f) with
     | .hold => (⟨[],[],[]⟩ : Selected)
     | .write q => ⟨[],[(true,q)],[]⟩
     | .acceptTour op p => ⟨[],[(true,BStarLongArithmetic.acceptFile raw.2 op p)],[]⟩).work=_
  rw [D]
  by_cases B : (f.fault != 0 || f.opcode.toNat != (ctrlOp.read raw.2).toNat)=true
  · simp only [if_pos B]; exact ⟨trivial,trivial⟩
  · simp only [if_neg B]
    by_cases A : (arithKind (ctrlOp.read raw.2).toNat).isSome=true
    · simp only [if_pos A]; exact ⟨trivial,trivial⟩
    · simp only [if_neg A]; exact ⟨trivial,trivial⟩

#print axioms exact_issue_any_token
#print axioms wait_reply_selected
end L4.BStarResetControllerEntry
