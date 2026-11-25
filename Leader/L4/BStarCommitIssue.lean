import Leader.L4.BStarCommitLineage

/-! Exact branch-level source issue and reset sequencing. Matching receipt bytes
are not themselves evidence of a source-issued tour. -/
namespace L4.BStarCommitIssue
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongCommand BStarLongDoor
open BStarLongClaims BStarLongEvents BStarLongWork

abbrev Desc := BStarLongPublication.Descriptor
def Allows (x : BitVec LW) (d : Desc) : Bool :=
  ((choice.read x).toNat==d.b0.val) || (d.need && ((choice.read x).toNat==d.b1.val))

def argument (x : BitVec LW) : Nat :=
  4*(sourceDescriptor.read x).toNat+(choice.read x).toNat

theorem commit_initial (x : BitVec LW) :
    initial commitOp x =
      (BStarLongPublication.decode (sourceDescriptor.read x)).bind
        (fun d => if Allows x d then some (argument x) else none) := by
  have H : BitVec.ofNat 7 (sourceDescriptor.read x).toNat=sourceDescriptor.read x := by simp
  simp [initial,commitOp,stageOp,sealOp,acquire,copyLoad,H,Allows,argument]
  cases BStarLongPublication.decode (sourceDescriptor.read x) <;> rfl

/-- Valid old ISSUE overwrites any old K0 token; WAIT is not an ISSUE.
No assertion of historical freshness follows from this one step. -/
theorem commit_door (x : BitVec LW) (k0 : Token) (d : Desc)
    (hp : (ctrlPhase.read x).toNat=1) (ho : (ctrlOp.read x).toNat=commitOp)
    (hd : BStarLongPublication.decode (sourceDescriptor.read x)=some d) :
    oldDoor x k0 =
      .write (if Allows x d then issued commitOp (argument x) else faultRestart) := by
  have hv : LongDoorGuard.valid manifest x=true := by
    change ((((ctrlPhase.read x).toNat==1) || ((ctrlPhase.read x).toNat==2)) &&
      decide ((ctrlOp.read x).toNat<manifest.opcodes))=true
    simp [hp,ho]
    decide
  cases ha : Allows x d <;> simp [oldDoor,hv,hp,ho,commit_initial,hd,ha]

theorem commit_door_invalid_descriptor (x : BitVec LW) (k0 : Token)
    (hv : LongDoorGuard.valid manifest x=true)
    (hp : (ctrlPhase.read x).toNat=1) (ho : (ctrlOp.read x).toNat=commitOp)
    (hd : BStarLongPublication.decode (sourceDescriptor.read x)=none) :
    oldDoor x k0=.write faultRestart := by
  simp [oldDoor,hv,hp,ho,commit_initial,hd]

theorem commit_written (x : BitVec LW) :
    let y := (issued commitOp (argument x)).apply x
    (ctrlPhase.read y).toNat=2 ∧
    ctrlOp.read y=ctrlOp.read x ∧
    atSite y 0=forward commitOp (argument x) := by
  simp only [issued,commitOp,show (411==1)=false by decide,Bool.false_eq_true,if_false,
    Patch.compose_apply]
  have H : (kField 0).offset+52≤ctrlPhase.offset := by decide
  have J : (kField 0).offset+52≤ctrlOp.offset := by decide
  have K : ctrlOp.offset+9≤ctrlPhase.offset := by decide
  refine ⟨?_,?_,atSite_after _ _ _⟩
  · unfold setToken
    rw [Field.read_other_assign _ _ _ _ (.inr H),Field.read_assign]
    decide
  · unfold setToken
    rw [Field.read_other_assign _ _ _ _ (.inr J),
      Field.read_other_assign _ _ _ _ (.inl K)]

theorem reset_receipt (x : BitVec LW) (p : Payload) (op : Nat)
    (hv : LongDoorGuard.valid manifest x=true)
    (hp : (ctrlPhase.read x).toNat=2) (ho : (ctrlOp.read x).toNat=op)
    (hf : p.fault=0) (hr : p.opcode.toNat=op) :
    (op=commitOp → oldDoor x (.reply p)=.write (schedule 0)) ∧
    (op=0 → oldDoor x (.reply p)=.write (schedule 1)) ∧
    (op=1 → oldDoor x (.reply p)=.write
      ((schedule 2).compose (((sourceDescriptor.assign 0).compose (choice.assign 0)).compose
        (candidateHeaders.assign 0)))) ∧
    (op=2 → oldDoor x (.reply p)=.write (schedule 3)) := by
  subst op
  have hlen := signature_pins.1
  refine ⟨?_,?_ ,?_,?_⟩ <;> intro E <;>
    simp [oldDoor,hv,hp,hr,E,hf,arithKind,afterReply,commitOp,sealOp,bitOp,admit,acquire] <;> omega

def doorClaim : CommandClaim := ⟨.door,R 0,none⟩

theorem door_claim (g : Pair LongGeometry) (h : g.2.axes.h6=true) :
    doorClaim∈orderedCommands g := by
  cases g with
  | mk x y =>
    change y.axes.h6=true at h
    cases a : (x.inside && x.last) <;> cases b : y.inside <;>
      simp only [orderedCommands,commandClaims,ends,h,a,b,if_true] <;> decide

/-- Grant/data preparation and cancellation do not synthesize a new door
operand. The actual offer reads old right K0 at the header's incoming seam. -/
theorem actual_door (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (h : g.2.axes.h6=true) :
    (doorClaim,.door (bind g.2 0 (atSite x.2 0)))∈actualOffers g x := by
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round
    BStarLongCommandData.gated offersOn
  simp only [List.mem_map]
  let d := (doorClaim,Offer.door (bind g.2 0 (atSite x.2 0)))
  refine ⟨d,?_,rfl⟩
  refine ⟨d,?_,rfl⟩
  refine ⟨d,?_,rfl⟩
  exact ⟨doorClaim,door_claim g h,rfl⟩

/-- A valid local COMMIT source issue has the exact argument later split
by the physical K1 departure. No truncation occurs in the 34-bit field. -/
theorem issued_argument (x : BitVec LW) :
    let n := (BitVec.ofNat 34 (argument x)).toNat
    n/4=(sourceDescriptor.read x).toNat ∧ n%4=(choice.read x).toNat := by
  have hj := (choice.read x).isLt
  have hd := (sourceDescriptor.read x).isLt
  have H : argument x < 2^34 := by unfold argument; omega
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt H]
  unfold argument
  omega

/-- The actual local seam offer contributes exactly this ISSUE patch to
the long row; it is not a physical publication and does not depend on the
same-mark terminal reply. This does not yet frame the joined-row patch. -/
theorem selected_commit_issue (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (hh : g.2.axes.h6=true) (d : Desc)
    (hp : (ctrlPhase.read x.2).toNat=1) (ho : (ctrlOp.read x.2).toNat=commitOp)
    (hd : BStarLongPublication.decode (sourceDescriptor.read x.2)=some d)
    (ha : Allows x.2 d=true) :
    let o : CmdOffer := (doorClaim,.door (bind g.2 0 (atSite x.2 0)))
    o∈actualOffers g x ∧ (selected g x o).work=[(true,issued commitOp (argument x.2))] ∧
      (selected g x o).publications=[] := by
  refine ⟨actual_door g x hh,?_⟩
  unfold selected
  change (match oldDoor x.2 (bind g.2 0 (atSite x.2 0)) with
    | .hold => (⟨[],[],[]⟩ : Selected)
    | .write q => ⟨[],[(true,q)],[]⟩
    | .acceptTour op p => ⟨[],[(true,BStarLongArithmetic.acceptFile x.2 op p)],[]⟩).work = _ ∧ _
  rw [commit_door _ _ d hp ho hd]
  simp [ha,doorClaim,atOld,R,BStarTrace.lane,
    commit_door _ _ d hp ho hd]

theorem rclear_outgoing (g : LongGeometry) (x : BitVec LW) (p : Payload)
    (hh : g.axes.h6=true) (hf : p.fault=0) (ho : p.opcode.toNat=1) :
    BStarLongOutgoing.execute g 1 x p=
      ⟨BStarLongOutgoing.descriptorClear,.forward p,none⟩ := by
  simp [BStarLongOutgoing.execute,hh,hf,ho]

theorem seal_no_need_schedules_commit (x : BitVec LW) (p : Payload) (d : Desc)
    (hd : BStarLongPublication.decode (sourceDescriptor.read x)=some d)
    (hn : d.need=false) (hb : p.argument.toNat%2≠1) :
    afterReply sealOp p x=
      (schedule commitOp).compose (choice.assign (BitVec.ofNat 2 d.b0.val)) := by
  simp [afterReply,sealOp,bitOp,admit,acquire,hd,hn,hb]

theorem seal_need_schedules_bit (x : BitVec LW) (p : Payload) (d : Desc)
    (hd : BStarLongPublication.decode (sourceDescriptor.read x)=some d)
    (hn : d.need=true) (hb : p.argument.toNat%2=1) :
    afterReply sealOp p x=schedule bitOp := by
  simp [afterReply,sealOp,bitOp,admit,acquire,hd,hn,hb]

theorem bit_schedules_commit (x : BitVec LW) (p : Payload) (d : Desc)
    (hd : BStarLongPublication.decode (sourceDescriptor.read x)=some d)
    (hn : d.need=true) :
    let b := p.argument.toNat%2==1
    afterReply bitOp p x=
      ((schedule commitOp).compose (delta.assign (BitVec.ofBool b))).compose
        (choice.assign (BitVec.ofNat 2 (if b then d.b1.val else d.b0.val))) := by
  simp [afterReply,sealOp,bitOp,admit,acquire,hd,hn,beq_iff_eq]

/-- In the grant phase an effective nominated release clears its own
incidence, regardless of competing old-state requests on the same mark. -/
theorem release_result (old rel ask : BStarLongGrant.Ports) (j : Fin 3)
    (h : rel j=true) : BStarLongGrant.result old rel ask j=false := by
  by_cases e : j=1
  · subst j
    simp [BStarLongGrant.result,BStarLongGrant.win,h]
  · simp [BStarLongGrant.result,BStarLongGrant.win,h,e]

end L4.BStarCommitIssue
