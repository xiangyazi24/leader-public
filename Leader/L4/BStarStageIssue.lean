import Leader.L4.BStarCommitIssue
import Leader.L4.BStarStageLive

/-! Exact source issue of STAGE and its descriptor on a subsequently
authenticated occurrence. Payload identity is not a custody proof. -/
namespace L4.BStarStageIssue
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongWork BStarCommitIssue
open BStarLongClaims BStarLongEvents

def argument (x : BitVec LW) : Nat :=
  (sourceDescriptor.read x).toNat*2^18+(candidateHeaders.read x).toNat

theorem argument_bound (x : BitVec LW) : argument x < 2^25 := by
  have h := (sourceDescriptor.read x).isLt
  have k := (candidateHeaders.read x).isLt
  unfold argument
  omega

theorem argument_split (x : BitVec LW) :
    let u := (BitVec.ofNat 34 (argument x)).toNat
    u/2^18=(sourceDescriptor.read x).toNat ∧
    u%2^18=(candidateHeaders.read x).toNat := by
  have k := (candidateHeaders.read x).isLt
  have h : argument x < 2^34 := Nat.lt_trans (argument_bound x) (by decide)
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt h]
  unfold argument
  omega

theorem stage_initial (x : BitVec LW) :
    initial stageOp x =
      (BStarLongPublication.decode (sourceDescriptor.read x)).map (fun _ => argument x) := by
  have H : BitVec.ofNat 7 (sourceDescriptor.read x).toNat=sourceDescriptor.read x := by simp
  simp [initial,stageOp,acquire,copyLoad,H,argument]
  cases BStarLongPublication.decode (sourceDescriptor.read x) <;> rfl

theorem stage_door (x : BitVec LW) (k0 : Token)
    (hp : (ctrlPhase.read x).toNat=1) (ho : (ctrlOp.read x).toNat=stageOp) :
    oldDoor x k0=.write (if (BStarLongPublication.decode (sourceDescriptor.read x)).isSome
      then issued stageOp (argument x) else faultRestart) := by
  have hv : LongDoorGuard.valid manifest x=true := by
    change ((((ctrlPhase.read x).toNat==1) || ((ctrlPhase.read x).toNat==2)) &&
      decide ((ctrlOp.read x).toNat<manifest.opcodes))=true
    simp [hp,ho]
    decide
  cases h : BStarLongPublication.decode (sourceDescriptor.read x) <;>
    simp [oldDoor,hv,hp,ho,stage_initial,h]

def payload (x : BitVec LW) : Payload := ⟨0,BitVec.ofNat 9 stageOp,0,0,BitVec.ofNat 34 (argument x)⟩

theorem issued_descriptor (x : BitVec LW) :
    BStarLongPublication.decode (BitVec.ofNat 7 ((payload x).argument.toNat/2^18)) =
      BStarLongPublication.decode (sourceDescriptor.read x) := by
  change BStarLongPublication.decode (BitVec.ofNat 7 ((BitVec.ofNat 34 (argument x)).toNat/2^18)) = _
  rw [(argument_split x).1]
  have H : BitVec.ofNat 7 (sourceDescriptor.read x).toNat=sourceDescriptor.read x := by simp
  rw [H]

theorem bound_forward_exact (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (d : Desc)
    (hd : BStarLongPublication.decode (sourceDescriptor.read x)=some d) :
    bind g j (.forward (payload x))=.forward (payload x) := by
  have H : BStarLongPublication.decode (BitVec.ofNat 7 ((payload x).argument.toNat / 2^18)) = some d :=
    (issued_descriptor x).trans hd
  have W : forwardWidth stageOp (payload x).argument.toNat=some 25 := by
    simp [forwardWidth,stageOp,admit,bitOp,acquire,copyLoad,descOK,H]
  have C : (payload x).argument.toNat < 2^25 := by
    have I : argument x < 2^34 := Nat.lt_trans (argument_bound x) (by decide)
    simpa [payload,Nat.mod_eq_of_lt I] using argument_bound x
  have P : cropped (payload x) 25=payload x := by
    simp [cropped,low,Nat.mod_eq_of_lt C]
  change (if (payload x).fault != 0 || decide (stageOp≥413) ||
      (payload x).outcome != 0 || !(if gate stageOp j g then
        decide (1≤(payload x).race.toNat ∧ (payload x).race.toNat≤5)
        else (payload x).race.toNat==0) then fault false
      else match forwardWidth stageOp (payload x).argument.toNat with
        | none => fault false
        | some w => .forward (cropped (payload x) w)) = _
  have Hg : gate stageOp j g=false := by simp [gate,stageOp,admit,bitOp]
  rw [W]
  simp [Hg,payload]
  exact congrArg Token.forward P

theorem stage_live_of_source_descriptor (g : LongGeometry) (j : Fin 11)
    (raw source : BitVec LW) (b : Fin 3) (d : Desc)
    (hd : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (hc : d.old=b) :
    BStarStageLive.StageLiveOwned g j raw b (payload source) := by
  intro _ _ _ _ d' h _
  rw [issued_descriptor,hd] at h
  exact (Option.some.inj h).symm ▸ hc

theorem stage_selected_issue (g : Pair LongGeometry) (x : Pair (BitVec LW)) (d : Desc)
    (hh : g.2.axes.h6=true)
    (hp : (ctrlPhase.read x.2).toNat=1) (ho : (ctrlOp.read x.2).toNat=stageOp)
    (hd : BStarLongPublication.decode (sourceDescriptor.read x.2)=some d) :
    let o : CmdOffer := (doorClaim,.door (bind g.2 0 (atSite x.2 0)))
    o∈actualOffers g x ∧ (selected g x o).work=[(true,issued stageOp (argument x.2))] ∧
      (selected g x o).publications=[] := by
  refine ⟨actual_door g x hh,?_⟩
  simp [selected,doorClaim,atOld,R,BStarTrace.lane,stage_door _ _ hp ho,hd]

theorem stage_written (x : BitVec LW) :
    let y := (issued stageOp (argument x)).apply x
    (ctrlPhase.read y).toNat=2 ∧ ctrlOp.read y=ctrlOp.read x ∧
    atSite y 0=.forward (payload x) := by
  simp only [issued,stageOp,show (408==1)=false by decide,Bool.false_eq_true,if_false,
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

end L4.BStarStageIssue
