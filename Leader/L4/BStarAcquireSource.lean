import Leader.L4.BStarFinalCandidate

/-! Exact interface between the physical ACQUIRE payload and the source
file. A syntactically valid return is not evidence of a fresh acquisition. -/
namespace L4.BStarAcquireSource
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongCommand
open BStarLongClaims BStarLongDoor BStarLongGrant BStarLongWork BStarCommitIssue

def initPayload : Payload := ⟨0,5,0,0,BitVec.ofNat 34 (2^33)⟩

theorem acquire_issue (x : BitVec LW) (k : Token)
    (hp : (ctrlPhase.read x).toNat=1) (ho : (ctrlOp.read x).toNat=acquire) :
    oldDoor x k=.write (issued acquire (2^33)) := by
  have hv : LongDoorGuard.valid manifest x=true := by
    change ((((ctrlPhase.read x).toNat==1) || ((ctrlPhase.read x).toNat==2)) &&
      decide ((ctrlOp.read x).toNat<manifest.opcodes))=true
    simp [hp,ho]
    decide
  simp [oldDoor,hv,hp,ho,initial]

theorem acquire_issued_token (x : BitVec LW) :
    atSite ((issued acquire (2^33)).apply x) 0=.forward initPayload := by
  simp only [issued,acquire,show (5==1)=false by decide,Bool.false_eq_true,if_false,
    Patch.compose_apply]
  exact atSite_after _ _ _

def capturePatch (p : Payload) : Patch LW :=
  (schedule 6).compose ((captures.assign (BitVec.ofNat 6 (p.argument.toNat/2^27))).compose
    (capturedHeaders.assign (BitVec.ofNat 27 p.argument.toNat)))

theorem acquire_receipt (x : BitVec LW) (p : Payload)
    (hp : (ctrlPhase.read x).toNat=2) (ho : (ctrlOp.read x).toNat=acquire)
    (hf : p.fault=0) (hr : p.opcode.toNat=acquire) (hs : p.outcome=0) :
    oldDoor x (.reply p)=.write (capturePatch p) := by
  have hv : LongDoorGuard.valid manifest x=true := by
    change ((((ctrlPhase.read x).toNat==1) || ((ctrlPhase.read x).toNat==2)) &&
      decide ((ctrlOp.read x).toNat<manifest.opcodes))=true
    simp [hp,ho]
    decide
  simp [oldDoor,hv,hp,ho,hf,hr,hs,arithKind,afterReply,admit,acquire,capturePatch]

theorem capture_file (x : BitVec LW) (p : Payload) :
    let y := (capturePatch p).apply x
    captures.read y=BitVec.ofNat 6 (p.argument.toNat/2^27) ∧
    capturedHeaders.read y=BitVec.ofNat 27 p.argument.toNat := by
  simp only [capturePatch,Patch.compose_apply]
  rw [Field.read_other_assign captures capturedHeaders _ _ (by decide),
    Field.read_assign,Field.read_assign]
  exact ⟨rfl,rfl⟩

theorem selected_acquire_receipt (g : Pair LongGeometry) (x : Pair (BitVec LW)) (p : Payload)
    (hh : g.2.axes.h6=true)
    (hp : (ctrlPhase.read x.2).toNat=2) (ho : (ctrlOp.read x.2).toNat=acquire)
    (hk : bind g.2 0 (atSite x.2 0)=.reply p)
    (hf : p.fault=0) (hr : p.opcode.toNat=acquire) (hs : p.outcome=0) :
    let o : CmdOffer := (doorClaim,.door (.reply p))
    o∈BStarLongEvents.actualOffers g x ∧ (selected g x o).work=[(true,capturePatch p)] := by
  refine ⟨hk ▸ actual_door g x hh,?_⟩
  simp [selected,doorClaim,R,BStarLongWork.atOld,BStarTrace.lane,
    acquire_receipt _ _ hp ho hf hr hs]

theorem center_read (x : BitVec LW) :
    (capturedSelector 1).read x=(captures.read x).extractLsb' 2 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have H : 2+i<6 := by omega
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,
    captures,capturedSelector]
  have E : 2189+2*(2-(1 : Fin 3).val)+i=2189+(2+i) := by omega
  rw [E]
  simp [H]

/-- Even an inherited matching receipt installs exactly these bits; the
theorem itself does not confer authority on the receipt. -/
theorem receipt_center (x : BitVec LW) (p : Payload) :
    (capturedSelector 1).read ((capturePatch p).apply x) =
      (BitVec.ofNat 6 (p.argument.toNat/2^27)).extractLsb' 2 2 := by
  rw [center_read,(capture_file x p).1]

/-- Source-file preservation is sufficient for the descriptor to encode the
same center bank as the successful capture. -/
theorem final_center_of_retained_capture (x y : BitVec LW) (p : Payload)
    (same : captures.read y=captures.read ((capturePatch p).apply x))
    (s : Fin 3)
    (bits : (BitVec.ofNat 6 (p.argument.toNat/2^27)).extractLsb' 2 2=BitVec.ofNat 2 s.val) :
    ∃ d, BStarLongPublication.decode
      (sourceDescriptor.read ((BStarLongArithmetic.acceptFile y BStarFinalCandidate.lastOp p).apply y)) =
      some d ∧ d.old=s := by
  have c : (capturedSelector 1).read y=BitVec.ofNat 2 s.val := by
    rw [center_read,same,(capture_file x p).1,bits]
  have c' : ((capturedSelector 1).read y).toNat=s.val := by
    rw [c,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_trans s.isLt (by decide : 3<2^2))]
  have h : ((capturedSelector 1).read y).toNat<3 := c' ▸ s.isLt
  refine ⟨BStarFinalCandidate.finalDesc y h,?_,Fin.ext c'⟩
  rw [(BStarFinalCandidate.final_fields y p h).1,BStarFinalCandidate.decode_final]

end L4.BStarAcquireSource
