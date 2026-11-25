import Leader.L4.BStarStageSourceFrame
import Leader.L4.BStarAcquireSource

namespace L4.BStarCaptureDoorHistory
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongClaims
open BStarLongWork BStarLongTransport BStarLongCommand BStarLongDoor BStarLongEvents
open BStarAcquireFrame BStarH6WordChart
open BStarCommitIssue

/-- A legal issue, an in-flight wait or a successful matching receipt
after ACQUIRE is a normal capture-preserving old source decision.
A restart is not admitted. This includes the final arithmetic receipt. -/
theorem normal_after_acquire (x : BitVec LW) (k : Token) (op : Nat)
    (V : LongDoorGuard.valid manifest x=true)
    (O : (ctrlOp.read x).toNat=op) (lo : 6≤op)
    (good :
      ((ctrlPhase.read x).toNat=1 ∧ ∃ a, initial op x=some a) ∨
      ((ctrlPhase.read x).toNat=2 ∧
        (k=.trail ∨ (∃ q,k=.forward q) ∨
          ∃ f,k=.reply f ∧ f.fault=0 ∧ f.opcode.toNat=op ∧
            (if (arithKind op).isSome then BStarLongArithmetic.acceptFile x op f
              else afterReply op f x) ≠ faultRestart))) :
    Normal x (oldDoor x k) := by
  rcases good with ⟨P,a,A⟩|⟨P,T⟩
  · rw [show oldDoor x k=.write (issued op a) by simp [oldDoor,V,O,P,A]]
    exact .issue _ _ (by omega)
  rcases T with rfl|⟨q,rfl⟩|⟨f,rfl,F,E,H⟩
  · rw [wait_holds_trail x V P]
    exact .hold
  · rw [wait_holds_forward x q V P]
    exact .hold
  · cases A : (arithKind op).isSome with
    | false =>
      have D : oldDoor x (.reply f)=.write (afterReply op f x) := by
        simp [oldDoor,V,O,P,F,E,A]
      rw [D]
      exact .reply _ _ (by unfold acquire; omega) (by simpa [A] using H)
    | true =>
      have D : oldDoor x (.reply f)=.acceptTour op f := by simp [oldDoor,V,O,P,F,E,A]
      rw [D]
      exact .tour _ _ (by simpa [A] using H)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "P" => production k₁ k₂ t₂ J₁ J₂ r c p c₁

private theorem joined_right_field (x : Pair (LargeSite P))
    (V : LongDoorGuard.valid manifest x.2.long=true)
    {m : Nat} (field : Field LW m) (hi : field.offset+m≤2195) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    field.read (largePair B x).2.long=field.read (patchPair (longWork g raw) raw).2 := by
  dsimp only
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  change field.read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
    ((longWork g raw).2.compose (longScratch g raw).2)).apply raw.2)=_
  have VV : LongDoorGuard.valid manifest raw.2=true := V
  simp only [LongDoorGuard.guard,VV,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false,
    Patch.compose_apply]
  exact Field.read_other_assign field offField _ _ (.inl (Nat.le_trans hi (by decide)))

/-- Project both packed capture fields across the actual joined right
source door; no condition on other endpoints' rows is needed. -/
theorem joined_normal (x : Pair (LargeSite P))
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (N : Normal x.2.long (oldDoor x.2.long
      (bind (longGeometry B x.2) 0 (atSite x.2.long 0)))) :
    capturedHeaders.read (largePair B x).2.long=capturedHeaders.read x.2.long ∧
      captures.read (largePair B x).2.long=captures.read x.2.long := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let k := bind g.2 0 (atSite raw.2 0)
  have D : ∀ (C : CommandClaim) (t : Token), (C,.door t)∈actualOffers g raw →
      C=doorClaim ∧ t=k := by
    intro C t M
    have F : (C,.door t)∈(actualOffers g raw).filter BStarDoorUnique.doorAction :=
      List.mem_filter.mpr ⟨M,rfl⟩
    rw [BStarDoorUnique.actual_door_singleton g raw hdr] at F
    obtain ⟨E,T⟩ := Prod.mk.inj (List.mem_singleton.mp F)
    exact ⟨E,Offer.door.inj T⟩
  have H : (lane true g).axes.h6=true := hdr
  have Q := long_work_preserves g raw true H (by
    intro C t M _
    obtain ⟨rfl,rfl⟩ := D C t M
    change Normal x.2.long (oldDoor x.2.long k)
    exact N)
  rw [joined_right_field hp x V capturedHeaders (by decide),
    joined_right_field hp x V captures (by decide)]
  exact Q

open BStarAcquireSource in
private theorem capture_over (f : Payload) (y : BitVec LW) :
    capturedHeaders.read ((capturePatch f).apply y)=BitVec.ofNat 27 f.argument.toNat ∧
      captures.read ((capturePatch f).apply y)=BitVec.ofNat 6 (f.argument.toNat/2^27) :=
  ⟨(capture_file y f).2,(capture_file y f).1⟩

/-- Literal joined successful ACQUIRE receipt installs both packed
fields, independently of concurrent old-pair rows. This is byte
provenance, not authentication of where the matching reply arose. -/
theorem joined_capture (x : Pair (LargeSite P)) (f : Payload)
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (ph : (ctrlPhase.read x.2.long).toNat=2)
    (op : (ctrlOp.read x.2.long).toNat=acquire)
    (R : bind (longGeometry B x.2) 0 (atSite x.2.long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=acquire) (S : f.outcome=0) :
    capturedHeaders.read (largePair B x).2.long=BitVec.ofNat 27 f.argument.toNat ∧
      captures.read (largePair B x).2.long=BitVec.ofNat 6 (f.argument.toNat/2^27) := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have RR : bind g.2 0 (atSite raw.2 0)=.reply f := R
  have work := (BStarAcquireSource.selected_acquire_receipt g raw f hdr ph op RR F O S).2
  have W : (selected g raw (doorClaim,.door (bind g.2 0 (atSite raw.2 0)))).work=
      [(true,BStarAcquireSource.capturePatch f)] := by rw [RR]; exact work
  constructor
  · rw [joined_right_field hp x V capturedHeaders (by decide)]
    exact BStarStageSourceFrame.door_field capturedHeaders (by decide) (by decide) g raw hdr _ W
      (fun _ => BitVec.ofNat 27 f.argument.toNat) (fun y => (capture_over f y).1)
  · rw [joined_right_field hp x V captures (by decide)]
    exact BStarStageSourceFrame.door_field captures (by decide) (by decide) g raw hdr _ W
      (fun _ => BitVec.ofNat 6 (f.argument.toNat/2^27)) (fun y => (capture_over f y).2)

local notation "X" => Fin n → LargeSite P
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Scope for one actual mark during the retained-capture interval.
Foreign marks need only old H6; an entering mark needs a normal
selected door decision, not a claim about successor fields. -/
def LiveMark (x : X) (i e : Fin n) : Prop :=
  oldH6 B x i=true ∧ (rightNeighbor e=i →
    let y := (x i).long
    LongDoorGuard.valid manifest y=true ∧
      Normal y (oldDoor y (bind (longGeometry B (x i)) 0 (atSite y 0))))

theorem mark_capture_hold (x : X) (i e : Fin n) (sep : e≠rightNeighbor e)
    (H : LiveMark hp x i e) :
    capturedHeaders.read (step x e i).long=capturedHeaders.read (x i).long ∧
      captures.read (step x e i).long=captures.read (x i).long := by
  by_cases own : rightNeighbor e=i
  · subst i
    have N := H.2 rfl
    let pair := (x e,x (rightNeighbor e))
    have HH : (oldHeaders B pair.2).h6=true := H.1
    have T := joined_normal hp pair HH N.1 N.2
    simpa only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true] using T
  by_cases E : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have HH : (oldHeaders B pair.1).h6=true := H.1
    simp only [AllSizeS1Geometry.step,if_true]
    exact ⟨BStarStageSourceFrame.left_foreign_field hp pair HH capturedHeaders (by decide) (by decide),
      BStarStageSourceFrame.left_foreign_field hp pair HH captures (by decide) (by decide)⟩
  · simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm own),and_self]

/-- Packed ACQUIRE captures and their center read survive every mixed
finite word of actual interleaved legal source and foreign marks. -/
theorem word_capture_hold (x : X) (i : Fin n) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (live : ∀ pre e tail,w=pre++e::tail → LiveMark hp (run x pre) i e) :
    let y := run x w
    capturedHeaders.read (y i).long=capturedHeaders.read (x i).long ∧
      captures.read (y i).long=captures.read (x i).long ∧
      (capturedSelector 1).read (y i).long=(capturedSelector 1).read (x i).long := by
  have W : capturedHeaders.read ((run x w) i).long=capturedHeaders.read (x i).long ∧
      captures.read ((run x w) i).long=captures.read (x i).long := by
    induction w generalizing x with
    | nil => exact ⟨rfl,rfl⟩
    | cons e w ih =>
      have H := mark_capture_hold hp x i e (sep e) (live [] e w rfl)
      have T := ih (step x e) (fun a f b E => live (e::a) f b (congrArg (List.cons e) E))
      exact ⟨T.1.trans H.1,T.2.trans H.2⟩
  refine ⟨W.1,W.2,?_⟩
  let y : BitVec LW := ((run x w) i).long
  let z : BitVec LW := (x i).long
  change (capturedSelector 1).read y=(capturedSelector 1).read z
  have E : captures.read y=captures.read z := W.2
  rw [BStarAcquireSource.center_read y,BStarAcquireSource.center_read z,E]

end L4.BStarCaptureDoorHistory
