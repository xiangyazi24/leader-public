import Leader.L4.BStarJoinedControllerReturn
import Leader.L4.BStarAcquireDoorHistory

namespace L4.BStarDirtyReplySweep
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongWork BStarLongEvents BStarLongCommandData
open BStarAcquireReturn BStarAcquireDoorHistory BStarLongLiteral

theorem bind_reply_class (g : LongGeometry) (j : Fin 11) (q : Payload) :
    ∃ f, bind g j (.reply q)=.reply f := by
  simp only [BStarLongCommand.bind]
  split
  · exact ⟨_,rfl⟩
  · split <;> exact ⟨_,rfl⟩

/-- Reverse priority at an arbitrary dirty predecessor, not just a
generated T. The old reply is consumed and its bound form moves toward
the source. A forward predecessor is the exact obstruction. -/
theorem reverse_predecessor (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (d : AtK) (q : Payload)
    (hc : C∈orderedCommands g) (hd : C.destination=some d)
    (noF : ∀ f, readK x C.source≠.forward f)
    (R : readK x d=.reply q) :
    ∃ f, bind (geometry g d.side) d.occurrence (.reply q)=.reply f ∧
      (C,.reverse (.reply f))∈gated g x := by
  obtain ⟨f,B⟩ := bind_reply_class (geometry g d.side) d.occurrence q
  refine ⟨f,B,(gated_mem g x C _).mpr ⟨hc,?_⟩⟩
  symm
  unfold gatedAt classifyOld
  change checkOffer g (BStarLongPrep.view x) (C,
    classify C (geometry g C.source.side)
      (bind (geometry g C.source.side) C.source.occurrence (readK x C.source))
      ((C.destination.map (fun a => bind (geometry g a.side)
        a.occurrence (readK x a))).getD .empty)) = _
  rw [hd]
  simp only [Option.map_some,Option.getD_some,R,B]
  have L := (link_shape g C d hc hd).2.1
  cases T : readK x C.source with
  | empty => simp [checkOffer,classify,L,BStarLongCommand.bind]
  | trail => simp [checkOffer,classify,L,BStarLongCommand.bind]
  | forward p => exact (noF p T).elim
  | reply p =>
    obtain ⟨f',P⟩ := bind_reply_class (geometry g C.source.side) C.source.occurrence p
    simp [P,checkOffer,classify,L]

theorem dirty_reverse_joined (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (d : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let out := Pair.map LargeSite.long (largePair b x)
    C∈orderedCommands g → C.destination=some d →
    (∀ f, readK raw C.source≠.forward f) → readK raw d=.reply pay →
    ∃ f, readK out C.source=.reply f ∧ readK out d=.empty := by
  dsimp only
  intro hc hd noF R
  obtain ⟨f,_,G⟩ := reverse_predecessor _ _ C d pay hc hd noF R
  have S := link_shape _ C d hc hd
  refine ⟨f,reverse_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C d _ hd S.1
    (fun a b => (S.2.2 a b).elim) G,?_⟩
  exact (joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x d (fun _ hz =>
    .inl (BStarAcquireJoinedHop.k0_dest _ C d hc hd hz).2)).trans
      (reverse_consumes _ _ C d _ hd G)

theorem bind_forward_class (g : LongGeometry) (j : Fin 11) (q : Payload) :
    ∃ f, bind g j (.forward q)=.forward f := by
  simp only [BStarLongCommand.bind]
  repeat' first | split
  all_goals exact ⟨_,rfl⟩

open BStarLongDoor BStarAcquireWaitControl BStarCommitIssue

/-- With an arbitrary old F/T, valid WAIT cannot restart or issue on the
own incoming edge. Its controller fields persist even if normalization
rewrites a malformed F's payload to the canonical fault. -/
theorem arbitrary_wait_hold_control (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let old : BitVec LW := x.2.long
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest old=true →
    (ctrlPhase.read old).toNat=2 →
    (atSite old 0=.trail ∨ ∃ f, atSite old 0=.forward f) →
    control (largePair b x).2.long=control old := by
  dsimp only
  intro hh V ph tag
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  exact (joined_control k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x V).trans
    (door_projection g raw hh [] (f:=id) (by
      have H : oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))=.hold := by
        rcases tag with T|⟨f,F⟩
        · rw [show atSite raw.2 0=.trail from T]
          exact wait_holds_trail _ V ph
        · obtain ⟨f',B⟩ := bind_forward_class g.2 0 f
          rw [show atSite raw.2 0=.forward f from F,B]
          exact wait_holds_forward _ _ V ph
      change (match oldDoor raw.2 (bind g.2 0 (atSite raw.2 0)) with
      | .hold => (⟨[],[],[]⟩ : Selected)
      | .write q => ⟨[],[(true,q)],[]⟩
      | .acceptTour op p => ⟨[],[(true,BStarLongArithmetic.acceptFile raw.2 op p)],[]⟩).work=[]
      rw [H]) (fun _ => rfl))

/-- On a valid WAIT with any raw reply, the selected old door consumes its
bound reply (even a canonical fault from malformed bytes), clears K0, and
does not issue on the same mark. -/
theorem wait_raw_reply (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let old : BitVec LW := x.2.long
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest old=true →
    (ctrlPhase.read old).toNat=2 → atSite old 0=.reply f →
    ∃ op, (op=0 ∨ ((ctrlOp.read old).toNat<op ∧ op<413)) ∧
      BStarResetControllerEntry.snapshot (largePair b x).2.long=((.empty,1),BitVec.ofNat 9 op) := by
  dsimp only
  intro hh V P D
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  obtain ⟨f',B⟩ := bind_reply_class g.2 0 f
  have H : bind g.2 0 (atSite x.2.long 0)=.reply f' := by
    rw [D]
    exact B
  exact BStarJoinedControllerReturn.joined_reply k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x f' hh V P H

end L4.BStarDirtyReplySweep
