import Leader.L4.BStarAcquireDoorHistory
import Leader.L4.BStarCommitLineage

namespace L4.BStarResetTaggedRows
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongWork BStarLongEvents BStarLongCommandData
open BStarAcquireReturn BStarLongRouting BStarLongLiteral

def resetPayload (op : Nat) : Payload := ⟨0, BitVec.ofNat 9 op, 0, 0, 0⟩

def ResetF (p : Payload) : Prop :=
  p=resetPayload 0 ∨ p=resetPayload 1 ∨ p=resetPayload 2 ∨ p=failedPayload

theorem bind_reset (g : LongGeometry) (j : Fin 11) (p : Payload) (h : ResetF p) :
    bind g j (.forward p)=.forward p := by
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [resetPayload, failedPayload, BStarLongCommand.bind, gate, admit, bitOp, forwardWidth,
          arithKind, cropped, low, fault, acquire, copyLoad, stageOp, sealOp, commitOp]

theorem bind_finish (g : LongGeometry) (j : Fin 11) (p : Payload) (h : ResetF p) :
    bind g j (finish p)=finish p ∧ ∃ q, finish p=.reply q := by
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [resetPayload, failedPayload, BStarLongCommand.bind, finish, replyWidth, arithKind,
      cropped, low, fault, acquire, admit, bitOp, sealOp]

theorem depart_reset (g : LongGeometry) (j : Fin 11) (p : Payload) (h : ResetF p) :
    depart g j p=some p := by
  rcases h with rfl|rfl|rfl|rfl <;> simp [resetPayload, failedPayload, depart, gate, admit, bitOp]

theorem arrive_reset (g : LongGeometry) (j : Fin 11) (p : Payload) (h : ResetF p) :
    arrive g j p=.forward p := by
  rcases h with rfl|rfl|rfl|rfl <;> simp [resetPayload, failedPayload, arrive, gate, admit, bitOp]

theorem check_reset (g : Pair LongGeometry) (old : At Sheet → BStarLongPackets.Lane)
    (C : CommandClaim) (p : Payload) (h : ResetF p) :
    checkOffer g old (C,.advance p)=.advance p := by
  rcases h with rfl|rfl|rfl|rfl <;> simp [resetPayload, failedPayload,checkOffer,checkFence]

theorem gated_reset (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (hc : C∈orderedCommands g)
    (nd : (C.kind==.door)=false)
    (hs : readK x C.source=.forward p) (hp : ResetF p) :
    (C,.advance p)∈gated g x := by
  apply (gated_mem g x C _).mpr
  refine ⟨hc,?_⟩
  symm
  unfold gatedAt classifyOld
  change checkOffer g (BStarLongPrep.view x) (C,
    classify C (geometry g C.source.side)
      (bind (geometry g C.source.side) C.source.occurrence (readK x C.source))
      ((C.destination.map (fun a => bind (geometry g a.side)
        a.occurrence (readK x a))).getD .empty)) = _
  rw [hs, bind_reset _ _ _ hp]
  simp [classify,nd,depart_reset _ _ _ hp, check_reset _ _ _ _ hp]

theorem actual_reset (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (hc : C∈orderedCommands g)
    (nd : (C.kind==.door)=false)
    (hs : readK x C.source=.forward p) (hp : ResetF p) :
    let q := if C.source∈(round g x).faults then failedPayload else p
    (C,.advance q)∈actualOffers g x ∧ ResetF q := by
  let q := if C.source∈(round g x).faults then failedPayload else p
  change (C,.advance q)∈actualOffers g x ∧ ResetF q
  have hq : ResetF q := by
    unfold q
    split
    · exact .inr (.inr (.inr rfl))
    · exact hp
  refine ⟨?_,hq⟩
  unfold actualOffers BStarLongGrant.run
  change (C,.advance q)∈(round g x).offered.map (BStarLongGrant.update g x (round g x).offered)
  apply List.mem_map.mpr
  refine ⟨(C,.advance q),?_,?_⟩
  · change (C,.advance q)∈(gated g x).map (cancel (round g x).faults)
    refine List.mem_map.mpr ⟨(C,.advance p),gated_reset g x C p hc nd hs hp,?_⟩
    by_cases hf : C.source∈(round g x).faults <;> simp [cancel,q,hf]
  · rcases hq with H|H|H|H <;> rw [H] <;>
      simp [BStarLongGrant.update, resetPayload, failedPayload, acquire]

theorem selected_reset (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (h : ResetF p) :
    (selected g x (C,.advance p)).k=advanceK g C p := by
  have hd : (BStarLongArithmetic.visit (geometry g C.source.side)
      C.source.occurrence (atOld x C.source) p).2=p := by
    rcases h with H|H|H|H <;> rw [H] <;>
      simp [BStarLongArithmetic.visit,BStarLongArithmetic.nodeOf, resetPayload, failedPayload]
  have ho : (BStarLongOutgoing.execute (geometry g C.source.side)
      C.source.occurrence (atOld x C.source) p).carried=.forward p := by
    rcases h with H|H|H|H <;> rw [H] <;>
      simp [BStarLongOutgoing.execute,BStarLongOutgoing.hold,resetPayload,failedPayload,
        stageOp, sealOp, commitOp]
    all_goals split <;> first | rfl | split <;> rfl
  unfold selected
  dsimp only
  rw [hd,ho]

theorem reset_terminal_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (hc : C∈orderedCommands g)
    (nd : (C.kind==.door)=false) (hd : C.destination=none)
    (hs : readK x C.source=.forward p) (hp : ResetF p) :
    let q := if C.source∈(round g x).faults then failedPayload else p
    readK (patchPair (longWork g x) x) C.source=finish q := by
  dsimp only
  obtain ⟨ha,hq⟩ := actual_reset g x C p hc nd hs hp
  exact last_selected_lands g x C (.advance _) C.source (finish _) [] [] ha
    (by rw [selected_reset _ _ _ _ hq]; simp [advanceK,hd]) (by simp)

theorem reset_link_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (d : AtK) (p : Payload) (hc : C∈orderedCommands g)
    (hd : C.destination=some d)
    (hs : readK x C.source=.forward p) (hp : ResetF p) :
    let q := if C.source∈(round g x).faults then failedPayload else p
    readK (patchPair (longWork g x) x) C.source=.trail ∧
      readK (patchPair (longWork g x) x) d=.forward q := by
  dsimp only
  have shape := link_shape g C d hc hd
  obtain ⟨ha,hq⟩ := actual_reset g x C p hc (by simp [shape.2.1]) hs hp
  have W := selected_reset g x C _ hq
  simp only [advanceK,hd,arrive_reset _ _ _ hq] at W
  constructor
  · exact last_selected_lands g x C (.advance _) C.source .trail [] [(d,.forward _)]
      ha W (by simpa using shape.1)
  · exact last_selected_lands g x C (.advance _) d (.forward _) [(C.source,.trail)] []
      ha W (by simp)

theorem reset_reverse_checked (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (d : AtK) (p : Payload) (hc : C∈orderedCommands g)
    (hd : C.destination=some d)
    (hs : readK x C.source=.trail) (ht : readK x d=finish p) (hp : ResetF p) :
    (C,.reverse (finish p))∈gated g x := by
  obtain ⟨fb,⟨q,H⟩⟩ := bind_finish (geometry g d.side) d.occurrence p hp
  apply (gated_mem g x C _).mpr
  refine ⟨hc,?_⟩
  symm
  unfold gatedAt classifyOld
  change checkOffer g (BStarLongPrep.view x) (C,
    classify C (geometry g C.source.side)
      (bind (geometry g C.source.side) C.source.occurrence (readK x C.source))
      ((C.destination.map (fun a => bind (geometry g a.side)
        a.occurrence (readK x a))).getD .empty)) = _
  rw [hd,hs]
  simp only [Option.map_some,Option.getD_some,ht,fb]
  simp [classify,(link_shape g C d hc hd).2.1,BStarLongCommand.bind,checkOffer,H]

theorem reset_reverse_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (d : AtK) (p : Payload) (hc : C∈orderedCommands g)
    (hd : C.destination=some d)
    (hs : readK x C.source=.trail) (ht : readK x d=finish p) (hp : ResetF p) :
    readK (patchPair (longWork g x) x) C.source=finish p ∧
      readK (patchPair (longWork g x) x) d=.empty := by
  have H := reset_reverse_checked g x C d p hc hd hs ht hp
  exact ⟨reverse_work g x C d _ hd (link_shape g C d hc hd).1 H,
    BStarAcquireDoorHistory.reverse_consumes g x C d _ hd H⟩

/-- On actual full production pairs the selected old reset front overwrites the
old suffix byte, even an arbitrary inherited reply. Both writes survive the
raw work, scratch and final invalid-door guard. -/
theorem reset_link_joined (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (d : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let out := Pair.map LargeSite.long (largePair b x)
    let q := if C.source∈(round g raw).faults then failedPayload else pay
    C∈orderedCommands g → C.destination=some d →
    readK raw C.source=.forward pay → ResetF pay →
    readK out C.source=.trail ∧ readK out d=.forward q := by
  dsimp only
  intro hc hd hsrc hpay
  have safe := (link_shape _ C d hc hd).2.2
  obtain ⟨H,J⟩ := reset_link_work _ _ C d pay hc hd hsrc hpay
  exact ⟨(joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source
        (fun hh hz => (safe hh hz).elim)).trans H,
      (joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x d
        (fun _ hz => .inl (BStarAcquireJoinedHop.k0_dest _ C d hc hd hz).2)).trans J⟩

theorem reset_terminal_joined (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let out := Pair.map LargeSite.long (largePair b x)
    let q := if C.source∈(round g raw).faults then failedPayload else pay
    C∈orderedCommands g → C.kind=.terminal → C.destination=none →
    C.source.occurrence.val=10 →
    readK raw C.source=.forward pay → ResetF pay → readK out C.source=finish q := by
  dsimp only
  intro hc ht hd h10 hsrc hpay
  exact (joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source
    (by intro _ hz; omega)).trans (reset_terminal_work _ _ C pay hc (by simp [ht]) hd hsrc hpay)

theorem reset_reverse_joined (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (d : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let out := Pair.map LargeSite.long (largePair b x)
    C∈orderedCommands g → C.destination=some d →
    readK raw C.source=.trail → readK raw d=finish pay → ResetF pay →
    readK out C.source=finish pay ∧ readK out d=.empty := by
  dsimp only
  intro hc hd hsrc hdst hpay
  have safe := (link_shape _ C d hc hd).2.2
  obtain ⟨H,J⟩ := reset_reverse_work _ _ C d pay hc hd hsrc hdst hpay
  exact ⟨(joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source
        (fun hh hz => (safe hh hz).elim)).trans H,
      (joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x d
        (fun _ hz => .inl (BStarAcquireJoinedHop.k0_dest _ C d hc hd hz).2)).trans J⟩

open BStarLongDoor

/-- A genuine valid ISSUE is independent of inherited old K0 bytes. -/
theorem reset_issue_decision (x : BitVec LW) (t : Token) (op : Nat)
    (hv : LongDoorGuard.valid manifest x=true)
    (phase : (ctrlPhase.read x).toNat=1) (tag : (ctrlOp.read x).toNat=op)
    (small : op=0 ∨ op=1 ∨ op=2) :
    oldDoor x t=.write (issued op 0) := by
  rcases small with rfl|rfl|rfl <;>
    simp [oldDoor,hv,phase,tag,initial,arithKind,acquire,copyLoad,stageOp,sealOp,commitOp]

/-- Neither a trail followed by a trail nor a trail followed by the
authenticated outward front can be stolen by a reverse offer. -/
theorem solid_prefix_holds (C : CommandClaim) (g : LongGeometry) (p : Payload)
    (link : C.kind=.link) :
    classify C g .trail .trail=.hold ∧
      classify C g .trail (.forward p)=.hold := by simp [classify,link]

/-- Includes canonical terminal fault returns: they really unwind the
trail, but schedule restart rather than count as successful RREL. -/
theorem reset_fault_door (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (hh : g.2.axes.h6=true) (hv : LongDoorGuard.valid manifest raw.2=true)
    (phase : (ctrlPhase.read raw.2).toNat=2)
    (k0 : atSite raw.2 0=finish failedPayload) :
    (actualOffers g raw).filter BStarDoorUnique.doorAction =
      [(BStarCommitIssue.doorClaim,.door (finish failedPayload))] ∧
    oldDoor raw.2 (finish failedPayload)=.write faultRestart := by
  constructor
  · have H := BStarDoorUnique.actual_door_singleton g raw hh
    rw [k0,(bind_finish _ _ _ (.inr (.inr (.inr rfl)))).1] at H
    exact H
  · simp [oldDoor,hv,phase,finish,failedPayload,fault]

end L4.BStarResetTaggedRows
