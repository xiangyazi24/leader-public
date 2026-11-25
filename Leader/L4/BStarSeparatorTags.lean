import Leader.L4.BStarAcquireReturn
import Leader.L4.BStarClearanceCommandFrame
import Leader.L4.BStarClearanceGate

/-! Arbitrary old F/D on the long separator, including canonical faults.
The classifier reads bound old tokens; a terminal F can still park. -/
namespace L4.BStarSeparatorTags
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongLiteral BStarLongTransport
open BStarLongWork BStarLongEvents

theorem canonical_forward (g : LongGeometry) (j : Fin 11) :
    BStarLongCommand.bind g j (fault false)=fault false := rfl

theorem canonical_reply (g : LongGeometry) (j : Fin 11) :
    BStarLongCommand.bind g j (fault true)=fault true := rfl

/-- Evaluate the two independent HOLD gates for any bound forward,
including a terminal. The second gate runs only after race departure. -/
theorem forward_gated_hold_iff (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (nd : c.kind≠.door)
    (old : bound g (readK x) c.source=.forward p) :
    gatedAt g x c=.hold ↔
      depart (geometry g c.source.side) c.source.occurrence p=none ∨
        ∃ q, depart (geometry g c.source.side) c.source.occurrence p=some q ∧
          checkFence g (BStarLongPrep.view x) c.source q=.hold := by
  unfold gatedAt classifyOld
  change checkOffer g (BStarLongPrep.view x)
    (c,classify c _ (bound g (readK x) c.source) _)=.hold ↔ _
  rw [old]
  simp only [classify,beq_iff_eq,nd,if_false]
  cases H : depart (geometry g c.source.side) c.source.occurrence p with
  | none => simp [checkOffer]
  | some q =>
    cases E : checkFence g (BStarLongPrep.view x) c.source q <;> simp [checkOffer,E]

/-- A parked forward does not consume any command slot. Old normalization
or a literal race observation may still rewrite its original bytes. -/
theorem forward_hold_selected (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (hm : c∈orderedCommands g) (nd : c.kind≠.door)
    (old : bound g (readK x) c.source=.forward p)
    (held : depart (geometry g c.source.side) c.source.occurrence p=none ∨
      ∃ q, depart (geometry g c.source.side) c.source.occurrence p=some q ∧
        checkFence g (BStarLongPrep.view x) c.source q=.hold) :
    (c,.hold)∈actualOffers g x ∧ (selected g x (c,.hold)).k=[] := by
  have H := (forward_gated_hold_iff g x c p nd old).mpr held
  have M : (c,.hold)∈gated g x := (gated_mem g x c _).mpr ⟨hm,H.symm⟩
  refine ⟨?_,rfl⟩
  unfold actualOffers BStarLongGrant.run round
  refine List.mem_map.mpr ⟨(c,.hold),List.mem_map.mpr ⟨(c,.hold),M,rfl⟩,?_⟩
  unfold BStarLongGrant.update
  dsimp only
  split <;> rfl

/-- A canonical fault forward is not a gate or FENCE hold. Prep
cancellation cannot change its canonical failure payload. -/
theorem canonical_fault_selected (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (hm : c∈orderedCommands g) (nd : c.kind≠.door)
    (old : bound g (readK x) c.source=fault false) :
    (c,.advance failedPayload)∈actualOffers g x := by
  have H : gatedAt g x c=.advance failedPayload := by
    unfold gatedAt classifyOld
    change checkOffer g (BStarLongPrep.view x)
      (c,classify c _ (bound g (readK x) c.source) _)=_
    rw [old,←failedPayload_canonical]
    simp [classify,nd,depart,checkOffer,checkFence,failedPayload]
  have M : (c,.advance failedPayload)∈gated g x := (gated_mem g x c _).mpr ⟨hm,H.symm⟩
  unfold actualOffers BStarLongGrant.run round
  refine List.mem_map.mpr ⟨(c,.advance failedPayload),List.mem_map.mpr ⟨(c,.advance failedPayload),M,?_⟩,?_⟩
  · unfold cancel
    dsimp only
    split <;> rfl
  · unfold BStarLongGrant.update
    dsimp only
    split
    · simp [failedPayload,acquire]
    · rfl

/-- A quiet old source takes any bound D on a selected link,
with no healthy-opcode, OK, or canonical-input assumption. -/
theorem reply_selected (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK) (q : Payload)
    (hm : c∈orderedCommands g) (hd : c.destination=some a)
    (source : BStarResetQuiet.quiet (bound g (readK x) c.source))
    (dest : bound g (readK x) a=.reply q) :
    (c,.reverse (.reply q))∈actualOffers g x := by
  have lk := (BStarAcquireReturn.link_shape g c a hm hd).2.1
  have H : gatedAt g x c=.reverse (.reply q) := by
    unfold gatedAt classifyOld
    change checkOffer g (BStarLongPrep.view x) (c,classify c _
      (bound g (readK x) c.source) ((c.destination.map (bound g (readK x))).getD .empty))=_
    rcases source with E|E <;> simp [E,hd,dest,lk,classify,checkOffer]
  have M := (gated_mem g x c _).mpr ⟨hm,H.symm⟩
  unfold actualOffers BStarLongGrant.run round
  refine List.mem_map.mpr ⟨(c,.reverse (.reply q)),List.mem_map.mpr ⟨_,M,rfl⟩,?_⟩
  unfold BStarLongGrant.update
  dsimp only
  split <;> rfl

private theorem promote_advance (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (m : (c,.advance p)∈gated g x) :
    ∃ q, (c,.advance q)∈actualOffers g x := by
  let d := round g x
  let v := cancel d.faults (c,.advance p)
  have V : v∈d.offered := List.mem_map.mpr ⟨_,m,rfl⟩
  let z := BStarLongGrant.update g x d.offered v
  have Z : z∈actualOffers g x := List.mem_map.mpr ⟨v,V,rfl⟩
  have P (q : Payload) : ∃ w, BStarLongGrant.update g x d.offered (c,.advance q)=(c,.advance w) := by
    unfold BStarLongGrant.update
    dsimp only
    split
    · split <;> exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
  have E : ∃ q, v=(c,.advance q) := by
    unfold v cancel
    dsimp only
    split <;> exact ⟨_,rfl⟩
  obtain ⟨q,H⟩ := E
  obtain ⟨w,T⟩ := P q
  exact ⟨w,(show z=(c,.advance w) by unfold z; rw [H,T]) ▸ Z⟩

/-- Every bound old F on a selected non-door link or terminal either
stays held by race/FENCE or issues an actual advance (possibly a
canonical fault after arbitration). -/
theorem forward_mark (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (hm : c∈orderedCommands g) (nd : c.kind≠.door)
    (old : bound g (readK x) c.source=.forward p) :
    (c,.hold)∈actualOffers g x ∨ ∃ q, (c,.advance q)∈actualOffers g x := by
  have G : gatedAt g x c=.hold ∨ ∃ q, gatedAt g x c=.advance q := by
    unfold gatedAt classifyOld
    change checkOffer g (BStarLongPrep.view x)
      (c,classify c _ (bound g (readK x) c.source) _)=.hold ∨
      ∃ q, checkOffer g (BStarLongPrep.view x)
        (c,classify c _ (bound g (readK x) c.source) _)=.advance q
    rw [old]
    simp only [classify,beq_iff_eq,nd,if_false]
    cases H : depart (geometry g c.source.side) c.source.occurrence p with
    | none => exact .inl rfl
    | some q =>
      cases E : checkFence g (BStarLongPrep.view x) c.source q
      · exact .inr ⟨q,by simp [checkOffer,E]⟩
      · exact .inl (by simp [checkOffer,E])
      · exact .inr ⟨failedPayload,by simp [checkOffer,E]⟩
  rcases G with H|⟨q,H⟩
  · exact .inl (forward_hold_selected g x c p hm nd old ((forward_gated_hold_iff g x c p nd old).mp H)).1
  · exact .inr (promote_advance g x c q ((gated_mem g x c _).mpr ⟨hm,H.symm⟩))

open BStarLongRouting BStarResetQuiet

/-- A selected arbitrary reverse D lands exactly at its prior
source, and clears the old destination, including a fault D. -/
theorem reply_lands (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK) (q : Payload)
    (hm : c∈orderedCommands g) (hd : c.destination=some a)
    (source : quiet (bound g (readK x) c.source))
    (dest : bound g (readK x) a=.reply q) :
    readK (patchPair (longWork g x) x) c.source=.reply q ∧
      readK (patchPair (longWork g x) x) a=.empty := by
  have ne := (BStarAcquireReturn.link_shape g c a hm hd).1
  obtain ⟨L,R⟩ := reverse_endpoints g x c a (.reply q) hd (Ne.symm ne)
    (reply_selected g x c a q hm hd source dest)
  change decode (readRaw _ c.source)=_ ∧ decode (readRaw _ a)=_
  rw [L,R,decode_encode,decode_encode]
  exact ⟨rfl,rfl⟩

private theorem fold_hold (a : AtK) (ws : List KWrite) (raw : BitVec 52)
    (H : avoids a ws) : ws.foldl (fun k w => putRaw k a w) raw=raw := by
  induction ws generalizing raw with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons,ih _ (fun q hm => H q (List.mem_cons_of_mem _ hm))]
    simp [putRaw,Ne.symm (H w List.mem_cons_self)]

/-- HOLD does not itself rewrite a raw field. Exact raw preservation
also excludes an enabled observation or canonical/discard rewrite;
this handles non-race parked FENCE and nonselected exterior slots. -/
theorem hold_raw_partition (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (hc : (c,.hold)∈actualOffers g x) (a : AtK)
    (ha : a∈c.slots) (nonK0 : a.occurrence.val≠0)
    (norm : avoids a (normalization g (readK x)))
    (obs : avoids a (observations g (readK x) (normalization g (readK x)++middle g x))) :
    readRaw (patchPair (longWork g x) x) a = readRaw x a := by
  have M := BStarResetQuietTable.hold_avoids g x c hc a ha
  rw [raw_transit _ _ _ nonK0,routing_parts]
  apply fold_hold
  intro w H
  rcases List.mem_append.mp H with H|H
  · exact (List.mem_append.mp H).elim (norm w) (M w)
  · exact obs w H

#print axioms forward_mark
#print axioms forward_gated_hold_iff
#print axioms forward_hold_selected
#print axioms canonical_fault_selected
#print axioms reply_selected
#print axioms reply_lands
#print axioms hold_raw_partition
end L4.BStarSeparatorTags
