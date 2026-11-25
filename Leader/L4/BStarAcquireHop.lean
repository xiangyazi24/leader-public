import Leader.L4.BStarAcquireLatch
import Leader.L4.BStarLongWork

namespace L4.BStarAcquireHop
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongWork BStarAcquireLatch

def Healthy (p : Payload) : Prop :=
  p.fault=0 ∧ p.opcode.toNat=acquire ∧ p.race=0 ∧ p.outcome=0 ∧
    selTriple (p.argument.toNat/2^27)=true

theorem bind_exact (g : LongGeometry) (j : Fin 11) (p : Payload) (h : Healthy p) :
    bind g j (.forward p)=.forward p := by
  obtain ⟨hf,ho,hr,hu,hs⟩ := h
  have H : (BitVec.ofNat 34 (p.argument.toNat % 2^34))=p.argument := by
    rw [Nat.mod_eq_of_lt p.argument.isLt]
    simp
  simp [BStarLongCommand.bind,gate,forwardWidth,hf,ho,hr,hu,hs,acquire,admit,bitOp,cropped,low,H]
  cases p
  simp_all

theorem depart_exact (g : LongGeometry) (j : Fin 11) (p : Payload)
    (h : p.opcode.toNat=acquire) : depart g j p=some p := by
  simp [depart,gate,h,acquire,admit,bitOp]

theorem arrive_exact (g : LongGeometry) (j : Fin 11) (p : Payload)
    (h : p.opcode.toNat=acquire) : arrive g j p=.forward p := by
  simp [arrive,gate,h,acquire,admit,bitOp]

theorem classify_forward (c : CommandClaim) (g : LongGeometry) (p : Payload) (v : Token)
    (hn : c.kind≠.door) (h : p.opcode.toNat=acquire) :
    classify c g (.forward p) v=.advance p := by
  simp [classify,hn,depart_exact g c.source.occurrence p h]

theorem check_keeps (g : Pair LongGeometry) (old : At Sheet → BStarLongPackets.Lane)
    (c : CommandClaim) (p : Payload) (h : p.opcode.toNat=acquire) :
    BStarLongCommandData.checkOffer g old (c,.advance p)=.advance p := by
  simp [BStarLongCommandData.checkOffer,BStarLongCommandData.checkFence,h,acquire]

theorem visit_exact (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload)
    (h : p.opcode.toNat=acquire) : BStarLongArithmetic.visit g j x p=(.empty _,p) := by
  unfold BStarLongArithmetic.visit
  rw [h]
  split <;> rfl

theorem outgoing_exact (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload)
    (h : p.opcode.toNat=acquire) : BStarLongOutgoing.execute g j x p=BStarLongOutgoing.hold p := by
  unfold BStarLongOutgoing.execute
  dsimp only
  rw [h]
  simp [acquire,stageOp,sealOp,commitOp]

/-- There is no arithmetic, descriptor, race, or binding rewrite on
a selected healthy ACQUIRE link. Its final payload is exactly the
already-arbitrated argument. -/
theorem selected_hop (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (k : AtK) (p : Payload)
    (hd : c.destination=some k) (ho : p.opcode.toNat=acquire) :
    (selected g x (c,.advance p)).k=[(c.source,.trail),(k,.forward p)] := by
  unfold selected
  dsimp only
  rw [visit_exact _ _ _ p ho]
  dsimp only
  rw [outgoing_exact _ _ _ p ho]
  simp [BStarLongOutgoing.hold,advanceK,hd,arrive_exact _ _ p ho]

def won (_g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (c : CommandClaim) (j : Fin 3) : Bool :=
  let a := BStarLongGrant.atOld x c.source.side
  BStarLongGrant.win (BStarLongGrant.original a)
    (fun k => BStarLongGrant.requested O c.source.side k BStarLongGrant.releaseOp)
    (fun k => BStarLongGrant.requested O c.source.side k acquire) j

def argUpdate (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (c : CommandClaim) (p : Payload) : Payload :=
  if j : c.source.occurrence.val<3 then
    if (BStarLongCommand.geometry g c.source.side).axes.h6 then
      BStarLongGrant.capture (BStarLongGrant.atOld x c.source.side) ⟨_,j⟩ p (won g x O c ⟨_,j⟩)
    else p
  else p

theorem grant_update_exact (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (c : CommandClaim) (p : Payload)
    (hf : p.fault=0) (ho : p.opcode.toNat=acquire) :
    BStarLongGrant.update g x O (c,.advance p)=(c,.advance (argUpdate g x O c p)) := by
  simp [BStarLongGrant.update,argUpdate,won,hf,ho]
  split <;> (try split) <;> rfl

theorem argUpdate_fields (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (c : CommandClaim) (p : Payload) :
    let q := argUpdate g x O c p
    q.fault=p.fault ∧ q.opcode=p.opcode ∧ q.race=p.race ∧ q.outcome=p.outcome := by
  unfold argUpdate
  split
  · split
    · unfold BStarLongGrant.capture BStarLongGrant.captureFields
      split <;> exact ⟨rfl,rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl,rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl,rfl⟩

theorem actual_update_hop (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (c : CommandClaim) (k : AtK) (p : Payload)
    (hd : c.destination=some k) (hf : p.fault=0) (ho : p.opcode.toNat=acquire) :
    (selected g x (BStarLongGrant.update g x O (c,.advance p))).k=
      [(c.source,.trail),(k,.forward (argUpdate g x O c p))] := by
  rw [grant_update_exact g x O c p hf ho]
  have H := (argUpdate_fields g x O c p).2.1
  exact selected_hop g x c k _ hd ((congrArg BitVec.toNat H).trans ho)

#print axioms bind_exact
#print axioms actual_update_hop

theorem argUpdate_noncapture (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (c : CommandClaim) (p : Payload)
    (h : 3≤c.source.occurrence.val ∨ (geometry g c.source.side).axes.h6=false) :
    argUpdate g x O c p=p := by
  rcases h with h|h
  · simp [argUpdate,Nat.not_lt.mpr h]
  · simp [argUpdate,h]

theorem argUpdate_loser (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (c : CommandClaim) (p : Payload)
    (j : c.source.occurrence.val<3) (hh : (geometry g c.source.side).axes.h6=true)
    (hw : won g x O c ⟨_,j⟩=false) :
    let q := argUpdate g x O c p
    q.argument=BitVec.ofNat 34 (p.argument.toNat%2^33) ∧ latch q=false := by
  simp only [argUpdate,dif_pos j,hh,if_true]
  unfold BStarLongGrant.capture
  refine ⟨by simp [BStarLongGrant.captureFields,hw],?_⟩
  rw [capture_latch,hw,Bool.and_false]

theorem argUpdate_winner (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (c : CommandClaim) (p : Payload)
    (j : c.source.occurrence.val<3) (hh : (geometry g c.source.side).axes.h6=true)
    (hw : won g x O c ⟨_,j⟩=true) :
    let old := BStarLongGrant.atOld x c.source.side
    let q := argUpdate g x O c p
    q.argument=BitVec.ofNat 34 (BStarLongGrant.replaceLane
      (BStarLongGrant.replaceLane p.argument.toNat (BStarLongPublication.readSel old).val
        (31-2*c.source.occurrence.val) 2)
      (BStarLongGrant.headerBits old).toNat (18-9*c.source.occurrence.val) 9)
      ∧ latch q=latch p := by
  dsimp only
  simp only [argUpdate,dif_pos j,hh,if_true]
  unfold BStarLongGrant.capture
  refine ⟨by simp [BStarLongGrant.captureFields,hw],?_⟩
  rw [capture_latch,hw,Bool.and_true]

/-- Read the actual two K write intents, including exact forwarding of
the 34-bit result after the arbitration. A full ring lineage still
needs the existing disjoint-write integration theorem. -/
theorem raw_selected_hop (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (c : CommandClaim) (k : AtK) (p : Payload)
    (hd : c.destination=some k) (hne : c.source≠k) (h : Healthy p) :
    let ys := (selected g x (BStarLongGrant.update g x O (c,.advance p))).k
    let out := readK (patchPair (compile ys) x)
    out c.source=.trail ∧ out k=.forward (argUpdate g x O c p) ∧
      ∀ a, a≠c.source → a≠k → out a=readK x a := by
  dsimp only
  rw [exact_k_transfer,actual_update_hop g x O c k p hd h.1 h.2.1]
  simp only [List.foldl_cons,List.foldl_nil,assign]
  refine ⟨by simp [hne],by simp,?_⟩
  intro a h1 h2
  simp [h1,h2]

#print axioms argUpdate_loser
#print axioms argUpdate_winner
#print axioms raw_selected_hop
end L4.BStarAcquireHop
