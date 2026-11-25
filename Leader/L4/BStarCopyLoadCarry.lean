import Leader.L4.BStarCopyOperand
import Leader.L4.BStarClearanceForward
import Leader.L4.BStarResetTaggedRows
import Leader.L4.BStarAcquireHistorySample

namespace L4.BStarCopyLoadCarry
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken BStarLongCommand
open BStarLongDoor BStarLongLiteral BStarLongEvents BStarLongTransport BStarLongCommandData
open BStarClearanceForward BStarResetTaggedRows BStarCopyOperand

def payload (u : Nat) : Payload := ⟨0,8,0,0,BitVec.ofNat 34 u⟩

theorem load_issue_payload (x : BitVec LW) (u : Nat) (I : initial 8 x=some u) :
    forward 8 u=.forward (payload ((BStarLongDoor.captures).read x).toNat) := by
  rw [(issue_load_operand x u I).1]
  rfl

theorem load_bind (g : LongGeometry) (j : Fin 11) (u : Nat)
    (width : u<64) (valid : selTriple u=true) :
    BStarLongCommand.bind g j (.forward (payload u))=.forward (payload u) := by
  have w34 : u<2^34 := by omega
  have val : (BitVec.ofNat 34 u).toNat=u := by
    simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt w34]
  have TC : cropped (payload u) 6=payload u := by
    unfold payload cropped low
    rw [val,Nat.mod_eq_of_lt width]
  simp [BStarLongCommand.bind,payload,gate,admit,bitOp,forwardWidth,copyLoad,
    acquire,val,valid]
  exact TC

theorem load_carries (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (C : CommandClaim) (u : Nat) :
    carried g raw C (payload u)=payload u := by
  unfold carried
  dsimp only
  have A : (BStarLongArithmetic.visit (geometry g C.source.side) C.source.occurrence
      (BStarLongWork.atOld raw C.source) (payload u)).2=payload u := by
    simp [BStarLongArithmetic.visit,payload,BStarLongArithmetic.nodeOf]
  rw [A]
  simp [BStarLongOutgoing.execute,BStarLongOutgoing.hold,payload,stageOp,sealOp,commitOp]

theorem load_arrive (g : LongGeometry) (j : Fin 11) (u : Nat) :
    arrive g j (payload u)=.forward (payload u) := by
  simp [arrive,gate,admit,bitOp,payload]

theorem load_advance (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (D : BStarLongTransport.AtK) (u : Nat)
    (width : u<64) (valid : selTriple u=true)
    (hc : C∈orderedCommands g) (hd : C.destination=some D)
    (read : readK raw C.source=.forward (payload u))
    (nf : C.source∉(round g raw).faults) :
    (C,.advance (payload u))∈actualOffers g raw := by
  have term := (BStarAcquireReturn.link_shape g C D hc hd).2.1
  have A : gatedAt g raw C=.advance (payload u) := by
    unfold gatedAt classifyOld
    change checkOffer g (BStarLongPrep.view raw) (C,classify C (geometry g C.source.side)
      (BStarLongCommand.bind (geometry g C.source.side) C.source.occurrence (readK raw C.source)) _) = _
    rw [read,load_bind _ _ _ width valid]
    simp [classify,term,depart,gate,admit,bitOp,checkOffer,checkFence,payload]
  have G := (gated_mem g raw C _).mpr ⟨hc,A.symm⟩
  have R : (C,.advance (payload u))∈(round g raw).offered :=
    List.mem_map.mpr ⟨_,G,by change (if C.source∈(round g raw).faults then _ else _)=_; rw [if_neg nf]⟩
  unfold actualOffers BStarLongGrant.run
  apply List.mem_map.mpr
  refine ⟨_,R,?_⟩
  by_cases h : C.source.occurrence.val<3 <;>
    simp [BStarLongGrant.update,h,payload,acquire]

/-- Full joined LOAD hop preserves the complete launched six-bit
selector word. If selected prep faults, the hypothesis is deliberately
not met: the actual token is replaced by a forward fault. -/
theorem load_hop_joined (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (D : BStarLongTransport.AtK) (u : Nat) (width : u<64) (valid : selTriple u=true) :
    let B := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry B) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.destination=some D →
    readK raw C.source=.forward (payload u) → C.source∉(round g raw).faults →
    let y := Pair.map LargeSite.long (largePair B x)
    readK y C.source=.trail ∧ readK y D=.forward (payload u) := by
  dsimp only
  intro mem dest old nf
  let B := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have shape := BStarAcquireReturn.link_shape g C D mem dest
  obtain ⟨src,dst⟩ := move_lands g raw C (payload u) D dest
    (load_advance g raw C D u width valid mem dest old nf) (Ne.symm shape.1)
  rw [load_carries,load_arrive] at dst
  have A := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source
        (fun h z => (shape.2.2 h z).elim)
  have E := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x D
        (fun _ z => .inl (BStarAcquireJoinedHop.k0_dest _ C D mem dest z).2)
  exact ⟨A.trans ((congrArg decode src).trans (decode_encode _)),
    E.trans ((congrArg decode dst).trans (decode_encode _))⟩

#print axioms load_hop_joined

open BStarH6WordChart BStarAcquireVisitOrder BStarResetRailRing BStarResetSchedule
open BStarClearanceSource
open BStarAcquireForwardTrace BStarResetQuietTable BStarResetMarkAdapter BStarLongLayout

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem load_hop_ring (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (C : CommandClaim) (D : BStarLongTransport.AtK) (u : Nat)
    (width : u<64) (valid : selTriple u=true)
    (hc : C∈orderedCommands (oldPair B x e)) (hd : C.destination=some D)
    (old : atCursor x (address e C.source)=.forward (payload u))
    (nf : C.source∉(round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).faults) :
    atCursor (step x e) (address e C.source)=.trail ∧
    atCursor (step x e) (address e D)=.forward (payload u) := by
  have H := load_hop_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) C D u width valid
    hc hd ((old_read x e _).trans old) nf
  exact ⟨(new_read B x e sep _).symm.trans H.1,(new_read B x e sep _).symm.trans H.2⟩

/-- The original raw-word observer for one LOAD. It follows successful
selected physical links, and accepts a silent mark only with an exact
slot frame. The statement does not equate tokens to identify a hop. -/
inductive LoadWord : X → Pos n → List (Fin n) → Pos n → Prop
  | nil (x j) : LoadWord x j [] j
  | off {x j e w last} (l : j.1≠e) (r : j.1≠rightNeighbor e)
      (rest : LoadWord (step x e) j w last) : LoadWord x j (e::w) last
  | held {x e w last} (a : BStarLongTransport.AtK)
      (sep : e≠rightNeighbor e)
      (door : DoorSafe (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) a)
      (quiet : ∀ q∈BStarLongRouting.routing (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long),q.1≠a)
      (rest : LoadWord (step x e) (address e a) w last) : LoadWord x (address e a) (e::w) last
  | hop {x e w last} (c : CommandClaim) (d : BStarLongTransport.AtK)
      (sep : e≠rightNeighbor e)
      (mem : c∈orderedCommands (oldPair B x e)) (dst : c.destination=some d)
      (clear : c.source∉(round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).faults)
      (rest : LoadWord (step x e) (address e d) w last) :
      LoadWord x (address e c.source) (e::w) last

theorem load_word_carries {x : X} {j last : Pos n} {w : List (Fin n)}
    (T : LoadWord hp x j w last) (u : Nat) (width : u<64) (valid : selTriple u=true)
    (start : atCursor x j=.forward (payload u)) :
    atCursor (BStarResetSchedule.run step x w) last=.forward (payload u) := by
  induction T with
  | nil _ _ => exact start
  | off l r _ ih =>
    exact ih ((BStarResetIdleRing.idle_off_pair hp _ _ _ l r).trans start)
  | @held x e w last a sep door quiet rest ih =>
    have H := BStarAcquireHistorySample.joined_silent k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) a door quiet
    exact ih ((new_read B x e sep a).symm.trans (H.trans ((old_read x e a).trans start)))
  | hop c d sep mem dst clear _ ih =>
    exact ih (load_hop_ring hp _ _ sep c d u width valid mem dst start clear).2

#print axioms load_hop_ring
#print axioms load_word_carries

theorem captured_operand_index (u : Nat) (width : u<64) (valid : selTriple u=true)
    (rev : Bool) :
    ∃ k : Fin 3, captureIndex (payload u) (whichCapture rev)=some k ∧
      k.val=(if rev then u%4 else u/16%4) := by
  have w34 : u<2^34 := by omega
  have val : (BitVec.ofNat 34 u).toNat=u := by simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt w34]
  have v := valid
  simp only [selTriple,Bool.and_eq_true,bne_iff_ne] at v
  cases rev
  · have k : u/16%4<3 := by omega
    exact ⟨⟨_,k⟩,by simp [captureIndex,whichCapture,payload,val,k],rfl⟩
  · have k : u%4<3 := by omega
    exact ⟨⟨_,k⟩,by simp [captureIndex,whichCapture,payload,val,k],rfl⟩

/-- The exact launch snapshot determines the selector word on the
selected physical LOAD word, not a distinct later source read. -/
theorem carries_from_launch (root : Fin n) (old launched : X)
    (L : Launch (old root).long (launched root).long)
    (op8 : (ctrlOp.read (old root).long).toNat=8)
    {w : List (Fin n)} {last : Pos n}
    (trail : LoadWord hp launched (root,0) w last) :
    let u := (captures.read (old root).long).toNat
    selTriple u=true ∧
    atCursor (BStarResetSchedule.run step launched w) last=.forward (payload u) := by
  dsimp only
  obtain ⟨_,u,H,snap⟩ := L
  rw [op8] at H
  have cap := issue_load_operand _ _ H
  rw [op8] at snap
  have Q := congrArg (fun z : (Token × BitVec 2) × BitVec 9 => z.1.1) snap
  change atCursor launched (root,0)=forward 8 u at Q
  rw [cap.1] at Q
  have V := cap.1 ▸ cap.2
  exact ⟨V,load_word_carries hp trail _ (by exact (captures.read (old root).long).isLt) V Q⟩

#print axioms captured_operand_index
#print axioms carries_from_launch

/-- A source-authenticated LOAD freezes the actually named old operand
at a generated inside K0/ls or K2/rs capture. The winning lane must
be exclusive (foreign-owner exclusion is proved independently). -/
theorem selected_freeze_from_launch (root : Fin n) (old launched : X)
    (L : Launch (old root).long (launched root).long)
    (op8 : (ctrlOp.read (old root).long).toNat=8)
    (w : List (Fin n)) (e : Fin n) (s : Side) (rev : Bool) (C : CommandClaim)
    (sep : e≠rightNeighbor e)
    (trail : LoadWord hp launched (root,0) w (address e C.source)) :
    let u := (captures.read (old root).long).toNat
    let x := BStarResetSchedule.run step launched w
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let i := site e s
    C∈orderedCommands g → C.kind≠.door →
    C.source=⟨s,loadOcc rev⟩ → (geometry g s).inside=true →
    (∀ a∈(round g raw).prep, a.claim.lane=loadLane s rev →
      a.claim=loadClaim s rev ∧ a.payload=loadPayload raw (loadLane s rev) (payload u)) →
    ∃ k : Fin 3,
      k.val=(if rev then u%4 else u/16%4) ∧
      (BStarLongPackets.readLane (BStarLongPackets.Sheet.index (loadLane s rev).occurrence)
        (step x e i).long).frozen=oldBankPacket (x i).long k := by
  dsimp only
  intro hc door origin inside exclusive
  let u := (captures.read (old root).long).toNat
  let x := BStarResetSchedule.run step launched w
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  obtain ⟨valid,hold⟩ := carries_from_launch hp root old launched L op8 trail
  have width : u<64 := (captures.read (old root).long).isLt
  obtain ⟨k,idx,val⟩ := captured_operand_index u width valid rev
  have r : readK raw C.source=.forward (payload u) := (old_read x e _).trans hold
  have bindExact : BStarLongCommand.bind (geometry g C.source.side) C.source.occurrence
      (oldTokens raw C.source)=.forward (payload u) := by
    change BStarLongCommand.bind _ _ (readK raw C.source)=_
    rw [r,load_bind _ _ _ width valid]
  have M := selected_load_payload g raw C (payload u) s rev k hc door origin bindExact (by rfl) (by rfl) inside idx
  have packEq : lane (s==.right) raw=(x (site e s)).long := by cases s <;> rfl
  have choose : loadPayload raw (loadLane s rev) (payload u)=oldBankPacket (x (site e s)).long k := by
    rw [←packEq]
    cases rev
    · change captureIndex (payload u) 0=some k at idx
      simp [loadLane,BStarCopyInjection.sourceLane,loadPayload,idx]
    · change captureIndex (payload u) 2=some k at idx
      simp [loadLane,BStarCopyInjection.sourceLane,loadPayload,idx]
  have sel := BStarCopyInjection.exclusive_winner
    (⟨loadClaim s rev,oldBankPacket (lane (s==.right) raw) k⟩ : BStarLongPrep.Offer)
    _ M (by
      intro a ma h
      have ⟨claim,pa⟩ := exclusive a ma h
      cases a
      simp only [BStarLongPrep.Offer.mk.injEq]
      exact ⟨claim,pa.trans (choose.trans (congrArg (fun b => oldBankPacket b k) packEq.symm))⟩)
  rw [packEq] at sel
  exact ⟨k,val,congrArg BStarLongPackets.Lane.frozen (ring_load hp x e sep s rev k sel)⟩

#print axioms selected_freeze_from_launch
end L4.BStarCopyLoadCarry
