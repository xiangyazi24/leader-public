import Leader.L4.BStarBitFollowRing
namespace L4.BStarBitDepart
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongEvents BStarLongWork BStarLongCommandData BStarBitParity BStarLongLiteral
open BStarLongTransport BStarLongRouting
private theorem sort_mem {C : Type} (key : C → Nat) (a : C) (xs : List C) :
    a∈offers key xs → a∈xs := by
  have ins (q : C) (tail : List C) : a∈BStarLongClaims.insert key q tail → a=q ∨ a∈tail := by
    induction tail with
    | nil => simp [BStarLongClaims.insert]
    | cons b bs ih =>
      unfold BStarLongClaims.insert
      split
      · simp
      · simp only [List.mem_cons]
        intro H
        rcases H with h|h
        · exact .inr (.inl h)
        · rcases ih h with qeq|bt
          · exact .inl qeq
          · exact .inr (.inr bt)
  induction xs with
  | nil => simp [offers]
  | cons q qs ih =>
    intro h
    change a∈BStarLongClaims.insert key q (offers key qs) at h
    exact List.mem_cons.mpr ((ins q _ h).imp_right ih)

private theorem fault_origin (old : At Sheet → BStarLongPackets.Lane)
    (ps : List BStarLongPrep.Offer) (a : At (Fin 11))
    (h : a∈BStarLongPrep.prepFaults old ps) :
    ∃ p∈ps, p.claim.origin=a := by
  unfold BStarLongPrep.prepFaults at h
  rcases List.mem_append.mp h with l|w
  · obtain ⟨q,m,rfl⟩ := List.mem_map.mp l
    exact ⟨q,sort_mem _ _ _ ((BStarLongPrep.arbitrate_losers [] _).subset m),rfl⟩
  · obtain ⟨q,m,rfl⟩ := List.mem_map.mp w
    rw [BStarLongPrep.arbitration,BStarLongPrep.arbitrate_winners] at m
    exact ⟨q,sort_mem _ _ _ ((select_sublist ..).subset (List.mem_filter.mp m).1),rfl⟩

private theorem prep_origin (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : At (Fin 11))
    (p : Payload) (q : BStarLongPrep.Offer) (h : q∈fieldOffers g x a p) :
    q.claim.origin=a := by
  unfold fieldOffers at h
  split at h
  · simp at h
  split at h
  · simp at h
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hb
    rfl

def cleanBit (v : Payload) (s : Side) : Payload :=
  {v with race:=0, argument:=BitVec.ofBool (firstBit s) |>.zeroExtend 34}

/-- A completed old gate selects the literal center link. Blocked FENCE,
foreign prep, and ACQUIRE grant processing do not mask this BIT advance. -/
theorem selected_depart (g : Pair LongGeometry) (x : Pair (BitVec LW)) (v : Payload)
    (s : Side) (B : bound g (readK x) (L 1)=.forward v)
    (F : v.fault=0) (P : v.opcode.toNat=bitOp) (G : gate bitOp 1 g.1=true)
    (done : v.race=finalCode s) :
    (centerLink g,.advance (cleanBit v s))∈actualOffers g x := by
  let q := cleanBit v s
  have qp : q.opcode.toNat=bitOp := P
  have qf : q.fault=0 := F
  have D := depart_final g.1 v s G F P done
  have D' : depart g.1 1 v=some q := D
  have raw : classifyOld g x (centerLink g)=.advance q := by
    unfold classifyOld
    change classify (centerLink g) g.1 (bound g (readK x) (L 1)) _=.advance q
    rw [B]
    simp only [classify, centerLink,link]
    change (match depart g.1 1 v with | none => Offer.hold | some w => Offer.advance w) = _
    rw [D']
  have gate : gatedAt g x (centerLink g)=.advance q := by
    simp [gatedAt, raw, checkOffer,checkFence,qp,bitOp]
  have N : L 1∉(round g x).faults := by
    intro bad
    obtain ⟨a,ha,orig⟩ := fault_origin _ _ _ bad
    obtain ⟨⟨c,o⟩,hc,H⟩ := List.mem_flatMap.mp ha
    cases o <;> try (simp at H)
    rename_i w
    change a∈fieldOffers g x c.source w at H
    have E := (prep_origin g x c.source w a H).symm.trans orig
    obtain ⟨cm,hq⟩ := (gated_mem g x c (.advance w)).mp hc
    have cEq := center_of g c cm (congrArg (fun z : At (Fin 11) => z.occurrence.val) E)
    subst c
    rw [gate] at hq
    injection hq with qEq
    subst w
    simp [fieldOffers,qp,bitOp,prepOf] at H
  have J := (gated_mem g x (centerLink g) (.advance q)).2 ⟨center_mem g,gate.symm⟩
  unfold actualOffers BStarLongGrant.run
  apply List.mem_map.mpr
  refine ⟨(centerLink g,.advance q),?_,?_⟩
  · change (centerLink g,.advance q) ∈ (gated g x).map (cancel (round g x).faults)
    exact List.mem_map.mpr ⟨_,J,by simp only [cancel, centerLink, link, N, if_false]⟩
  · simpa [BStarLongGrant.update,centerLink,link,qp,bitOp,acquire] using (show q=cleanBit v s from rfl)

theorem carried_bit (g : Pair LongGeometry) (x : Pair (BitVec LW)) (c : CommandClaim)
    (p : Payload) (P : p.opcode.toNat=bitOp) :
    BStarClearanceForward.carried g x c p=p := by
  have H : BStarLongArithmetic.nodeOf bitOp=none := by decide
  have A : (BStarLongArithmetic.visit (geometry g c.source.side) c.source.occurrence
      (atOld x c.source) p).2=p := by
    unfold BStarLongArithmetic.visit
    split
    · rfl
    · rw [P,H]
  unfold BStarClearanceForward.carried
  dsimp only
  rw [A]
  simp [BStarLongOutgoing.execute,P,bitOp,stageOp,sealOp,commitOp,BStarLongOutgoing.hold]

/-- Both command slots of the full joined row on the completed outgoing mark.
The receiving slot is not another BIT gate: it receives the completed bit. -/
theorem joined_depart (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : Side)
    (v : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let dest : AtK := R (if g.2.axes.h6 then 2 else 1)
    bound g (readK raw) (L 1)=.forward v →
    v.fault=0 → v.opcode.toNat=bitOp → v.race=finalCode s →
    gate bitOp 1 g.1=true →
    gate bitOp dest.occurrence g.2=false →
    let post : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    readRaw post (L 1)=encode .trail ∧
      readRaw post dest=encode (.forward (cleanBit v s)) := by
  dsimp only
  intro old F op done G next
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let a : AtK := R (if g.2.axes.h6 then 2 else 1)
  have sel := selected_depart g raw v s old F op G done
  obtain ⟨Lw,Rw⟩ := BStarClearanceForward.move_lands g raw (centerLink g) (cleanBit v s) a
    rfl sel (by intro H; cases (congrArg (fun j : AtK => j.side) H : Side.left=Side.right))
  rw [carried_bit _ _ _ (cleanBit v s) op] at Rw
  have V : arrive (geometry g a.side) a.occurrence (cleanBit v s)=.forward (cleanBit v s) := by
    change arrive g.2 a.occurrence (cleanBit v s)=_
    have P : (cleanBit v s).opcode.toNat=bitOp := op
    change gate bitOp a.occurrence g.2=false at next
    simp [arrive,P,next]
  rw [V] at Rw
  have nl : (L 1 : AtK)≠R 0 := by decide
  have nr : a≠R 0 := by
    dsimp only [a]
    split <;> decide
  exact ⟨(BStarResetQuiet.joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x (L 1)
      (fun H _ => (nl H).elim)).trans Lw,
    (BStarResetQuiet.joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a
      (fun H _ => (nr H).elim)).trans Rw⟩

end L4.BStarBitDepart
