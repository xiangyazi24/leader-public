import Leader.L4.BStarNumericTerminal
import Leader.L4.BStarAcquireVisitWitness
import Leader.L4.BStarNumericWidth

/-! Forward health of the literal numeric command rows. Valid operand
tags are required only at significant LOAD slots. -/
namespace L4.BStarFreshNumeric

open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongCommandData
open BStarLongCommand BStarLongArithmetic BStarLongSignatures BStarNumericCarry
open BStarNumericWidth BStarLongPackets L4.Compiler.Native

private theorem prep_fault_origin (g : Pair LongGeometry) (x : Pair (BitVec LW)) (j : AtK)
    (h : j∈(round g x).faults) :
    ∃ c q, c.source=j ∧ (c,.advance q)∈gated g x ∧
      ∃ op, prepOf q.opcode.toNat=some op := by
  let L := preparedBy g x (gated g x)
  have hf : j∈BStarLongPrep.prepFaults (BStarLongPrep.view x) L := h
  unfold BStarLongPrep.prepFaults at hf
  have general (o : BStarLongPrep.Offer) (xs : List BStarLongPrep.Offer)
      (h : o∈offers BStarLongPrep.offerPriority xs) : o∈xs := by
    induction xs with
    | nil => exact h
    | cons b rest ih =>
      change o∈insert BStarLongPrep.offerPriority b (offers BStarLongPrep.offerPriority rest) at h
      exact List.mem_cons.mpr ((mem_insert BStarLongPrep.offerPriority b o _).mp h |>.imp_right ih)
  have chosen (o : BStarLongPrep.Offer) (h : o∈(BStarLongPrep.arbitration L).1) : o∈L := by
    unfold BStarLongPrep.arbitration at h
    rw [BStarLongPrep.arbitrate_winners] at h
    exact general o L ((select_sublist _ _ _).subset h)
  have rejected (o : BStarLongPrep.Offer) (h : o∈(BStarLongPrep.arbitration L).2) : o∈L :=
    general o L ((BStarLongPrep.arbitrate_losers [] (offers BStarLongPrep.offerPriority L)).subset h)
  have witness : ∃ o∈L, o.claim.origin=j := by
    rcases List.mem_append.mp hf with H|H
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,rejected o ho,rfl⟩
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,chosen o (List.mem_filter.mp ho).1,rfl⟩
  obtain ⟨o,ho,he⟩ := witness
  unfold L preparedBy at ho
  obtain ⟨⟨c,s⟩,hc,hO⟩ := List.mem_flatMap.mp ho
  cases s <;> simp only at hO
  all_goals try cases hO
  rename_i q
  unfold fieldOffers at hO
  split at hO
  · cases hO
  · split at hO
    · cases hO
    · rename_i op hOp
      obtain ⟨cl,hcl,rfl⟩ := List.mem_map.mp hO
      obtain ⟨sh,hsh,rfl⟩ := List.mem_map.mp hcl
      exact ⟨c,q,he,hc,op,hOp⟩

structure Healthy (p : Payload) : Prop where
  numeric : Numeric p
  race : p.race=0
  outcome : p.outcome=0
  width : ∃ w, forwardWidth p.opcode.toNat p.argument.toNat=some w ∧ p.argument.toNat<2^w

theorem Healthy.bound {p : Payload} (H : Healthy p) (g : LongGeometry) (j : Fin 11) :
    BStarLongCommand.bind g j (.forward p)=.forward p := by
  obtain ⟨w,W,S⟩ := H.width
  exact slot_bind g j p H.numeric H.race H.outcome w W S

private theorem no_prep (op : Nat) (h : 13≤op) : prepOf op=none := by
  unfold prepOf
  split <;> first | omega | rfl

/-- A numeric forward at a genuine selected command source always advances;
neither another claim's prep fault nor ACQUIRE arbitration can change it. -/
theorem selected_advance (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload)
    (mem : C∈orderedCommands g) (kind : C.kind≠.door)
    (R : readK raw C.source=.forward p) (H : Healthy p) :
    (C,.advance p)∈actualOffers g raw := by
  have old : oldTokens raw C.source=.forward p := R
  have slot := H.bound (geometry g C.source.side) C.source.occurrence
  have gate := numeric_gate (geometry g C.source.side) C.source.occurrence p H.numeric
  have N : p.opcode.toNat≠11 := by have := H.numeric.2.1; omega
  have A : gatedAt g raw C=.advance p := by
    unfold gatedAt classifyOld
    dsimp only
    rw [old,slot]
    simp [classify,kind,depart,gate,checkOffer,checkFence,N]
  have keep : C.source∉(round g raw).faults := by
    intro bad
    obtain ⟨D,q,e,hD,op,eq⟩ := prep_fault_origin g raw C.source bad
    obtain ⟨memD,E⟩ := (gated_mem g raw D (.advance q)).mp hD
    have same := BStarAcquireIncidence.same_claim g D C D.source memD mem
      (by simp [Claim.slots]) (by simp [Claim.slots,e])
    subst D
    rw [A] at E
    injection E with Q
    subst q
    rw [no_prep _ H.numeric.2.1] at eq
    cases eq
  have after : (C,.advance p)∈(round g raw).offered := by
    change (C,.advance p)∈(gated g raw).map (cancel (round g raw).faults)
    exact List.mem_map.mpr ⟨_,(gated_mem g raw C _).mpr ⟨mem,A.symm⟩,by simp [cancel,keep]⟩
  have op : p.opcode.toNat≠acquire := by
    unfold acquire
    have := H.numeric.2.1
    omega
  exact List.mem_map.mpr ⟨_,after,by simp [BStarLongGrant.update,op]⟩

private theorem exists_node {op : Nat} (L : 13≤op) (U : op<408) :
    ∃ i c, nodeOf op=some i ∧ get i=some c := by
  have len : op-13<tourNodes.length := by rw [actual_table_lengths.1]; omega
  let i := tourNodes[op-13]
  have im : i∈tourNodes := List.getElem_mem len
  rw [BStarCmpReceipt.physical_table] at im
  have bound : i<literal.length := by
    rw [actual_table_lengths.2]
    exact List.mem_range.mp (List.mem_filter.mp im).1
  exact ⟨i,literal[i],by simp [nodeOf,Nat.not_lt.mpr L,List.getElem?_eq_getElem len,i],
    by simp [BStarLongArithmetic.get,List.getElem?_eq_getElem bound]⟩

/-- The two retained inputs have valid data tags. Their digits may have any
values, including the same value. -/
def operands (x : BitVec LW) : Prop :=
  (∃ left,(readLane 1 x).retained=.data left) ∧ ∃ right,(readLane 3 x).retained=.data right

private theorem load_defined (raw : BitVec LW) (p : Payload) (op : Numeric p)
    {i w : Nat} (q : Fin 3) (f : Fin 9) (node : nodeOf p.opcode.toNat=some i)
    (code : BStarLongArithmetic.get i=some (.load q f)) (width : forwardWidth p.opcode.toNat p.argument.toNat=some w)
    (small : p.argument.toNat<2^w) (data : operands raw) :
    ∃ value,digitLoad raw q f p.argument.toNat=some value := by
  by_cases center : q.val=1
  · have kind := kind_exact op.2.1 op.2.2 node code
    rw [width_numeric op.2.1 op.2.2,kind] at width
    simp only [codeKind,if_pos center] at width
    by_cases bad : p.argument.toNat%4=3
    · simp [bad] at width
    · have wtwo : w=2 := by simpa [bad] using width.symm
      subst w
      have legal : p.argument.toNat<3 := by omega
      simp [digitLoad,center,legal]
  · obtain ⟨⟨l,left⟩,r,right⟩ := data
    by_cases zero : q.val=0
    · simp [digitLoad,zero,left,Digit9.nibble]
    · simp [digitLoad,center,zero,right,Digit9.nibble]

/-- A legal old payload stays healthy at a significant arithmetic visit.
Only LOAD can read a packet tag. The other instructions accept every old
numeric register value, including dirty unused digits. -/
theorem visit_healthy (g : LongGeometry) (k : Fin 11) (raw : BitVec LW) (p : Payload)
    (old : Numeric p) (race : p.race=0) (outcome : p.outcome=0)
    (w : Nat) (width : forwardWidth p.opcode.toNat p.argument.toNat=some w)
    (small : p.argument.toNat<2^w) (data : k.val=1 → g.inside=true → operands raw) :
    let q := (visit g k raw p).2
    Numeric q ∧ q.opcode=p.opcode ∧ q.race=0 ∧ q.outcome=0 ∧
      forwardWidth q.opcode.toNat q.argument.toNat=some w ∧ q.argument.toNat<2^w := by
  have unchanged (same : visit g k raw p=(.empty _,p)) :
      let q := (visit g k raw p).2
      Numeric q ∧ q.opcode=p.opcode ∧ q.race=0 ∧ q.outcome=0 ∧
        forwardWidth q.opcode.toNat q.argument.toNat=some w ∧ q.argument.toNat<2^w := by
    dsimp only
    rw [same]
    exact show Numeric p ∧ p.opcode=p.opcode ∧ p.race=0 ∧ p.outcome=0 ∧
      forwardWidth p.opcode.toNat p.argument.toNat=some w ∧ p.argument.toNat<2^w from
      ⟨old,rfl,race,outcome,width,small⟩
  by_cases atOne : k.val=1
  · by_cases inside : g.inside=true
    · have ok := data atOne inside
      have atK : k=1 := Fin.ext atOne
      subst k
      obtain ⟨i,c,node,code⟩ := exists_node old.2.1 old.2.2
      have F : (physicalDigit g raw i c p).2.fault=0 := by
        cases c <;> try exact old.1
        case load q f =>
          obtain ⟨d,test⟩ := load_defined raw p old q f node code width small ok
          simpa only [physicalDigit,test] using old.1
      obtain ⟨new,same⟩ := digit_numeric g raw i c p old F
      obtain ⟨W,L,R,O⟩ := digit_width g raw i c p old node code w width small F
      dsimp only
      rw [visit_significant g raw p i c old node code inside]
      exact ⟨new,same,R.trans race,O.trans outcome,W,L⟩
    · exact unchanged (visit_padding g k raw p (.inr (Bool.eq_false_iff.mpr inside)))
  · exact unchanged (visit_padding g k raw p (.inl atOne))

open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarResetMarkAdapter BStarResetRailRing

variable {k₁ k₂ t₂ J₁ J₂ r c pmod c₁ n : Nat} (hp : 0<pmod)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c pmod c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- A physical link of the geometric cursor case split carries a
healthy numeric token forward, without assuming post-step health. -/
theorem ring_link {x : X} {addr : Nat → Pos n} {len k : Nat}
    (e : Fin n) (he : e≠rightNeighbor e) (L : linkAt hp x e addr len k)
    (p : Payload) (old : project addr x k=.forward p) (H : Healthy p)
    (data : (addr k).2.val=1 → (longGeometry B (x (addr k).1)).inside=true →
      operands (x (addr k).1).long) :
    ∃ q, project addr (step x e) (k+1)=.forward q ∧ Healthy q ∧ q.opcode=p.opcode := by
  obtain ⟨_,C,a,mem,dst,src,landing⟩ := L
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have R := (old_read x e C.source).trans ((congrArg (atCursor x) src).symm.trans old)
  have NK : C.kind≠.door := by
    rw [(BStarAcquireReturn.link_shape g C a mem dst).2.1]
    decide
  have sel := selected_advance g raw C p mem NK R H
  let v := (visit (geometry g C.source.side) C.source.occurrence (atOld raw C.source) p).2
  have D : C.source.occurrence.val=1 → (geometry g C.source.side).inside=true →
      operands (atOld raw C.source) := by
    rw [src] at data
    have E (side : Side) : geometry g side=longGeometry B (x (site e side)) := by cases side <;> rfl
    have O (a : AtK) : atOld raw a=(x (site e a.side)).long := by obtain ⟨side,j⟩ := a; cases side <;> rfl
    rw [E]
    rw [O]
    exact data
  obtain ⟨w,W,S⟩ := H.width
  obtain ⟨hN,hO,hR,hY,hW,hS⟩ :=
    visit_healthy (geometry g C.source.side) C.source.occurrence (atOld raw C.source) p
      H.numeric H.race H.outcome w W S D
  have J := joined_numeric_lands k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp (x e,x (rightNeighbor e)) C a p dst sel hN
  have E := (new_read B x e he a).trans ((congrArg (atCursor (step x e)) landing).symm)
  exact ⟨v,E.symm.trans J,⟨hN,hR,hY,w,hW,hS⟩,hO⟩

/-- A geometric terminal mark turns an old healthy numeric forward
into its exact healthy reply, including the last numeric opcode. -/
theorem ring_turn {x : X} {addr : Nat → Pos n} {len : Nat}
    (e : Fin n) (he : e≠rightNeighbor e) (L : onTerminal hp x e addr len)
    (p : Payload) (old : project addr x len=.forward p) (H : Healthy p) :
    project addr (step x e) len=.reply (BStarNumericReceipt.output p) := by
  obtain ⟨C,mem,kind,dst,K,src⟩ := L
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have R := (old_read x e C.source).trans ((congrArg (atCursor x) src).symm.trans old)
  have NK : C.kind≠.door := by rw [kind]; decide
  have sel := selected_advance g raw C p mem NK R H
  have J := BStarNumericTerminal.joined_terminal k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp
    (x e,x (rightNeighbor e)) C p K dst sel H.numeric
  have E := (new_read B x e he C.source).trans ((congrArg (atCursor (step x e)) src).symm)
  exact E.symm.trans J

end L4.BStarFreshNumeric
