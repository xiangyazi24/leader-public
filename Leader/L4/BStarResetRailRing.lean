import Leader.L4.BStarResetTaggedRows
import Leader.L4.BStarSeparatingRail
import Leader.L4.BStarAcquireForwardTrace
import Leader.L4.BStarResetDoor

/-! Link and terminal service of the original reset occurrence in the
actual joined ring, with an explicit fault branch. -/
namespace L4.BStarResetRailRing
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongWork BStarLongCommandData BStarResetTaggedRows
open BStarH6WordChart BStarAcquireForwardTrace

def Holds (op : Nat) (p : Payload) : Prop := p=resetPayload op ∨ p=failedPayload

def resetTag (op : Nat) : BStarSeparatingRail.Tag where
  F t := ∃ q, Holds op q ∧ t=.forward q
  D t := ∃ q, Holds op q ∧ t=finish q

theorem reset_of_holds (op : Nat) (ho : op<3) (pay : Payload)
    (h : Holds op pay) : ResetF pay := by
  obtain rfl|rfl := h
  · have q : op=0 ∨ op=1 ∨ op=2 := by omega
    rcases q with rfl|rfl|rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr rfl))

theorem old_read {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)) (e : Fin n) (a : AtK) :
    readK ((x e).long,(x (rightNeighbor e)).long) a=atCursor x (site e a.side,a.occurrence) := by
  cases a with
  | mk s j => cases s <;> rfl

theorem new_read {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
    (b : LargeRows (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (he : e≠rightNeighbor e) (a : AtK) :
    readK (Pair.map LargeSite.long (largePair b (x e,x (rightNeighbor e)))) a
      = atCursor (AllSizeS1Geometry.step b x e) (site e a.side,a.occurrence) := by
  cases a with
  | mk s j =>
    cases s
    · simp [readK,atCursor,site,AllSizeS1Geometry.step,lane,L,Pair.map]
    · simp [readK,atCursor,site,AllSizeS1Geometry.step,lane,L,Pair.map,Ne.symm he]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem forward_service (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (C : CommandClaim) (d : AtK) (op : Nat) (ho : op<3)
    (hc : C∈orderedCommands (oldPair B x e)) (hd : C.destination=some d)
    (F : (resetTag op).F (atCursor x (site e C.source.side,C.source.occurrence))) :
    let y := AllSizeS1Geometry.step B x e
    atCursor y (site e C.source.side,C.source.occurrence)=.trail ∧
    (resetTag op).F (atCursor y (site e d.side,d.occurrence)) := by
  obtain ⟨pay,H,R⟩ := F
  have src := (old_read x e C.source).trans R
  obtain ⟨A,D⟩ := reset_link_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) C d pay hc hd src (reset_of_holds op ho pay H)
  let Q := if C.source∈(round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).faults
    then failedPayload else pay
  change readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) d=.forward Q at D
  refine ⟨(new_read B x e he C.source).symm.trans A,⟨Q,?_,(new_read B x e he d).symm.trans D⟩⟩
  unfold Q
  split
  · exact .inr rfl
  · exact H

theorem terminal_service (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (C : CommandClaim) (op : Nat) (ho : op<3)
    (hc : C∈orderedCommands (oldPair B x e)) (hk : C.kind=.terminal)
    (hd : C.destination=none) (ht : C.source.occurrence.val=10)
    (F : (resetTag op).F (atCursor x (site e C.source.side,C.source.occurrence))) :
    (resetTag op).D
      (atCursor (AllSizeS1Geometry.step B x e) (site e C.source.side,C.source.occurrence)) := by
  obtain ⟨pay,H,R⟩ := F
  have src := (old_read x e C.source).trans R
  have A := reset_terminal_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) C pay hc hk hd ht src (reset_of_holds op ho pay H)
  let Q := if C.source∈(round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).faults
    then failedPayload else pay
  change readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) C.source=finish Q at A
  refine ⟨Q,?_,(new_read B x e he C.source).symm.trans A⟩
  unfold Q
  split
  · exact .inr rfl
  · exact H

theorem backward_service (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (C : CommandClaim) (d : AtK) (op : Nat) (ho : op<3)
    (hc : C∈orderedCommands (oldPair B x e)) (hd : C.destination=some d)
    (trail : atCursor x (site e C.source.side,C.source.occurrence)=.trail)
    (D : (resetTag op).D (atCursor x (site e d.side,d.occurrence))) :
    let y := AllSizeS1Geometry.step B x e
    (resetTag op).D (atCursor y (site e C.source.side,C.source.occurrence)) ∧
    atCursor y (site e d.side,d.occurrence)=.empty := by
  obtain ⟨pay,H,R⟩ := D
  obtain ⟨A,K⟩ := reset_reverse_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) C d pay hc hd ((old_read x e C.source).trans trail)
    ((old_read x e d).trans R) (reset_of_holds op ho pay H)
  exact ⟨⟨pay,H,(new_read B x e he C.source).symm.trans A⟩,(new_read B x e he d).symm.trans K⟩

open BStarLongDoor

/-- The marked source can consume either success or its own fault.
Only the original healthy receipt schedules the next opcode. -/
theorem source_service (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (op : Nat) (ho : op<3)
    (hh : oldH6 B x (rightNeighbor e)=true)
    (hv : LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true)
    (ph : (ctrlPhase.read (x (rightNeighbor e)).long).toNat=2)
    (code : (ctrlOp.read (x (rightNeighbor e)).long).toNat=op)
    (D : (resetTag op).D (atCursor x (rightNeighbor e,0))) :
    let y := AllSizeS1Geometry.step B x e
    atCursor y (rightNeighbor e,0)=.empty ∧
    (ctrlPhase.read (y (rightNeighbor e)).long)=1 ∧
    (atCursor x (rightNeighbor e,0)=finish (resetPayload op) →
       (ctrlOp.read (y (rightNeighbor e)).long)=BitVec.ofNat 9 (op+1)) := by
  dsimp only
  let g := oldPair B x e
  let src : BitVec LW := (x (rightNeighbor e)).long
  let z := (largePair B (x e,x (rightNeighbor e))).2.long
  have yEq : (AllSizeS1Geometry.step B x e (rightNeighbor e)).long=z := by
    simp [AllSizeS1Geometry.step,Ne.symm he,z]
  have readPost : atCursor (AllSizeS1Geometry.step B x e) (rightNeighbor e,0)=atSite z 0 := by
    change atSite (AllSizeS1Geometry.step B x e (rightNeighbor e)).long 0=atSite z 0
    exact congrArg (fun v => atSite v 0) yEq
  have G : ∀ p, Holds op p → atSite src 0=finish p →
      BStarLongCommand.bind g.2 0 (atSite src 0)=finish p := by
    intro p H R
    rw [R]
    exact (bind_finish _ _ _ (reset_of_holds op ho _ H)).1
  obtain ⟨q,H,R⟩ := D
  change atSite src 0=finish q at R
  have SF : finish (resetPayload op)=.reply (resetPayload op) := by
    have T : op=0 ∨ op=1 ∨ op=2 := by omega
    rcases T with rfl|rfl|rfl <;> rfl
  have opRead : (resetPayload op).opcode.toNat=op := by
    change (BitVec.ofNat 9 op).toNat=op
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    omega
  rcases H with E|E
  · subst q
    have HH := G (resetPayload op) (.inl rfl) R
    rw [SF] at HH
    have U := BStarResetDoor.joined_reset_advance k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) op (resetPayload op) ho rfl opRead hh ph code HH
    exact ⟨readPost.trans U.1, (congrArg (fun w => ctrlPhase.read w) yEq).trans
      (congrArg Prod.fst U.2),fun _ => (congrArg (fun w => ctrlOp.read w) yEq).trans (congrArg Prod.snd U.2)⟩
  · subst q
    let f : Payload := ⟨1,0,0,2,0⟩
    have FF : finish failedPayload=.reply f := rfl
    have HH := G failedPayload (.inr rfl) R
    rw [FF] at HH
    have U := BStarResetDoor.joined_fault_consumed k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) f (by decide) hh hv ph HH
    exact ⟨readPost.trans (congrArg Prod.fst U), (congrArg (fun w => ctrlPhase.read w) yEq).trans
      (congrArg Prod.snd U),fun ok => by
        change atSite src 0=finish (resetPayload op) at ok
        have neq := Token.reply.inj ((FF.symm.trans R.symm).trans (ok.trans SF))
        have P := congrArg Payload.fault neq
        change (1 : BitVec 1)=0 at P
        contradiction⟩

#print axioms source_service
#print axioms forward_service
#print axioms terminal_service
#print axioms backward_service
end L4.BStarResetRailRing
