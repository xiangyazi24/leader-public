import Leader.L4.WidthChecksum
import Leader.L4.BStarShort

namespace L4.WidthTokenTransport
open AllSizeProtocol WidthByteRows WidthChecksum

abbrev wire {c : Nat} (x : BitVec (W c)) : BitVec 16 :=
  (suffixField c 14 16 (by decide)).read x

abbrev phase {c : Nat} (x : BitVec (W c)) : Nat := WidthByteRows.get (c:=c) x 7 2 (by decide)
abbrev opcode {c : Nat} (x : BitVec (W c)) : Nat := WidthByteRows.get (c:=c) x 9 3 (by decide)

private theorem empty_apply {w : Nat} (x : BitVec w) : (Patch.empty w).apply x=x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  exact Patch.hold _ _ _ (by simp [Patch.empty])


/-- The responder's source does not act on decoded F/T in valid WAIT,
regardless of opcode/argument mismatch or whether F is faulted. -/
theorem wait_ft_door {c : Nat} (v : BitVec (W c)) (t : Token)
    (P : phase (c:=c) v=2) (O : opcode (c:=c) v≤5)
    (T : t.tag=1 ∨ t.tag=2) :
    doorPatch (c:=c) v t=.empty _ := by
  have N : ¬5 < opcode (c:=c) v := by omega
  rcases T with T|T <;> simp [doorPatch,P,N,T]

/-- Every decoded F, not just a clean one, emits the literal trail on
the left plus the departing token at its interior successor. At a
header boundary the left slot takes the finished reply instead. -/
theorem forward_wire {c : Nat} (r : Nat) (hu hv : Bool) (u v : BitVec (W c))
    (F : (packet (c:=c) u).tag=2) :
    let t := (departing (c:=c) r (offset (c:=c) hu u) u (packet (c:=c) u)).2
    let q := row (c:=c) r (hu,hv) (u,v)
    wire (c:=c) (q.1.apply u)=encode (if hv then finish t else trailToken) ∧
      (hv=false → wire (c:=c) (q.2.apply v)=encode t) := by
  change (decode (wire (c:=c) u)).tag=2 at F
  cases hv <;>
    simp [row,F,packet,Patch.compose_apply,tokenPatch,Field.read_assign]

/-- Reverse motion is not a provenance test: the row relays the old
decoded reply even through an empty left slot. A fresh F has priority. -/
theorem reverse_wire {c : Nat} (r : Nat) (hu : Bool) (u v : BitVec (W c))
    (F : (packet (c:=c) u).tag≠2) (D : (packet (c:=c) v).tag=3) :
    let q := row (c:=c) r (hu,false) (u,v)
    wire (c:=c) (q.1.apply u)=encode (packet (c:=c) v) ∧
      wire (c:=c) (q.2.apply v)=encode emptyToken := by
  change (decode (wire (c:=c) u)).tag≠2 at F
  change (decode (wire (c:=c) v)).tag=3 at D
  simp [row,F,D,packet,Patch.compose_apply,tokenPatch,Field.read_assign]

theorem terminal_trail_drains {c : Nat} (r : Nat) (hu : Bool) (u v : BitVec (W c))
    (T : (packet (c:=c) u).tag=1) :
    wire (c:=c) (((row (c:=c) r (hu,true) (u,v)).1).apply u)=encode emptyToken := by
  change (decode (wire (c:=c) u)).tag=1 at T
  simp [row,T,Patch.compose_apply,tokenPatch,Field.read_assign]

theorem empty_successor_drains {c : Nat} (r : Nat) (hu : Bool) (u v : BitVec (W c))
    (T : (packet (c:=c) u).tag=1) (E : (packet (c:=c) v).tag=0) :
    wire (c:=c) (((row (c:=c) r (hu,false) (u,v)).1).apply u)=encode emptyToken := by
  change (decode (wire (c:=c) u)).tag=1 at T
  change (decode (wire (c:=c) v)).tag=0 at E
  simp [row,T,E,Patch.compose_apply,tokenPatch,Field.read_assign]

private theorem apply_canon {c : Nat} (v : BitVec (W c)) (d : Token) :
    (if d.fault then tokenPatch c d else Patch.empty _).apply v =
      if d.fault then (tokenPatch c d).apply v else v := by
  by_cases F : d.fault=true
  · rw [if_pos F,if_pos F]
  · rw [if_neg F,if_neg F,empty_apply]

/-- On a valid source WAIT F/T, an incoming header row acts only by
canonical fault materialization. Healthy F/T holds the entire byte. -/
theorem wait_ft_row {c : Nat} (r : Nat) (hu : Bool) (u v : BitVec (W c))
    (P : phase (c:=c) v=2) (O : opcode (c:=c) v≤5)
    (T : (packet (c:=c) v).tag=1 ∨ (packet (c:=c) v).tag=2) :
    let d := packet (c:=c) v
    ((row (c:=c) r (hu,true) (u,v)).2).apply v =
      if d.fault then (tokenPatch c d).apply v else v := by
  have D := wait_ft_door v (packet (c:=c) v) P O T
  have V : doorPatch (c:=c) v (decode (wire (c:=c) v))=.empty _ := D
  by_cases F : (decode (wire (c:=c) u)).tag=2
  · simp [row,packet,V,F,Patch.compose_apply,empty_apply] 
    exact apply_canon v _
  · by_cases G : (decode (wire (c:=c) u)).tag=1 <;>
      simp [row,packet,V,F,G,Patch.compose_apply,empty_apply] <;> exact apply_canon v _

#print axioms wait_ft_door
#print axioms forward_wire
#print axioms reverse_wire
#print axioms terminal_trail_drains
#print axioms empty_successor_drains
#print axioms wait_ft_row

/-- Literal codec fact: arbitrary raw padding can fault but cannot
change the old two-bit family. -/
theorem decode_tag (x : BitVec 16) : (decode x).tag=(x.extractLsb' 14 2).toNat := by
  unfold decode faultCode
  dsimp only
  split
  · rfl
  split
  · rfl
  · rfl

/-- A canonical D-fault remains an inherited reply through decoding. -/
@[simp] theorem fault_reply_codec : decode (encode (faultCode 3))=faultCode 3 := by decide

@[simp] theorem fault_forward_codec : decode (encode (faultCode 2))=faultCode 2 := by decide

@[simp] theorem empty_codec : decode (encode emptyToken)=emptyToken := by decide
@[simp] theorem trail_codec : decode (encode trailToken)=trailToken := by decide

open WidthByteRows in
/-- A concrete old E / inherited PASS-COMPARE pair has a PASS-COMPARE
reply at the left after this one edge, without any forwarding event. -/
theorem reverse_through_empty_fixture :
    let c := 6
    let d : Token := {tag:=3,op:=2,arg:=3}
    let u : BitVec (W c) := 0
    let v : BitVec (W c) := BitVec.ofNat _ (encode d).toNat
    let q := row (c:=c) 5 (true,false) (u,v)
    packet (c:=c) u=emptyToken ∧ packet (c:=c) v=d ∧
      packet (c:=c) (q.1.apply u)=d ∧ packet (c:=c) (q.2.apply v)=emptyToken := by decide

#print axioms decode_tag
#print axioms fault_reply_codec
#print axioms fault_forward_codec
#print axioms reverse_through_empty_fixture

/-- The production wrapper only erases dormant controller flags at
[16,18), so the preceding raw equations lift without losing any
token bit on either side of the pair. -/
theorem work_wire_projection {c : Nat} (r : Nat) (h : Pair Bool) (x : Pair (BitVec (W c))) :
    let p := BStarShort.widthWork (c:=c) r h x
    let q := row (c:=c) r h x
    wire (c:=c) (p.1.apply x.1)=wire (c:=c) (q.1.apply x.1) ∧
      wire (c:=c) (p.2.apply x.2)=wire (c:=c) (q.2.apply x.2) := by
  refine ⟨rfl,?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have E := BStarShort.width_apply_outside (c:=c) r h x i (.inl I)
  change
    (((BStarShort.widthWork (c:=c) r h x).2.apply x.2).extractLsb' 0 16).getLsbD i =
      (((row (c:=c) r h x).2.apply x.2).extractLsb' 0 16).getLsbD i
  simpa [I] using E

#print axioms work_wire_projection
end L4.WidthTokenTransport
