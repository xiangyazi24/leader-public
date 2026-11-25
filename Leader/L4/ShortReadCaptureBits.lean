import Leader.L4.ShortReadForward

namespace L4.ShortReadCaptureBits
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortReadForward

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Public bit accessor for the READ packet payload. -/
def bitAt (p i : Nat) : Bool := (p >>> i)%2==1

/-- A capture exists only at a real old header and only if its
old-pair allocator wins that exact lane. -/
def wins {s n : Nat} (x : Raw s n) (e : Fin n) (j : Fin 3) : Bool :=
  header x e && readWins (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j

def seenSelector {s n : Nat} (x : Raw s n) (e : Fin n) : Bool :=
  (x e).mis1.getLsbD 92

def seenValue {s n : Nat} (x : Raw s n) (e : Fin n) : Bool :=
  (x e).mis1.getLsbD (88-get (x e).mis1 92 1 (by decide))

def updateBit {s n : Nat} (x : Raw s n) (e : Fin n) (j : Fin 3)
    (d : Nat) (i : Fin 6) : Bool :=
  if wins x e j then
    if i.val=5-j.val then seenSelector x e
    else if i.val=2-j.val then seenValue x e
    else bitAt d i.val
  else bitAt d i.val

theorem hop_bits {s n : Nat} (x : Raw s n) (e : Fin n) (j k : Fin 3)
    (d : Nat) (L : d<128) (H : oldK (header x e) (x e).mis1 j=readFront d) :
    let q := hopPacket x e j k
    bitAt q.payload 6 = (bitAt d 6 && (!header x e || wins x e j)) ∧
      ∀ i : Fin 6, bitAt q.payload i.val = updateBit x e j d i := by
  let hv := header x (rightNeighbor e)
  let u := (x e).mis1
  let v := (x (rightNeighbor e)).mis1
  have op : (oldK (header x e) u j).opcode=3 := congrArg Token.opcode H
  have live : (oldK (header x e) u j).fault=false := congrArg Token.fault H
  have P : (oldK (header x e) u j).payload<128 := by rw [show oldK (header x e) u j=readFront d from H]; exact L
  have sticky := read_forwardPacket_sticky (header x e) hv u v j k op live P
  have payload := congrArg Token.payload (read_forwardPacket (header x e) hv u v j k op live)
  have old : (oldK (header x e) u j).payload=d := congrArg Token.payload H
  refine ⟨?_,?_⟩
  · have A : bitAt (hopPacket x e j k).payload 6 =
          (bitAt (oldK (header x e) u j).payload 6 &&
            (!header x e || readWins (header x e) hv u v j)) := sticky
    rw [A,old]
    unfold wins
    cases h : header x e <;> simp [hv,u,v]
  · intro i
    change bitAt (forwardPacket (header x e) hv u v j k).payload i.val =
      updateBit x e j d i
    rw [payload]
    rw [old]
    unfold updateBit wins
    cases h : header x e
    · simp
    · cases w : readWins true hv u v j
      · simp only [Bool.true_and,Bool.false_eq_true,if_false,if_true]
        exact (readLoss_bits d L).2.2 i
      · simp only [Bool.true_and,if_true]
        have Q := readCapture_native u j d L
        by_cases hi : i.val=5-j.val
        · rw [if_pos hi,hi]
          exact Q.1
        · rw [if_neg hi]
          by_cases hi' : i.val=2-j.val
          · rw [if_pos hi',hi']
            exact Q.2
          · rw [if_neg hi']
            exact (readCapture_bits u j d L).2.2.2.2 i hi hi'

theorem reply_of_hop_payload {s n : Nat} (x : Raw s n) (e : Fin n) (j : Fin 3)
    (d : Nat) (H : oldK (header x e) (x e).mis1 j=readFront d) :
    let q := (hopPacket x e j 0).payload
    replyPacket x e j = if bitAt q 6 then {tag:=3, opcode:=3, payload:=q%64}
      else {tag:=3,opcode:=3,outcome:=1} := by
  have op : (oldK (header x e) (x e).mis1 j).opcode=3 := congrArg Token.opcode H
  have live : (oldK (header x e) (x e).mis1 j).fault=false := congrArg Token.fault H
  unfold replyPacket hopPacket
  rw [read_turnPacket _ _ _ _ _ op live,read_forwardPacket _ _ _ _ _ _ op live]
  rfl

private theorem low_mod_fin :
    ∀ (d : Fin 128) (i : Fin 6), bitAt (d.val%64) i.val=bitAt d.val i.val := by decide

theorem low_mod (d : Nat) (L : d<128) (i : Fin 6) :
    bitAt (d%64) i.val=bitAt d i.val := low_mod_fin ⟨d,L⟩ i

theorem terminal_bits {s n : Nat} (x : Raw s n) (e : Fin n) (j : Fin 3)
    (d : Nat) (L : d<128) (H : oldK (header x e) (x e).mis1 j=readFront d) :
    let r := replyPacket x e j
    ((r.outcome==0) = (bitAt d 6 && (!header x e || wins x e j))) ∧
      ((r.outcome==0)=true → ∀ i : Fin 6, bitAt r.payload i.val=updateBit x e j d i) := by
  let q := (hopPacket x e j 0).payload
  have A := reply_of_hop_payload x e j d H
  have HB : bitAt q 6 = (bitAt d 6 && (!header x e || wins x e j)) ∧
      ∀ i : Fin 6, bitAt q i.val=updateBit x e j d i := hop_bits x e j 0 d L H
  have qlt : q<128 := (hop_packet_canonical x e j 0 d L H).1
  change replyPacket x e j = if bitAt q 6 then {tag:=3, opcode:=3, payload:=q%64}
      else {tag:=3,opcode:=3,outcome:=1} at A
  dsimp only
  rw [←HB.1,A]
  cases h : bitAt q 6
  · simp
  · simp only [if_true]
    refine ⟨rfl,?_⟩
    intro _ i
    exact (low_mod q qlt i).trans (HB.2 i)

private theorem low_wire_fin :
    ∀ (d : Fin 64) (i : Fin 6), (BitVec.ofNat 6 d.val).getLsbD i.val=bitAt d.val i.val := by decide

theorem low_wire (d : Fin 64) (i : Fin 6) :
    (BitVec.ofNat 6 d.val).getLsbD i.val=bitAt d.val i.val := low_wire_fin d i

end L4.ShortReadCaptureBits
