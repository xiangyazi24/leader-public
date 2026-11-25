import Leader.L4.ShortResetRow
import Leader.L4.ShortOwnerSourceTable

namespace L4.ShortHelloAdmitCodec
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortControllerEntrance ShortOwnerSourceTable ShortResetRow

/-- A canonical ADMIT wire F packet. With the old K1 gate active,
only races 1..5 are valid. Away from the gate only race 0 is valid. -/
def admitForward (won : Bool) (race : Nat) : Token :=
  {tag:=2,opcode:=2,payload:=won.toNat,race:=race}

def admitReply (won : Bool) : Token :=
  {tag:=3,opcode:=2,payload:=won.toNat}

theorem decode_hello :
    ∀ gate : Bool, decode gate (encode helloForward)=helloForward ∧
                   decode gate (encode helloReply)=helloReply := by decide

theorem decode_admit_reply :
    ∀ (gate won : Bool), decode gate (encode (admitReply won))=admitReply won := by decide

private theorem admit_codec_finite :
    ∀ (gate won : Bool) (r : Fin 8), decode gate (encode (admitForward won r.val))=
      if (if gate then 1≤r.val ∧ r.val≤5 else r.val=0) then
        admitForward won r.val else faultToken 2 := by decide

theorem decode_admit_forward (gate won : Bool) (r : Nat) (B : r<8) :
    decode gate (encode (admitForward won r))=
      if (if gate then 1≤r ∧ r≤5 else r=0) then
        admitForward won r else faultToken 2 :=
  admit_codec_finite gate won ⟨r,B⟩

theorem admit_gate_header (b : BitVec 96) (j : Fin 3) :
    atGate true b j=true ↔ j=1 := by
  simp [atGate,off,Fin.ext_iff]

theorem admit_gate_k0 (h : Bool) (b : BitVec 96) : atGate h b 0=false := by
  simp [atGate]

/-- HELLO cannot change the gate or carry a payload. A canonical
D1 consumed at the real WAIT1 door clears K0 and enters ISSUE2. -/
theorem consume_hello {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (cmd : get (x (rightNeighbor e)).mis1 78 3 (by decide)=1)
    (D : (kField 0).read (x (rightNeighbor e)).mis1=encode helloReply) :
    let y := (rawNext s x e (rightNeighbor e)).mis1
    (kField 0).read y=encode E ∧ pc y=10 := by
  have K : oldK true (x (rightNeighbor e)).mis1 0=helloReply := by
    unfold oldK
    rw [D,(decode_hello _).2]
  have H := raw_wait_exit_table x e sep head 1 phase cmd (by decide) (by rw [K]; decide)
  simpa only [K,show advances 1 helloReply=true by decide,if_true] using H

/-- The literal WAIT2 door clears K0 and enters ISSUE3 exactly on
payload 1; payload 0 instead enters ISSUE0, before the next reset
tour. This lemma classifies the byte, not its provenance. -/
theorem consume_admit {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (cmd : get (x (rightNeighbor e)).mis1 78 3 (by decide)=2)
    (won : Bool)
    (D : (kField 0).read (x (rightNeighbor e)).mis1=encode (admitReply won)) :
    let y := (rawNext s x e (rightNeighbor e)).mis1
    (kField 0).read y=encode E ∧ pc y=(if won then 11 else 8) := by
  have K : oldK true (x (rightNeighbor e)).mis1 0=admitReply won := by
    unfold oldK
    rw [D,decode_admit_reply]
  have H := raw_wait_exit_table x e sep head 2 phase cmd (by decide)
    (by rw [K]; cases won <;> decide)
  have X : advances 2 (admitReply won)=won := by cases won <;> decide
  simpa only [K,X] using H

#print axioms decode_hello
#print axioms decode_admit_reply
#print axioms decode_admit_forward
#print axioms admit_gate_header
#print axioms admit_gate_k0
#print axioms consume_hello
#print axioms consume_admit
end L4.ShortHelloAdmitCodec
