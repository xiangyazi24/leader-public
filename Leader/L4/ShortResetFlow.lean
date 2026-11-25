import Leader.L4.MISByteRows

namespace L4.ShortResetFlow
open AllSizeProtocol MISByteCodec
set_option maxHeartbeats 3000000

def resetForward : Token := { tag := 2 }
def resetReply : Token := { tag := 3 }

theorem resetForward_decode (gate : Bool) :
    decode gate (encode resetForward)=resetForward := by
  cases gate <;> decide

theorem resetReply_decode (gate : Bool) :
    decode gate (encode resetReply)=resetReply := by
  cases gate <;> decide

theorem trail_decode (gate : Bool) : decode gate (encode T)=T := by
  cases gate <;> decide

theorem empty_decode (gate : Bool) : decode gate (encode E)=E := by
  cases gate <;> decide

theorem read_putK (j : Fin 3) (t : Token) (x : BitVec 96) :
    (kField j).read ((putK j t).apply x)=encode t :=
  Field.read_assign _ _ _

theorem read_putK_other (j k : Fin 3) (h : j≠k) (t : Token) (x : BitVec 96) :
    (kField j).read ((putK k t).apply x)=(kField j).read x := by
  have h' := fun a : j.val=k.val => h (Fin.ext a)
  have hj := j.isLt
  have hk := k.isLt
  apply Field.read_other_assign
  change 19*(2-j.val)+19≤19*(2-k.val) ∨ 19*(2-k.val)+19≤19*(2-j.val)
  omega

theorem read_put_high (j : Fin 3) {o w : Nat} (ho : 57≤o) (fits : o+w≤96)
    (val : Nat) (x : BitVec 96) :
    (kField j).read ((put o w fits val).apply x)=(kField j).read x := by
  apply Field.read_other_assign
  left
  change 19*(2-j.val)+19≤o
  omega

theorem reset_issue_source (x : BitVec 96) (t : Token)
    (phase : get x 81 2 (by decide)=1) (op : get x 78 3 (by decide)=0) :
    source x t =
      (resetSource.compose (put 81 2 (by decide) 2),some resetForward) := by
  simp [source,phase,op,resetForward]

theorem reset_consume_source (x : BitVec 96)
    (phase : get x 81 2 (by decide)=2) (op : get x 78 3 (by decide)=0) :
    source x resetReply=(phaseOp 1 1,some E) := by
  simp [source,phase,op,resetReply]

end L4.ShortResetFlow
