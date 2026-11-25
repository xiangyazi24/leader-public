import Leader.L4.WidthChecksum

namespace L4.WidthOwnerController

open AllSizeProtocol WidthByteRows
set_option maxHeartbeats 1600000

def phase {c : Nat} (x : BitVec (W c)) : Nat :=
  WidthByteRows.get (c:=c) x 7 2 (by decide)
def opcode {c : Nat} (x : BitVec (W c)) : Nat :=
  WidthByteRows.get (c:=c) x 9 3 (by decide)
def argument {c : Nat} (x : BitVec (W c)) : Nat :=
  WidthByteRows.get (c:=c) x 12 2 (by decide)
def done {c : Nat} (x : BitVec (W c)) : Nat :=
  WidthByteRows.get (c:=c) x 1 1 (by decide)
def pick {c : Nat} (x : BitVec (W c)) : Nat :=
  WidthByteRows.get (c:=c) x 2 1 (by decide)

def nextControl (op a : Nat) : Nat × Nat :=
  match op with
  | 0 => (1,0)
  | 1 => (if a==1 then 2 else 5,0)
  | 2 => (3,a)
  | 3 => (4,0)
  | 4 => (1,0)
  | _ => (0,0)

def clearDoor (c op arg : Nat) : Patch (W c) :=
  (control c 1 op arg).compose (tokenPatch c emptyToken)

theorem wait_on_live {c : Nat} (x : BitVec (W c)) (t : Token)
    (P : phase (c:=c) x=2) (O : opcode (c:=c) x≤5) (T : t.tag=1 ∨ t.tag=2) :
    doorPatch (c:=c) x t = .empty _ := by
  unfold phase at P
  unfold opcode at O
  rcases T with T|T <;>
    simp [doorPatch,P, Nat.not_lt.mpr O,T]

theorem wait_fault_or_empty {c : Nat} (x : BitVec (W c)) (t : Token)
    (P : phase (c:=c) x=2) (O : opcode (c:=c) x≤5)
    (A : t.tag=0 ∨ (t.tag=3 ∧ t.fault=true)) :
    doorPatch (c:=c) x t = clearDoor c 0 0 := by
  unfold phase at P
  unfold opcode at O
  rcases A with A|⟨A,F⟩
  · simp [doorPatch,P, Nat.not_lt.mpr O,A,clearDoor]
  · simp [doorPatch,P, Nat.not_lt.mpr O,A,F,clearDoor]

theorem wait_good_reply {c : Nat} (x : BitVec (W c)) (t : Token)
    (P : phase (c:=c) x=2) (O : opcode (c:=c) x≤5)
    (A : t.tag=3) (B : t.op=opcode (c:=c) x) (F : t.fault=false) :
    doorPatch (c:=c) x t =
      match t.op with
      | 0 => clearDoor c 1 0
      | 1 => clearDoor c (if t.arg==1 then 2 else 5) 0
      | 2 => clearDoor c 3 t.arg
      | 3 => clearDoor c 4 0
      | 4 => clearDoor c 1 0
      | _ => clearDoor c 0 0 := by
  unfold phase at P
  unfold opcode at O B
  rw [←B] at O
  have K : t.op=0 ∨ t.op=1 ∨ t.op=2 ∨ t.op=3 ∨ t.op=4 ∨ t.op=5 := by omega
  rcases K with K|K|K|K|K|K <;>
    simp [doorPatch,P,←B,K,A,F,clearDoor]

/-- The first genuine BEGIN is the actual ISSUE0 source row. There is
no condition on old K: the source overwrites it rather than crediting
an inherited forward or reply token. -/
theorem issue_begin {c : Nat} (x : BitVec (W c)) (t : Token)
    (P : phase (c:=c) x=1) (O : opcode (c:=c) x=0) :
    doorPatch (c:=c) x t =
      (put c 7 2 (by decide) 2).compose (tokenPatch c {tag:=2}) := by
  unfold phase at P
  unfold opcode at O
  simp [doorPatch,P,O]

theorem incoming_issue_begin_wire {c : Nat} (r : Nat) (hu : Bool)
    (u v : BitVec (W c)) (P : phase (c:=c) v=1) (O : opcode (c:=c) v=0) :
    ((suffixField c 14 16 (by decide)).read
      ((row (c:=c) r (hu,true) (u,v)).2.apply v))=encode {tag:=2} := by
  unfold row
  simp only [issue_begin v _ P O,if_true,Patch.compose_apply]
  exact Field.read_assign _ _ _

theorem incoming_issue_begin_phase {c : Nat} (r : Nat) (hu : Bool)
    (u v : BitVec (W c)) (P : phase (c:=c) v=1) (O : opcode (c:=c) v=0) :
    phase (c:=c) ((row (c:=c) r (hu,true) (u,v)).2.apply v)=2 := by
  unfold row
  simp only [issue_begin v _ P O,if_true,Patch.compose_apply]
  unfold phase WidthByteRows.get put tokenPatch
  rw [Field.read_other_assign _ _ _ _ (.inr (by simp [suffixField])),Field.read_assign]
  rfl

private theorem get_after_put_other {c : Nat} (x : BitVec (W c))
    (j k : Nat) (J : j+1≤30) (K : k+1≤30) (N : j≠k) (a : Nat) :
    WidthByteRows.get (c:=c) ((put c k 1 K a).apply x) j 1 J =
    WidthByteRows.get (c:=c) x j 1 J := by
  unfold WidthByteRows.get put
  rw [Field.read_other_assign]
  simp only [suffixField]
  by_cases E : j<k
  · right; omega
  · left; omega

private theorem get_after_put_zero {c : Nat} (x : BitVec (W c))
    (j : Nat) (J : j+1≤30) :
    WidthByteRows.get (c:=c) ((put c j 1 J 0).apply x) j 1 J = 0 := by
  unfold WidthByteRows.get put
  rw [Field.read_assign]
  rfl

/-- BEGIN resets DONE, PICK and the carry counter but does not paint
IN/LAST, which must already be retained on a self-protecting suffix. -/
theorem begin_departure_fields {c : Nat} (r i : Nat) (x : BitVec (W c)) :
    let y := (departing (c:=c) r i x {tag:=2}).1.apply x
    done (c:=c) y=0 ∧ pick (c:=c) y=0 ∧ WidthChecksum.counter (c:=c) y=0 ∧
      inside (c:=c) y=inside (c:=c) x ∧ last (c:=c) y=last (c:=c) x ∧
      WidthChecksum.output (c:=c) y=WidthChecksum.output (c:=c) x := by
  simp only [departing, Bool.false_eq_true, if_false, Patch.compose_apply, done, pick,
    WidthChecksum.counter, inside, last, WidthChecksum.output]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [get_after_put_other _ 1 5 _ _ (by decide),
      get_after_put_other _ 1 2 _ _ (by decide),get_after_put_zero]
  · rw [get_after_put_other _ 2 5 _ _ (by decide),get_after_put_zero]
  · rw [get_after_put_zero]
  · rw [get_after_put_other _ 3 5 _ _ (by decide),
      get_after_put_other _ 3 2 _ _ (by decide),get_after_put_other _ 3 1 _ _ (by decide)]
  · rw [get_after_put_other _ 4 5 _ _ (by decide),
      get_after_put_other _ 4 2 _ _ (by decide),get_after_put_other _ 4 1 _ _ (by decide)]
  · rw [get_after_put_other _ 6 5 _ _ (by decide),
      get_after_put_other _ 6 2 _ _ (by decide),get_after_put_other _ 6 1 _ _ (by decide)]

end L4.WidthOwnerController
