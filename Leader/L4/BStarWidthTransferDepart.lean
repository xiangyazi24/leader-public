import Leader.L4.BStarWidthTransferPair

namespace L4.BStarWidthTransferDepart
open AllSizeProtocol

/-- Local data lanes in the WIDTH opcode table, independent of source and rail. -/
structure Data where
  done : BitVec 1
  pick : BitVec 1
  inside : BitVec 1
  last : BitVec 1
  count : BitVec 1
  width : BitVec 1
  deriving DecidableEq, Repr

def lane (c j : Nat) (h : j≤6) : Field (WidthByteRows.W c) 1 :=
  WidthByteRows.suffixField c j 1 (by omega)

def readData {c : Nat} (x : BitVec (WidthByteRows.W c)) : Data :=
  ⟨(lane c 1 (by decide)).read x,(lane c 2 (by decide)).read x,
    (lane c 3 (by decide)).read x,(lane c 4 (by decide)).read x,
    (lane c 5 (by decide)).read x,(lane c 6 (by decide)).read x⟩

/-- Typed operation table using old data, effective offset, and bound old F.
Assigned data fields reflect the semantic branch, not an applied packed patch. -/
def execute (c r i : Nat) (x : Data) (t : WidthByteRows.Token) :
    Data × WidthByteRows.Token :=
  if t.fault then (x,t) else
  match t.op with
  | 0 => ({x with done:=0,pick:=0,count:=0},t)
  | 1 =>
    let choose := x.done.toNat==0 && t.arg==0
    let b := choose.toNat
    ({x with pick:=BitVec.ofNat 1 b,done:=BitVec.ofNat 1 (b ||| x.done.toNat)},
      {t with arg:=t.arg ||| b})
  | 2 =>
    if i<c then
      let cmp := fun d prior =>
        if x.count.toNat<d then 1 else if d<x.count.toNat then 2 else prior
      ({x with}, {t with arg := 4*cmp ((r >>> i)%2) (t.arg/4) + cmp (((r-1) >>> i)%2) (t.arg%4)})
    else (x,t)
  | 3 =>
    if x.pick.toNat==1 then
      ({x with inside:=BitVec.ofNat 1 (t.arg/2),last:=BitVec.ofNat 1 (t.arg%2)},t)
    else (x,t)
  | 4 =>
    if i<c then
      let k := t.arg+x.count.toNat
      ({x with count:=BitVec.ofNat 1 (k%2)},{t with arg:=k/2})
    else (x,t)
  | 5 => ({x with width:=if i<c then x.count else 0},t)
  | _ => (x,t)

/-- Every field assigned by an opcode contributes support even if its
old value equals its new value. Off-domain tokens have no data authority. -/
def assigns (c i : Nat) (x : Data) (t : WidthByteRows.Token) (j : Nat) : Prop :=
  t.fault=false ∧
  match t.op with
  | 0 => j=1 ∨ j=2 ∨ j=5
  | 1 => j=2 ∨ j=1
  | 3 => x.pick.toNat=1 ∧ (j=3 ∨ j=4)
  | 4 => i<c ∧ j=5
  | 5 => j=6
  | _ => False

private theorem hold_empty {w : Nat} (x : BitVec w) : (Patch.empty w).apply x=x := by
  simp [Patch.empty,Patch.apply]

private theorem read_other_lane {c j k : Nat} (hj : j≤6) (hk : k≤6) (ne : j≠k)
    (v : BitVec 1) (x : BitVec (WidthByteRows.W c)) :
    (lane c j hj).read (((lane c k hk).assign v).apply x)=(lane c j hj).read x := by
  apply Field.read_other_assign
  change 30-j-1+1≤30-k-1 ∨ 30-k-1+1≤30-j-1
  omega

private theorem write_done {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : BitVec 1) :
    readData (c:=c) (((lane c 1 (by decide)).assign v).apply x) =
      {readData (c:=c) x with done:=v} := by
  unfold readData
  rw [Field.read_assign,
    read_other_lane (c:=c) (j:=2) (k:=1) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=3) (k:=1) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=4) (k:=1) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=5) (k:=1) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=6) (k:=1) (by decide) (by decide) (by decide)]

private theorem write_pick {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : BitVec 1) :
    readData (c:=c) (((lane c 2 (by decide)).assign v).apply x) =
      {readData (c:=c) x with pick:=v} := by
  unfold readData
  rw [Field.read_assign,
    read_other_lane (c:=c) (j:=1) (k:=2) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=3) (k:=2) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=4) (k:=2) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=5) (k:=2) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=6) (k:=2) (by decide) (by decide) (by decide)]

private theorem write_inside {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : BitVec 1) :
    readData (c:=c) (((lane c 3 (by decide)).assign v).apply x) =
      {readData (c:=c) x with inside:=v} := by
  unfold readData
  rw [Field.read_assign,
    read_other_lane (c:=c) (j:=1) (k:=3) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=2) (k:=3) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=4) (k:=3) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=5) (k:=3) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=6) (k:=3) (by decide) (by decide) (by decide)]

private theorem write_last {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : BitVec 1) :
    readData (c:=c) (((lane c 4 (by decide)).assign v).apply x) =
      {readData (c:=c) x with last:=v} := by
  unfold readData
  rw [Field.read_assign,
    read_other_lane (c:=c) (j:=1) (k:=4) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=2) (k:=4) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=3) (k:=4) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=5) (k:=4) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=6) (k:=4) (by decide) (by decide) (by decide)]

private theorem write_count {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : BitVec 1) :
    readData (c:=c) (((lane c 5 (by decide)).assign v).apply x) =
      {readData (c:=c) x with count:=v} := by
  unfold readData
  rw [Field.read_assign,
    read_other_lane (c:=c) (j:=1) (k:=5) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=2) (k:=5) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=3) (k:=5) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=4) (k:=5) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=6) (k:=5) (by decide) (by decide) (by decide)]

private theorem write_width {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : BitVec 1) :
    readData (c:=c) (((lane c 6 (by decide)).assign v).apply x) =
      {readData (c:=c) x with width:=v} := by
  unfold readData
  rw [Field.read_assign,
    read_other_lane (c:=c) (j:=1) (k:=6) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=2) (k:=6) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=3) (k:=6) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=4) (k:=6) (by decide) (by decide) (by decide),
    read_other_lane (c:=c) (j:=5) (k:=6) (by decide) (by decide) (by decide)]

private theorem write_done_nat {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : Nat) :
    readData (c:=c) ((WidthByteRows.put c 1 1 (by decide) v).apply x) =
      {readData (c:=c) x with done:=BitVec.ofNat 1 v} := write_done x _
private theorem write_pick_nat {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : Nat) :
    readData (c:=c) ((WidthByteRows.put c 2 1 (by decide) v).apply x) =
      {readData (c:=c) x with pick:=BitVec.ofNat 1 v} := write_pick x _
private theorem write_inside_nat {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : Nat) :
    readData (c:=c) ((WidthByteRows.put c 3 1 (by decide) v).apply x) =
      {readData (c:=c) x with inside:=BitVec.ofNat 1 v} := write_inside x _
private theorem write_last_nat {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : Nat) :
    readData (c:=c) ((WidthByteRows.put c 4 1 (by decide) v).apply x) =
      {readData (c:=c) x with last:=BitVec.ofNat 1 v} := write_last x _
private theorem write_count_nat {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : Nat) :
    readData (c:=c) ((WidthByteRows.put c 5 1 (by decide) v).apply x) =
      {readData (c:=c) x with count:=BitVec.ofNat 1 v} := write_count x _
private theorem write_width_nat {c : Nat} (x : BitVec (WidthByteRows.W c)) (v : Nat) :
    readData (c:=c) ((WidthByteRows.put c 6 1 (by decide) v).apply x) =
      {readData (c:=c) x with width:=BitVec.ofNat 1 v} := write_width x _

/-- Exact all-raw data and token transfer for the departing opcode,
including malformed tokens and any effective offset. -/
theorem execute_transfer {c : Nat} (r i : Nat) (x : BitVec (WidthByteRows.W c))
    (t : WidthByteRows.Token) :
    let q := WidthByteRows.departing (c:=c) r i x t
    (readData (c:=c) (q.1.apply x),q.2) = execute c r i (readData (c:=c) x) t := by
  obtain ⟨tag,op,arg,fault⟩ := t
  cases fault
  · match op with
    | 0 =>
      simp only [WidthByteRows.departing,execute,Bool.false_eq_true,if_false,
        Patch.compose_apply,write_count_nat,write_pick_nat,write_done_nat]
      rfl
    | 1 =>
      simp only [WidthByteRows.departing,execute,Bool.false_eq_true,if_false,
        Patch.compose_apply,write_done_nat,write_pick_nat]
      have E (a : Bool) : (if a=true then 1 else 0 : Nat) = a.toNat := by cases a <;> rfl
      rw [E]
      rfl
    | 2 =>
      simp only [WidthByteRows.departing,execute,Bool.false_eq_true,if_false]
      split <;> (rw [hold_empty] <;> rfl)
    | 3 =>
      simp only [WidthByteRows.departing,execute,Bool.false_eq_true,if_false]
      split
      · rename_i H
        change (((readData (c:=c) x).pick.toNat==1)=true) at H
        simp only [H,if_true,Patch.compose_apply,write_last_nat,write_inside_nat]
      · rename_i H
        change ¬(((readData (c:=c) x).pick.toNat==1)=true) at H
        simp only [H,Bool.false_eq_true,if_false,hold_empty]
    | 4 =>
      simp only [WidthByteRows.departing,execute,Bool.false_eq_true,if_false]
      split
      · rw [write_count_nat]; rfl
      · rw [hold_empty]
    | 5 =>
      simp only [WidthByteRows.departing,execute,Bool.false_eq_true,if_false,write_width_nat]
      split
      · have E : BitVec.ofNat 1 (WidthByteRows.get (c:=c) x 5 1 (by decide)) =
            (readData (c:=c) x).count := by
          change BitVec.ofNat 1 (readData (c:=c) x).count.toNat = _
          simp
        rw [E]
      · rfl
    | n+6 =>
      change (readData (c:=c) ((Patch.empty _).apply x),_)= (readData (c:=c) x,_)
      rw [hold_empty]
      rfl
  · change (readData (c:=c) ((Patch.empty _).apply x),_)= (readData (c:=c) x,_)
    rw [hold_empty]
    rfl

private theorem put_support {c j : Nat} (hj : j≤6) (v b : Nat) :
    (WidthByteRows.put c j 1 (by omega) v).mask.getLsbD b=true ↔ b=29-j := by
  change (((lane c j hj).assign (BitVec.ofNat 1 v)).mask.getLsbD b=true) ↔ _
  rw [Field.inMask]
  change (30-j-1≤b ∧ b<30-j-1+1) ↔ _
  omega

private theorem compose_support {w b : Nat} (p q : Patch w) :
    ((p.compose q).mask.getLsbD b=true) ↔ p.mask.getLsbD b=true ∨ q.mask.getLsbD b=true := by
  simp only [Patch.compose,BitVec.getLsbD_or,Bool.or_eq_true]

private theorem empty_support {w b : Nat} : ((Patch.empty w).mask.getLsbD b=true) ↔ False := by
  simp [Patch.empty]

/-- Exact numerical support of a departing operation; every assignment
is counted even where it leaves the previous raw bit unchanged. -/
theorem execute_support {c : Nat} (r i : Nat) (x : BitVec (WidthByteRows.W c))
    (t : WidthByteRows.Token) (b : Nat) :
    (WidthByteRows.departing (c:=c) r i x t).1.mask.getLsbD b=true ↔
      ∃ j, assigns c i (readData (c:=c) x) t j ∧ b=29-j := by
  obtain ⟨tag,op,arg,fault⟩ := t
  cases fault
  · match op with
    | 0 =>
      simp only [WidthByteRows.departing,assigns,Bool.false_eq_true,if_false,true_and,
        compose_support,put_support (by decide : 1≤6),put_support (by decide : 2≤6),
        put_support (by decide : 5≤6)]
      simp [or_and_right,exists_or,or_comm,or_assoc]
    | 1 =>
      simp only [WidthByteRows.departing,assigns,Bool.false_eq_true,if_false,true_and,
        compose_support,put_support (by decide : 1≤6),put_support (by decide : 2≤6)]
      simp [or_and_right,exists_or,or_comm]
    | 2 =>
      simp only [WidthByteRows.departing,assigns,Bool.false_eq_true,if_false,true_and]
      split <;> simp [empty_support]
    | 3 =>
      simp only [WidthByteRows.departing,assigns,Bool.false_eq_true,if_false,true_and]
      split
      · rename_i H
        change (((readData (c:=c) x).pick.toNat==1)=true) at H
        have P := beq_iff_eq.mp H
        simp only [P,true_and,compose_support,
          put_support (by decide : 3≤6),put_support (by decide : 4≤6)]
        simp [or_and_right,exists_or,or_comm]
      · rename_i H
        change ¬(((readData (c:=c) x).pick.toNat==1)=true) at H
        have P : (readData (c:=c) x).pick.toNat≠1 := fun e => H (beq_iff_eq.mpr e)
        simp [P,empty_support]
    | 4 =>
      simp only [WidthByteRows.departing,assigns,Bool.false_eq_true,if_false,true_and]
      split
      · rename_i H
        simp only [H,true_and,put_support (by decide : 5≤6)]
        simp
      · rename_i H
        simp [H,empty_support]
    | 5 =>
      simp only [WidthByteRows.departing,assigns,Bool.false_eq_true,if_false,true_and,
        put_support (by decide : 6≤6)]
      simp
    | n+6 =>
      change ((Patch.empty (WidthByteRows.W c)).mask.getLsbD b=true ↔ ∃ j : Nat, (false=false ∧ False) ∧ b=29-j)
      simp [empty_support]
  · simp [WidthByteRows.departing,assigns,empty_support]

#print axioms execute_transfer
#print axioms execute_support
end L4.BStarWidthTransferDepart

