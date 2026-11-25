import Leader.L4.ShortControllerMIS1

namespace L4.ShortOwnerSourceTable
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortControllerEntrance

def held (t : Token) : Bool := t.tag==1 || t.tag==2

def rejected (op : Nat) (t : Token) : Bool :=
  t.tag != 3 || t.opcode != op || t.fault || t.outcome==1

/-- A good COMMIT reply takes the reset branch too. ADMIT must return
the admitted bit. Every other accepted reply advances only one opcode. -/
def advances (op : Nat) (t : Token) : Bool :=
  !rejected op t && decide (op<6) && !(op==2 && t.payload != 1)

def ackPatch (op : Nat) (t : Token) : Patch 96 :=
  if op=3 then
    (((phaseOp 1 (op+1)).compose (put 72 6 (by decide) t.payload)).compose
      (put 68 4 (by decide) 0))
  else phaseOp 1 (op+1)

/-- Exact controller truth table read from the old responder byte.
No ACK label here certifies where the supplied old token originated. -/
theorem wait_table (u : BitVec 96) (t : Token) (op : Nat)
    (phase : get u 81 2 (by decide)=2)
    (cmd : get u 78 3 (by decide)=op) (L : op<7) :
    source u t =
      if held t then (Patch.empty 96,none)
      else if advances op t then (ackPatch op t,some E)
      else (resetSource,some E) := by
  have op7 : op≠7 := by omega
  by_cases F : held t=true
  · have FH : t.tag=1 ∨ t.tag=2 := by simpa [held] using F
    rcases FH with H|H <;> simp [source,phase,cmd,op7,held,H]
  · have FH : t.tag≠1 ∧ t.tag≠2 := by
      constructor
      · intro E; exact F (by simp [held,E])
      · intro E; exact F (by simp [held,E])
    have S : op=0 ∨ op=1 ∨ op=2 ∨ op=3 ∨ op=4 ∨ op=5 ∨ op=6 := by omega
    cases B : rejected op t
    · have BC : (t.tag != 3 || t.opcode != op || t.fault || t.outcome==1)=false := B
      rcases S with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · simp [source,phase,cmd,FH.1,FH.2,held,BC,advances,B,ackPatch]
      · simp [source,phase,cmd,FH.1,FH.2,held,BC,advances,B,ackPatch]
      · by_cases h : t.payload=1
        · simp [source,phase,cmd,FH.1,FH.2,held,BC,advances,B,ackPatch,h]
        · simp [source,phase,cmd,FH.1,FH.2,held,BC,advances,B,h]
      · simp [source,phase,cmd,FH.1,FH.2,held,BC,advances,B,ackPatch]
      · simp [source,phase,cmd,FH.1,FH.2,held,BC,advances,B,ackPatch]
      · simp [source,phase,cmd,FH.1,FH.2,held,BC,advances,B,ackPatch]
      · simp [source,phase,cmd,FH.1,FH.2,held,BC,advances,B]
    · have BC : (t.tag != 3 || t.opcode != op || t.fault || t.outcome==1)=true := B
      simp [source,phase,cmd,op7,FH.1,FH.2,held,BC,advances,B]

theorem issue_table (u : BitVec 96) (t : Token) (op : Nat)
    (phase : get u 81 2 (by decide)=1)
    (cmd : get u 78 3 (by decide)=op) (P : 0<op) (L : op<7) :
    source u t =
      (put 81 2 (by decide) 2,
        some {tag:=2,opcode:=op,payload:=if op=3 then 64 else if 4≤op then issuedDescriptor u else 0}) := by
  rw [issue_fresh u t op phase cmd L,if_neg (by omega : op≠0)]
  congr 1

theorem good_admit_reply (t : Token) (A : rejected 2 t=false) :
    advances 2 t=true ↔ t.payload=1 := by simp [advances,A]

theorem good_commit_reply_resets (u : BitVec 96) (t : Token)
    (phase : get u 81 2 (by decide)=2) (cmd : get u 78 3 (by decide)=6)
    (N : held t=false) : source u t=(resetSource,some E) := by
  rw [wait_table u t 6 phase cmd (by decide)]
  simp [N,advances]

private theorem reset_pc (x : BitVec 96) : pc (resetSource.apply x)=8 := by
  let a : Field 96 5 := lane 78 5 (by decide)
  let b : Field 96 26 := lane 57 26 (by decide)
  let v : BitVec 26 := BitVec.ofNat 26 (2^24)
  have read_zero : a.read ((b.assign v).apply x)=a.read ((b.assign v).apply 0) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hh := (b.inMask v (a.offset+i)).mpr
      (show b.offset≤a.offset+i ∧ a.offset+i<b.offset+26 from by
        change 57≤78+i ∧ 78+i<57+26
        omega)
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    rw [Patch.write _ _ _ hh,Patch.write _ _ _ hh]
  exact (congrArg BitVec.toNat read_zero).trans (by decide)

private theorem phase_pc (x : BitVec 96) (op : Nat) (lt : op<8) :
    pc ((phaseOp 1 op).apply x)=8+op := by
  unfold pc MISByteCodec.get phaseOp put
  rw [Field.read_assign,BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

private theorem read_phase_pc (x : BitVec 96) (reply : Token) :
    pc (((phaseOp 1 4).compose (put 72 6 (by decide) reply.payload)).compose
      (put 68 4 (by decide) 0) |>.apply x)=12 := by
  let a : Field 96 5 := lane 78 5 (by decide)
  let b : Field 96 6 := lane 72 6 (by decide)
  let c : Field 96 4 := lane 68 4 (by decide)
  rw [Patch.compose_apply,Patch.compose_apply]
  change (a.read ((c.assign 0).apply ((b.assign (BitVec.ofNat 6 reply.payload)).apply
    ((phaseOp 1 4).apply x)))).toNat=12
  rw [Field.read_other_assign a c _ _ (.inr (by decide)),
    Field.read_other_assign a b _ _ (.inr (by decide))]
  exact phase_pc x 4 (by decide)

private theorem assigned_k0_pc (t : Token) (b : BitVec 96) :
    pc ((putK 0 t).apply b)=pc b :=
  congrArg BitVec.toNat (Field.read_other_assign (lane 78 5 (by decide)) (kField 0)
    (encode t) b (.inr (by decide)))

/-- On a non-held literal WAIT mark at the physical door, the source
clears K0 and its next PC is exact, not an unclassified disjunction. -/
theorem raw_wait_exit_table {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true) (op : Nat)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (cmd : get (x (rightNeighbor e)).mis1 78 3 (by decide)=op) (L : op<7)
    (N : held (oldK true (x (rightNeighbor e)).mis1 0)=false) :
    let t := oldK true (x (rightNeighbor e)).mis1 0
    let y := (rawNext s x e (rightNeighbor e)).mis1
    (kField 0).read y=encode E ∧ pc y=(if advances op t then 8+(op+1) else 8) := by
  dsimp only
  let old := (x (rightNeighbor e)).mis1
  let t := oldK true old 0
  let y := (rawNext s x e (rightNeighbor e)).mis1
  let P := if advances op t then ackPatch op t else resetSource
  have EE : source old t=(P,some E) := by
    rw [wait_table old t op phase cmd L,show held t=false from N]
    simp only [Bool.false_eq_true,if_false]
    unfold P
    split <;> rfl
  obtain ⟨b,_,A⟩ := ShortControllerMIS1.source_door_raw x e sep head
  change ∀ {k : Nat} (f : Field 96 k), f.offset+k≤93 →
      f.read y = f.read (match (source old t).2 with
        | none => (source old t).1.apply b
        | some q => (putK 0 q).apply ((source old t).1.apply b)) at A
  rw [EE] at A
  have K := (A (kField 0) (by decide)).trans (ShortResetFlow.read_putK _ _ _)
  have V := congrArg BitVec.toNat (A (lane 78 5 (by decide)) (by decide))
  change pc y=pc ((putK 0 E).apply (P.apply b)) at V
  rw [assigned_k0_pc] at V
  refine ⟨K,V.trans ?_⟩
  unfold P
  by_cases F : advances op t=true
  · rw [if_pos F,if_pos F]
    have op6 : op<6 := by
      unfold advances at F
      simp only [Bool.and_eq_true_iff,decide_eq_true_eq] at F
      exact F.1.2
    unfold ackPatch
    by_cases E : op=3
    · rw [if_pos E,E]
      exact read_phase_pc b t
    · rw [if_neg E]
      exact phase_pc b (op+1) (by omega)
  · rw [if_neg F,if_neg F]
    exact reset_pc b

#print axioms raw_wait_exit_table
#print axioms wait_table
#print axioms issue_table
#print axioms good_admit_reply
#print axioms good_commit_reply_resets

theorem advances_iff (op : Nat) (t : Token) :
    advances op t=true ↔ op<6 ∧ t.tag=3 ∧ t.opcode=op ∧ t.fault=false ∧
      t.outcome≠1 ∧ (op=2 → t.payload=1) := by
  by_cases H : op=2 <;>
    simp [advances,rejected,H,and_assoc,and_comm,and_left_comm]

/-- A WAIT source holds the entire source/file window on actual F/T
arrival, even while other lanes at the endpoints execute their rows. -/
theorem raw_wait_held_table {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true) (op : Nat)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (cmd : get (x (rightNeighbor e)).mis1 78 3 (by decide)=op) (L : op<7)
    (hold : held (oldK true (x (rightNeighbor e)).mis1 0)=true) :
    ∀ {k : Nat} (f : Field 96 k), 57≤f.offset → f.offset+k≤83 →
      f.read (rawNext s x e (rightNeighbor e)).mis1=f.read (x (rightNeighbor e)).mis1 := by
  let old := (x (rightNeighbor e)).mis1
  let t := oldK true old 0
  have EE : source old t=(Patch.empty 96,none) := by
    rw [wait_table old t op phase cmd L,if_pos hold]
  obtain ⟨b,B,F⟩ := ShortControllerMIS1.source_door_raw x e sep head
  change ∀ {k : Nat} (f : Field 96 k), f.offset+k≤93 →
      f.read (rawNext s x e (rightNeighbor e)).mis1 =
        f.read (match (source old t).2 with
          | none => (source old t).1.apply b
          | some q => (putK 0 q).apply ((source old t).1.apply b)) at F
  rw [EE] at F
  have Id : (Patch.empty 96).apply b=b := by
    change b &&& BitVec.allOnes 96 ||| 0=b
    rw [BitVec.and_allOnes]
    exact BitVec.or_zero
  intro k f a z
  have T := F f (by omega)
  change f.read (rawNext s x e (rightNeighbor e)).mis1=f.read ((Patch.empty 96).apply b) at T
  rw [Id] at T
  exact T.trans (B f a z)

#print axioms advances_iff
#print axioms raw_wait_held_table
end L4.ShortOwnerSourceTable
