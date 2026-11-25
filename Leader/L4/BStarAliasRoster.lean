import Leader.L4.BStarAliasFold

/-! Kernel-checked arithmetic receipt partition of the pinned 474 SSA
instructions. Relative head ordinal (k) is wire opcode (13+k). -/
namespace L4.BStarAliasRoster
open BStarLongArithmetic BStarLongSignatures BStarCmpReceipt
open AllSizeProtocol BStarTrace BStarLongLayout
open L4.Compiler.Native

def start (k : Nat) : Nat := tourNodes[k]?.getD 474

def chunk (k : Nat) : List Code :=
  (literal.drop (start k)).take (start (k+1)-start k)

def legalChunk (k : Nat) : Bool :=
  let a := start k
  let e := start (k+1)
  decide (a<e) && decide (e≤474) &&
    ((get a).map physical).getD false &&
    ((literal.drop (a+1)).take (e-a-1)).all (fun c => !physical c) &&
    (if e=474 then true else ((get e).map physical).getD false)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem first_last :
    nodeOf 13=some 0 ∧ nodeOf 407=some 473 ∧ start 395=474 := by
  decide +kernel

/-- First arithmetic work is scheduled by the actual preceding
opcode-12 receipt; arithmetic ordinal zero is not a convention alone. -/
theorem first_receipt (x : BitVec LW) (p : BStarLongToken.Payload) :
    BStarLongDoor.afterReply 12 p x =
      (BStarLongDoor.schedule 13).compose
        ((BStarLongDoor.scalarFile.assign 0).compose (BStarLongLayout.need.assign 0)) := by
  rfl

theorem scheduled_node {k : Nat} (h : k<395) :
    nodeOf (13+k)=some (start k) := by
  have L : tourNodes.length=395 := actual_table_lengths.1
  have M : k<tourNodes.length := by omega
  have E : tourNodes[k]?=some (tourNodes[k]'M) := by simp [M]
  simp [nodeOf,start,E]

theorem next_scheduled_node {k : Nat} (h : k<394) :
    nodeOf ((13+k)+1)=some (start (k+1)) := by
  simpa [Nat.add_assoc] using scheduled_node (k:=k+1) (by omega)

def suffix (k : Nat) : List Code :=
  ((literal.drop (start k+1)).take (start (k+1)-start k-1))

def rosterOK (k : Nat) : Bool :=
  legalChunk k &&
    decide (((literal.drop (start k+1)).takeWhile (fun c => !physical c))=suffix k)

theorem aliases_take (old : BitVec LW) (j : Nat) (cs : List Code) (xs : Pending) :
    aliases old j cs xs=aliases old j (cs.takeWhile (fun c => !physical c)) xs := by
  induction cs generalizing j xs with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp [physical,aliases,List.takeWhile,aliasValue,ih]

/-- The comparison predicate for the accepted literal itself. -/
def literalCmp (i : Nat) : Prop := ((get i).map isCmp).getD false=true

def aliasChecks : Nat → List Code → Bool
  | _, [] => true
  | j, c::cs =>
    !((get j).map isCmp).getD false &&
    (match c with
      | .header _ _ | .bconst _ => true
      | .cmpEq a | .cmpLt a => decide (a<j) && ((get a).map isCmp).getD false
      | _ => false) && aliasChecks (j+1) cs

def entryOK (k : Nat) := rosterOK k && aliasChecks (start k+1) (suffix k)

private theorem serial : ∀ k : Fin 395, entryOK k.val=true := by
  intro k
  have H := k.isLt
  have part : k.val / 10 < 40 := by omega
  have rem : k.val % 10 < 10 := Nat.mod_lt _ (by decide)
  have E : k.val = 10*(k.val/10) + k.val%10 := by omega
  have C : ∀ b : Fin 40, (List.range 10).all (fun j =>
      if 10*b.val+j<395 then entryOK (10*b.val+j) else true)=true := by
    intro b
    have Q := b.isLt
    have B : b.val=0 ∨ b.val=1 ∨ b.val=2 ∨ b.val=3 ∨ b.val=4 ∨ b.val=5 ∨ b.val=6 ∨ b.val=7 ∨ b.val=8 ∨ b.val=9 ∨ b.val=10 ∨ b.val=11 ∨ b.val=12 ∨ b.val=13 ∨ b.val=14 ∨ b.val=15 ∨ b.val=16 ∨ b.val=17 ∨ b.val=18 ∨ b.val=19 ∨ b.val=20 ∨ b.val=21 ∨ b.val=22 ∨ b.val=23 ∨ b.val=24 ∨ b.val=25 ∨ b.val=26 ∨ b.val=27 ∨ b.val=28 ∨ b.val=29 ∨ b.val=30 ∨ b.val=31 ∨ b.val=32 ∨ b.val=33 ∨ b.val=34 ∨ b.val=35 ∨ b.val=36 ∨ b.val=37 ∨ b.val=38 ∨ b.val=39 := by omega
    rcases B with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> (rw [h]; decide +kernel)
  have Z := List.all_eq_true.mp (C ⟨k.val/10,part⟩) (k.val%10) (List.mem_range.mpr rem)
  rw [← E,if_pos H] at Z
  exact Z

theorem valid_chunk {k : Nat} (h : k<395) : legalChunk k=true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (serial ⟨k,h⟩)).1).1

theorem maximal_suffix {k : Nat} (h : k<395) :
    (literal.drop (start k+1)).takeWhile (fun c => !physical c)=suffix k :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (serial ⟨k,h⟩)).1).2

theorem partition_prefix {k : Nat} (h : k≤395) :
    (List.range k).flatMap chunk=literal.take (start k) := by
  induction k with
  | zero => have Z : start 0=0 := by decide +kernel
            simp [Z]
  | succ k ih =>
    have H := valid_chunk (k:=k) (by omega)
    unfold legalChunk at H
    have L : start k < start (k+1) := by
      simp only [Bool.and_eq_true] at H
      exact of_decide_eq_true H.1.1.1.1
    rw [List.range_succ,List.flatMap_append,ih (by omega)]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,chunk]
    rw [List.take_drop,show start k+(start (k+1)-start k)=start (k+1) by omega]
    have E := List.take_append_drop (start k) (literal.take (start (k+1)))
    rwa [List.take_take,Nat.min_eq_left (by omega)] at E

theorem partition : (List.range 395).flatMap chunk=literal := by
  rw [partition_prefix (by decide),first_last.2.2]
  exact List.take_of_length_le (by simp only [literal_length, Nat.le_refl])

/-- The actual lowering traverses exactly the kernel-certified maximal
alias suffix; the next physical opcode retires the next SSA head. -/
theorem accept_roster (old : BitVec LW) (p : BStarLongToken.Payload)
    {k : Nat} (H : k<394) (c : Code) (G : get (start k)=some c) :
    let pending := (nodeResult old p.argument.toNat c).toList.map (fun v => (start k,v))
    let xs := aliases old (start k+1) (suffix k) pending
    acceptFile old (13+k) p =
      (BStarLongOutgoing.fuse (xs.reverse.map fun (a,v) => writeScalar a v)).compose
        (BStarLongDoor.schedule (13+(k+1))) := by
  dsimp only
  rw [BStarAliasFold.accept_nonfinal old (13+k) p (start k) c
    (scheduled_node (by omega)) G (by omega)]
  rw [aliases_take, maximal_suffix (by omega : k<395)]
  simp [Nat.add_assoc]

open BStarAliasFold L4.Compiler.Interp

theorem checked_segment (bank : Bank) (old : BitVec LW) (j : Nat) (cs : List Code)
    (H : ∀ q i, ((capturedHeader q i).read old).toNat=(bank.hdr q i).toNat)
    (C : aliasChecks j cs=true) :
    Segment bank old literalCmp j cs := by
  induction cs generalizing j with
  | nil => exact .nil _
  | cons c cs ih =>
    simp only [aliasChecks,Bool.and_eq_true,Bool.not_eq_true'] at C
    obtain ⟨⟨fresh,legal⟩,tail⟩ := C
    refine .cons ?_ ?_ (ih _ tail)
    · cases c <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at legal
      all_goals first
        | exact False.elim legal
        | exact .header _ _ (H _ _)
        | exact .literal _
        | exact .eq _ (of_decide_eq_true legal.1) legal.2
        | exact .lt _ (of_decide_eq_true legal.1) legal.2
    · unfold literalCmp
      rw [fresh]
      decide

theorem roster_segment (bank : Bank) (old : BitVec LW) {k : Nat} (K : k<395)
    (H : ∀ q i, ((capturedHeader q i).read old).toNat=(bank.hdr q i).toNat) :
    Segment bank old literalCmp (start k+1) (suffix k) :=
  checked_segment bank old _ _ H (Bool.and_eq_true_iff.mp (serial ⟨k,K⟩)).2

theorem roster_alias_run {r : Nat} (T : PrimTable r) (bank : Bank) (old : BitVec LW)
    {k : Nat} (K : k<395) (regs : List Value) (xs : Pending)
    (H : ∀ q i, ((capturedHeader q i).read old).toNat=(bank.hdr q i).toNat)
    (L : regs.length=start k+1) (R : WellRep old xs regs literalCmp) :
    WellRep old (aliases old (start k+1) (literal.drop (start k+1)) xs)
      (runCodes T bank regs (suffix k)) literalCmp := by
  rw [aliases_take,maximal_suffix K]
  exact alias_fold T bank old literalCmp _ _ _ _ (roster_segment bank old K H) L R

end L4.BStarAliasRoster
