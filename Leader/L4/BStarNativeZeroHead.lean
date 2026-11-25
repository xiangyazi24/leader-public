import Leader.L4.BStarNumericCompleteSweep
import Leader.L4.BStarNativeReceiptInduction

namespace L4.BStarNativeZeroHead
open AllSizeProtocol BStarTrace BStarLongToken BStarLongLayout
open BStarLongArithmetic BStarLongRegisters BStarPhysicalDigitSem BStarPhysicalWordSem
open L4.Compiler.Digits L4.Compiler.Native L4.Compiler.Interp
open BStarAliasFold BStarAliasRoster BStarNativeReceiptInduction

theorem first_op : nodeOf 13=some 0 ∧ get 0=some (.const .zero) := by decide +kernel

theorem zero_slot : WordSlot 0 := by unfold WordSlot; decide +kernel

/-- No position or accumulator assumption is needed for CONST zero.
Every actual significant write installs the accepted digit and leaves
the incoming accumulator alone. -/
theorem digit_zero {w : Nat} {g : Fin w → LongGeometry}
    {old updated : Fin w → BitVec LW} {tokens : Nat → Payload}
    (S : DigitSweep g old updated 0 (.const .zero) tokens) :
    (∀ j, num (updated j) 0=0) ∧
    ∀ j : Fin w, tokens j.val=tokens (j.val+1) := by
  have row (j : Fin w) :
      ((writeNum 0 0).apply (old j),tokens j.val)=(updated j,tokens (j.val+1)) := S.step j
  constructor
  · intro j
    have E : (writeNum 0 0).apply (old j)=updated j := congrArg Prod.fst (row j)
    rw [←E]
    exact num_write_of_lt zero_slot (by decide) _
  · intro j
    exact congrArg Prod.snd (row j)

theorem accepted_head {r : Nat} (T : PrimTable r) (bank : Bank) (H : PrimSem T bank)
    (regs : List Value) : evalInstr (toInstr T bank (.const .zero)) regs=.word 0 := by
  change Value.word (den (T.const .zero) (readArgs regs []))=_
  rw [H.const]
  simp [ConstId.val]

/-- The initialized scalar representation for PC13 has no slots.
Its real CONST zero head is a distributed word, not a scalar. -/
theorem first_head_rep (x : BitVec LW) (p : Payload) :
    WellRep x (headPending x 0 p (.const .zero)) [.word 0] literalCmp := by
  have notCmp : ¬literalCmp 0 := by unfold literalCmp; decide +kernel
  intro j J
  have Z : j=0 := by simp only [List.length_singleton] at J; omega
  subst j
  refine ⟨?_,fun K => (notCmp K).elim⟩
  intro b E
  contradiction

open BStarNumericHitSweep BStarNumericCompleteSweep BStarNumericCarry
open BStarNumericChronology BStarNumericConsecutive BStarNumericReceipt
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetMarkAdapter BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarLongCommand BStarLongClaims BStarLongWork BStarLongEvents
open BStarResetChartTouch BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

/-- Reuse the complete sweep from the genuine first native hit, and
read back all of its significant target occurrences from one and the
same actual pre-turn physical bank. -/
theorem first_actual_zero {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {door : Fin n} {w : List (Fin n)}
    (F : Found hp base (fun j => S.getD j fall) len 13 x w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run x w) door 13) :
    ∃ (pre : List (Fin n)) (turn : Fin n) (ret : List (Fin n)) (ds : List D)
      (before : List (Fin n)) (launch : Fin n) (after : List (Fin n)),
      w=pre++turn::ret ∧ pre=before++launch::after ∧
      Aligned hp base (fun j => S.getD j fall) len 13
        (step (run x before) launch) 0 after len ds ∧
      let visits := ds.filter (significant hp base (fun j => S.getD j fall))
      ∀ j : Fin visits.length, num ((run x pre) visits[j.val].mark).long 0=0 := by
  obtain ⟨pre,turn,ret,_,_,W,_,_,_,_,_,_,before,launch,after,i,code,P,N,G,sweep⟩ :=
    of_found hp chart sep F H (by decide) (by decide)
  obtain rfl := Option.some.inj (N.symm.trans first_op.1)
  obtain rfl := Option.some.inj (G.symm.trans first_op.2)
  obtain ⟨ds,align,tokens,_,sweepExact,R⟩ := sweep
  refine ⟨pre,turn,ret,ds,before,launch,after,W,P,align,?_⟩
  dsimp only
  intro j
  have E := (digit_zero sweepExact).1 j
  have Z := (R j 0).2
  have Q : run x pre=run (step (run x before) launch) after := by
    rw [P,BStarResetSchedule.run_append]
    rfl
  unfold num at E ⊢
  rw [Q,←Z]
  exact E

/-- Concrete distributed interpretation of one word SSA register.
When a chart enumerates the claimed owner sites, this reads their
literal packed nibbles in that chart's little-endian order. -/
def wordAt {width : Nat} (y : X) (site : Fin width → Fin n)
    (reg : Nat) (slot : WordSlot reg) : Nat :=
  val (readWord (fun j => (y (site j)).long) reg slot)

theorem wordAt_zero {width : Nat} (y : X) (site : Fin width → Fin n)
    (H : ∀ j, num (y (site j)).long 0=0) :
    wordAt y site 0 zero_slot=0 := by
  let word := readWord (fun j => (y (site j)).long) 0 zero_slot
  have V : ∀ j, (word j).val=0 := H
  have P : ∀ j (e : j≤width), valJ word j e=0 := by
    intro j
    induction j with
    | zero => intro e; rfl
    | succ j ih =>
      intro e
      rw [val_succ,ih,V,Nat.mul_zero,Nat.add_zero]
  exact P width (by omega)

/-- Once the exact sweep's significant sites cover the accepted
chart, its pre-turn digit image and the first native register agree
as words. The scalar representation is combined at the same head,
without introducing an artificial header-side numeric slot. -/
theorem typed_first {width : Nat} (T : PrimTable width) (bank : Bank)
    (sem : PrimSem T bank) (y : X) (site : Fin width → Fin n)
    (wire : BitVec LW) (payload : Payload) (H : ∀ j, num (y (site j)).long 0=0) :
    let regs := runCodes T bank [] [Code.const .zero]
    readReg regs 0=.word (wordAt y site 0 zero_slot) ∧
      WellRep wire (headPending wire 0 payload (.const .zero)) regs literalCmp := by
  change readReg [evalInstr (toInstr T bank (.const .zero)) []] 0=_
    ∧ WellRep wire (headPending wire 0 payload (.const .zero))
      [evalInstr (toInstr T bank (.const .zero)) []] literalCmp
  rw [accepted_head T bank sem,wordAt_zero y site H]
  exact ⟨rfl,first_head_rep wire payload⟩

#print axioms wordAt_zero
#print axioms typed_first
#print axioms first_actual_zero
#print axioms accepted_head
#print axioms first_head_rep
end L4.BStarNativeZeroHead
