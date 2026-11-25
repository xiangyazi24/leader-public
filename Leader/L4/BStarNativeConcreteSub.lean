import Leader.L4.BStarNativePrefixInduction
import Leader.L4.BStarNativeAtLaunch
import Leader.L4.BStarNativeSubInitializedHit

namespace L4.BStarNativeConcreteSub
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken BStarLongDoor BStarLongCommand
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarGeneratedBandScan BStarScalarHistory
open BStarResetChartService BStarResetMarkAdapter BStarSeparatorControl
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6WordChart
open BStarLongFixedRouting BStarResetChartTouch BStarOwnerControlHistory
open BStarResetControllerEntry BStarClearanceSource BStarAcquireWaitControl
open BStarLiteralPC BStarArithmeticControllerReturn BStarJoinedControllerReturn

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "PROTO" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step PROTO
local notation "run" => BStarResetSchedule.run step

open BStarScalarFlightTrace BStarNativeReceiptTape BStarScalarFits
open BStarAliasFold BStarAliasRoster BStarNativeReceiptInduction
open BStarLongArithmetic L4.Compiler.Native L4.Compiler.Interp
open BStarPhysicalDigitSem

open BStarNativeScalarRecurrence BStarNativeOperandCustody
open BStarNativeZeroHead BStarNumericChartCoverage

open BStarNativePackedRep

open BStarLongSignatures
open L4.Compiler.Digits

open BStarNativePriorInputs

open BStarNativeAtLaunch BStarNativeSubInitializedHit BStarH6Ordinal BStarOwnerLaunchOrigin
open BStarNativeScalarRecurrence BStarScalarFits

/-- Concrete SUB branch of the native dispatcher. Prior operands are
derived from the true Hit's PackedRep and the pinned operand roster;
no arithmetic value, scalar payload, or physical result is assumed. -/
theorem sub_branch {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (prior flight tail : List (Fin n)) (door : Fin n) (W : w=prior++flight++door::tail)
    {width k a b : Nat} (K : k<395) (width_pos : 0<width)
    (G : get (start k)=some (.sub a b))
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (flags : ∀ i, (longGeometry PROTO (base i)).inside=decide (oldOrdinal PROTO base hh i<width))
    (notShort : ∀ i,oldH6 PROTO base (rightNeighbor i)=true → width≤oldOrdinal PROTO base hh i+1)
    (table : PrimTable width) (bank : Bank) (sem : PrimSem table bank) (regs : List Value) :
    let addr := fun j => S.getD j fall
    let sites := digitSite hp base addr len width L
    let root := (addr 0).1
    let st := run initial prior
    let x := run st flight
    Found hp base addr len (13+k) st flight (.back 0) →
    Flat hp st root flight →
    Hit hp base addr len x door (13+k) →
    PackedRep x root sites k regs →
    let out := evalInstr (toInstr table bank (.sub a b)) regs
    (∀ slot : WordSlot (start k), out=.word (wordAt (step x door) sites (start k) slot)) ∧
    (∀ f, bind (longGeometry PROTO (x root)) 0 (atSite (x root).long 0)=.reply f →
      ScalarHead table bank (x root).long k regs (.sub a b) f) := by
  dsimp only
  intro F flat H R
  let adr := fun j => S.getD j fall
  let r0 := (adr 0).1
  have node := scheduled_node K
  have slots := literal_typed (start k) (.sub a b) G
  simp only [typedSlots,wordCheck,Bool.and_eq_true,beq_iff_eq] at slots
  have idx : 13+k-13=k := by omega
  have lenEq : regs.length=start (13+k-13) := by rw [idx]; exact R.length
  obtain ⟨before,launch,after,_,lenProof,split,_,_,_,Q⟩ := actual_initialized_hit_sub hp chart sep F H
    (by omega) (by omega) width_pos node G slots.1.1 slots.1.2 slots.2 flags notShort table bank sem regs lenEq R.scalar
  have op : pc (run (run initial prior) flight) r0=13+k := H.2.2.1
  have data : a∈dataOperands (.sub a b) := by simp [dataOperands]
  have input := arg_at_flight_launch hp chart sep rootK whole band prior flight (door::tail) W
    before after launch split K (.sub a b) G data L flat op regs R slots.1.2
  have dataB : b∈dataOperands (.sub a b) := by simp [dataOperands]
  have inputB := arg_at_flight_launch hp chart sep rootK whole band prior flight (door::tail) W
    before after launch split K (.sub a b) G dataB L flat op regs R slots.2
  have args : ([a,b] : List Nat)[0]?=some a := rfl
  have argsB : ([a,b] : List Nat)[1]?=some b := rfl
  have accepted := Q (input.trans (argW_get (regs:=regs) (width:=width) args).symm)
    (inputB.trans (argW_get (regs:=regs) (width:=width) argsB).symm)
  obtain ⟨result,f,exactResult,word,bound,fit,rep⟩ := accepted
  constructor
  · intro slot
    exact exactResult.trans (congrArg Value.word word)
  · intro g G
    obtain rfl := Token.reply.inj (G.symm.trans bound)
    refine .ready fit True.intro ?_
    rw [exactResult]
    simpa only [idx] using rep

theorem sub_ready {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (prior flight tail : List (Fin n)) (door : Fin n) (W : w=prior++flight++door::tail)
    {width k a b : Nat} (K : k<395) (width_pos : 0<width)
    (G : get (start k)=some (.sub a b))
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (flags : ∀ i, (longGeometry PROTO (base i)).inside=decide (oldOrdinal PROTO base hh i<width))
    (notShort : ∀ i,oldH6 PROTO base (rightNeighbor i)=true → width≤oldOrdinal PROTO base hh i+1)
    (table : PrimTable width) (bank : Bank) (sem : PrimSem table bank) (regs : List Value) :
    let addr := fun j => S.getD j fall
    let sites := digitSite hp base addr len width L
    let root := (addr 0).1
    let st := run initial prior
    let x := run st flight
    Found hp base addr len (13+k) st flight (.back 0) →
    Flat hp st root flight →
    Hit hp base addr len x door (13+k) →
    PackedRep x root sites k regs →
    (∀ q d, ((capturedHeader q d).read (x root).long).toNat=(bank.hdr q d).toNat) →
    BStarNativePrefixInduction.Ready hp table bank x (step x door) root sites k (.sub a b) regs := by
  dsimp only
  intro found flat hit packed capture
  obtain ⟨word,scalar⟩ := sub_branch hp chart sep rootK whole band prior flight tail door W K
    width_pos G L flags notShort table bank sem regs found flat hit packed
  exact ⟨G,capture,fun f R => .inr (scalar f R),fun _ _ _ bad => by contradiction,word⟩

#print axioms sub_ready
#print axioms sub_branch
end L4.BStarNativeConcreteSub
