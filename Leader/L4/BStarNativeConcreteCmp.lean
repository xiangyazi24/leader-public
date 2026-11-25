import Leader.L4.BStarNativePrefixInduction
import Leader.L4.BStarNativeAtLaunch
import Leader.L4.BStarNativeCmpHit

namespace L4.BStarNativeConcreteCmp
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

open BStarNativeAtLaunch BStarNativeCmpHit BStarH6Ordinal BStarOwnerLaunchOrigin
open BStarNativeScalarRecurrence BStarScalarFits

private def check (i : Nat) : Bool :=
  match get i with
  | some (.cmp ..) => !wordCheck i
  | _ => true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem census : (List.range 474).all check=true := by decide +kernel

private theorem no_slot {i a b : Nat} (G : get i=some (.cmp a b)) : ¬WordSlot i := by
  have I := (List.getElem?_eq_some_iff.mp G).1
  rw [literal_length] at I
  have H := List.all_eq_true.mp census i (List.mem_range.mpr I)
  intro W
  simp [check,G,wordCheck,show BStarLongRegisters.widthAt BStarLongRegisters.wordWidths i=4 from W] at H

theorem cmp_ready {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (prior flight tail : List (Fin n)) (door : Fin n) (W : w=prior++flight++door::tail)
    {width k a b : Nat} (K : k<395) (width_pos : 0<width)
    (G : get (start k)=some (.cmp a b))
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
    BStarNativePrefixInduction.Ready hp table bank x (step x door) root sites k (.cmp a b) regs := by
  dsimp only
  intro F flat H R capture
  let adr := fun j => S.getD j fall
  let r0 := (adr 0).1
  have node := scheduled_node K
  have slots := literal_typed (start k) (.cmp a b) G
  simp only [typedSlots,wordCheck,Bool.and_eq_true,beq_iff_eq] at slots
  have idx : 13+k-13=k := by omega
  have lenEq : regs.length=start (13+k-13) := by rw [idx]; exact R.length
  obtain ⟨before,launch,after,_,lenProof,split,_,_,_,Q⟩ := actual_initialized_hit_cmp hp chart sep F H
    (by omega) (by omega) width_pos node G slots.1 slots.2 flags notShort table bank sem regs lenEq R.scalar
  have op : pc (run (run initial prior) flight) r0=13+k := H.2.2.1
  have data : a∈dataOperands (.cmp a b) := by simp [dataOperands]
  have input := arg_at_flight_launch hp chart sep rootK whole band prior flight (door::tail) W
    before after launch split K (.cmp a b) G data L flat op regs R slots.1
  have dataB : b∈dataOperands (.cmp a b) := by simp [dataOperands]
  have inputB := arg_at_flight_launch hp chart sep rootK whole band prior flight (door::tail) W
    before after launch split K (.cmp a b) G dataB L flat op regs R slots.2
  have args : ([a,b] : List Nat)[0]?=some a := rfl
  have argsB : ([a,b] : List Nat)[1]?=some b := rfl
  obtain ⟨_,f,_,bound,exactArg,_⟩ := Q (input.trans (argW_get (regs:=regs) (width:=width) args).symm)
    (inputB.trans (argW_get (regs:=regs) (width:=width) argsB).symm)
  refine ⟨G,capture,?_,fun _ _ _ E => by contradiction,fun slot => (no_slot G slot).elim⟩
  intro g E
  obtain rfl := Token.reply.inj (E.symm.trans bound)
  exact .inr (.cmp rfl sem exactArg)

end L4.BStarNativeConcreteCmp
