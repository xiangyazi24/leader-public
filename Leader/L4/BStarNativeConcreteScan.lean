import Leader.L4.BStarNativePrefixInduction
import Leader.L4.BStarNativeAtLaunch
import Leader.L4.BStarNativeScanHit
import Leader.L4.BStarNativeScanPosition

namespace L4.BStarNativeConcreteScan
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
open BStarNumericConsecutive BStarAcquireForwardTrace

open BStarNativeAtLaunch BStarNativeScanHit BStarH6Ordinal BStarOwnerLaunchOrigin
open BStarNativeScalarRecurrence BStarScalarFits

private def check (i : Nat) : Bool :=
  match get i with
  | some (.scan5 ..) => !wordCheck i
  | _ => true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem census : (List.range 474).all check=true := by decide +kernel

private theorem no_slot {i a : Nat} (G : get i=some (.scan5 a)) : ¬WordSlot i := by
  have I := (List.getElem?_eq_some_iff.mp G).1
  rw [literal_length] at I
  have H := List.all_eq_true.mp census i (List.mem_range.mpr I)
  intro W
  simp [check,G,wordCheck,show BStarLongRegisters.widthAt BStarLongRegisters.wordWidths i=4 from W] at H

theorem scan_ready {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (prior flight tail : List (Fin n)) (door : Fin n) (W : w=prior++flight++door::tail)
    {width k a : Nat} (K : k<395) (width_ge : 2≤width)
    (G : get (start k)=some (.scan5 a))
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (flags : ∀ i, (longGeometry PROTO (base i)).inside=decide (oldOrdinal PROTO base hh i<width))
    (notShort : ∀ i,oldH6 PROTO base (rightNeighbor i)=true → width≤oldOrdinal PROTO base hh i+1)
    (positions : ∀ before launch after post ds,
      flight=before++launch::(after++post) →
      Aligned hp base (fun j => S.getD j fall) len (13+k)
        (step (run (run initial prior) before) launch) 0 after len ds →
      let visits := ds.filter (significant hp base (fun j => S.getD j fall))
      ∀ j : Fin visits.length, ScanPosition (geom hp visits[j.val]) j.val)
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
    BStarNativePrefixInduction.Ready hp table bank x (step x door) root sites k (.scan5 a) regs := by
  dsimp only
  intro F flat H R capture
  let adr := fun j => S.getD j fall
  let r0 := (adr 0).1
  have node := scheduled_node K
  have slots := literal_typed (start k) (.scan5 a) G
  simp only [typedSlots,wordCheck,beq_iff_eq] at slots
  have idx : 13+k-13=k := by omega
  have lenEq : regs.length=start (13+k-13) := by rw [idx]; exact R.length
  obtain ⟨before,launch,after,_,lenProof,split,_,_,_,Q⟩ := actual_initialized_hit_scan hp chart sep F H
    (by omega) (by omega) width_ge node G slots flags notShort positions table bank sem regs lenEq R.scalar
  have op : pc (run (run initial prior) flight) r0=13+k := H.2.2.1
  have data : a∈dataOperands (.scan5 a) := by simp [dataOperands]
  have input := arg_at_flight_launch hp chart sep rootK whole band prior flight (door::tail) W
    before after launch split K (.scan5 a) G data L flat op regs R slots
  have args : ([a] : List Nat)[0]?=some a := rfl
  obtain ⟨result,f,exactResult,bound,exactArg,fit,rep⟩ :=
    Q (input.trans (argW_get (regs:=regs) (width:=width) args).symm)
  refine ⟨G,capture,?_,?_,fun slot => (no_slot G slot).elim⟩
  · intro g E
    obtain rfl := Token.reply.inj (E.symm.trans bound)
    refine .inr (.ready ?_ True.intro ?_)
    · simpa [PayloadBound,exactArg] using fit
    · rw [exactResult]
      simpa only [idx] using rep
  · intro g E _ _
    obtain rfl := Token.reply.inj (E.symm.trans bound)
    rw [exactArg,exactResult]
    exact ⟨fit,rfl⟩

theorem scan_ready_after_zero {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (prior flight tail : List (Fin n)) (door : Fin n) (W : w=prior++flight++door::tail)
    {width k a : Nat} (K : k<395) (width_ge : 2≤width)
    (G : get (start k)=some (.scan5 a))
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (flags : ∀ i, (longGeometry PROTO (base i)).inside=decide (oldOrdinal PROTO base hh i<width))
    (notShort : ∀ i,oldH6 PROTO base (rightNeighbor i)=true → width≤oldOrdinal PROTO base hh i+1)
    (zeroStart : X) (zeroFlight gap : List (Fin n)) (zeroDoor : Fin n)
    (Z : Found hp base (fun j => S.getD j fall) len 13 zeroStart zeroFlight (.back 0))
    (ZH : Hit hp base (fun j => S.getD j fall) len (run zeroStart zeroFlight) zeroDoor 13)
    (sameStart : run initial prior=run (step (run zeroStart zeroFlight) zeroDoor) gap)
    (stable : ∀ u i, Layout PROTO (run zeroStart u) i=Layout PROTO base i)
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
    BStarNativePrefixInduction.Ready hp table bank x (step x door) root sites k (.scan5 a) regs := by
  dsimp only
  intro F flat H R capture
  refine scan_ready hp chart sep rootK whole band prior flight tail door W K width_ge G L flags notShort ?_
    table bank sem regs F flat H R capture
  intro before launch after _ ds _ A
  have exactA : Aligned hp base (fun j => S.getD j fall) len (13+k)
      (run (step (run zeroStart zeroFlight) zeroDoor) (gap++before++[launch])) 0 after len ds := by
    rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append,←sameStart]
    exact A
  exact BStarNativeScanPosition.later_scan_positions hp chart sep Z ZH (gap++before++[launch])
    after exactA (fun u _ _ i => stable u i) flags notShort

#print axioms scan_ready_after_zero

#print axioms scan_ready
end L4.BStarNativeConcreteScan
