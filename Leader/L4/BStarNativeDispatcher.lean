import Leader.L4.BStarNativeLoadReady
import Leader.L4.BStarNativePartialDispatcher
import Leader.L4.BStarNativeDispatchCapture

namespace L4.BStarNativeDispatcher
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


open BStarNativePrefixInduction BStarNativeHeadRoster
open BStarNativeLoadReady BStarNativeLoadTours

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The checked all-head dispatcher on the exact genuine 395-receipt
word. Existing physical LOAD certificates supply numeric inputs; the
current capture bits and the first true PC13 cut are transported and
extracted within this theorem, not supplied as per-head hypotheses. -/
theorem from_native_word {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    {width : Nat} (width_ge : 2≤width)
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (flags : ∀ i, (longGeometry PROTO (base i)).inside=decide (oldOrdinal PROTO base hh i<width) ∧
      (longGeometry PROTO (base i)).last=decide (oldOrdinal PROTO base hh i+1=width))
    (notShort : ∀ i,oldH6 PROTO base (rightNeighbor i)=true → width≤oldOrdinal PROTO base hh i+1)
    (stable : ∀ u i,Layout PROTO base i=Layout PROTO (run initial u) i)
    (table : PrimTable width) (bank : Bank) (sem : PrimSem table bank)
    (pins : ∀ q d, ((capturedHeader q d).read (initial (S.getD 0 fall).1).long).toNat=
      (bank.hdr q d).toNat)
    (tape : NativeTape hp base (fun j => S.getD j fall) len initial 13 w 395)
    (data : ∀ (q : Fin 3) (d : Fin 9), ∃ u e v, w=u++e::v ∧
      Hit hp base (fun j => S.getD j fall) len (run initial u) e (loadOp q d) ∧
      ∀ s : WordSlot (loadNode q d),
        wordAt (step (run initial u) e)
          (digitSite hp base (fun j => S.getD j fall) len width L) (loadNode q d) s=
            bank.digits q d%16^width) :
    Dispatcher hp table bank base initial (fun j => S.getD j fall) len
      (digitSite hp base (fun j => S.getD j fall) len width L) w := by
  have live := BStarNativeDispatchCapture.live_of_band hp chart sep whole stable band
  have capture := BStarNativeDispatchCapture.retained hp initial (S.getD 0 fall).1 w sep live bank pins
  cases tape with
  | take _ flat found hit _ =>
    exact BStarNativePartialDispatcher.assemble hp chart sep rootK whole band width_ge L flags
      notShort stable table bank sem capture _ _ _ rfl found flat hit
      (BStarNativeLoadReady.callback hp _ rootK sep whole band table bank sem capture data)

#print axioms from_native_word
end L4.BStarNativeDispatcher
