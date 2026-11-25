import Leader.L4.BStarNativePrefixInduction
import Leader.L4.BStarNativeFinalImage

namespace L4.BStarNativeCheckedOutput
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

open BStarNativePackedRep BStarNativeScanNat BStarOwnerLaunchOrigin

open BStarNativePrefixInduction BStarNativeFinalImage BStarFinalCandidate

/-- Close the distinct PC407 acceptance from the typed prefix of the
same genuine tape. This connects the conditional per-family dispatcher
to physical NEED/header/descriptor and the actual ISSUE408 cut. -/
theorem actual_output {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (stable : ∀ u i,Layout PROTO base i=Layout PROTO (run initial u) i)
    {width : Nat} (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (table : PrimTable width) (bank : Bank)
    (D : Dispatcher hp table bank base initial (fun j => S.getD j fall) len
      (digitSite hp base (fun j => S.getD j fall) len width L) w)
    (T : NativeTape hp base (fun j => S.getD j fall) len initial 13 w 395)
    (legal : ∀ pre e tail, w=pre++e::tail →
      Hit hp base (fun j => S.getD j fall) len (run initial pre) e 407 →
      ((capturedSelector 1).read (run initial pre (S.getD 0 fall).1).long).toNat<3) :
    let sites := digitSite hp base (fun j => S.getD j fall) len width L
    let root := (S.getD 0 fall).1
    let ys := runCodes table bank [] literal
    ∃ pre e tail, w=pre++e::tail ∧
      Hit hp base (fun j => S.getD j fall) len (run initial pre) e 407 ∧
      let x := run initial pre
      let fresh := (step x e root).long
      PackedRep (step x e) root sites 395 ys ∧
      BStarResetControllerEntry.snapshot fresh=((.empty,1), BitVec.ofNat 9 stageOp) ∧
      need.read fresh=BitVec.ofBool (readReg ys BStarLongSignatures.needIx).asBool ∧
      candidateHeaders.read fresh=BitVec.ofNat 18 ((BStarLongSignatures.outHeaders0++
        BStarLongSignatures.outHeaders1).foldl (fun a j => a*2+((readReg ys j).asBool).toNat) 0) ∧
      ∃ h : ((capturedSelector 1).read (x root).long).toNat<3,
        sourceDescriptor.read fresh=BStarLongPublication.encode (finalDesc (x root).long h) ∧
        (finalDesc (x root).long h).need=(readReg ys BStarLongSignatures.needIx).asBool := by
  have verified := verify_all hp chart sep rootK whole band stable L table bank D T
  obtain ⟨pre,e,tail,W,hit,packed,scan⟩ := final_prefix hp verified (by decide) (by decide)
  let sites := digitSite hp base (fun j => S.getD j fall) len width L
  have h := legal pre e tail W hit
  obtain ⟨P,issue,needEq,headers,desc,descNeed⟩ := final_hit hp chart (sep e) hit sites
    (digit_on_chart hp base (fun j => S.getD j fall) len width L) table bank packed h
  exact ⟨pre,e,tail,W,hit,P,issue,needEq,headers,h,desc,descNeed⟩

#print axioms actual_output
end L4.BStarNativeCheckedOutput
