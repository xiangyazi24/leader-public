import Leader.L4.BStarNativePackedRep
import Leader.L4.BStarNativeOperandCustody
import Leader.L4.Compiler.DigitsWords

namespace L4.BStarNativePriorInputs
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


open L4.Compiler.Digits

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

def dataOperands : Code → List Nat
  | .maskB a | .shl3 a | .scan5 a => [a]
  | .add a b | .sub a b | .cmp a b | .mux _ a b => [a,b]
  | _ => []

private def checks (k : Nat) : Bool :=
  match get (start k) with
  | none => false
  | some c => (dataOperands c).all fun a =>
      wordCheck a && (List.range k).any (fun j => start j==a)

private theorem census : (List.range 395).all checks=true := by
  decide +kernel

theorem data_origin {k a : Nat} (K : k<395) (c' : Code)
    (G : get (start k)=some c') (A : a∈dataOperands c') :
    ∃ j<k, start j=a ∧ WordSlot a := by
  have V := List.all_eq_true.mp census k (List.mem_range.mpr K)
  simp only [checks,G] at V
  have Q := List.all_eq_true.mp V a A
  obtain ⟨J,E⟩ := Bool.and_eq_true_iff.mp Q
  obtain ⟨j,M,H⟩ := List.any_eq_true.mp E
  exact ⟨j,List.mem_range.mp M,beq_iff_eq.mp H,beq_iff_eq.mp J⟩

theorem argW_get {width : Nat} {regs : List Value} {xs : List Nat} {i a : Nat}
    (A : xs[i]?=some a) :
    argW width (readArgs regs xs) i=(readReg regs a).asWord % 16^width := by
  simp [argW,readArgs,readReg,List.getElem?_map,A]

theorem argB_get {regs : List Value} {xs : List Nat} {i a : Nat}
    (A : xs[i]?=some a) :
    argB (readArgs regs xs) i=(readReg regs a).asBool := by
  simp [argB,readArgs,readReg,List.getElem?_map,A]

theorem arg_of_packed {width k a : Nat} (x : X) (i : Fin n)
    (sites : Fin width → Fin n) (regs : List Value) (R : PackedRep x i sites k regs)
    (K : k<395) (c' : Code) (G : get (start k)=some c') (A : a∈dataOperands c') :
    ∃ slot : WordSlot a,
      (readReg regs a).asWord % 16^width=wordAt x sites a slot := by
  obtain ⟨j,jk,eq,slot⟩ := data_origin K c' G A
  subst a
  refine ⟨slot,?_⟩
  rw [R.numeric j jk slot]
  change wordAt x sites (start j) slot % 16^width=wordAt x sites (start j) slot
  apply Nat.mod_eq_of_lt
  unfold wordAt
  exact valJ_lt _ _ (Nat.le_refl _)

theorem arg_at_launch_of_hit {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (pre tape post : List (Fin n)) (W : w=pre++tape++post)
    {k width a : Nat} (K : k<395) (c' : Code) (G : get (start k)=some c')
    (A : a∈dataOperands c')
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (pcAt : pc (run initial pre) (S.getD 0 fall).1=13+k)
    (regs : List Value) :
    let ds := digitSite hp base (fun j => S.getD j fall) len width L
    PackedRep (run (run initial pre) tape) (S.getD 0 fall).1 ds k regs →
    ∃ slot : WordSlot a, (readReg regs a).asWord % 16^width=wordAt (run initial pre) ds a slot := by
  dsimp only
  intro R
  obtain ⟨j,jk,e,slot⟩ := data_origin K c' G A
  have node : nodeOf (13+j)=some a := (scheduled_node (by omega : j<395)).trans (congrArg some e)
  have H := retain_word hp chart sep rootK whole band pre tape post W (13+j) a width node slot L (by omega)
  obtain ⟨s,V⟩ := arg_of_packed _ _ _ regs R K c' G A
  exact ⟨s,V.trans H⟩

#print axioms arg_at_launch_of_hit
end L4.BStarNativePriorInputs
