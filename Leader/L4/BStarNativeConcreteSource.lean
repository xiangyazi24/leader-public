import Leader.L4.BStarNativePrefixInduction
import Leader.L4.BStarNativeHeadRoster

namespace L4.BStarNativeConcreteSource
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

open BStarNativePrefixInduction BStarNativeScanNat

def boolOutput : Code → Bool
  | .bconst .. | .header .. | .cmpEq .. | .cmpLt .. | .not .. | .and ..
  | .or .. | .bmux .. | .phaseEq .. => true
  | _ => false

def boolInputs : Code → List Nat
  | .not a => [a]
  | .and a b | .or a b => [a,b]
  | .bmux q a b => [q,a,b]
  | _ => []

def check (i : Nat) : Bool :=
  match get i with
  | none => false
  | some c =>
    !BStarNativeHeadRoster.boolHead c ||
      (!wordCheck i &&
       ((boolInputs c).all fun j => decide (j<i) && ((get j).map boolOutput).getD false) &&
       (match c with
        | .phaseEq j _ => decide (j<i) && ((get j).map fun c => match c with
            | .scan5 _ => true
            | _ => false).getD false
        | _ => true))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem census : (List.range 474).all check=true := by
  decide +kernel

private theorem eval_bool {width : Nat} (T : PrimTable width) (bank : Bank)
    (regs : List Value) {c : Code} (H : boolOutput c=true) :
    ∃ b, evalInstr (toInstr T bank c) regs=.boolean b := by
  cases c <;> cases H <;>
    first | exact ⟨_,rfl⟩ | (simp only [toInstr,evalInstr]; exact ⟨_,rfl⟩)

theorem source_inputs {width : Nat} (T : PrimTable width) (bank : Bank)
    {k : Nat} (K : k<395) (c' : Code) (G : get (start k)=some c')
    (sourceHead : BStarNativeHeadRoster.boolHead c'=true) :
    SourceTypes (regsBefore T bank k) c' ∧ ¬WordSlot (start k) := by
  have inBounds : start k<474 := by
    have H := (List.getElem?_eq_some_iff.mp G).1
    rw [literal_length] at H
    exact H
  have check := List.all_eq_true.mp census _ (List.mem_range.mpr inBounds)
  simp only [BStarNativeConcreteSource.check,G,sourceHead,Bool.not_true,Bool.false_or,Bool.and_eq_true] at check
  obtain ⟨⟨slot,data⟩,phase⟩ := check
  have has (j : Nat) (J : j∈boolInputs c') : HasBool (regsBefore T bank k) j := by
    have q := List.all_eq_true.mp data j J
    simp only [Bool.and_eq_true,decide_eq_true_eq] at q
    have inList : j<(L4.Compiler.Native.literal.take (start k)).length := by
      simp only [List.length_take,literal_length,Nat.min_eq_left (by omega : start k≤474)]
      exact q.1
    have old := runCodes_new T bank [] (L4.Compiler.Native.literal.take (start k)) j inList
    have jL : j<L4.Compiler.Native.literal.length := by rw [literal_length]; omega
    have Q := q.2
    change (L4.Compiler.Native.literal[j]?.map boolOutput).getD false=true at Q
    rw [List.getElem?_eq_getElem jL] at Q
    simp only [Option.map_some,Option.getD_some] at Q
    change ∃ b, readReg (runCodes T bank [] (L4.Compiler.Native.literal.take (start k))) j=.boolean b
    simp only [List.length_nil,Nat.zero_add] at old
    rw [old,List.getElem_take]
    exact eval_bool T bank _ Q
  constructor
  · cases c' <;> simp [BStarNativeHeadRoster.boolHead,BStarNativeHeadRoster.family] at sourceHead
    · rename_i a
      exact .neg a (has a (by simp [boolInputs]))
    · rename_i a b
      exact .and a b (has a (by simp [boolInputs])) (has b (by simp [boolInputs]))
    · rename_i a b
      exact .or a b (has a (by simp [boolInputs])) (has b (by simp [boolInputs]))
    · rename_i q a b
      exact .mux q a b (has q (by simp [boolInputs])) (has a (by simp [boolInputs])) (has b (by simp [boolInputs]))
    · rename_i a j
      have P := phase
      simp only [Bool.and_eq_true,decide_eq_true_eq] at P
      cases H : get a with
      | none => simp [H] at P
      | some op =>
        cases op <;> simp [H] at P
        rename_i q
        exact .phase a j q (by rw [prefix_length T bank (by omega)]; exact P) H
  · intro H
    have E : wordCheck (start k)=true := beq_iff_eq.mpr H
    simp [E] at slot

/-- All actual Boolean heads use this branch from emitted typing alone;
physical operand agreement is subsequently derived by the induction. -/
theorem source_ready {width : Nat} (T : PrimTable width) (bank : Bank)
    {k : Nat} (K : k<395) (c' : Code) (G : get (start k)=some c')
    (sourceHead : BStarNativeHeadRoster.boolHead c'=true)
    (x y : X) (root : Fin n) (sites : Fin width → Fin n)
    (capture : ∀ q d, ((capturedHeader q d).read (x root).long).toNat=(bank.hdr q d).toNat) :
    Ready hp T bank x y root sites k c' (regsBefore T bank k) := by
  obtain ⟨types,slot⟩ := source_inputs T bank K c' G sourceHead
  refine ⟨G,capture,fun _ _ => .inl types,?_,fun s => (slot s).elim⟩
  intro f h a E
  subst c'
  contradiction

end L4.BStarNativeConcreteSource
