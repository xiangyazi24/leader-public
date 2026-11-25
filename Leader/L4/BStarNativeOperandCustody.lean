import Leader.L4.BStarNativeNumberRetention
import Leader.L4.BStarNativeZeroHead
import Leader.L4.BStarNumericChartCoverage

namespace L4.BStarNativeOperandCustody
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongArithmetic
open BStarLongRegisters BStarPhysicalWordSem BStarNumericChartCoverage BStarNativeZeroHead
open BStarAcquireLiteralChain BStarH6WordChart BStarGeneratedOwner
open BStarResetMarkAdapter BStarLongWork BStarLongClaims BStarResetChartTouch
open BStarLongLiteral BStarLongEvents BStarAcquireVisitOrder BStarResetRailRing BStarNumericCarry BStarLongCommand
open BStarPhysicalDigitSem BStarNativeReceiptTape
open L4.Compiler.Digits

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- Each canonical digit site represents a genuine K1 in the fixed owner chart. -/
theorem digit_address {base : X} {addr : Nat → Pos n} {len width : Nat}
    (L : (significantSites hp base addr len).length = width) (d : Fin width) :
    ∃ k, k < len ∧ addr k = (digitSite hp base addr len width L d, 1) := by
  have M : digitSite hp base addr len width L d ∈ significantSites hp base addr len :=
    List.getElem_mem _
  obtain ⟨k,hk,eq⟩ := List.mem_map.mp M
  obtain ⟨rng,sig⟩ := List.mem_filter.mp hk
  have one := (Bool.and_eq_true_iff.mp sig).1
  exact ⟨k,List.mem_range.mp rng,Prod.ext eq (Fin.ext (beq_iff_eq.mp one))⟩

/-- An earlier distributed output keeps its whole canonical value on
a later physical subword, in particular through the next actual launch. -/
theorem retain_word {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode} (rootK : (S.getD 0 fall).2=0)
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w m)
    (band : BStarNativeReceiptTape.CompilerBand hp initial (S.getD 0 fall).1 w)
    (pre tape post : List (Fin n)) (W : w=pre++tape++post)
    (oldOp j width : Nat) (node : nodeOf oldOp=some j) (slot : WordSlot j)
    (L : (significantSites hp base (fun k => S.getD k fall) len).length=width)
    (later : oldOp<BStarGeneratedBandScan.pc (run initial pre) (S.getD 0 fall).1) :
    let ds := digitSite hp base (fun k => S.getD k fall) len width L
    wordAt (run (run initial pre) tape) ds j slot =
      wordAt (run initial pre) ds j slot := by
  dsimp only
  unfold wordAt
  apply congrArg val
  funext d
  obtain ⟨k,hk,loc⟩ := digit_address hp L d
  have E := BStarNativeNumberRetention.retain_later_native hp chart sep rootK T band
    pre tape post W _ k (Nat.le_of_lt hk) loc oldOp j node later
  apply Fin.ext
  change num (run (run initial pre) tape _).long j =
    num (run initial pre _).long j
  exact congrArg BitVec.toNat E

/-- Transport the exact result of an earlier real receipt across
the intervening compiler marks and the actual selected launch mark. -/
theorem at_launch {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode} (rootK : (S.getD 0 fall).2=0)
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w m)
    (band : BStarNativeReceiptTape.CompilerBand hp initial (S.getD 0 fall).1 w)
    (pre mid post : List (Fin n)) (launch : Fin n)
    (W : w=(pre++mid)++launch::post)
    (oldOp j width : Nat) (node : nodeOf oldOp=some j) (slot : WordSlot j)
    (L : (significantSites hp base (fun k => S.getD k fall) len).length=width)
    (later : oldOp<BStarGeneratedBandScan.pc (run initial pre) (S.getD 0 fall).1)
    (value : Nat)
    (known : wordAt (run initial pre)
      (digitSite hp base (fun k => S.getD k fall) len width L) j slot = value) :
    wordAt (step (run initial (pre++mid)) launch)
      (digitSite hp base (fun k => S.getD k fall) len width L) j slot = value := by
  have W' : w=pre++(mid++[launch])++post := by
    simp only [List.append_assoc,List.singleton_append] at W ⊢
    exact W
  have hold := retain_word hp chart sep rootK T band pre (mid++[launch]) post W'
    oldOp j width node slot L later
  rw [BStarResetSchedule.run_append,←BStarResetSchedule.run_append step initial pre mid] at hold
  exact hold.trans known

#print axioms at_launch
#print axioms retain_word
end L4.BStarNativeOperandCustody
