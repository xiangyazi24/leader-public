import Leader.L4.BStarNativeScalarRecurrence
import Leader.L4.BStarNativeOperandCustody

namespace L4.BStarNativePackedRep
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

set_option maxRecDepth 8192

structure PackedRep {width : Nat} (x : X) (root : Fin n) (sites : Fin width → Fin n)
    (k : Nat) (regs : List Value) : Prop where
  length : regs.length=start k
  scalar : WellRep (x root).long [] regs literalCmp
  numeric : ∀ j<k, ∀ slot : WordSlot (start j),
    readReg regs (start j)=.word (wordAt x sites (start j) slot)

theorem start_lt {a b : Nat} (ab : a<b) (B₀ : b≤395) : start a<start b := by
  induction b with
  | zero => omega
  | succ b ih =>
    have here := (BStarNativeReceiptInduction.bounds (k:=b) (by omega)).1
    by_cases E : a=b
    · simpa only [E] using here
    · exact Nat.lt_trans (ih (by omega) (by omega)) here

/-- Native SSA indices are not changed by the accepted chunk's
later aliases including those of the same receipt. -/
theorem chunk_head_read {r : Nat} {k : Nat} (K : k<395)
    (table : PrimTable r) (bank : Bank) (regs : List Value) (L : regs.length=start k)
    (c : Code) (G : get (start k)=some c) :
    readReg (runCodes table bank regs (chunk k)) (start k)=
      evalInstr (toInstr table bank c) regs := by
  rw [chunk_cons K c G,←L]
  exact runCodes_new table bank regs (c::suffix k) 0 (by simp)

theorem step_packed {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (before mid suffix : List (Fin n)) (e next : Fin n)
    (W : w=before++e::(mid++suffix))
    {width k : Nat} (K : k<394)
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (c' : Code) (G : get (start k)=some c') :
    let addr := fun j => S.getD j fall
    let root := (addr 0).1
    let sites := digitSite hp base addr len width L
    let x := run initial before
    let y := step x e
    let z := run y mid
    (∀ i, Layout PROTO base i=Layout PROTO x i) →
    Hit hp base addr len x e (13+k) →
    GeneratedOwner hp base addr len y .idle mid (.busy (13+k+1) (.back 0)) →
    Flat hp y root mid →
    Hit hp base addr len z next (13+k+1) →
    (∀ u i,Layout PROTO base i=Layout PROTO (run y u) i) →
    ∀ (table : PrimTable width) (bank : Bank) (regs : List Value),
    PackedRep x root sites k regs →
    (∀ q d, ((capturedHeader q d).read (x root).long).toNat=(bank.hdr q d).toNat) →
    (∀ f, bind (longGeometry PROTO (x root)) 0 (atSite (x root).long 0)=.reply f →
      ScalarHead table bank (x root).long k regs c' f) →
    (∀ slot : WordSlot (start k), evalInstr (toInstr table bank c') regs=
      .word (wordAt y sites (start k) slot)) →
    PackedRep z root sites (k+1) (runCodes table bank regs (chunk k)) := by
  dsimp only
  intro same hit gen flat nhit nextSame table bank regs packed capture scalar word
  let root := (S.getD 0 fall).1
  let sites := digitSite hp base (fun j => S.getD j fall) len width L
  let x := run initial before
  let y := step x e
  let z := run y mid
  let head := evalInstr (toInstr table bank c') regs
  have headlen : (regs++[head]).length=start k+1 := by simp [packed.length]
  obtain ⟨f,found,_,_⟩ := hit.2.2.2.2.2
  have assumptions := head_ready table bank (x root).long k regs c' f G packed.length
    packed.scalar (scalar f found)
  have R := hit_scalar_store_next hp C same sep K c' G hit gen flat nhit nextSame table bank
    (regs++[head]) headlen capture assumptions.2.1 (fun g hg => by
      have E : g=f := Token.reply.inj (hg.symm.trans found)
      subst g
      exact ⟨assumptions.1,assumptions.2.2⟩)
  have K' : k<395 := by omega
  have C₀ : runCodes table bank regs (chunk k)=runCodes table bank (regs++[head]) (BStarAliasRoster.suffix k) := by
    rw [chunk_cons K' c' G]
    rfl
  refine ⟨?_, by rw [C₀]; exact R, ?_⟩
  · have bounds := BStarNativeReceiptInduction.bounds K'
    rw [runCodes_length,packed.length]
    unfold chunk
    simp only [List.length_take,List.length_drop,literal_length]
    omega
  · intro j J slot
    by_cases q : j=k
    · subst j
      have W' : w=(before++[e])++mid++suffix := by
        simpa [List.append_assoc] using W
      have YY : run initial (before++[e])=y := by rw [BStarResetSchedule.run_append]; rfl
      have nextPC : pc y root=13+k+1 := hit.2.2.2.1
      have later : 13+k<pc (run initial (before++[e])) root := by
        rw [YY,nextPC]
        omega
      have N := retain_word hp C sep rootK whole band (before++[e]) mid suffix W'
        (13+k) (start k) width (scheduled_node K') slot L later
      rw [YY] at N
      exact (chunk_head_read K' table bank regs packed.length c' G).trans ((word slot).trans (congrArg Value.word N.symm))
    · have J₀ : j<k := by omega
      have idx : start j<regs.length := packed.length.symm ▸ start_lt J₀ (by omega)
      have W' : w=before++(e::mid)++suffix := by simpa [List.cons_append,List.append_assoc] using W
      have nowPC : pc x root=13+k := hit.2.2.1
      have earlier : 13+j<pc x root := by rw [nowPC]; omega
      have N := retain_word hp C sep rootK whole band before (e::mid) suffix W'
        (13+j) (start j) width (scheduled_node (by omega)) slot L earlier
      exact (runCodes_prefix table bank regs (chunk k) (start j) idx).trans
        ((packed.numeric j J₀ slot).trans (congrArg Value.word N.symm))

end L4.BStarNativePackedRep
