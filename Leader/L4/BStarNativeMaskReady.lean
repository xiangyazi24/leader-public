import Leader.L4.BStarNativeAtLaunch
import Leader.L4.BStarNativeMaskActual
import Leader.L4.BStarNativePrefixInduction
import Leader.L4.BStarNativeNumberRetention

namespace L4.BStarNativeMaskReady
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken BStarLongCommand
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6Ordinal
open BStarOwnerLaunchOrigin BStarNativeReceiptTape BStarNativePrefixInduction
open BStarLongArithmetic L4.Compiler.Native L4.Compiler.Interp
open BStarNativeReceiptInduction BStarAliasRoster BStarAliasFold BStarNativeScalarRecurrence
open BStarNumericChartCoverage
open BStarResetChartTouch BStarResetMarkAdapter BStarSeparatingRail BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

open BStarGeneratedOwner BStarGeneratedPCAncestry BStarNativeAtLaunch BStarNativePackedRep
open BStarLongSignatures L4.Compiler.Digits
open BStarGeneratedBandScan
open BStarPhysicalDigitSem BStarNativePriorInputs BStarLongRegisters BStarLiteralPC

/-- MASKB never overlays a source scalar; extending by its distributed word
therefore preserves the exact old scalar representation. -/
theorem scalar {width : Nat} (T : PrimTable width) (bank : Bank)
    (old : BitVec LW) (k : Nat) (f : Payload) (a : Nat) (regs : List Value)
    (G : get (start k)=some (.maskB a)) (L : regs.length=start k)
    (R : WellRep old [] regs literalCmp) : ScalarHead T bank old k regs (.maskB a) f := by
  have U : ¬literalCmp (start k) := by simp [literalCmp,G,BStarCmpReceipt.isCmp]
  refine .ready True.intro True.intro ?_
  have W : ∃ m, evalInstr (toInstr T bank (.maskB a)) regs=.word m := ⟨_,rfl⟩
  obtain ⟨m,W⟩ := W
  simp only [headPending,nodeResult,Option.toList_none,List.map_nil,W]
  intro i hi
  by_cases h : i<regs.length
  · have E := readReg_append_left regs [Value.word m] i h
    simpa only [BoolRep,CmpRep,E] using R i h
  · have eq : i=regs.length := by simp at hi; omega
    subst i
    have E : readReg (regs++[Value.word m]) regs.length=.word m := by
      simp [readReg]
    refine ⟨?_,?_⟩
    · intro b H
      rw [E] at H
      contradiction
    · intro C
      exact False.elim (U (L ▸ C))


/-- Concrete MASKB readiness on the actual raw receipt. The first genuine
PC13 sweep supplies offsets and successor-END, while the exact native
prefix retains the input through this head's launch. -/
theorem ready {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (prior flight tail : List (Fin n)) (door : Fin n) (W : w=prior++flight++door::tail)
    {width k a : Nat} (K : k<395) (hr : 1<width)
    (G : get (start k)=some (.maskB a))
    {w0 between : List (Fin n)} {door0 : Fin n}
    (F0 : Found hp base (fun j => S.getD j fall) len 13 initial w0 (.back 0))
    (H0 : Hit hp base (fun j => S.getD j fall) len (run initial w0) door0 13)
    (splitPrior : prior=w0++door0::between)
    (stable : ∀ u, ∀ j, Layout B (run initial u) j=Layout B base j)
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (flags : ∀ j, (longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<width) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
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
    Ready hp table bank x (step x door) root sites k (.maskB a) regs := by
  dsimp only
  intro F flat H R capture
  let adr := fun j => S.getD j fall
  let r0 := (adr 0).1
  have node := scheduled_node K
  have slots := literal_typed (start k) (.maskB a) G
  simp only [typedSlots,wordCheck,Bool.and_eq_true,beq_iff_eq] at slots
  have same : run initial prior=run (step (run initial w0) door0) between := by
    rw [splitPrior,BStarResetSchedule.run_append]
    rfl
  obtain ⟨before,launch,after,_,split,Q⟩ := BStarNativeMaskActual.mask_receipt hp chart sep
    F0 H0 same F H (by omega) (by omega) node G slots.1 slots.2 hr flags notShort
    (fun u _ _ => stable u) table bank sem regs
  have op : pc (run (run initial prior) flight) r0=13+k := H.2.2.1
  have data : a∈dataOperands (.maskB a) := by simp [dataOperands]
  have input := arg_at_flight_launch hp chart sep rootK whole band prior flight (door::tail) W
    before after launch split K (.maskB a) G data L flat op regs R slots.2
  have args : ([a] : List Nat)[0]?=some a := rfl
  have eq := Q (input.trans (argW_get (regs:=regs) (width:=width) args).symm)
  refine ⟨G,capture,fun f _ => Or.inr (scalar table bank _ k f a _ G R.length R.scalar),?_,?_⟩
  · intro _ _ _ bad
    cases bad
  · intro slot
    exact eq

#print axioms ready
end L4.BStarNativeMaskReady
