import Leader.L4.BStarNativePrefixInduction
import Leader.L4.BStarNativeAtLaunch
import Leader.L4.BStarNativeMuxHit
import Leader.L4.BStarNativeConcreteSource

namespace L4.BStarNativeConcreteMux
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

open BStarNativeAtLaunch BStarNativeMuxHit BStarH6Ordinal BStarOwnerLaunchOrigin
open BStarNativeScalarRecurrence BStarScalarFits

open BStarNativeMuxHit BStarNativeScanNat

private theorem extend_mux (old : BitVec LW) (regs : List Value) (k q a b value : Nat)
    (G : get (start k)=some (.mux q a b)) (L : regs.length=start k)
    (R : WellRep old [] regs literalCmp) (f : Payload) :
    WellRep old (headPending old k f (.mux q a b)) (regs++[.word value]) literalCmp := by
  intro i I
  rw [List.length_append,List.length_singleton] at I
  by_cases E : i=regs.length
  · subst i
    refine ⟨?_,?_⟩
    · intro b V
      simp [readReg] at V
    · rw [L]
      simp [literalCmp,G,BStarCmpReceipt.isCmp]
  · have lt : i<regs.length := by omega
    have eq : readReg (regs++[.word value]) i=readReg regs i := by
      simp [readReg,List.getElem?_append_left lt]
    unfold headPending nodeResult
    simpa only [Option.toList_none,List.map_nil,BoolRep,CmpRep,eq] using R i lt

theorem mux_ready {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (prior flight tail : List (Fin n)) (door : Fin n) (W : w=prior++flight++door::tail)
    {width k q a b : Nat} (K : k<395) (width_pos : 0<width)
    (G : get (start k)=some (.mux q a b))
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (flags : ∀ i, (longGeometry PROTO (base i)).inside=decide (oldOrdinal PROTO base hh i<width))
    (notShort : ∀ i,oldH6 PROTO base (rightNeighbor i)=true → width≤oldOrdinal PROTO base hh i+1)
    (stable : ∀ u i,Layout PROTO base i=Layout PROTO (run initial u) i)
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
    q<regs.length →
    BStarNativeScanNat.HasBool regs q →
    (∀ q d, ((capturedHeader q d).read (x root).long).toNat=(bank.hdr q d).toNat) →
    BStarNativePrefixInduction.Ready hp table bank x (step x door) root sites k (.mux q a b) regs := by
  dsimp only
  intro F flat H R qbound QB capture
  let adr := fun j => S.getD j fall
  let r0 := (adr 0).1
  let st := run initial prior
  have node := scheduled_node K
  have slots := literal_typed (start k) (.mux q a b) G
  simp only [typedSlots,wordCheck,Bool.and_eq_true,beq_iff_eq] at slots
  obtain ⟨before,launch,after,_,_,split,_,_,Q⟩ := actual_hit_mux hp chart sep F H
    (by omega) (by omega) width_pos node G slots.1.1 slots.1.2 slots.2 flags notShort table bank sem regs
  have op : pc (run st flight) r0=13+k := H.2.2.1
  have data : a∈dataOperands (.mux q a b) := by simp [dataOperands]
  have input := arg_at_flight_launch hp chart sep rootK whole band prior flight (door::tail) W
    before after launch split K (.mux q a b) G data L flat op regs R slots.1.2
  have dataB : b∈dataOperands (.mux q a b) := by simp [dataOperands]
  have inputB := arg_at_flight_launch hp chart sep rootK whole band prior flight (door::tail) W
    before after launch split K (.mux q a b) G dataB L flat op regs R slots.2
  have args : ([q,a,b] : List Nat)[1]?=some a := rfl
  have argsB : ([q,a,b] : List Nat)[2]?=some b := rfl
  have argsQ : ([q,a,b] : List Nat)[0]?=some q := rfl
  obtain ⟨_,_,remaining⟩ := BStarGeneratedTapeCuts.split hp prior (flight++door::tail)
    ((W.trans (List.append_assoc _ _ _)) ▸ whole)
  obtain ⟨_,pft,_⟩ := BStarGeneratedTapeCuts.split hp flight (door::tail) remaining
  have startPC : pc st r0=13+k := (flat flight [] (List.append_nil _).symm).symm.trans op
  have same : ∀ s i, Layout PROTO base i=Layout PROTO (run st s) i := by
    intro s i
    simpa only [BStarResetSchedule.run_append] using stable (prior++s) i
  have flightMarks := flat_flight hp chart same sep pft flat (by omega : 13≤pc st r0)
    (by omega : pc st r0≤408)
  have suffixMarks : ∀ u e v,launch::after=u++e::v →
      FlightMark hp (run (run st before) u) r0 e := by
    intro u e v E
    rw [←BStarResetSchedule.run_append]
    exact flightMarks (before++u) e v (by rw [split,E,List.append_assoc])
  have hold : source (run st flight r0).long q=source (run st before r0).long q := by
    rw [split,BStarResetSchedule.run_append]
    exact word_scalar_hold hp (run st before) r0 (launch::after) sep suffixMarks q
  obtain ⟨t,tRead⟩ := QB
  have hq := (R.scalar q qbound).1 t tRead
  have selector : source (run st before r0).long q=(argB (readArgs regs [q,a,b]) 0).toNat := by
    rw [←hold,argB_get (regs:=regs) argsQ,tRead]
    exact hq
  have value := Q selector (input.trans (argW_get (regs:=regs) (width:=width) args).symm)
    (inputB.trans (argW_get (regs:=regs) (width:=width) argsB).symm)
  refine ⟨G,capture,?_,fun _ _ _ bad => by contradiction,fun _ => value⟩
  intro f _
  refine .inr (.ready True.intro True.intro ?_)
  rw [value]
  exact extend_mux _ _ _ _ _ _ _ G R.length R.scalar f

open BStarNativeConcreteSource

private def muxSelectorCheck (i : Nat) : Bool :=
  match get i with
  | some (.mux q _ _) => decide (q<i) && ((get q).map boolOutput).getD false
  | _ => true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem muxSelectorCensus : (List.range 474).all muxSelectorCheck=true := by decide +kernel

theorem mux_selector_typed {width k q a b : Nat} (T : PrimTable width) (bank : Bank)
    (K : k<395) (G : get (start k)=some (.mux q a b)) :
    q<(regsBefore T bank k).length ∧ HasBool (regsBefore T bank k) q := by
  have h := (List.getElem?_eq_some_iff.mp G).1
  rw [literal_length] at h
  have H := List.all_eq_true.mp muxSelectorCensus _ (List.mem_range.mpr h)
  simp only [muxSelectorCheck,G,Bool.and_eq_true,decide_eq_true_eq] at H
  refine ⟨by rw [prefix_length T bank (by omega)]; exact H.1,?_⟩
  have qb : q<(L4.Compiler.Native.literal.take (start k)).length := by
    simp only [List.length_take,literal_length,Nat.min_eq_left (by omega : start k≤474)]
    exact H.1
  have O := runCodes_new T bank [] (L4.Compiler.Native.literal.take (start k)) q qb
  have E := H.2
  change (L4.Compiler.Native.literal[q]?.map boolOutput).getD false=true at E
  rw [List.getElem?_eq_getElem (by rw [literal_length]; omega)] at E
  simp only [Option.map_some,Option.getD_some] at E
  change ∃ x, readReg (runCodes T bank [] (L4.Compiler.Native.literal.take (start k))) q=.boolean x
  simp only [List.length_nil,Nat.zero_add] at O
  rw [O]
  rw [List.getElem_take]
  generalize L4.Compiler.Native.literal[q]'(by rw [literal_length]; omega)=c at E ⊢
  cases c <;> cases E <;> exact ⟨_,rfl⟩

theorem mux_ready_accepted {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (prior flight tail : List (Fin n)) (door : Fin n) (W : w=prior++flight++door::tail)
    {width k q a b : Nat} (K : k<395) (width_pos : 0<width)
    (G : get (start k)=some (.mux q a b))
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (flags : ∀ i, (longGeometry PROTO (base i)).inside=decide (oldOrdinal PROTO base hh i<width))
    (notShort : ∀ i,oldH6 PROTO base (rightNeighbor i)=true → width≤oldOrdinal PROTO base hh i+1)
    (stable : ∀ u i,Layout PROTO base i=Layout PROTO (run initial u) i)
    (table : PrimTable width) (bank : Bank) (sem : PrimSem table bank) :
    let addr := fun j => S.getD j fall
    let sites := digitSite hp base addr len width L
    let root := (addr 0).1
    let st := run initial prior
    let x := run st flight
    Found hp base addr len (13+k) st flight (.back 0) →
    Flat hp st root flight →
    Hit hp base addr len x door (13+k) →
    PackedRep x root sites k (regsBefore table bank k) →
    (∀ q d, ((capturedHeader q d).read (x root).long).toNat=(bank.hdr q d).toNat) →
    BStarNativePrefixInduction.Ready hp table bank x (step x door) root sites k (.mux q a b) (regsBefore table bank k) := by
  dsimp only
  intro F flat H R capture
  obtain ⟨fits,typed⟩ := mux_selector_typed table bank K G
  exact mux_ready hp chart sep rootK whole band prior flight tail door W K width_pos G L
    flags notShort stable table bank sem _ F flat H R fits typed capture

#print axioms mux_ready_accepted

#print axioms mux_selector_typed

#print axioms mux_ready
end L4.BStarNativeConcreteMux
