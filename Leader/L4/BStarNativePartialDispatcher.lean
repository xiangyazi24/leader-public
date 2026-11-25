import Leader.L4.BStarNativeConstReady
import Leader.L4.BStarNativeMaskReady
import Leader.L4.BStarNativeFirstSplit
import Leader.L4.BStarNativeConcreteSource
import Leader.L4.BStarNativeConcreteAdd
import Leader.L4.BStarNativeConcreteSub
import Leader.L4.BStarNativeConcreteShift
import Leader.L4.BStarNativeConcreteCmp
import Leader.L4.BStarNativeConcreteScan
import Leader.L4.BStarNativeConcreteMux

namespace L4.BStarNativePartialDispatcher
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

/-- LOAD remains the single interface to the selected COMMIT value proof. -/
inductive Remaining : Code → Prop
  | load (q : Fin 3) (d : Fin 9) : Remaining (.load q d)

private theorem firstCode : get (start 0)=some (.const .zero) := by
  have N := scheduled_node (k:=0) (by decide)
  rw [show 13+0=13 by rfl,first_last.1] at N
  rw [←Option.some.inj N]
  rfl

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Compose all non-LOAD branches. Later offset-sensitive heads derive
their earlier physical PC13 on the same tape, not from an offset oracle. -/
theorem assemble {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
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
    (capture : ∀ u v,w=u++v → ∀ q d, ((capturedHeader q d).read (run initial u (S.getD 0 fall).1).long).toNat=
      (bank.hdr q d).toNat)
    (first rest : List (Fin n)) (firstDoor : Fin n) (W0 : w=first++firstDoor::rest)
    (found0 : Found hp base (fun j => S.getD j fall) len 13 initial first (.back 0))
    (flat0 : Flat hp initial (S.getD 0 fall).1 first)
    (hit0 : Hit hp base (fun j => S.getD j fall) len (run initial first) firstDoor 13) :
    let addr := fun j => S.getD j fall
    let sites := digitSite hp base addr len width L
    (∀ (prior pre tail : List (Fin n)) (e : Fin n) (k : Nat), k<394 →
      w=prior++(pre++e::tail) →
      let st := run initial prior
      let x := run st pre
      Found hp base addr len (13+k) st pre (.back 0) →
      Flat hp st (addr 0).1 pre →
      Hit hp base addr len x e (13+k) →
      PackedRep x (addr 0).1 sites k (regsBefore table bank k) →
      ∀ c', get (start k)=some c' → Remaining c' →
      Ready hp table bank x (step x e) (addr 0).1 sites k c' (regsBefore table bank k)) →
    Dispatcher hp table bank base initial addr len sites w := by
  dsimp only
  intro fallback prior pre tail e k K W
  dsimp only
  intro F flat H R _
  have K' : k<395 := by omega
  obtain ⟨i,c',familyId,N,G,HF⟩ := BStarNativeHeadRoster.dispatch (op:=13+k) (by omega) (by omega)
  rw [scheduled_node K'] at N
  obtain rfl := Option.some.inj N
  have W' : w=prior++pre++e::tail := W.trans (List.append_assoc _ _ _).symm
  have cap := capture (prior++pre) (e::tail) W'
  simp only [BStarResetSchedule.run_append] at cap
  have pos : 0<width := by omega
  have inFlags := fun i => (flags i).1
  have stable' : ∀ u i,Layout PROTO (run initial u) i=Layout PROTO base i :=
    fun u i => (stable u i).symm
  have after_first (positive : 0<k) : ∃ between,prior=first++firstDoor::between :=
    BStarNativeFirstSplit.after_first hp (base:=base) (initial:=initial) (addr:=fun j => S.getD j fall) (len:=len) positive W0 W flat0 hit0 flat H
  refine ⟨c',?_⟩
  by_cases isBool : boolHead c'=true
  · exact BStarNativeConcreteSource.source_ready hp table bank K' c' G isBool _ _ _ _ cap
  cases c' with
  | load q d => exact fallback prior pre tail e k K W F flat H R _ G (.load q d)
  | const v =>
    refine BStarNativeConstReady.ready hp (initial:=initial) chart sep K' v G F H ?_ (by omega) flags notShort L
      table bank sem cap R
    intro positive
    obtain ⟨between,E⟩ := after_first positive
    refine ⟨first,firstDoor,between,found0,hit0,?_,fun u _ _ i => stable' u i⟩
    rw [E,BStarResetSchedule.run_append]
    rfl
  | maskB a =>
    have positive : 0<k := by
      by_cases positive : 0<k
      · exact positive
      · have eq : k=0 := by omega
        subst k
        rw [firstCode] at G
        cases G
    obtain ⟨between,E⟩ := after_first positive
    exact BStarNativeMaskReady.ready hp chart sep rootK whole band prior pre tail e W' K'
      (by omega) G found0 hit0 E stable' L flags notShort table bank sem _ F flat H R cap
  | add a b =>
    exact BStarNativeConcreteAdd.add_ready hp chart sep rootK whole band
      prior pre tail e W' K' pos G L inFlags notShort table bank sem _ F flat H R cap
  | sub a b =>
    exact BStarNativeConcreteSub.sub_ready hp chart sep rootK whole band
      prior pre tail e W' K' pos G L inFlags notShort table bank sem _ F flat H R cap
  | shl3 a =>
    exact BStarNativeConcreteShift.shift_ready hp chart sep rootK whole band
      prior pre tail e W' K' pos G L inFlags notShort table bank sem _ F flat H R cap
  | cmp a b =>
    exact BStarNativeConcreteCmp.cmp_ready hp chart sep rootK whole band
      prior pre tail e W' K' pos G L inFlags notShort table bank sem _ F flat H R cap
  | mux q a b =>
    exact BStarNativeConcreteMux.mux_ready_accepted hp chart sep rootK whole band
      prior pre tail e W' K' pos G L inFlags notShort stable table bank sem F flat H R cap
  | scan5 a =>
    have positive : 0<k := by
      by_cases positive : 0<k
      · exact positive
      · have eq : k=0 := by omega
        subst k
        rw [firstCode] at G
        cases G
    obtain ⟨gap,Z⟩ := after_first positive
    have E : run initial prior=run (step (run initial first) firstDoor) gap := by
      rw [Z,BStarResetSchedule.run_append]
      rfl
    exact BStarNativeConcreteScan.scan_ready_after_zero hp chart sep rootK whole band
      prior pre tail e W' K' width_ge G L inFlags notShort initial first gap firstDoor found0 hit0 E stable'
      table bank sem _ F flat H R cap
  | bconst b => simp [family] at HF
  | header q d => simp [family] at HF
  | cmpEq a => simp [family] at HF
  | cmpLt a => simp [family] at HF
  | not a => exact (isBool rfl).elim
  | and a b => exact (isBool rfl).elim
  | or a b => exact (isBool rfl).elim
  | bmux q a b => exact (isBool rfl).elim
  | phaseEq a j => exact (isBool rfl).elim

end L4.BStarNativePartialDispatcher
