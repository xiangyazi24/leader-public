import Leader.L4.BStarNativePriorInputs

namespace L4.BStarNativeAtLaunch
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

/-- All canonical family operand agreements at their exhibited launch
follow from the later Hit's PackedRep on the same Flat itinerary.
The split merely identifies the launch cut; its PC is derived. -/
theorem arg_at_flight_launch {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (prior flight rest : List (Fin n)) (W : w=prior++flight++rest)
    (before after : List (Fin n)) (launch : Fin n) (split : flight=before++launch::after)
    {width k a : Nat} (K : k<395) (c' : Code) (G : get (start k)=some c')
    (A : a∈dataOperands c')
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (flat : Flat hp (run initial prior) (S.getD 0 fall).1 flight)
    (op : pc (run (run initial prior) flight) (S.getD 0 fall).1=13+k)
    (regs : List Value) :
    let sites := digitSite hp base (fun j => S.getD j fall) len width L
    PackedRep (run (run initial prior) flight) (S.getD 0 fall).1 sites k regs →
    ∀ slot : WordSlot a,
      wordAt (step (run (run initial prior) before) launch) sites a slot =
      (readReg regs a).asWord % 16^width := by
  dsimp only
  intro R slot
  let pl := before++[launch]
  have fw : flight=pl++after := by simpa [pl,List.append_assoc] using split
  have earlier : pc (run initial (prior++pl)) (S.getD 0 fall).1=13+k := by
    rw [BStarResetSchedule.run_append,flat pl after fw,←flat flight [] (List.append_nil _).symm]
    exact op
  have w' : w=(prior++pl)++after++rest := by rw [W,fw]; simp [List.append_assoc]
  have E : run (run initial (prior++pl)) after=run (run initial prior) flight := by
    rw [BStarResetSchedule.run_append,←BStarResetSchedule.run_append,←fw]
  have Q := arg_at_launch_of_hit hp chart sep rootK whole band (prior++pl) after rest w'
    K c' G A L earlier regs (E.symm ▸ R)
  obtain ⟨ss,value⟩ := Q
  rw [BStarResetSchedule.run_append] at value
  unfold pl at value
  rw [BStarResetSchedule.run_append] at value
  exact value.symm

#print axioms arg_at_flight_launch
end L4.BStarNativeAtLaunch
