import Leader.L4.BStarNativePackedRep
import Leader.L4.BStarNativeScanNat
import Leader.L4.BStarNativeUniqueHit

namespace L4.BStarNativePrefixInduction
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

open BStarNativeScanNat BStarOwnerLaunchOrigin

set_option maxRecDepth 8192
set_option maxHeartbeats 1400000

structure Ready {width : Nat} (table : PrimTable width) (bank : Bank)
    (x y : X) (root : Fin n) (sites : Fin width → Fin n) (k : Nat)
    (c' : Code) (regs : List Value) : Prop where
  code : get (start k)=some c'
  capture : ∀ q d, ((capturedHeader q d).read (x root).long).toNat=(bank.hdr q d).toNat
  scalar : ∀ f : Payload,
    bind (longGeometry PROTO (x root)) 0 (atSite (x root).long 0)=.reply f →
    SourceTypes regs c' ∨ ScalarHead table bank (x root).long k regs c' f
  scan : ∀ f : Payload,
    bind (longGeometry PROTO (x root)) 0 (atSite (x root).long 0)=.reply f →
    ∀ a, c'=.scan5 a → f.argument.toNat<32 ∧
      (evalInstr (toInstr table bank c') regs).asWord=f.argument.toNat
  word : ∀ slot : WordSlot (start k), evalInstr (toInstr table bank c') regs=
    .word (wordAt y sites (start k) slot)

/-- Every consume in order carries its exact accepted pre-receipt
register file. No new marks, launches, or receipts are generated. -/
inductive Verified {width : Nat} (table : PrimTable width) (bank : Bank)
    (base : X) (addr : Nat → Pos n) (len : Nat) (sites : Fin width → Fin n) :
    X → Nat → List (Fin n) → Nat → Prop where
  | done {x k w} : Verified table bank base addr len sites x k w 0
  | take {x k pre tail e count}
      (hit : Hit hp base addr len (run x pre) e (13+k))
      (packed : PackedRep (run x pre) (addr 0).1 sites k (regsBefore table bank k))
      (scan : ScanNatRep (run x pre (addr 0).1).long (regsBefore table bank k))
      (rest : Verified table bank base addr len sites (step (run x pre) e) (k+1) tail count) :
      Verified table bank base addr len sites x k (pre++e::tail) (count+1)

def Dispatcher {width : Nat} (table : PrimTable width) (bank : Bank)
    (base initial : X) (addr : Nat → Pos n) (len : Nat) (sites : Fin width → Fin n)
    (w : List (Fin n)) : Prop :=
  ∀ (prior pre tail : List (Fin n)) (e : Fin n) (k : Nat), k<394 →
    w=prior++(pre++e::tail) →
    let st := run initial prior
    let x := run st pre
    Found hp base addr len (13+k) st pre (.back 0) →
    Flat hp st (addr 0).1 pre →
    Hit hp base addr len x e (13+k) →
    PackedRep x (addr 0).1 sites k (regsBefore table bank k) →
    ScanNatRep (x (addr 0).1).long (regsBefore table bank k) →
    ∃ c', Ready hp table bank x (step x e) (addr 0).1 sites k c' (regsBefore table bank k)

private theorem advance_pair {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {mode : Mode} (rootK : (S.getD 0 fall).2=0)
    (whole : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w mode)
    (band : CompilerBand hp initial (S.getD 0 fall).1 w)
    (stable : ∀ u i,Layout PROTO base i=Layout PROTO (run initial u) i)
    {width : Nat} (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (table : PrimTable width) (bank : Bank)
    (prior pre mid tail : List (Fin n)) (e next : Fin n)
    (W : w=prior++(pre++e::(mid++tail))) (k : Nat) (K : k<394) (c' : Code) :
    let addr := fun j => S.getD j fall
    let sites := digitSite hp base addr len width L
    let root := (addr 0).1
    let x := run (run initial prior) pre
    let y := step x e
    let z := run y mid
    (hit : Hit hp base addr len x e (13+k)) →
    GeneratedOwner hp base addr len y .idle mid (.busy (13+k+1) (.back 0)) →
    Flat hp y root mid →
    Hit hp base addr len z next (13+k+1) →
    PackedRep x root sites k (regsBefore table bank k) →
    ScanNatRep (x root).long (regsBefore table bank k) →
    Ready hp table bank x y root sites k c' (regsBefore table bank k) →
    PackedRep z root sites (k+1) (regsBefore table bank (k+1)) ∧
    ScanNatRep (z root).long (regsBefore table bank (k+1)) := by
  dsimp only
  intro hit future flat nhit packed scan ready
  let root := (S.getD 0 fall).1
  let x := run (run initial prior) pre
  let y := step x e
  let z := run y mid
  have eqX := BStarResetSchedule.run_append step initial prior pre
  have same : ∀ i, Layout PROTO base i=Layout PROTO x i := by
    intro i
    change Layout PROTO base i=Layout PROTO (run (run initial prior) pre) i
    exact eqX ▸ stable (prior++pre) i
  have nextSame : ∀ u, ∀ i, Layout PROTO base i=Layout PROTO (run y u) i := by
    intro u i
    have A := stable ((prior++pre)++e::u) i
    rw [BStarResetSchedule.run_append,eqX] at A
    exact A
  have scalar (f : Payload) (reply : bind (longGeometry PROTO (x root)) 0
      (atSite (x root).long 0)=.reply f) : ScalarHead table bank (x root).long k (regsBefore table bank k) c' f := by
    rcases ready.scalar f reply with h|h
    · exact .bool (source_head_of_rep packed.scalar scan h)
    · exact h
  have exactW : w=(prior++pre)++e::(mid++tail) := by simpa [List.append_assoc] using W
  have futurePacked := step_packed hp chart sep rootK whole band (prior++pre) mid tail e next exactW K L c' ready.code
  rw [eqX] at futurePacked
  have V := futurePacked same hit future flat nhit nextSame table bank _ packed ready.capture scalar ready.word
  obtain ⟨f,found,_,_⟩ := hit.2.2.2.2.2
  have A := actual_scanNat_step hp chart same sep K c' ready.code hit future flat nextSame f found
    table bank _ packed.length scan (ready.scan f found)
  rw [prefix_step table bank (by omega : k<395)]
  exact ⟨V,A⟩

/-- Proof reconstructed after workspace rollback. The chronological recursion stores
the typed register images at actual pre-consume cuts, not at supplied surrogate indices. -/
private theorem verify_from {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
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
    {cur : X} {op count : Nat} {tapeWord : List (Fin n)}
    (T : NativeTape hp base (fun j => S.getD j fall) len cur op tapeWord count) :
    ∀ (prior : List (Fin n)) (k : Nat), cur=run initial prior → op=13+k →
    w=prior++tapeWord → k+count≤395 →
    (∀ pre tail e, tapeWord=pre++e::tail →
      Hit hp base (fun j => S.getD j fall) len (run cur pre) e (13+k) →
      PackedRep (run cur pre) (S.getD 0 fall).1
        (digitSite hp base (fun j => S.getD j fall) len width L) k (regsBefore table bank k) ∧
      ScanNatRep (run cur pre (S.getD 0 fall).1).long (regsBefore table bank k)) →
    Verified hp table bank base (fun j => S.getD j fall) len
      (digitSite hp base (fun j => S.getD j fall) len width L) cur k tapeWord count := by
  induction T with
  | done _ _ _ => exact fun _ _ _ _ _ _ _ => .done
  | @take cur op pre tail e count ahead flat found hit rest ih =>
    intro prior k state actual W limit rep
    subst op
    have aWord : w=prior++(pre++e::tail) := W
    obtain ⟨packed,scan⟩ := rep pre tail e rfl hit
    refine .take hit packed scan ?_
    let newPrior := (prior++pre)++[e]
    have runNew : step (run cur pre) e=run initial newPrior := by
      rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append,←state]
      rfl
    have newW : w=newPrior++tail := by
      simpa [newPrior,List.append_assoc] using W
    refine ih newPrior (k+1) runNew (by omega) newW (by omega) ?_
    intro targetPre targetTail targetMark targetSplit targetHit
    cases rest with
    | done Trest atEnd flatEnd =>
      have no : pc (run (step (run cur pre) e) targetPre) (S.getD 0 fall).1 =
          pc (run (step (run cur pre) e) targetPre) (S.getD 0 fall).1 + 1 := by
        have P := flatEnd targetPre (targetMark::targetTail) targetSplit
        have Q := flatEnd (targetPre++[targetMark]) targetTail
          (by simpa [List.append_assoc] using targetSplit)
        rw [BStarResetSchedule.run_append] at Q
        have hh : pc (run (run (step (run cur pre) e) targetPre) [targetMark]) (S.getD 0 fall).1 =
            pc (run (step (run cur pre) e) targetPre) (S.getD 0 fall).1 + 1 := by
          change pc (step (run (step (run cur pre) e) targetPre) targetMark) (S.getD 0 fall).1 =
            pc (run (step (run cur pre) e) targetPre) (S.getD 0 fall).1 + 1
          exact targetHit.2.2.2.1.trans (congrArg (· + 1) targetHit.2.2.1).symm
        exact P.trans (Q.symm.trans hh)
      omega
    | @take y expected mid tail' next remain future flatNext foundNext hitNext restNext =>
      have a : w=(newPrior++mid)++next::tail' := by
        simpa [List.append_assoc] using newW
      have b : w=(newPrior++targetPre)++targetMark::targetTail := by
        rw [newW,targetSplit,←List.append_assoc]
      have hh₁ : Hit hp base (fun j => S.getD j fall) len (run initial (newPrior++mid)) next (13+(k+1)) := by
        rw [BStarResetSchedule.run_append,←runNew]
        exact hitNext
      have hh₂ : Hit hp base (fun j => S.getD j fall) len (run initial (newPrior++targetPre))
          targetMark (13+(k+1)) := by
        rw [BStarResetSchedule.run_append,←runNew]
        exact targetHit
      obtain ⟨E,EM,_⟩ := BStarNativeUniqueHit.unique hp rootK sep whole band a b hh₁ hh₂
      have E' : mid=targetPre := List.append_cancel_left E
      subst targetPre
      subst targetMark
      have bound : k<394 := by omega
      have start := D prior pre (mid++next::tail') e k bound aWord
      rw [←state] at start
      obtain ⟨c,ready⟩ := start found flat hit packed scan
      have AP := advance_pair hp chart sep rootK whole band stable L table bank prior pre mid (next::tail') e next aWord
        k bound c
      rw [←state] at AP
      exact AP hit future flatNext hitNext packed scan ready

/-- Specialization to the entire genuine 395-receipt compiler slice. -/
theorem verify_all {base initial : X} {hh : ∃ i,oldH6 PROTO base i=true}
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
    (T : NativeTape hp base (fun j => S.getD j fall) len initial 13 w 395) :
    Verified hp table bank base (fun j => S.getD j fall) len
      (digitSite hp base (fun j => S.getD j fall) len width L) initial 0 w 395 := by
  apply verify_from hp chart sep rootK whole band stable L table bank D T [] 0 rfl rfl rfl (by decide)
  intro pre tail e W H
  rw [prefix_zero]
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · decide +kernel
  · intro i h
    simp at h
  · intro i h
    omega
  · unfold ScanNatRep
    simp

/-- The final cut of a verified chronological subsequence; earlier cuts
are concatenated without changing or re-selecting any actual mark. -/
theorem final_prefix {width : Nat} {table : PrimTable width} {bank : Bank}
    {base x : X} {addr : Nat → Pos n} {len k count : Nat}
    {sites : Fin width → Fin n} {w : List (Fin n)}
    (T : Verified hp table bank base addr len sites x k w count)
    (pos : 0<count) (total : k+count=395) :
    ∃ pre e tail, w=pre++e::tail ∧
      Hit hp base addr len (run x pre) e 407 ∧
      PackedRep (run x pre) (addr 0).1 sites 394 (regsBefore table bank 394) ∧
      ScanNatRep (run x pre (addr 0).1).long (regsBefore table bank 394) := by
  induction T with
  | done => omega
  | @take x k pre tail e count hit packed scan rest ih =>
    by_cases h : count=0
    · have K : k=394 := by omega
      subst k
      exact ⟨pre,e,tail,rfl,hit,packed,scan⟩
    · obtain ⟨u,mark,t,W,H,P,S⟩ := ih (by omega) (by omega)
      refine ⟨pre++e::u,mark,t,?_,?_⟩
      · simpa [List.append_assoc] using congrArg (fun a => pre++e::a) W
      · have E : run x (pre++e::u)=run (step (run x pre) e) u := by
          rw [show pre++e::u=(pre++[e])++u by simp [List.append_assoc]]
          rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append]
          rfl
        rw [E]
        exact ⟨H,P,S⟩

#print axioms verify_all
#print axioms final_prefix
end L4.BStarNativePrefixInduction
