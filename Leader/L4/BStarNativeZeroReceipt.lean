import Leader.L4.BStarNativeZeroHead
import Leader.L4.BStarNumericChartCoverage
import Leader.L4.BStarNumericWordFrame
namespace L4.BStarNativeZeroReceipt
open AllSizeProtocol BStarTrace BStarLongToken BStarLongLayout
open BStarLongArithmetic BStarLongRegisters BStarPhysicalDigitSem BStarPhysicalWordSem
open L4.Compiler.Digits L4.Compiler.Native L4.Compiler.Interp
open BStarAliasFold BStarAliasRoster BStarNativeReceiptInduction

open BStarNumericHitSweep BStarNumericCompleteSweep BStarNumericCarry
open BStarNumericChronology BStarNumericConsecutive BStarNumericReceipt
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetMarkAdapter BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarLongCommand BStarLongClaims BStarLongWork BStarLongEvents
open BStarResetChartTouch BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

open BStarH6Ordinal BStarNativeZeroHead BStarNumericChartCoverage BStarNumericWordFrame
open BStarGeneratedOwner BStarGeneratedTapeCuts BStarLongLiteral
open BStarResetRailRing BStarSeparatorControl
set_option maxRecDepth 4096

/-- The chart-ordered word is the accepted first value at the actual
consume cut, and still after the consuming mark. No independent
return history or chart coverage assumption is supplied. -/
theorem zero_receipt {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {door : Fin n} {w : List (Fin n)} {width : Nat}
    (F : Found hp base (fun j => S.getD j fall) len 13 x w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run x w) door 13)
    (flags : ∀ i, (longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    (T : PrimTable width) (bank : Bank) (sem : PrimSem T bank) :
    let addr := fun j => S.getD j fall
    let y := run x w
    ∃ L : (significantSites hp base addr len).length=width,
      let site := digitSite hp base addr len width L
      let regs := runCodes T bank [] [.const .zero]
      readReg regs 0=.word (wordAt y site 0 zero_slot) ∧
      readReg regs 0=.word (wordAt (step y door) site 0 zero_slot) ∧
      ∃ actual : Payload,
        let wire := (y (addr 0).1).long
        BStarLongCommand.bind (longGeometry B (y (addr 0).1)) 0 (atSite wire 0)=.reply actual ∧
        WellRep wire (headPending wire 0 actual (.const .zero)) regs literalCmp := by
  dsimp only
  let addr := fun j => S.getD j fall
  obtain ⟨pre,turn,ret,W,outward,E,backward⟩ := BStarAcquireAckAncestry.found_split_turn hp F
  have replay : run x w=run (step (run x pre) turn) ret := by
    rw [W,BStarResetSchedule.run_append]
    rfl
  have old : Current hp base addr len (run x pre) (.busy 13 (.out len)) := by
    obtain ⟨u,w',e,O,_,_,_,U⟩ := outward
    rw [O,BStarResetSchedule.run_append]
    exact (BStarAcquireHistoryReturn.busy_end hp U : Current hp base addr len
      (run (step (run x u) e) w') (.busy 13 (.out len)))
  obtain ⟨C,v,sel,kind,dst,K,idx⟩ := BStarStageTerminalHealth.selected_turn hp chart turn
    (sep turn) 13 old (busy_start hp backward)
  obtain ⟨_,before,launch,after,i,code,P,N,G,sweep⟩ := of_selected hp chart sep outward backward
    (replay ▸ H) (by decide) (by decide) C v K dst idx sel
  obtain rfl := Option.some.inj (N.symm.trans first_op.1)
  obtain rfl := Option.some.inj (G.symm.trans first_op.2)
  obtain ⟨ds,align,tokens,_,sweepExact,R⟩ := sweep
  have L := significant_length hp chart align flags notShort
  refine ⟨L,?_⟩
  let site := digitSite hp base addr len width L
  have Bk : BusyOnly hp base addr len 13 (run x pre) (.out len) (turn::ret) (.back 0) :=
    .cons old E backward
  have full (j : Fin width) :
      num ((run x w) (site j)).long 0=0 ∧ num (step (run x w) door (site j)).long 0=0 := by
    obtain ⟨q,siteEq⟩ := digitSite_of_visit hp align width L j
    let visits := ds.filter (significant hp base addr)
    let d := visits[j.val]'q
    change site j=d.mark at siteEq
    have mem : d∈visits := List.getElem_mem q
    obtain ⟨memDs,sig⟩ := List.mem_filter.mp mem
    obtain ⟨V,_,less⟩ := Aligned.record_facts hp align d memDs
    have one := (Aligned.record_significant hp align d memDs sig).1
    have main : d.claim∈orderedCommands (oldPair B d.old d.mark) := by
      rw [←actualOffers_claims _ ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)]
      exact List.mem_map.mpr ⟨_,V.1,rfl⟩
    have left : d.claim.source.side=.left := by rw [center_of _ _ main one]; rfl
    have pos : addr d.index=(site j,1) := by
      have addrEq : addr d.index=address d.mark d.claim.source := V.2.2.1
      rw [addrEq]
      have J : d.claim.source=BStarLongClaims.L 1 := by
        rw [center_of _ _ main one]
        rfl
      rw [J]
      change (d.mark,(1 : Fin 11))=(site j,1)
      exact congrArg (fun a => (a,(1 : Fin 11))) siteEq.symm
    have dig := (digit_zero sweepExact).1 ⟨j.val,q⟩
    have outEq := (R ⟨j.val,q⟩ 0).2
    have Q : run x pre=run (step (run x before) launch) after := by
      rw [P,BStarResetSchedule.run_append]
      rfl
    have zeroPre : num ((run x pre) (site j)).long 0=0 := by
      rw [siteEq,Q]
      unfold num at dig ⊢
      rw [←outEq]
      exact dig
    have retain := busy_past hp Bk sep (Nat.le_of_lt less) (site j) pos less 0
    have W' : run x w=run (run x pre) (turn::ret) := by
      rw [W,BStarResetSchedule.run_append]
    have zeroHit : num ((run x w) (site j)).long 0=0 := by
      unfold num at zeroPre ⊢
      rw [W',retain]
      exact zeroPre
    have now := H.1
    have nf : ¬anyTag.F (atCursor (run x w) (site j,1)) := by
      rw [←pos]
      exact BStarOwnerControlHistory.pointed_backward_no_forward _ len 0 now.2.1
        d.index (Nat.le_of_lt less)
    have retainDoor := step_no_forward hp (run x w) door (site j) 0 (sep door) nf
    refine ⟨zeroHit,?_⟩
    unfold num at zeroHit ⊢
    rwa [retainDoor]
  obtain ⟨actual,bound,_,_⟩ := H.2.2.2.2.2
  have fst := typed_first T bank sem (run x w) site (run x w (addr 0).1).long actual (fun j => (full j).1)
  have snd := typed_first T bank sem (step (run x w) door) site (run x w (addr 0).1).long actual (fun j => (full j).2)
  exact ⟨fst.1,snd.1,actual,bound,fst.2⟩

end L4.BStarNativeZeroReceipt
