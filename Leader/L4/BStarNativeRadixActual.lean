import Leader.L4.BStarNativeOffsetDigitAt
import Leader.L4.BStarNumericCompleteSweep
import Leader.L4.Compiler.DigitsWords
import Leader.L4.BStarNativeZeroHead
import Leader.L4.BStarNumericChartCoverage
import Leader.L4.BStarNumericWordFrame
namespace L4.BStarNativeRadixActual
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
open BStarLongFixedRouting

private theorem digit_radix (g : LongGeometry) (x : BitVec LW) (i width j : Nat) (v : Payload)
    (cv : ConstId) (hc : cv=.one ∨ cv=.eight ∨ cv=.max)
    (hz : cv≠.max → (off g==0)=decide (j=0)) :
    physicalDigit g x i (.const cv) v=(writeNum i (constDigit cv (positionAt width j)).val,v) := by
  rcases hc with rfl|rfl|rfl
  · have H := hz (by decide)
    change ((if g.axes.h6 then 0 else min 5 g.offset)==0)=decide (j=0) at H
    simp only [physicalDigit,litDigit,constDigit,positionAt,constSmallStep,H]
    by_cases h0 : j=0 <;> simp [h0] <;> rfl
  · have H := hz (by decide)
    change ((if g.axes.h6 then 0 else min 5 g.offset)==0)=decide (j=0) at H
    simp only [physicalDigit,litDigit,constDigit,positionAt,constSmallStep,H]
    by_cases h0 : j=0 <;> simp [h0] <;> rfl
  · rfl

/-- Actual constant ONE, EIGHT or MAX at its matching physical receipt.
ONE/EIGHT use only the old zero-offset test; MAX does not inspect it. -/
theorem radix_receipt {base initial x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {door0 door : Fin n} {w0 between w : List (Fin n)} {width op i : Nat}
    (F0 : Found hp base (fun j => S.getD j fall) len 13 initial w0 (.back 0))
    (H0 : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run initial w0) door0 13)
    (atLate : x=run (step (run initial w0) door0) between)
    (F : Found hp base (fun j => S.getD j fall) len op x w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run x w) door op)
    (lo : 13≤op) (hi : op<408) (node : nodeOf op=some i)
    (cv : ConstId) (hc : cv=.one ∨ cv=.eight ∨ cv=.max) (code : get i=some (.const cv))
    (slot : WordSlot i) (hr : 1≤width)
    (flags : ∀ j, (longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (stable : ∀ u v,w0++door0::(between++w)=u++v →
      ∀ j, Layout B (run initial u) j=Layout B base j)
    (T : PrimTable width) (bank : Bank) (sem : PrimSem T bank) (regs : List Value) :
    ∃ L : (significantSites hp base (fun j => S.getD j fall) len).length=width,
      evalInstr (toInstr T bank (.const cv)) regs =
        .word (wordAt (step (run x w) door) (digitSite hp base (fun j => S.getD j fall) len width L) i slot) := by
  let addr := fun j => S.getD j fall
  obtain ⟨pre,turn,ret,W,outward,E,backward⟩ := BStarAcquireAckAncestry.found_split_turn hp F
  have replay : run x w=run (step (run x pre) turn) ret := by
    rw [W,BStarResetSchedule.run_append]
    rfl
  have old : Current hp base addr len (run x pre) (.busy op (.out len)) := by
    obtain ⟨u,w',e,O,_,_,_,U⟩ := outward
    rw [O,BStarResetSchedule.run_append]
    exact (BStarAcquireHistoryReturn.busy_end hp U : Current hp base addr len
      (run (step (run x u) e) w') (.busy op (.out len)))
  obtain ⟨C,v,sel,_,dst,K,idx⟩ := BStarStageTerminalHealth.selected_turn hp chart turn
    (sep turn) op old (busy_start hp backward)
  obtain ⟨_,before,launch,after,i',c',P,N,G,sweep⟩ := of_selected hp chart sep outward backward
    (replay ▸ H) lo hi C v K dst idx sel
  have ii := Option.some.inj (N.symm.trans node)
  subst i'
  have cc := Option.some.inj (G.symm.trans code)
  subst c'
  obtain ⟨ds,align,tokens,seq,sweepExact,R⟩ := sweep
  have L := significant_length hp chart align flags notShort
  let site := digitSite hp base addr len width L
  refine ⟨L,?_⟩
  have Bk : BusyOnly hp base addr len op (run x pre) (.out len) (turn::ret) (.back 0) :=
    .cons old E backward
  have ords := aligned_ordinals hp chart align flags notShort
  have ORD (j : Fin width) : oldOrdinal B base hh (site j)=j.val := by
    have E := congrArg (fun z : List Nat => z[j.val]?) ords
    have Lj : j.val<(significantSites hp base addr len).length := by
      change j.val<(significantSites hp base (fun j => S.getD j fall) len).length
      rw [L]
      exact j.isLt
    have Rj : j.val<(List.range width).length := by simpa only [List.length_range] using j.isLt
    rw [List.getElem?_map,List.getElem?_eq_getElem Lj,
      List.getElem?_eq_getElem Rj,List.getElem_range] at E
    exact Option.some.inj E
  have full (j : Fin width) :
      num (step (run x w) door (site j)).long i=(constDigit cv (positionAt width j.val)).val := by
    obtain ⟨q,siteEq⟩ := digitSite_of_visit hp align width L j
    let visits := ds.filter (significant hp base addr)
    let d := visits[j.val]'q
    change site j=d.mark at siteEq
    have mem : d∈visits := List.getElem_mem q
    obtain ⟨memDs,sig⟩ := List.mem_filter.mp mem
    obtain ⟨V,sameOld,less⟩ := Aligned.record_facts hp align d memDs
    have one := (Aligned.record_significant hp align d memDs sig).1
    have main : d.claim∈orderedCommands (oldPair B d.old d.mark) := by
      rw [←actualOffers_claims _ ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)]
      exact List.mem_map.mpr ⟨_,V.1,rfl⟩
    have axis : d.claim.source.side=.left := by rw [center_of _ _ main one]; rfl
    have gg : geom hp d=longGeometry B (d.old d.mark) := by unfold geom; rw [axis]; rfl
    have pos : addr d.index=(d.mark,1) := by
      have E : addr d.index=address d.mark d.claim.source := V.2.2.1
      rw [E,show d.claim.source=BStarLongClaims.L 1 by rw [center_of _ _ main one]; rfl]
      rfl
    have offs (_hv : cv≠.max) : (off (geom hp d)==0)=decide (j.val=0) := by
      let middle := between++before++[launch]
      have launchEq : run (step (run initial w0) door0) middle=step (run x before) launch := by
        unfold middle
        simp only [List.append_assoc,BStarResetSchedule.run_append]
        rw [←atLate]
        rfl
      have aligned : Aligned hp base addr len op
          (run (step (run initial w0) door0) middle) 0 after len ds := launchEq.symm ▸ align
      have same : ∀ u v,w0++door0::(middle++after)=u++v →
          ∀ k, Layout B (run initial u) k=Layout B base k := by
        intro u z e
        apply stable u (z++turn::ret)
        have Q := congrArg (fun a => a++turn::ret) e
        rw [W,P]
        simpa [middle,List.append_assoc] using Q
      have ho := BStarNativeOffsetDigitAt.later_offset hp chart sep F0 H0 middle after aligned same
        flags notShort d mem
      rw [ho, ←siteEq, ORD j]
      by_cases h : j.val=0 <;> simp [h, Nat.min_eq_zero_iff]
    have digit := digit_radix (geom hp d) (byte d) i width j.val d.offer cv hc offs
    have buf := (R ⟨j.val,q⟩ i).2
    change (numeric i).read ((physicalDigit (geom hp d) (byte d) i (.const cv) d.offer).1.apply (byte d))=
      (numeric i).read ((run (step (run x before) launch) after) d.mark).long at buf
    rw [digit] at buf
    have Q : run x pre=run (step (run x before) launch) after := by
      rw [P,BStarResetSchedule.run_append]; rfl
    have retain := busy_past hp Bk sep (Nat.le_of_lt less) d.mark pos less i
    have W' : run x w=run (run x pre) (turn::ret) := by rw [W,BStarResetSchedule.run_append]
    have nowHit := H.1
    have nf : ¬anyTag.F (atCursor (run x w) (d.mark,1)) := by
      rw [←pos]
      exact BStarOwnerControlHistory.pointed_backward_no_forward _ len 0 nowHit.2.1
        d.index (Nat.le_of_lt less)
    have retainDoor := step_no_forward hp (run x w) door d.mark i (sep door) nf
    rw [siteEq]
    unfold num
    rw [retainDoor,W',retain,Q,←buf]
    exact num_write_of_lt slot (constDigit cv _).isLt _
  have Word : wordAt (step (run x w) door) site i slot =
      val (fun j : Fin width => constDigit cv (positionAt width j.val)) := by
    unfold wordAt val
    apply valJ_congr
    intro j hj _
    exact full ⟨j,hj⟩
  have exactVal : val (fun j : Fin width => constDigit cv (positionAt width j.val))=cv.val width := by
    rcases hc with rfl|rfl|rfl
    · exact small_word hr 1
    · exact small_word hr 8
    · exact max_word
  have Bnd := valJ_lt (fun j : Fin width => constDigit cv (positionAt width j.val)) width (Nat.le_refl _)
  change val _<16^width at Bnd
  rw [Word,exactVal]
  change Value.word (den (T.const cv) (readArgs regs []))=_
  rw [sem.const,Nat.mod_eq_of_lt (exactVal ▸ Bnd)]

#print axioms radix_receipt
end L4.BStarNativeRadixActual
