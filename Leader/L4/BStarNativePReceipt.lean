import Leader.L4.BStarNumericCompleteSweep
import Leader.L4.Compiler.DigitsWords
import Leader.L4.BStarNativeZeroHead
import Leader.L4.BStarNumericChartCoverage
import Leader.L4.BStarNumericWordFrame
namespace L4.BStarNativePReceipt
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

private theorem digit_p (g : LongGeometry) (x : BitVec LW) (i width j : Nat) (v : Payload)
    (last : (g.inside && g.last)=decide (j+1=width)) :
    physicalDigit g x i (.const .p) v=
      (writeNum i (constPStep (positionAt width j)).val,v) := by
  simp only [physicalDigit,litDigit,constPStep,positionAt,last]
  by_cases h : j+1=width <;> simp [h] <;> rfl

/-- An actual matched CONST(P) tour stores its accepted base-16
word at the source consume. The final-digit flag uses the old physical
geometry; no successor-END or prior CONST-zero itinerary is needed. -/
theorem p_receipt {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {door : Fin n} {w : List (Fin n)} {width op i : Nat}
    (F : Found hp base (fun j => S.getD j fall) len op x w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run x w) door op)
    (lo : 13≤op) (hi : op<408) (node : nodeOf op=some i) (code : get i=some (.const .p))
    (slot : WordSlot i) (hr : 1≤width)
    (flags : ∀ j, (longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<width) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (T : PrimTable width) (bank : Bank) (sem : PrimSem T bank) (regs : List Value) :
    ∃ L : (significantSites hp base (fun j => S.getD j fall) len).length=width,
      evalInstr (toInstr T bank (.const .p)) regs =
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
  have fl := fun j => (flags j).1
  have L := significant_length hp chart align fl notShort
  let site := digitSite hp base addr len width L
  refine ⟨L,?_⟩
  have Bk : BusyOnly hp base addr len op (run x pre) (.out len) (turn::ret) (.back 0) :=
    .cons old E backward
  have ords := aligned_ordinals hp chart align fl notShort
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
      num (step (run x w) door (site j)).long i=(constPStep (positionAt width j.val)).val := by
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
    have oldInside : (geom hp d).inside=true :=
      (Aligned.record_significant hp align d memDs sig).2
    have oldLast : (geom hp d).last=(longGeometry B (base d.mark)).last := by
      rw [gg]
      exact (congrArg (fun z : Bool × Bool × Bool => z.2.2) (sameOld d.mark)).symm
    have hlast : ((geom hp d).inside && (geom hp d).last)=decide (j.val+1=width) := by
      rw [oldInside,Bool.true_and,oldLast,(flags d.mark).2,←siteEq,ORD j]
    have digit := digit_p (geom hp d) (byte d) i width j.val d.offer hlast
    have buf := (R ⟨j.val,q⟩ i).2
    change (numeric i).read ((physicalDigit (geom hp d) (byte d) i (.const .p) d.offer).1.apply (byte d))=
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
    exact num_write_of_lt slot (constPStep _).isLt _
  have Word : wordAt (step (run x w) door) site i slot =
      val (fun j : Fin width => constPStep (positionAt width j.val)) := by
    unfold wordAt val
    apply valJ_congr
    intro j hj _
    exact full ⟨j,hj⟩
  rw [Word,p_word hr]
  change Value.word (den (T.const .p) (readArgs regs []))=_
  rw [sem.const]
  apply congrArg Value.word
  unfold ConstId.val
  apply Nat.mod_eq_of_lt
  have Bnd := valJ_lt (fun j : Fin width => constPStep (positionAt width j.val)) width (Nat.le_refl _)
  change val _<16^width at Bnd
  rwa [p_word hr] at Bnd

end L4.BStarNativePReceipt
