import Leader.L4.BStarNativeOffsetDigitAt
import Leader.L4.Compiler.DigitsWords
import Leader.L4.BStarNativeZeroHead
import Leader.L4.BStarNumericChartCoverage
import Leader.L4.BStarNumericWordFrame
namespace L4.BStarNativeMaskActual
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

open BStarNativeEndCache BStarLongFixedRouting

private theorem ord_same {x y : X} (hx : ∃ j,oldH6 B x j=true)
    (hy : ∃ j,oldH6 B y j=true) (h : ∀ j,Layout B x j=Layout B y j) (j : Fin n) :
    oldOrdinal B x hx j=oldOrdinal B y hy j := by
  have f : oldH6 B x=oldH6 B y := funext (fun i => congrArg Prod.fst (h i))
  unfold oldOrdinal
  generalize oldH6 B x = xx at f hx ⊢
  generalize oldH6 B y = yy at f hy ⊢
  subst yy
  rfl

/-- The actual completed MASKB consume holds the accepted
little-endian result. Successor-END is derived from the earlier true
CONST zero itinerary on the same tape; only ordinary layout and
offset facts of the later visit follow from the actual first receipt. -/
theorem mask_receipt {base initial late : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {door0 door : Fin n} {w0 between w : List (Fin n)} {width op i a : Nat}
    (F0 : Found hp base (fun j => S.getD j fall) len 13 initial w0 (.back 0))
    (H0 : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run initial w0) door0 13)
    (atLate : late=run (step (run initial w0) door0) between)
    (F : Found hp base (fun j => S.getD j fall) len op late w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run late w) door op)
    (lo : 13≤op) (hi : op<408) (node : nodeOf op=some i) (code : get i=some (.maskB a))
    (slot : WordSlot i) (inputSlot : WordSlot a) (hr : 1<width)
    (flags : ∀ j, (longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<width) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (stable : ∀ u v,w0++door0::(between++w)=u++v →
      ∀ j, Layout B (run initial u) j=Layout B base j)
    (T : PrimTable width) (bank : Bank) (sem : PrimSem T bank) (regs : List Value) :
    ∃ (before : List (Fin n)) (launch : Fin n) (after : List (Fin n))
      (L : (significantSites hp base (fun j => S.getD j fall) len).length=width),
      w=before++launch::after ∧
      let y := step (run late before) launch
      let sites := digitSite hp base (fun j => S.getD j fall) len width L
      wordAt y sites a inputSlot=argW width (readArgs regs [a]) 0 →
      evalInstr (toInstr T bank (.maskB a)) regs =
        .word (wordAt (step (run late w) door) (digitSite hp base (fun j => S.getD j fall) len width L) i slot) := by
  let addr := fun j => S.getD j fall
  obtain ⟨pre,turn,ret,W,outward,E,backward⟩ := BStarAcquireAckAncestry.found_split_turn hp F
  have replay : run late w=run (step (run late pre) turn) ret := by
    rw [W,BStarResetSchedule.run_append]
    rfl
  have old : Current hp base addr len (run late pre) (.busy op (.out len)) := by
    obtain ⟨u,w',e,O,_,_,_,U⟩ := outward
    rw [O,BStarResetSchedule.run_append]
    exact (BStarAcquireHistoryReturn.busy_end hp U : Current hp base addr len
      (run (step (run late u) e) w') (.busy op (.out len)))
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
  have actualSplit : w=before++launch::(after++turn::ret) := by
    rw [W,P,List.append_assoc]
    rfl
  refine ⟨before,launch,after++turn::ret,L,actualSplit,?_⟩
  dsimp only
  intro inputAgree
  let input : Word width := readWord (fun j => (step (run late before) launch (site j)).long)
    a inputSlot
  have Bk : BusyOnly hp base addr len op (run late pre) (.out len) (turn::ret) (.back 0) :=
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
      num (step (run late w) door (site j)).long i=(maskStep (input j) (positionAt width j.val)).val := by
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
    have now : ∃ j,oldH6 B d.old j=true := by
      obtain ⟨j,E0⟩ := hh
      exact ⟨j,(congrArg Prod.fst (sameOld j)).symm.trans E0⟩
    have ord := fun k => ord_same hp hh now sameOld k
    have ordJ : oldOrdinal B d.old now d.mark=j.val := by rw [←ord,←siteEq]; exact ORD j
    let middle := between++before++[launch]
    have launchEq : run (step (run initial w0) door0) middle=step (run late before) launch := by
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
    have fNow (k : Fin n) : (longGeometry B (d.old k)).inside=decide (oldOrdinal B d.old now k<width) ∧
        (longGeometry B (d.old k)).last=decide (oldOrdinal B d.old now k+1=width) := by
      have E := (flags k)
      rw [ord k] at E
      exact ⟨(congrArg (fun z : Bool × Bool × Bool => z.2.1) (sameOld k)).symm.trans E.1,
        (congrArg (fun z : Bool × Bool × Bool => z.2.2) (sameOld k)).symm.trans E.2⟩
    have shortNow (E : oldH6 B d.old (rightNeighbor d.mark)=true) :
        width≤oldOrdinal B d.old now d.mark+1 := by
      rw [←ord]
      exact notShort _ ((congrArg Prod.fst (sameOld _)).trans E)
    have geo := BStarNativeOffsetDigitAt.later_digit_at hp chart sep F0 H0 middle after aligned same d mem now width hr
      (by rw [ordJ]; exact j.isLt) fl notShort fNow shortNow
    rw [ordJ] at geo
    have digit := mask_row (geom hp d) (byte d) i a width j.val d.offer inputSlot
      (BStarLongSector.constants_of_chart _ _ _ geo)
    have inputEq : nib (byte d) a inputSlot=input j := by
      apply Fin.ext
      change num (byte d) a=num (step (run late before) launch (site j)).long a
      rw [siteEq]
      exact congrArg BitVec.toNat (R ⟨j.val,q⟩ a).1
    rw [inputEq] at digit
    have buf := (R ⟨j.val,q⟩ i).2
    change (numeric i).read ((physicalDigit (geom hp d) (byte d) i (.maskB a) d.offer).1.apply (byte d))=
      (numeric i).read ((run (step (run late before) launch) after) d.mark).long at buf
    rw [digit] at buf
    have Q : run late pre=run (step (run late before) launch) after := by
      rw [P,BStarResetSchedule.run_append]; rfl
    have retain := busy_past hp Bk sep (Nat.le_of_lt less) d.mark pos less i
    have W' : run late w=run (run late pre) (turn::ret) := by rw [W,BStarResetSchedule.run_append]
    have nowHit := H.1
    have nf : ¬anyTag.F (atCursor (run late w) (d.mark,1)) := by
      rw [←pos]
      exact BStarOwnerControlHistory.pointed_backward_no_forward _ len 0 nowHit.2.1
        d.index (Nat.le_of_lt less)
    have retainDoor := step_no_forward hp (run late w) door d.mark i (sep door) nf
    rw [siteEq]
    unfold num
    rw [retainDoor,W',retain,Q,←buf]
    exact num_write_of_lt slot (maskStep (input j) _).isLt _
  have Word : wordAt (step (run late w) door) site i slot =
      val (fun j : Fin width => maskStep (input j) (positionAt width j.val)) := by
    unfold wordAt val
    apply valJ_congr
    intro j hj _
    exact full ⟨j,hj⟩
  rw [Word,mask_word (by omega)]
  change Value.word (den T.maskB (readArgs regs [a]))=_
  rw [sem.maskB]
  have inputValue : val input = argW width (readArgs regs [a]) 0 := inputAgree
  rw [inputValue]

end L4.BStarNativeMaskActual
