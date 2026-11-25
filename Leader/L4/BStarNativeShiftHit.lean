import Leader.L4.BStarNativeShiftInitial
import Leader.L4.BStarNativeShiftHead
import Leader.L4.BStarNativeZeroReceipt

namespace L4.BStarNativeShiftHit
set_option maxHeartbeats 700000
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

open BStarScalarFits BStarNativeShiftHead BStarNumericTailCarry BStarH6Ordinal BStarNativeZeroHead

open BStarNativeAddInitial BStarClearanceSource BStarLongDoor

private theorem split_last {α : Type} (l : List α) (H : l≠[]) :
    ∃ xs x,l=xs++[x] := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    cases l with
    | nil => exact ⟨[],a,rfl⟩
    | cons b l =>
      obtain ⟨xs,x,h⟩ := ih (by simp)
      exact ⟨a::xs,x,congrArg (List.cons a) h⟩

/-- Genuine Hit entry for SHL3. The launch, selected turn, ordered
significant visits (including the last one), and reply are recovered
from the one physical tape. Remaining data premises are stated at the
exhibited launch image and first actual digit offer. -/
theorem actual_initialized_hit_shift {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {door : Fin n} {w : List (Fin n)} {width op i a : Nat}
    (F : Found hp base (fun j => S.getD j fall) len op x w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run x w) door op)
    (lo : 13≤op) (hi : op<408) (width_pos : 0<width)
    (N : nodeOf op=some i) (G : get i=some (.shl3 a))
    (hiSlot : WordSlot i) (ha : WordSlot a)
    (flags : ∀ j, (longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (TT : PrimTable width) (bank : Bank) (sem : PrimSem TT bank) (regs : List Value)
    (rs : regs.length=start (op-13))
    (oldScalar : WellRep ((run x w) (S.getD 0 fall).1).long [] regs literalCmp) :
    let addr := fun j => S.getD j fall
    let z := run x w
    let wire := (z (addr 0).1).long
    ∃ (before : List (Fin n)) (launch : Fin n) (after : List (Fin n)) (first : D) (L : (significantSites hp base addr len).length=width),
      w=before++launch::after ∧
      Departure.Valid hp addr first ∧ significant hp base addr first=true ∧
      first.offer.argument.toNat=0 ∧
      let y := step (run x before) launch
      let site := digitSite hp base addr len width L
      wordAt y site a ha=argW width (readArgs regs [a]) 0 →
      ∃ result actual,
        evalInstr (toInstr TT bank (.shl3 a)) regs=.word result ∧
        result=wordAt (step z door) site i hiSlot ∧
        BStarLongCommand.bind (longGeometry B (z (addr 0).1)) 0 (atSite wire 0)=.reply actual ∧
        PayloadBound (.shl3 a) actual.argument.toNat ∧
        WellRep wire (headPending wire (op-13) actual (.shl3 a))
          (regs++[.word result]) literalCmp := by
  dsimp only
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
  obtain ⟨C,v,sel,kind,dst,K,idx⟩ := BStarStageTerminalHealth.selected_turn hp chart turn
    (sep turn) op old (busy_start hp backward)
  obtain ⟨health,hcode,_⟩ := BStarReplyBack.numeric_selected_from_hit hp chart sep backward
    (replay ▸ H) lo hi C v K dst idx sel
  obtain ⟨⟨qEnd,atEnd,numEnd,opEnd⟩,_⟩ := BStarNumericTerminal.selected_return hp chart sep
    backward C v K dst idx sel health
  obtain ⟨before,after,launch,P,_,realLaunch,atPC,launchWord⟩ := outward
  have replay2 : run x pre=run (step (run x before) launch) after := by
    rw [P,BStarResetSchedule.run_append]
    rfl
  have nodeEnd : nodeOf qEnd.opcode.toNat=some i := by rw [opEnd,hcode,N]
  have endHere := replay2 ▸ atEnd
  obtain ⟨ds,align,tokens,seq,sweepExact,R⟩ := BStarNumericHealthy.successful_sweep hp chart sep
    launchWord (Nat.le_refl _) qEnd endHere numEnd i (.shl3 a) nodeEnd G
  have L := significant_length hp chart align flags notShort
  let visits := ds.filter (significant hp base addr)
  have length : visits.length=width := by
    have eq := congrArg List.length (aligned_sites hp align)
    rw [List.length_map,L] at eq
    exact eq
  obtain ⟨earlier,last,lastEq⟩ := split_last visits (by intro Q; rw [Q] at length; simp at length; omega)
  have hit' := replay2 ▸ (replay ▸ H)
  have back' := replay2 ▸ backward
  have sel' := replay2 ▸ sel
  have oldScalar' := replay2 ▸ (replay ▸ oldScalar)
  have dec : w=before++launch::(after++turn::ret) := by rw [W,P,List.append_assoc]; rfl
  have goodZero : 0<visits.length := by omega
  let first := visits[0]'goodZero
  have reads : tokens 0=first.offer := seq ⟨0,goodZero⟩
  have inVisits : first∈visits := List.getElem_mem goodZero
  obtain ⟨inDs,isSignificant⟩ := List.mem_filter.mp inVisits
  have firstValid := (Aligned.record_facts hp align first inDs).1
  have Fsplit : visits=first::visits.drop 1 := by
    have frontEq := List.drop_eq_getElem_cons goodZero
    simpa using frontEq
  have healthFirst := (BStarNumericHealthy.records_ready hp chart sep align
    (Nat.le_refl _) qEnd endHere numEnd i (.shl3 a) nodeEnd G first inVisits).1.1
  have init : first.offer.argument.toNat=0 := BStarNativeShiftInitial.shift_first_from_launch
    hp chart sep align lo hi N G atPC realLaunch first (visits.drop 1) Fsplit healthFirst
  refine ⟨before,launch,after++turn::ret,first,L,dec,firstValid,isSignificant,init,?_⟩
  intro wa
  have initial : arg tokens 0=0 := by
    unfold arg
    rw [reads]
    exact init
  have relate (reg : Nat) (slot : WordSlot reg) :
      val (readWord (fun j : Fin visits.length => byte visits[j.val]) reg slot)=
        wordAt (step (run x before) launch) (digitSite hp base addr len width L) reg slot := by
    unfold wordAt
    clear wa
    revert L
    cases length
    intro L
    unfold val
    apply valJ_congr
    intro j hj _
    have U := (R ⟨j,hj⟩ reg).1
    obtain ⟨bound,eq⟩ := digitSite_of_visit hp align visits.length L ⟨j,hj⟩
    change num (byte (visits[j]'hj)) reg =
      num (step (run x before) launch (digitSite hp base addr len visits.length L ⟨j,hj⟩)).long reg
    rw [eq]
    exact congrArg BitVec.toNat U
  let fresh := fun j : Fin visits.length =>
    ((physicalDigit (geom hp visits[j.val]) (byte visits[j.val]) i (.shl3 a)
      visits[j.val].offer).1).apply (byte visits[j.val])
  have resultAt (j : Fin width) :
      ∃ h : j.val<visits.length,
        num (fresh ⟨j.val,h⟩) i=
          num (step (run x w) door (digitSite hp base addr len width L j)).long i := by
    obtain ⟨h,eq⟩ := digitSite_of_visit hp align width L j
    let d := visits[j.val]'h
    have M : d∈visits := List.getElem_mem h
    obtain ⟨ins,sig⟩ := List.mem_filter.mp M
    obtain ⟨V,_,less⟩ := Aligned.record_facts hp align d ins
    have one := (Aligned.record_significant hp align d ins sig).1
    have main : d.claim∈orderedCommands (oldPair B d.old d.mark) := by
      rw [←actualOffers_claims _ ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)]
      exact List.mem_map.mpr ⟨_,V.1,rfl⟩
    have pos : addr d.index=(d.mark,1) := by
      have addrEq : addr d.index=address d.mark d.claim.source := V.2.2.1
      rw [addrEq]
      have J : d.claim.source=BStarLongClaims.L 1 := by rw [center_of _ _ main one]; rfl
      rw [J]
      rfl
    have Bk : BusyOnly hp base addr len op (run x pre) (.out len) (turn::ret) (.back 0) :=
      .cons old E backward
    have keep := BStarNumericWordFrame.busy_past hp Bk sep (Nat.le_of_lt less) d.mark pos less i
    have W' : run x w=run (run x pre) (turn::ret) := by
      rw [W,BStarResetSchedule.run_append]
    have now := H.1
    have nf : ¬BStarSeparatorControl.anyTag.F (atCursor (run x w) (d.mark,1)) := by
      rw [←pos]
      exact BStarOwnerControlHistory.pointed_backward_no_forward _ len 0 now.2.1
        d.index (Nat.le_of_lt less)
    have done := BStarNumericWordFrame.step_no_forward hp (run x w) door d.mark i (sep door) nf
    have beforeTurn :
        (numeric i).read (fresh ⟨j.val,h⟩)=(numeric i).read (run x pre d.mark).long := by
      rw [replay2]
      exact (R ⟨j.val,h⟩ i).2
    refine ⟨h,?_⟩
    change digitSite hp base addr len width L j=d.mark at eq
    rw [eq]
    unfold num
    exact congrArg BitVec.toNat (beforeTurn.trans ((W' ▸ keep).symm.trans done.symm))
  have outputWord : val (readWord fresh i hiSlot)=
      wordAt (step (run x w) door) (digitSite hp base addr len width L) i hiSlot := by
    unfold wordAt
    clear wa
    revert resultAt L
    cases length
    intro L _freshSite resultAt hpoint
    unfold val
    apply valJ_congr
    intro j hj _
    exact (hpoint ⟨j,hj⟩).choose_spec
  have out := actual_shift_refines hp chart sep align back' hit' lo hi C v K dst idx sel' i a N G
    earlier last lastEq tokens hiSlot ha flags notShort TT bank sem regs rs oldScalar' initial seq sweepExact
    ((relate a ha).trans wa)
  rw [←replay2,←replay] at out
  exact ⟨val (readWord fresh i hiSlot),out.2.choose,out.1,outputWord,out.2.choose_spec⟩

end L4.BStarNativeShiftHit
