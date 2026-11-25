import Leader.L4.BStarNativeScanInitial
import Leader.L4.BStarNativeScanSem
import Leader.L4.BStarNumericTailCarry
import Leader.L4.Compiler.DigitsWords
import Leader.L4.BStarNativeZeroReceipt

namespace L4.BStarNativeScanHit
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

open BStarNumericTailCarry

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

/-- Genuine Hit entry for SCAN5. The launch, selected turn, ordered
significant visits (including the last one), and reply are recovered
from the one physical tape. Remaining data premises are stated at the
exhibited launch image and first actual digit offer. -/
theorem actual_initialized_hit_scan {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {door : Fin n} {w : List (Fin n)} {width op i a : Nat}
    (F : Found hp base (fun j => S.getD j fall) len op x w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run x w) door op)
    (lo : 13≤op) (hi : op<408) (width_ge : 2≤width)
    (N : nodeOf op=some i) (G : get i=some (.scan5 a))
    (ha : WordSlot a)
    (flags : ∀ j, (longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (positions : ∀ before launch after post ds,
      w=before++launch::(after++post) →
      Aligned hp base (fun j => S.getD j fall) len op
        (step (run x before) launch) 0 after len ds →
      let visits := ds.filter (significant hp base (fun j => S.getD j fall))
      ∀ j : Fin visits.length, ScanPosition (geom hp visits[j.val]) j.val)
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
        evalInstr (toInstr TT bank (.scan5 a)) regs=.word result ∧
        BStarLongCommand.bind (longGeometry B (z (addr 0).1)) 0 (atSite wire 0)=.reply actual ∧
        actual.argument.toNat=result ∧ result<32 ∧
        WellRep wire (headPending wire (op-13) actual (.scan5 a))
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
    launchWord (Nat.le_refl _) qEnd endHere numEnd i (.scan5 a) nodeEnd G
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
    (Nat.le_refl _) qEnd endHere numEnd i (.scan5 a) nodeEnd G first inVisits).1.1
  have init : first.offer.argument.toNat=0 := BStarNativeScanInitial.scan_first_from_launch
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
  have lhs := (relate a ha).trans wa
  have lens : visits.length≥2 := by omega
  have scan := BStarNativeScanSem.scan_value sweepExact ha initial lens (positions before launch after (turn::ret) ds dec align)
  rw [lhs] at scan
  obtain ⟨tailEq,returned⟩ := receipt_of_sweep hp chart sep align back' hit' lo hi
    C v K dst idx sel' i (.scan5 a) N G earlier last lastEq tokens seq sweepExact
  let actual := output (tokens visits.length)
  have retActual : bind (longGeometry B (run x w (addr 0).1)) 0
      (atSite (run x w (addr 0).1).long 0)=.reply actual := by
    rw [←replay2,←replay] at returned
    exact returned
  let result := argW width (readArgs regs [a]) 0 % 32
  have value : arg tokens visits.length=result := scan
  have fit : arg tokens visits.length<32 := by rw [value]; exact Nat.mod_lt _ (by decide)
  have Kind : arithKind (tokens visits.length).opcode.toNat=some .scan := by
    rw [tailEq,hcode]
    exact BStarNumericWidth.kind_exact lo hi N G
  have pval : actual.argument.toNat=result := by
    have width : resultWidth (tokens visits.length).opcode.toNat=5 := by simp [resultWidth,Kind]
    change (arg tokens visits.length % 2^resultWidth (tokens visits.length).opcode.toNat) % 2^34=_
    rw [width,Nat.mod_eq_of_lt fit,Nat.mod_eq_of_lt (by omega),value]
  refine ⟨result,actual,?_,retActual,pval,value ▸ fit,?_⟩
  · change Value.word (den TT.scan5 (readArgs regs [a]))=_
    rw [sem.scan5]
  · intro j hj
    have ks := rs
    by_cases E : j=start (op-13)
    · subst j
      constructor
      · intro b q
        have eq : readReg (regs++[Value.word result]) (start (op-13))=.word result := by
          rw [←rs]; simp [readReg]
        rw [eq] at q
        contradiction
      · have I : start (op-13)=i := by
          have S := scheduled_node (k:=op-13) (by omega)
          rw [show 13+(op-13)=op by omega] at S
          exact Option.some.inj (S.symm.trans N)
        simp [literalCmp,I,G,BStarCmpReceipt.isCmp]
    · have less : j<regs.length := by simp only [List.length_append,List.length_singleton] at hj; omega
      have W := readReg_append_left regs [Value.word result] j less
      have keep : newest (run x w (addr 0).1).long
          (headPending (run x w (addr 0).1).long (op-13) actual (.scan5 a)) j=
          newest (run x w (addr 0).1).long [] j := by
        simp [headPending,nodeResult,newest,show start (op-13)≠j from Ne.symm E]
      dsimp only [addr] at keep
      exact ⟨fun b F => keep.trans ((oldScalar j less).1 b (W.symm ▸ F)),
        fun C => by simpa only [CmpRep,W,keep] using (oldScalar j less).2 C⟩

end L4.BStarNativeScanHit
