import Leader.L4.BStarStageTerminalHealth
import Leader.L4.Height.FreshInjectEntry
import Leader.L4.Height.FreshWonAttempt
import Leader.L4.Height.FreshOrderedPrefix
import Leader.L4.Height.FreshStripGeometry

namespace L4.Height.FreshOrderedAttempt
open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles FreshFirstAcquire
open BStarResetMarkAdapter BStarOwnerLaunchOrigin BStarLongWork BStarResetRailRing
open BStarLongEvents BStarLongTransport BStarLongClaims BStarLongCommandData
open BStarLongDoor BStarH6WordChart BStarResetChartTouch BStarGeneratedOwner BStarAcquireAnchors
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarSteeredLikelihood BStarLongToken
open BStarCopyFenceSaturation BStarCopyMarkedLedger FreshOrderedPrefix
open BStarCopyRightStrip (addr)
open BStarCopyLeftDeposit (headFirst)
open BStarCopyLeftPending (pending)
open BStarCopyRightMark (stripWord)
open BStarCopyRightMixed (planOf)

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "hp" => (show 0<2 by decide)
local notation "h" => oldH6 (rows s) g.base
local notation "r" => radWidth s

/-- At the last outward INJECT position, the two fully released FIFO streams
represent the selected LOADs, in order, in the original physical lanes. -/
def Images (before fin : Raw s n) (left dest other : Fin n) (ls rs top : Nat) : Prop :=
  let ld := fun i=>frozenDigit (BStarCopyLeftMark.sample before left ls i)
  let rd := fun i=>frozenDigit (BStarCopyRightDeposit.lanes before (addr other (rs+i)) .rs)
  (∃ t : Ledger Nat, ∃ q : Nat→Option Nat,
    t.release.pending=[] ∧ OrderedPrefix (pending id r) t (headFirst ls q) ∧
    BStarCopyLeftRetained.RetainedMatches ld fin (addr left ls) r t ∧
    BStarCopyLeftMark.UpstreamMatches ld fin left ls q) ∧
  (∃ t : Ledger Nat, ∃ q : Nat→Option Nat,
    t.release.pending=[] ∧ OrderedPrefix (planOf (fun j=>j-rs) rs top) t (stripWord top q) ∧
    BStarCopyRightRetained.RetainedMatches rd fin dest r t ∧
    BStarCopyRightMark.MobileMatches rd fin other rs top q)

/-- A finite physical prefix through the end of INJECT, including
both FIFO streams and the authentic subsequent ISSUE11 receipt. -/
def ReachedInject (o : Owners h) (base w : Word n) : Prop :=
    ∃ u acq lead door out turn tail S len fall,
      w=u++acq::(lead++door::(out++turn::tail)) ∧
      let y := rawNext s (rawRun x (base++u)) acq
      let front := lead++door::out
      let slot := fun j=>S.getD j fall
      ∃ C : Chart hp g.base g.hh o S len fall,
        Current hp g.base slot len (rawRun x base) .idle ∧ PC y (slot 0).1=6 ∧ GeneratedOwner hp g.base slot len y .idle front (.busy 10 (.out len)) ∧
        Event hp slot len (rawRun y front) turn (.busy 10 (.out len)) (.busy 10 (.back len)) ∧
        BStarCopyFenceCuts.LiveAt hp C y front ∧
        project slot (rawRun y front) len=.forward injectUnit ∧
        (∃ back ack rest,tail=back++ack::rest ∧
          BusyOnly hp g.base slot len 10 (rawNext s (rawRun y front) turn) (.back len) back (.back 0) ∧
          BStarNativeReceiptTape.Hit hp g.base slot len (rawRun (rawNext s (rawRun y front) turn) back) ack 10 ∧
          Current hp g.base slot len (rawNext s (rawRun (rawNext s (rawRun y front) turn) back) ack) .idle ∧
          BStarCopyFenceCuts.LiveAt hp C y (front++turn::back)) ∧
        ∃ ls a rs top,addr (slot 0).1 ls=(slot len).1 ∧
          Images (rawRun y (lead++[door])) (rawRun y front) (slot 0).1 (slot len).1 a ls rs top

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2400000 in
theorem on_fresh_attempt (P : Production g) (o : Owners h) (base w after candidates : Word n)
    (nextR : Fin n) (cuts : Releases g o 5 base) (nextRelease : accepted g o (base++w) nextR)
    (tape : emit (chooseBy (RivalLedger.mask g o)) [] candidates=(base++w)++after)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh o 1).1 ((base++w)++after)) :
    ReachedInject g o base w := by
  obtain ⟨u,acq,v,_,_,_,W,_,_,snap⟩ :=
    FreshWonAttempt.to_issue_six g P o base w after candidates nextR cuts nextRelease tape miss
  obtain ⟨a,first,B,paid⟩ := FreshConflicts.target_release g o cuts
  obtain ⟨S,len,fall,C,released,_⟩ := ReleaseGrantReceipt.released_chart P o a first paid
  let slot := fun j=>S.getD j fall
  let root := (slot 0).1
  let z := rawNext s (rawRun x a) first
  let y := rawNext s (rawRun x (base++u)) acq
  have rootID : root=RivalLedger.source g o := congrArg Prod.fst C.root
  have initial : rawRun x base=z := by
    rw [B]
    exact BStarResetSchedule.run_append (rawNext s) x a [first]
  have src : rawRun z (u++[acq])=y := by
    have join (state : Raw s n) (a b : Word n) :
        rawRun state (a++b)=rawRun (rawRun state a) b :=
      BStarResetSchedule.run_append (rawNext s) state a b
    rw [←initial,join]
    change rawNext s (rawRun (rawRun x base) u) acq=rawNext s (rawRun x (base++u)) acq
    rw [join]
  have eq : BStarResetControllerEntry.snapshot (y root).long=((.empty,1),BitVec.ofNat 9 6) := by
    rw [rootID]; exact snap
  have phase : (BStarLongDoor.ctrlPhase.read (y root).long).toNat=1 :=
    congrArg (fun t : (Token×BitVec 2)×BitVec 9=>t.1.2.toNat) eq
  have pc : PC y root=6 := congrArg (fun t : (Token×BitVec 2)×BitVec 9=>t.2.toNat) eq
  have q := g.closed _ first (ready_run P a).1
  obtain ⟨m,_,_,cur⟩ := generated_word hp C g.Q g.fiber (fun p good j=>g.closed p j good)
    (separation P) (u++[acq]) .idle q released
  change Current hp g.base slot len (rawRun z (u++[acq])) m at cur
  rw [src] at cur
  have idle : Current hp g.base slot len y .idle := by
    cases m with
    | idle => exact cur
    | busy op cursor => exact ((by decide : (2:Nat)≠1) (cur.1.2.2.1.symm.trans phase)).elim
  have rawEnd : rawRun x (base++w)=rawRun y v := by
    have cut : base++w=(base++u)++acq::v := by rw [W,List.append_assoc]
    rw [cut]
    exact BStarResetSchedule.run_append (rawNext s) x (base++u) (acq::v)
  have reset : PC (rawRun y v) root=2 := by
    rw [←rawEnd,rootID]; exact nextRelease.2.1
  have entry := FreshInjectEntry.front_before_reset P o a first paid C (u++[acq]) v
  change Current hp g.base slot len z .idle → Current hp g.base slot len (rawRun z (u++[acq])) .idle → _ at entry
  rw [src] at entry
  obtain ⟨front,turn,tail,V,G,M,live,returns⟩ := entry released idle pc reset
  obtain ⟨ls,a',rs,top,L,join,size,flags,R,D,head,own,count,leftCover,rightCover⟩ :=
    FreshStripGeometry.strips_cover P C
  obtain ⟨lead,door,out,F,unitAt,image⟩ := ordered_from_issue hp C (separation P) G live pc
    root ls L rfl size flags (slot len).1 a' rs top R D head own count leftCover rightCover
  obtain ⟨back,ack,rest,suffix,flight,consume,afterAck,fullLive⟩ := returns
  have terminal : onTerminal hp (rawRun y front) turn slot len := by
    obtain ⟨cl,f,selected,kind,dest,port,loc⟩ := BStarStageTerminalHealth.selected_turn
      hp C turn (separation P turn) 10 (BStarGeneratedTapeCuts.at_end hp G)
        (busy_start hp flight)
    have mem : cl∈orderedCommands (oldPair (rows s) (rawRun y front) turn) := by
      rw [←actualOffers_claims _ (((rawRun y front) turn).long,
        ((rawRun y front) (rightNeighbor turn)).long)]
      exact List.mem_map.mpr ⟨(cl,.advance f),selected,rfl⟩
    exact ⟨cl,mem,kind,dest,port,loc⟩
  have ackUnit := FreshOrderedPrefix.unit_turn hp (S:=S) (fall:=fall) turn (separation P turn)
    terminal unitAt
  have hit := FreshCopyReceipt.ordinary hp C (separation P) 10 (by decide) (by decide)
    flight ackUnit ack consume
  subst front
  refine ⟨u,acq,lead,door,out,turn,tail,S,len,fall,?_,C,initial.symm ▸ released,pc,G,M,live,unitAt,⟨back,ack,rest,suffix,flight,hit,afterAck,fullLive⟩,ls,a',rs,top,join,image⟩
  simp only [W,V,List.append_assoc,List.cons_append]

/-- The stopped histories quantified by FreshCyclePublishes yield both
packed streams on the literal emitted word if publication is still absent. -/
theorem on_stopped_history (P : Production g) (i : Header h) (base w : Word n)
    (z : History s n) (actual : Consistent x (policy g i) i.val z)
    (cuts : Releases g (ProductionClients.serviceOwner g i) 5 base) (nextR : Fin n)
    (last : accepted g (ProductionClients.serviceOwner g i) (base++w) nextR)
    (suffix : z.emitted=(base++w)++[nextR]) (miss : ¬z.published) :
    ReachedInject g (ProductionClients.serviceOwner g i) base w := by
  let target := ProductionClients.serviceOwner g i
  have tape : emit (chooseBy (RivalLedger.mask g target)) [] z.candidates=(base++w)++[nextR] :=
    actual.1.symm.trans suffix
  have absent : ¬RawServiceCore.publishes x i.val ((base++w)++[nextR]) :=
    fun H=>miss (actual.2.2.mpr (suffix.symm ▸ H))
  apply on_fresh_attempt g P target base w [nextR] z.candidates nextR cuts last tape
  simpa only [target,ProductionClients.service_header] using absent

end L4.Height.FreshOrderedAttempt
