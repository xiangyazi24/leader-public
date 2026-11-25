import Leader.L4.Height.FreshFirstAcquire
import Leader.L4.Height.AdmissionActualFirst
import Leader.L4.BStarAdmissionTraceBound
import Leader.L4.BStarPaceChronology

namespace L4.Height.FreshAdmissionStart

open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarH6WordChart BStarAcquireAnchors
open BStarGeneratedOwner BStarResetChartTouch BStarSeparatingRail BStarSteeredLikelihood
open BStarLongDoor BStarLongToken BStarLongCommand BStarTrace BStarLongWork BStarLongClaims
open BStarClearanceSource BStarOwnerLaunchOrigin BStarClearanceRaceMark
open BStarResetControllerEntry BStarAdmitIncidentGeometry
open FreshFirstAcquire Classical

noncomputable section

variable {s n : Nat}
local notation "hp" => (show 0<2 by decide)
local notation "B" => rows s

private theorem run_join (y : Raw s n) (a w : Word n) :
    rawRun y (a++w)=rawRun (rawRun y a) w :=
  BStarResetSchedule.run_append (rawNext s) y a w

private theorem run_snoc (y : Raw s n) (a : Word n) (e : Fin n) :
    rawRun y (a++[e])=rawNext s (rawRun y a) e :=
  run_join y a [e]

private theorem snapshot_pc {y : Raw s n} {i : Fin n} {op : Nat}
    (within : op<512)
    (snap : snapshot (y i).long=((.empty,1),BitVec.ofNat 9 op)) : PC y i=op := by
  have H := congrArg (fun p : (Token×BitVec 2)×BitVec 9=>p.2.toNat) snap
  change PC y i=(BitVec.ofNat 9 op).toNat at H
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt within] using H

private theorem scope_exit (y : Raw s n) (i : Fin n) (op : Nat) (w : Word n)
    (old : PC y i=op) (new : PC (rawRun y w) i≠op) :
    ∃ a e b,w=a++e::b ∧ PC (rawRun y a) i=op ∧ PC (rawNext s (rawRun y a) e) i≠op := by
  induction w generalizing y with
  | nil => exact (new old).elim
  | cons e w ih =>
    by_cases stop : PC (rawNext s y e) i=op
    · obtain ⟨a,f,b,W,L,R⟩ := ih (rawNext s y e) stop new
      exact ⟨e::a,f,b,congrArg (List.cons e) W,L,R⟩
    · exact ⟨[],e,w,rfl,old,stop⟩

variable {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 B g.base

private theorem return_event {y : Raw s n} {o : Owners h}
    {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (P : Production g) (C : Chart hp g.base g.hh o S L fall) (qy : g.Q y)
    (op : Nat) (defined : initial op (y (S.getD 0 fall).1).long≠none) (e : Fin n)
    {a b : Mode}
    (cur : Current hp g.base (fun k=>S.getD k fall) L y a)
    (mark : Event hp (fun k=>S.getD k fall) L y e a b)
    (post : Current hp g.base (fun k=>S.getD k fall) L (rawNext s y e) b)
    (old : PC y (S.getD 0 fall).1=op)
    (exit : PC (rawNext s y e) (S.getD 0 fall).1≠op) :
    a=.busy op (.back 0) ∧ b=.idle := by
  cases mark with
  | idle_hold away =>
    rcases BStarOwnerControlHistory.idle_launch_or_hold hp C (g.fiber y qy) cur.2
      (separation P) e cur.1 with A|A|A
    · have same := congrArg (fun c : BitVec 2×BitVec 9=>c.2.toNat) A.2.2.1
      exact (exit (same.trans old)).elim
    · exact (away A.1).elim
    · exact (away A.1).elim
  | bad_issue _ bad =>
    change initial (PC y (S.getD 0 fall).1) (y (S.getD 0 fall).1).long=none at bad
    rw [old] at bad
    exact (defined bad).elim
  | launch _ _ => exact (exit (post.1.2.2.2.trans old)).elim
  | transit _ _ _ _ _ => exact (exit (post.1.2.2.2.trans (cur.1.2.2.2.symm.trans old))).elim
  | arrived_hold _ _ => exact (exit (post.1.2.2.2.trans (cur.1.2.2.2.symm.trans old))).elim
  | consume k _ _ => exact ⟨congrArg (fun j=>Mode.busy j (.back 0)) (cur.1.2.2.2.symm.trans old),rfl⟩

theorem return_state_of_change {z : Raw s n} {o : Owners h}
    {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (P : Production g) (C : Chart hp g.base g.hh o S L fall) (qz : g.Q z)
    (idle : Current hp g.base (fun k=>S.getD k fall) L z .idle)
    (w : Word n) (e : Fin n) (op : Nat)
    (defined : initial op (rawRun z w (S.getD 0 fall).1).long≠none)
    (old : PC (rawRun z w) (S.getD 0 fall).1=op)
    (exit : PC (rawNext s (rawRun z w) e) (S.getD 0 fall).1≠op) :
    GeneratedOwner hp g.base (fun k=>S.getD k fall) L z .idle w (.busy op (.back 0)) ∧
      Event hp (fun k=>S.getD k fall) L (rawRun z w) e (.busy op (.back 0)) .idle ∧
      Current hp g.base (fun k=>S.getD k fall) L (rawNext s (rawRun z w) e) .idle := by
  obtain ⟨a,G,q,cur⟩ := generated_word hp C g.Q g.fiber (fun z q e=>g.closed z e q)
    (separation P) w .idle qz idle
  obtain ⟨b,M,post⟩ := current_step hp C g.Q g.fiber (fun z q e=>g.closed z e q)
    (separation P) q e a cur
  obtain ⟨A,D⟩ := return_event g P C q op defined e cur M post old exit
  subst a
  subst b
  exact ⟨G,M,post⟩

theorem return_of_change {z : Raw s n} {o : Owners h}
    {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (P : Production g) (C : Chart hp g.base g.hh o S L fall) (qz : g.Q z)
    (idle : Current hp g.base (fun k=>S.getD k fall) L z .idle)
    (w : Word n) (e : Fin n) (op : Nat)
    (defined : initial op (rawRun z w (S.getD 0 fall).1).long≠none)
    (old : PC (rawRun z w) (S.getD 0 fall).1=op)
    (exit : PC (rawNext s (rawRun z w) e) (S.getD 0 fall).1≠op) :
    GeneratedOwner hp g.base (fun k=>S.getD k fall) L z .idle w (.busy op (.back 0)) ∧
      Event hp (fun k=>S.getD k fall) L (rawRun z w) e (.busy op (.back 0)) .idle := by
  obtain ⟨G,M,_⟩ := return_state_of_change g P C qz idle w e op defined old exit
  exact ⟨G,M⟩

private theorem band_return {z : Raw s n} {o : Owners h}
    {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (P : Production g) (C : Chart hp g.base g.hh o S L fall) (qz : g.Q z)
    (idle : Current hp g.base (fun k=>S.getD k fall) L z .idle)
    (w : Word n) (e : Fin n) (op : Nat) (band : BStarPaceChronology.paceBand op)
    (old : PC (rawRun z w) (S.getD 0 fall).1=op)
    (exit : PC (rawNext s (rawRun z w) e) (S.getD 0 fall).1≠op) :
    GeneratedOwner hp g.base (fun k=>S.getD k fall) L z .idle w (.busy op (.back 0)) ∧
      Event hp (fun k=>S.getD k fall) L (rawRun z w) e (.busy op (.back 0)) .idle :=
  return_of_change g P C qz idle w e op (fun none => Option.some_ne_none _ ((BStarPaceChronology.paceBand_initial _ band _).symm.trans none)) old exit

private theorem pace_returns {z : Raw s n} {o : Owners h}
    {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (P : Production g) (C : Chart hp g.base g.hh o S L fall)
    (w : Word n) (e : Fin n)
    (G : GeneratedOwner hp g.base (fun k=>S.getD k fall) L z .idle w (.busy 3 (.back 0)))
    (M : Event hp (fun k=>S.getD k fall) L (rawRun z w) e (.busy 3 (.back 0)) .idle) :
    PC (rawNext s (rawRun z w) e) (S.getD 0 fall).1=admit := by
  obtain ⟨a,b,f,W,_,launch,atPC,flight⟩ := from_idle hp G
  have replay : rawRun z w=rawRun (rawNext s (rawRun z a) f) b := by
    rw [W]
    exact run_join z a (f::b)
  have ack := AdmissionTour.pace_from_clean_issue hp C (separation P) f atPC launch flight e (replay ▸ M)
  exact snapshot_pc (by decide) (replay.symm ▸ ack)

private theorem center_client (target : Owners h) : RivalLedger.clients g target 2=target := by
  apply Subtype.ext
  change (target.val+2-2)%(total h : Int)=target.val
  rw [show target.val+2-2=target.val by omega,Int.emod_eq_of_lt target.property.1 target.property.2]

private theorem admit_gate_idx (P : Production g) (target : Owners h)
    {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh target S L fall) :
    ∃ k,k+1<L ∧ S.getD (k+1) fall=(ProductionClients.gate g target 2,1) := by
  let i := ProductionClients.gate g target 2
  have own : commandOwner h i 1=target.val := by
    simpa only [center_client g target] using (ProductionClients.gate_address g P target 2).2
  obtain ⟨d,hd,D⟩ := List.getElem_of_mem (C.cover (i,1) (by rfl) own)
  have idx : S.getD d fall=(i,1) := (List.getElem_eq_getD _).symm.trans D
  have size := C.length
  have hL : d≠L := by
    intro E
    rw [E,C.terminal] at idx
    exact (by decide : (10 : Fin 11)≠1) (congrArg Prod.snd idx)
  cases d with
  | zero =>
    rw [C.root] at idx
    exact ((by decide : (0 : Fin 11)≠1) (congrArg Prod.snd idx)).elim
  | succ k => exact ⟨k,by omega,idx⟩

private theorem age_on_original {i : Fin n} {lead w : Word n}
    (recent : CandidateResidence.newAdmission (rawRun x lead) i w) :
    CandidateResidence.newAdmission x i (lead++w) := by
  obtain ⟨a,e,v,W,issue,latest⟩ := recent
  have split : lead++w=(lead++a)++e::v := by simp only [W,List.append_assoc]
  refine ⟨lead++a,e,v,split,?_,?_⟩
  · change e=RearTrace.predecessor i ∧
      Launch (rawRun x (lead++a) i).long (rawNext s (rawRun x (lead++a)) e i).long ∧
      (ctrlOp.read (rawRun x (lead++a) i).long).toNat=admit
    rw [run_join]
    exact issue
  · intro b f c E bad
    apply latest b f c E
    have R : rawRun x (((lead++a)++[e])++b)=rawRun (rawRun x lead) ((a++[e])++b) := by
      rw [show ((lead++a)++[e])++b=lead++((a++[e])++b) by simp only [List.append_assoc],run_join]
    rwa [R] at bad

private theorem miss_prefix (i : Fin n) (a b : Word n)
    (miss : ¬RawServiceCore.publishes x i (a++b)) : ¬RawServiceCore.publishes x i a := by
  rintro ⟨u,v,E,H⟩
  exact miss ⟨u,v++b,by simp only [E,List.append_assoc,List.cons_append],H⟩

/-- A complete target ADMIT after the own release consumes a positive
reply on the original mask. The credited FIRST is located on the
original emitted tape even if the target was busy at the query. -/
theorem target_admit_returns {target : Owners h} {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (P : Production g) (C : Chart hp g.base g.hh target S L fall)
    (lead u suffix candidates : Word n) (ack : Fin n)
    (T : GeneratedOwner hp g.base (fun k=>S.getD k fall) L (rawRun x lead) .idle u (.busy admit (.back 0)))
    (E : Event hp (fun k=>S.getD k fall) L (rawRun (rawRun x lead) u) ack (.busy admit (.back 0)) .idle)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=(lead++u)++suffix)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 ((lead++u)++suffix)) :
    PC (rawNext s (rawRun (rawRun x lead) u) ack) (RivalLedger.source g target)=acquire := by
  let addr := fun k=>S.getD k fall
  let i := ProductionClients.gate g target 2
  let z := rawRun x lead
  let root := RivalLedger.source g target
  have rootID : (addr 0).1=root := congrArg Prod.fst C.root
  have own : RivalLedger.clients g target 2=target := center_client g target
  obtain ⟨k,K,loc⟩ := admit_gate_idx g P target C
  have O := (ProductionClients.gate_address g P target 2).1
  obtain ⟨launchPre,before,quiet,middle,after,launch,arrival,first,other,seen,_,W,off,firstAt,_,_,_,
    milestones,snap,_⟩ := BStarAdmissionTraceBound.actual_tour_bound hp C (Ready g)
      (fun y q=>g.fiber y q.1) (fun y q e=>ready_next P q e) (fun _ q=>q.2)
      (separation P) (ready_run P lead) i k K loc O u T ack E
  obtain ⟨door,issued,pc,flight,_,_,_,_,cur,read⟩ := milestones
  let localPre := launchPre++launch::(before++arrival::quiet)
  let localPost := middle++other::after
  let b := lead++localPre
  let a := lead++launchPre
  have split : u=localPre++first::localPost := by
    simp only [localPre,localPost,W,List.append_assoc,List.cons_append]
  obtain ⟨mode,priorTape,_⟩ := BStarGeneratedTapeCuts.split hp localPre (first::localPost) (split ▸ T)
  have modeID := L4.Height.current_mode_unique hp mode (.busy admit (.out (k+1)))
    (BStarGeneratedTapeCuts.at_end hp priorTape) cur
  have priorTape' : GeneratedOwner hp g.base addr L z .idle localPre (.busy admit (.out (k+1))) :=
    modeID ▸ priorTape
  have age : CandidateResidence.newAdmission x root b := by
    rcases CandidateResidence.admission_age priorTape' with ⟨age,_⟩|⟨_,d,mode,_⟩
    · rw [rootID] at age
      exact age_on_original age
    · cases mode
  have emitted_cut : emit (chooseBy (RivalLedger.mask g target)) [] candidates=b++first::(localPost++suffix) := by
    simp only [tape,split,b,List.append_assoc,List.cons_append]
  obtain ⟨_,cand,_,_,_,choose,_⟩ := BStarEmittedCut.marked_cut _ [] candidates b (localPost++suffix) first emitted_cut
  have firstEq : first=incident i seen := by
    cases seen with
    | left => exact firstAt
    | right =>
      change rightNeighbor first=i at firstAt
      exact (RearTrace.predecessor_right first).symm.trans (congrArg RearTrace.predecessor firstAt)
  have choose' : chooseBy (RivalLedger.mask g target) b cand=incident i seen := by
    simpa only [List.nil_append,firstEq] using choose
  have atFirst : rawRun z localPre=rawRun x b := (run_join x lead localPre).symm
  change Current hp g.base addr L (rawRun z localPre) (.busy admit (.out (k+1))) at cur
  change bind (longGeometry B (rawRun z localPre i)) 1 (atSite (rawRun z localPre i).long 1)=
    .forward (AdmissionTour.atGate 1) at read
  rw [atFirst] at cur read
  have atLaunch : rawRun z launchPre=rawRun x a := (run_join x lead launchPre).symm
  change Launch (rawRun z launchPre (addr 0).1).long
    (rawNext s (rawRun z launchPre) launch (addr 0).1).long at issued
  change (ctrlOp.read (rawRun z launchPre (addr 0).1).long).toNat=admit at pc
  change BusyOnly hp g.base addr L admit (rawNext s (rawRun z launchPre) launch) (.out 0) before (.out k) at flight
  rw [atLaunch] at issued pc flight
  have actualIssue : ProductionClients.issue g target 2 a launch := by
    change ProductionAdmissions.issues hp x (RivalLedger.source g (RivalLedger.clients g target 2)) a launch
    rw [own]
    change ProductionAdmissions.issues hp x root a launch
    rw [←rootID]
    exact ⟨door,issued,pc⟩
  have offsite : ∀ e∈quiet,∀ side,e≠incident i side := by
    intro e mem side eq
    apply off e mem side
    rw [eq]
    cases side with
    | left => rfl
    | right => exact RearTrace.right_predecessor i
  have cut : b=(a++[launch])++(before++arrival::quiet) := by
    simp only [b,a,localPre,List.append_assoc,List.singleton_append]
  have noPublish : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 b :=
    miss_prefix _ b (first::(localPost++suffix))
      (by simpa only [split,b,List.append_assoc,List.cons_append] using miss)
  have live : RivalLedger.live g target 2 b := by
    refine ⟨⟨trivial,noPublish⟩,?_,⟨target,S,L,fall,k+1,AdmissionTour.atGate 1,C,loc,cur,read,rfl,rfl,rfl⟩⟩
    change CandidateResidence.newAdmission x (RivalLedger.source g (RivalLedger.clients g target 2)) b
    rw [own]
    exact age
  have funded : RivalLedger.funded g target 2 b := by
    have ready : RivalLedger.live g target 2 ((a++[launch])++(before++arrival::quiet)) := cut ▸ live
    have chart : Chart hp g.base g.hh (RivalLedger.clients g target 2) S L fall := own.symm ▸ C
    exact cut.symm ▸ RivalLedger.funded_at_arrival g target 2 chart rfl a before quiet launch arrival
      (k+1) k loc actualIssue flight (by omega) (by omega) offsite ready
  obtain ⟨_,_,chosen⟩ := AdmissionActualFirst.actual_hit g target P.large (fun _ _=>True) 2 b cand seen
    choose' funded.1 funded.2
  have chooseLeft : incident i seen=incident i .left := by
    have ownVal : (AdmissionPolicyCore.client h g.hh target 2).val=target.val :=
      congrArg Subtype.val own
    have gateID : AdmissionPolicyCore.gate g target 2=i := rfl
    rw [gateID, if_pos ownVal] at chosen
    exact chosen
  have side : seen=.left := (incident_gate_injective h g.hh i i false false O O seen .left chooseLeft).2.2
  have A : snapshot (rawNext s (rawRun z u) ack (addr 0).1).long =
      ((.empty,1),BitVec.ofNat 9 (if seen==.left then acquire else 412)) := snap
  rw [side] at A
  have L : PC (rawNext s (rawRun z u) ack) (addr 0).1=acquire :=
    snapshot_pc (by decide) A
  exact (congrArg (fun j : Fin n => PC (rawNext s (rawRun z u) ack) j=acquire) rootID).mp L

/-- An unpublished emitted interval between two actual own RREL
receipts necessarily visits PC5 before the second receipt. -/
theorem visits_acquire_between_releases (P : Production g) (target : Owners h)
    (a w after candidates : Word n) (r nextR : Fin n)
    (release : accepted g target a r)
    (nextRelease : accepted g target ((a++[r])++w) nextR)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=(((a++[r])++w)++after))
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 (((a++[r])++w)++after)) :
    ∃ u v,w=u++v ∧ PC (rawRun (rawRun x (a++[r])) u) (RivalLedger.source g target)=acquire := by
  let lead := a++[r]
  let z := rawRun x lead
  let root := RivalLedger.source g target
  obtain ⟨S,L,fall,C,atRelease,_⟩ := ReleaseGrantReceipt.released_chart P target a r release
  let addr := fun k=>S.getD k fall
  have rootID : (addr 0).1=root := congrArg Prod.fst C.root
  have idle : Current hp g.base addr L z .idle := by
    change Current hp g.base addr L (rawRun x (a++[r])) .idle
    rw [run_snoc]
    exact atRelease
  have q := (ready_run P lead).1
  have starts : PC z root=3 := by
    change PC (rawRun x (a++[r])) root=3
    rw [run_snoc]
    exact release.2.2
  have ends : PC (rawRun z w) root=2 := by
    change PC (rawRun (rawRun x lead) w) root=2
    rw [←run_join]
    exact nextRelease.2.1
  obtain ⟨pre,paceAck,rest,W,oldP,exitP⟩ := scope_exit z root 3 w starts
    (by rw [ends]; decide)
  obtain ⟨GP,EP⟩ := band_return g P C q idle pre paceAck 3 (.inl rfl)
    ((congrArg (fun i : Fin n => PC (rawRun z pre) i=3) rootID).mpr oldP)
    ((congrArg (fun i : Fin n => PC (rawNext s (rawRun z pre) paceAck) i≠3) rootID).mpr exitP)
  have at4 : PC (rawNext s (rawRun z pre) paceAck) root=admit := by
    exact (congrArg (fun i : Fin n => PC (rawNext s (rawRun z pre) paceAck) i=admit) rootID).mp
      (pace_returns g P C pre paceAck GP EP)
  have endpoint : rawRun z w=rawRun (rawNext s (rawRun z pre) paceAck) rest := by
    rw [W]
    exact run_join z pre (paceAck::rest)
  obtain ⟨preAdmit,admitAck,tail,V,oldA,exitA⟩ :=
    scope_exit (rawNext s (rawRun z pre) paceAck) root admit rest at4
      (by rw [←endpoint,ends]; decide)
  let u := (pre++[paceAck])++preAdmit
  have delim : w=u++admitAck::tail := by
    simp only [W,V,u,List.append_assoc,List.nil_append,List.cons_append]
  have shifted : rawRun z u=rawRun (rawNext s (rawRun z pre) paceAck) preAdmit := by
    change rawRun z ((pre++[paceAck])++preAdmit)=_
    rw [run_join,run_snoc]
  have oldA' : PC (rawRun z u) root=admit := (congrArg (fun y : Raw s n => PC y root=admit) shifted).mpr oldA
  have exitA' : PC (rawNext s (rawRun z u) admitAck) root≠admit :=
    (congrArg (fun y : Raw s n => PC (rawNext s y admitAck) root≠admit) shifted).mpr exitA
  obtain ⟨GA,EA⟩ := band_return g P C q idle u admitAck admit (.inr (.inl rfl))
    ((congrArg (fun i : Fin n => PC (rawRun z u) i=admit) rootID).mpr oldA')
    ((congrArg (fun i : Fin n => PC (rawNext s (rawRun z u) admitAck) i≠admit) rootID).mpr exitA')
  have tapeID : (lead++w)++after=(lead++u)++(admitAck::(tail++after)) := by
    simp only [delim,List.append_assoc,List.cons_append]
  have positive := target_admit_returns g P C lead u (admitAck::(tail++after)) candidates admitAck GA EA
    (tape.trans tapeID) (tapeID ▸ miss)
  refine ⟨u++[admitAck],tail,?_,?_⟩
  · simpa only [List.append_assoc,List.singleton_append] using delim
  · rwa [run_snoc]

/-- The target interval in the five-release construction visits
ACQUIRE on the same emitted tape that ends at its next own release. -/
theorem visits_acquire_after_five_releases (P : Production g) (target : Owners h)
    (base w after candidates : Word n) (nextR : Fin n)
    (cuts : Releases g target 5 base) (nextRelease : accepted g target (base++w) nextR)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=(base++w)++after)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 ((base++w)++after)) :
    ∃ u v,w=u++v ∧ PC (rawRun (rawRun x base) u) (RivalLedger.source g target)=acquire := by
  obtain ⟨a,r,W,A⟩ := FreshConflicts.target_release g target cuts
  subst base
  exact visits_acquire_between_releases g P target a w after candidates r nextR A nextRelease tape miss

/-- The first genuine target ACQUIRE receipt occurs on the unpublished
post-release interval, with the physical all-win itinerary. -/
theorem first_itinerary_between_releases (P : Production g) (target : Owners h)
    (base w after candidates : Word n) (nextR : Fin n)
    (cuts : Releases g target 5 base) (nextRelease : accepted g target (base++w) nextR)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=(base++w)++after)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 ((base++w)++after)) :
    ∃ u e v S L fall,w=u++e::v ∧ BeforeFirstReturn (rawRun x base) (RivalLedger.source g target) u ∧
      Chart hp g.base g.hh target S L fall ∧
      FreshAcquireReceipt.Itinerary g.base (rawRun x base) S L fall u e := by
  have seen := visits_acquire_after_five_releases g P target base w after candidates nextR cuts nextRelease tape miss
  have ending : PC (rawRun (rawRun x base) w) (RivalLedger.source g target)≠acquire := by
    rw [←run_join]
    have old : PC (rawRun x (base++w)) (RivalLedger.source g target)=2 := nextRelease.2.1
    rw [old]
    decide
  exact itinerary_of_visited_acquire g P target base w after candidates cuts tape miss seen ending

end
end L4.Height.FreshAdmissionStart

