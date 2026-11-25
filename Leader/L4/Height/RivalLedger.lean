import Leader.L4.Height.FreshAttempt
import Leader.L4.Height.ReleaseGrantReceipt
import Leader.L4.Height.CandidatePolicy
import Leader.L4.BStarAdmissionCreditPhysical
import Leader.L4.BStarAdmissionTraceBound
import Leader.L4.BStarEmittedCut

namespace L4.Height.RivalLedger

open AllSizeProtocol PhysicalCustody ProductionCustody BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarAcquireAnchors BStarResetChartTouch BStarGeneratedOwner
open BStarTrace BStarLongWork BStarLongClaims BStarLongToken BStarLongCommand BStarLongDoor
open BStarSeparatingRail BStarOwnerLaunchOrigin BStarSteeredLikelihood BStarParkedSteering
open BStarClearanceRaceMark BStarBitParity BStarResetNoAcquire BStarGrantBirth
open BStarResetMarkAdapter BStarClearanceSource
open Classical

noncomputable section

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 (rows s) g.base
local notation "hp" => (show 0<2 by decide)

abbrev clients (target : Owners h) := ProductionClients.client h g.hh target

abbrev live (target : Owners h) := CandidateResidence.live (g:=g) target (fun _ _ => True)

abbrev mask (target : Owners h) := ProductionClients.redirect g target (live g target)

abbrev source (o : Owners h) := (endpoint h g.hh o 0).1

def funded (target : Owners h) (j : Fin 5) (a : Word n) : Prop :=
  live g target j a ∧
    AdmissionMask.credit (ProductionClients.issue g target j)
      (AdmissionMask.hitAt (ProductionClients.gate g target j) (live g target j)) a=true

private theorem rawRun_snoc (y : Raw s n) (a : Word n) (e : Fin n) :
    rawRun y (a++[e])=rawNext s (rawRun y a) e :=
  BStarResetSchedule.run_append (rawNext s) y a [e]

private theorem run_join (z : Raw s n) (u v : Word n) :
    rawRun z (u++v)=rawRun (rawRun z u) v :=
  BStarResetSchedule.run_append (rawNext s) z u v

private theorem decisions_cut (cost : Word n → Fin n → Nat) (a b tail : Word n)
    (f : Fin n) (one : cost (a++b) f=1) :
    1≤decisions cost a (b++f::tail) := by
  induction b generalizing a with
  | nil =>
    change 1≤cost a f+decisions cost (a++[f]) tail
    rw [List.append_nil] at one
    omega
  | cons e b ih =>
    change 1≤cost a e+decisions cost (a++[e]) (b++f::tail)
    have paid := ih (a++[e]) (by simpa only [List.append_assoc,List.singleton_append] using one)
    omega

/-- A funded old FIRST cut on the actual emitted word spends one decision
and its incidence is right-first. The charge also covers a right input. -/
theorem paid_rival_first (P : Production g) (target : Owners h) (j : Fin 5)
    (rival : (clients g target j).val≠target.val)
    (w a v : Word n) (f : Fin n)
    (tape : emit (chooseBy (mask g target)) [] w=a++f::v)
    (armed : funded g target j a)
    (incidentAt : ∃ t,f=incident (ProductionClients.gate g target j) t) :
    f=incident (ProductionClients.gate g target j) .right ∧
    prescribed (mask g target) a f=1 ∧
    1≤decisions (prescribed (mask g target)) [] (emit (chooseBy (mask g target)) [] w) := by
  let i := ProductionClients.gate g target j
  let fresh (b : Word n) (k : Fin n) := ∃ l, k=ProductionClients.gate g target l ∧
    live g target l b ∧ AdmissionMask.credit (ProductionClients.issue g target l)
      (AdmissionMask.hitAt (ProductionClients.gate g target l) (live g target l)) b=true
  let pick (_ : Word n) (k : Fin n) : Side := if commandOwner h k 1=target.val then Side.left else Side.right
  have matchMask : mask g target=redirectTo h g.hh fresh pick := rfl
  have F : fresh a i := ⟨j,rfl,armed.1,armed.2⟩
  have I := ProductionClients.gate_address g P target j
  have side : pick a i=.right := by
    change (if commandOwner h i 1=target.val then Side.left else Side.right)=_
    rw [I.2,if_neg rival]
  obtain ⟨_,e,_,_,_,emitE,_⟩ := BStarEmittedCut.marked_cut (chooseBy (mask g target)) [] w a v f tape
  rw [List.nil_append,matchMask] at emitE
  obtain ⟨t,T⟩ := incidentAt
  have supported := support_of_fresh (redirectTo_isFresh h g.hh fresh pick)
  obtain ⟨u,eq⟩ := BStarGatePolicySplice.incident_preimage (supported a) i I.1 e t (emitE.trans T)
  rw [eq] at emitE
  have output := redirectTo_fresh_hit h g.hh fresh pick a i I.1 F u
  have pay := redirectTo_charges_fresh h g.hh fresh pick a i I.1 F u
  rw [side] at output
  rw [emitE,←matchMask] at pay
  refine ⟨emitE.symm.trans output,pay,?_⟩
  rw [tape]
  exact decisions_cut _ [] a v f (by simpa only [List.nil_append] using pay)

/-- The flight criterion supplies the actual ledger bit at the first
post-arrival incident. A proper-tourSplit incidence before K1 cannot spend it. -/
theorem funded_at_arrival (target : Owners h) (j : Fin 5)
    {o : Owners h} {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S L fall) (owner : o=clients g target j)
    (a u quiet : Word n) (launch arrival : Fin n) (k t : Nat)
    (atGate : S.getD k fall=(ProductionClients.gate g target j,1))
    (I : ProductionClients.issue g target j a launch)
    (flight : BusyOnly hp g.base (fun l=>S.getD l fall) L admit
      (rawNext s (rawRun x a) launch) (.out 0) u (.out t))
    (before : t<k) (within : k≤L)
    (offsite : ∀ e∈quiet,∀ s,e≠incident (ProductionClients.gate g target j) s)
    (eligible : live g target j ((a++[launch])++(u++arrival::quiet))) :
    funded g target j ((a++[launch])++(u++arrival::quiet)) := by
  let root := (S.getD 0 fall).1
  let i := ProductionClients.gate g target j
  let l := live g target j
  let issue := ProductionClients.issue g target j
  let hit := AdmissionMask.hitAt i l
  have rootID : root=source g (clients g target j) :=
    (congrArg Prod.fst C.root).trans (congrArg (source g) owner)
  have actual : BStarAdmissionCreditFlight.genuineIssue hp x root a launch := by
    rw [rootID]
    exact I
  refine ⟨eligible,?_⟩
  exact BStarAdmissionCreditPhysical.bound_credit hp a u quiet launch arrival i atGate actual
    flight before within l
    (fun b H => by
      obtain ⟨_,_,_,_,_,p,_,_,_,F,_,_,_⟩ := H.2.2
      exact ⟨p,F⟩)
    (AdmissionMask.credit issue hit)
    (fun _ => by
      rw [AdmissionMask.credit_snoc]
      simp only [AdmissionMask.advanceCredit, if_pos (show issue a launch from I)])
    (fun b e old no => by
      rw [AdmissionMask.credit_snoc]
      have off : ¬hit b e := no
      by_cases launchNow : issue b e <;> simp [AdmissionMask.advanceCredit,launchNow,off,old])
    offsite

/-- The returned payload, consume mark and post-release launch are all
located on this single physical tape. -/
def PositiveReturn (o : Owners h) (lead u : Word n) (e : Fin n) (f : Payload) : Prop :=
  ∃ (S : List (Pos n)) (L : Nat) (fall : Pos n),
    Chart hp g.base g.hh o S L fall ∧
    GeneratedOwner hp g.base (fun j=>S.getD j fall) L (rawRun x lead) .idle u (.busy admit (.back 0)) ∧
    Event hp (fun j=>S.getD j fall) L (rawRun (rawRun x lead) u) e (.busy admit (.back 0)) .idle ∧
    (let y := rawRun x (lead++u) (source g o)
     bind (longGeometry (rows s) y) 0 (atSite y.long 0)=.reply f) ∧
    f.fault=0 ∧ f.opcode.toNat=admit ∧ f.argument.toNat%2=1

/-- A literal PC5 entrance after own RREL inverts to a genuine new
ADMIT launch and a matching positive receipt. The idle chart supplied
at the release is the origin of the uninterrupted ADMIT flight. -/
theorem positive_at_entry (P : Production g) (o : Owners h)
    (a u : Word n) (r e : Fin n) (release : ProductionCycles.accepted g o a r)
    (off : (ctrlOp.read (rawRun x ((a++[r])++u) (source g o)).long).toNat≠acquire)
    (on : (ctrlOp.read (rawNext s (rawRun x ((a++[r])++u)) e (source g o)).long).toNat=acquire) :
    ∃ f,PositiveReturn g o (a++[r]) u e f := by
  obtain ⟨S,L,fall,C,idle,_⟩ := ReleaseGrantReceipt.released_chart P o a r release
  let addr := fun k=>S.getD k fall
  let root := (addr 0).1
  let lead := a++[r]
  let z := rawRun x lead
  let y := rawRun x (lead++u)
  have rootID : root=source g o := congrArg Prod.fst C.root
  have initial : Current hp g.base addr L z .idle := by
    change Current hp g.base addr L (rawRun x (a++[r])) .idle
    rw [rawRun_snoc]
    exact idle
  have replay : rawRun z u=y := (BStarResetSchedule.run_append (rawNext s) x lead u).symm
  obtain ⟨m,G,q,cur⟩ := generated_word hp C g.Q g.fiber (fun z q f=>g.closed z f q)
    (separation P) u .idle (ready_run P lead).1 initial
  change g.Q (rawRun z u) at q
  change Current hp g.base addr L (rawRun z u) m at cur
  rw [replay] at q cur
  obtain ⟨d,E,after⟩ := current_step hp C g.Q g.fiber (fun z q f=>g.closed z f q)
    (separation P) q e m cur
  have old : (ctrlOp.read (y root).long).toNat≠acquire := by simpa only [y,lead,rootID] using off
  have new : (ctrlOp.read (rawNext s y e root).long).toNat=acquire := by
    simpa only [y,lead,rootID] using on
  have positive : ∃ f, m=.busy admit (.back 0) ∧ d=.idle ∧
      bind (longGeometry (rows s) (y root)) 0 (atSite (y root).long 0)=.reply f ∧
      f.fault=0 ∧ f.opcode.toNat=admit ∧ f.argument.toNat%2=1 := by
    apply Classical.byContradiction
    intro none
    have out := FreshAttempt.denied_source_step hp C (separation P) (g.fiber _ q) e
      cur E after old (fun f M D R F O bit => none ⟨f,M,D,R,F,O,bit⟩)
    exact out new
  obtain ⟨f,M,D,R,F,O,A⟩ := positive
  subst m
  subst d
  exact ⟨f,S,L,fall,C,G,replay.symm ▸ E,by simpa only [y,lead,rootID] using R,F,O,A⟩

private theorem no_acquire_at_owned_of_pc (P : Production g) (o : Owners h)
    (a w : Word n) (r i : Fin n) (j : Fin 3) (release : ProductionCycles.accepted g o a r)
    (own : commandOwner h i (slot j)=o.val)
    (off : (ctrlOp.read (rawRun x ((a++[r])++w) (source g o)).long).toNat≠acquire) :
    NoAcquireAt (rawRun x ((a++[r])++w)) i j := by
  obtain ⟨S,L,fall,C,idle,_⟩ := ReleaseGrantReceipt.released_chart P o a r release
  let addr := fun k=>S.getD k fall
  let lead := a++[r]
  let z := rawRun x lead
  have rootID : (addr 0).1=source g o := congrArg Prod.fst C.root
  have initial : Current hp g.base addr L z .idle := by
    change Current hp g.base addr L (rawRun x (a++[r])) .idle
    rw [rawRun_snoc]
    exact idle
  have here : rawRun z w=rawRun x (lead++w) :=
    (BStarResetSchedule.run_append (rawNext s) x lead w).symm
  obtain ⟨m,G,_,cur⟩ := generated_word hp C g.Q g.fiber (fun z q f=>g.closed z f q)
    (separation P) w .idle (ready_run P lead).1 initial
  have offMode : ∀ z,m≠.busy acquire z := by
    intro j M
    subst m
    have pc : (ctrlOp.read (rawRun z w (addr 0).1).long).toNat=acquire := cur.1.2.2.2
    rw [here,rootID] at pc
    exact off pc
  have no := FreshAttempt.owned_no_acquire hp C (separation P) G cur i j own offMode
  change NoAcquireAt (rawRun z w) i j at no
  rwa [here] at no

private def pc (o : Owners h) (a : Word n) :=
  (ctrlOp.read (rawRun x a (source g o)).long).toNat

private theorem pc_first_entry (o : Owners h) (a u : Word n)
    (off : pc g o a≠acquire) (on : pc g o (a++u)=acquire) :
    ∃ v e w, u=v++e::w ∧ pc g o (a++v)≠acquire ∧ pc g o ((a++v)++[e])=acquire := by
  induction u generalizing a with
  | nil => exact (off (by simpa only [List.append_nil] using on)).elim
  | cons e u ih =>
    by_cases E : pc g o (a++[e])=acquire
    · exact ⟨[],e,u,rfl,by simpa only [List.append_nil] using off,
        by simpa only [List.append_nil] using E⟩
    · obtain ⟨v,f,w,T,H,J⟩ := ih (a++[e]) E
        (by simpa only [List.append_assoc,List.singleton_append] using on)
      exact ⟨e::v,f,w,congrArg (List.cons e) T,
        by simpa only [List.append_assoc,List.singleton_append] using H,
        by simpa only [List.append_assoc,List.singleton_append] using J⟩

private theorem post_release_return_of_acquire (P : Production g) (o : Owners h)
    (a w : Word n) (r : Fin n) (receipt : ProductionCycles.accepted g o a r)
    (active : (ctrlOp.read (rawRun x ((a++[r])++w) (source g o)).long).toNat=acquire) :
    ∃ u accept f v, w=u++accept::v ∧ PositiveReturn g o (a++[r]) u accept f := by
  let lead := a++[r]
  have head : pc g o lead=3 := by
    change (ctrlOp.read (rawRun x (a++[r]) (source g o)).long).toNat=3
    rw [rawRun_snoc]
    exact receipt.2.2
  have off : pc g o lead≠acquire := fun H => (by decide : (3 : Nat)≠acquire) (head.symm.trans H)
  obtain ⟨u,accept,v,T,prior,entered⟩ := pc_first_entry g o lead w off active
  have new : (ctrlOp.read (rawNext s (rawRun x (lead++u)) accept (source g o)).long).toNat=acquire := by
    simpa only [pc,rawRun_snoc] using entered
  obtain ⟨f,result⟩ := positive_at_entry g P o a u r accept receipt prior new
  exact ⟨u,accept,f,v,T,result⟩

/-- If a cleared owned bit is later set, there is a literal positive
ADMIT receipt after this very RREL. It precedes the birth and traces
to a new launch on the same tape. -/
theorem post_release_return_of_nonzero (P : Production g) (o : Owners h)
    (a w : Word n) (r e : Fin n) (j : Fin 3)
    (receipt : ProductionCycles.accepted g o a r)
    (own : commandOwner h e (slot j)=o.val)
    (nonzero : bit (rawRun x ((a++[r])++w)) e j≠0) :
    ∃ u accept f v, w=u++accept::v ∧ PositiveReturn g o (a++[r]) u accept f := by
  let lead := a++[r]
  have zero : bit (rawRun x lead) e j=0 := by
    obtain ⟨_,_,_,_,_,zero⟩ := ReleaseGrantReceipt.released_chart P o a r receipt
    change bit (rawRun x (a++[r])) e j=0
    rw [rawRun_snoc]
    exact zero e j own
  have nonzero' : bit (rawRun (rawRun x lead) w) e j≠0 := by
    rwa [←run_join]
  obtain ⟨before,mark,after,W,_,winner,_⟩ :=
    born_after_zero hp (separation P) (rawRun x lead) e j w zero nonzero'
  have winner' : WonAt hp (rawRun x (lead++before)) mark e j := by
    rwa [run_join]
  have on : pc g o (lead++before)=acquire := by
    apply Classical.byContradiction
    intro off
    exact no_win_at hp _ mark e j (no_acquire_at_owned_of_pc g P o a before r e j receipt own off) winner'
  obtain ⟨u,accept,f,v,T,result⟩ :=
    post_release_return_of_acquire g P o a before r receipt on
  refine ⟨u,accept,f,v++mark::after,?_,result⟩
  simp only [W,T,List.append_assoc,List.cons_append]

/-- The earlier observed FIRST and its credit on the same post-release word. -/
def ReturnFirst (target : Owners h) (j : Fin 5) (lead u : Word n)
    (b : Word n) (mark : Fin n) (t : Side) : Prop :=
  ∃ pre post, u=pre++mark::post ∧ b=lead++pre ∧
    funded g target j b ∧ mark=incident (ProductionClients.gate g target j) t

private theorem busy_append {base z : Raw s n} {addr : Nat → Pos n} {L op : Nat}
    {a b d : Cursor} {u v : Word n}
    (left : BusyOnly hp base addr L op z a u b)
    (right : BusyOnly hp base addr L op (rawRun z u) b v d) :
    BusyOnly hp base addr L op z a (u++v) d := by
  induction left with
  | nil _ => exact right
  | cons I E _ ih => exact .cons I E (ih right)

private theorem busy_no_launch {base z : Raw s n} {addr : Nat → Pos n} {L op : Nat}
    {a b : Cursor} (u v : Word n) (e : Fin n)
    (T : BusyOnly hp base addr L op z a (u++e::v) b) :
    ¬Launch (rawRun z u (addr 0).1).long (rawNext s (rawRun z u) e (addr 0).1).long := by
  induction u generalizing z a with
  | nil =>
    intro A
    exact Mode.noConfusion (BStarGeneratedTapeCuts.idle_of_issue hp (busy_start hp T) A.1)
  | cons f u ih =>
    cases T with
    | cons _ _ tail => exact ih tail

private theorem miss_prefix (i : Fin n) (a w : Word n)
    (miss : ¬RawServiceCore.publishes x i (a++w)) : ¬RawServiceCore.publishes x i a := by
  rintro ⟨pre,post,W,hit⟩
  exact miss ⟨pre,post++w,by simp only [W,List.append_assoc,List.cons_append],hit⟩

private theorem chart_gate (P : Production g) (target : Owners h) (j : Fin 5)
    {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh (clients g target j) S L fall) :
    ∃ k,k+1<L ∧ S.getD (k+1) fall=(ProductionClients.gate g target j,1) := by
  let i := ProductionClients.gate g target j
  have act : BStarAcquireRailCoverage.active (longGeometry (rows s) (g.base i)) 1=true := by
    simp [BStarAcquireRailCoverage.active]
  have own := (ProductionClients.gate_address g P target j).2
  obtain ⟨d,hd,D⟩ := List.getElem_of_mem (C.cover (i,1) act own)
  have idx : S.getD d fall=(i,1) := (List.getElem_eq_getD _).symm.trans D
  have size := C.length
  have H : d≤L := by omega
  have h0 : d≠0 := by
    intro E
    rw [E,C.root] at idx
    have bad : (0 : Fin 11)=1 := congrArg Prod.snd idx
    exact (by decide : (0 : Fin 11)≠1) bad
  have hL : d≠L := by
    intro E
    rw [E,C.terminal] at idx
    have bad : (10 : Fin 11)=1 := congrArg Prod.snd idx
    exact (by decide : (10 : Fin 11)≠1) bad
  cases d with
  | zero => exact (h0 rfl).elim
  | succ k => exact ⟨k,by omega,idx⟩

/-- On an unpublished tape, a completed positive ADMIT identifies
its genuine funded FIRST and returns exactly the bit of that incidence. -/
theorem funded_return_of_miss (P : Production g) (target : Owners h)
    (j : Fin 5) (lead w : Word n) (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 (lead++w))
    {u v : Word n} {e : Fin n} {f : Payload} (W : w=u++e::v)
    (ret : PositiveReturn g (clients g target j) lead u e f) :
    ∃ b mark t,ReturnFirst g target j lead u b mark t ∧
      f.argument.toNat%2=(firstBit t).toNat := by
  obtain ⟨S,L,fall,C,T,E,F,_,_,_⟩ := ret
  let addr := fun k=>S.getD k fall
  let o := clients g target j
  let root := source g o
  let i := ProductionClients.gate g target j
  let z := rawRun x lead
  have rootID : (addr 0).1=root := congrArg Prod.fst C.root
  obtain ⟨k,K,loc⟩ := chart_gate g P target j C
  have O := (ProductionClients.gate_address g P target j).1
  obtain ⟨p,before,gap,middle,after,door,enter,first,other,t,_,U,quiet,firstAt,_,_,_,A,_,returned⟩ :=
    BStarAdmissionTraceBound.actual_tour_bound hp C (Ready g)
      (fun y q => g.fiber y q.1) (fun y q f => ready_next P q f) (fun _ q=>q.2)
      (separation P) (ready_run P lead) i k K loc O u T e E
  obtain ⟨doorID,launch,op,flight,depart,_,arrived,quietBusy,atFirst,rawFirst⟩ := A
  let a := lead++p
  let launched := rawNext s (rawRun x a) door
  let departs := rawRun launched before
  let arrives := rawNext s departs enter
  let b := (a++[door])++(before++enter::gap)
  have launchAt : rawRun z p=rawRun x a := (run_join x lead p).symm
  change Launch (rawRun z p (addr 0).1).long (rawNext s (rawRun z p) door (addr 0).1).long at launch
  change (ctrlOp.read (rawRun z p (addr 0).1).long).toNat=admit at op
  change BusyOnly hp g.base addr L admit (rawNext s (rawRun z p) door) (.out 0) before (.out k) at flight
  change Current hp g.base addr L (rawRun (rawNext s (rawRun z p) door) before) (.busy admit (.out k)) at depart
  rw [launchAt] at launch op flight depart
  have issue : ProductionClients.issue g target j a door := by
    refine ⟨?_,?_,?_⟩
    · exact doorID.trans (congrArg RearTrace.predecessor rootID)
    · exact (congrArg (fun root : Fin n =>
        Launch (rawRun x a root).long (rawNext s (rawRun x a) door root).long) rootID).mp launch
    · exact (congrArg (fun root : Fin n => (ctrlOp.read (rawRun x a root).long).toNat=admit)
        rootID).mp op
  have arriveEq : rawRun z (p++door::(before++[enter]))=arrives := by
    rw [run_join]
    change rawRun (rawNext s (rawRun z p) door) (before++[enter])=_
    rw [rawRun_snoc,launchAt]
  have oldEq : rawRun z (p++door::(before++enter::gap))=rawRun x b := by
    change rawRun (rawRun x lead) _=rawRun x _
    rw [←run_join]
    simp only [b,a,List.append_assoc,List.singleton_append]
  change Current hp g.base addr L (rawRun z (p++door::(before++[enter]))) (.busy admit (.out (k+1))) at arrived
  change BusyOnly hp g.base addr L admit (rawRun z (p++door::(before++[enter]))) (.out (k+1)) gap (.out (k+1)) at quietBusy
  change Current hp g.base addr L (rawRun z (p++door::(before++enter::gap))) (.busy admit (.out (k+1))) at atFirst
  change bind (longGeometry (rows s) (rawRun z (p++door::(before++enter::gap)) i)) 1
    (atSite (rawRun z (p++door::(before++enter::gap)) i).long 1)=.forward (AdmissionTour.atGate 1) at rawFirst
  rw [arriveEq] at arrived quietBusy
  rw [oldEq] at atFirst rawFirst
  have qdep : g.Q departs :=
    ProductionCustody.keep g launched before (g.closed _ door (ready_run P a).1)
  obtain ⟨m,event,haveMode⟩ := current_step hp C g.Q g.fiber (fun y q f=>g.closed y f q)
    (separation P) qdep enter (.busy admit (.out k)) depart
  have same : m=.busy admit (.out (k+1)) := current_mode_unique hp _ _ haveMode arrived
  have onArrival : Event hp addr L departs enter (.busy admit (.out k)) (.busy admit (.out (k+1))) :=
    same ▸ event
  have through : BusyOnly hp g.base addr L admit launched (.out 0) (before++enter::gap) (.out (k+1)) :=
    busy_append flight (.cons depart onArrival quietBusy)
  have age : CandidateResidence.newAdmission x root b := by
    refine ⟨a,door,before++enter::gap,by simp only [b,List.append_assoc,List.singleton_append],issue,?_⟩
    intro c f d cut bad
    have H := busy_no_launch c d f (cut ▸ through)
    have eq : rawRun x ((a++[door])++c)=rawRun launched c := by
      rw [run_join,rawRun_snoc]
    apply H
    simpa only [eq,rootID] using bad.2
  have offsite : ∀ f∈gap,∀ u,f≠incident i u := by
    intro f F u eq
    apply quiet f F u
    rw [eq]
    cases u with
    | left => rfl
    | right => exact RearTrace.right_predecessor i
  have markEq : first=incident i t := by
    cases t with
    | left => exact firstAt
    | right =>
      change rightNeighbor first=i at firstAt
      rw [←firstAt]
      exact (RearTrace.predecessor_right first).symm
  let pre := p++door::(before++enter::gap)
  let post := middle++other::after
  have tourSplit : u=pre++first::post := by
    simp only [pre,post,U,List.append_assoc,List.cons_append]
  have B : b=lead++pre := by
    simp only [b,a,pre,List.append_assoc,List.singleton_append]
  have missB : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 b := by
    apply miss_prefix (x:=x) _ b (first::(post++e::v))
    simpa only [B,W,tourSplit,List.append_assoc,List.cons_append] using miss
  have eligible : live g target j b := by
    refine ⟨⟨trivial,missB⟩,age,?_⟩
    exact ⟨o,S,L,fall,k+1,AdmissionTour.atGate 1,C,loc,atFirst,rawFirst,rfl,rfl,rfl⟩
  have credit : funded g target j b :=
    funded_at_arrival g target j C rfl a before gap door enter (k+1) k loc issue
      flight (by omega) (by omega) offsite eligible
  have eq : rawRun z u=rawRun x (lead++u) := (run_join x lead u).symm
  change (let y := rawRun z u (addr 0).1
    bind (longGeometry (rows s) y) 0 (atSite y.long 0)=.reply (AdmissionTour.packet true (t==.left))) at returned
  rw [eq,rootID] at returned
  have packet : f=AdmissionTour.packet true (t==.left) :=
    Token.reply.inj (F.symm.trans returned)
  refine ⟨b,first,t,⟨pre,post,tourSplit,B,credit,markEq⟩,?_⟩
  rw [packet]
  cases t <;> decide

/-- A surviving rival bit would yield a concrete charged FIRST on the
unpublished tape, with the actual return and its own launch retained. -/
theorem charged_of_post_release_nonzero (P : Production g) (target : Owners h)
    (j : Fin 5) (rival : (clients g target j).val≠target.val)
    (a w candidates : Word n) (r i : Fin n) (port : Fin 3)
    (receipt : ProductionCycles.accepted g (clients g target j) a r)
    (own : commandOwner h i (slot port)=(clients g target j).val)
    (tape : emit (chooseBy (mask g target)) [] candidates=(a++[r])++w)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 ((a++[r])++w))
    (nonzero : bit (rawRun x ((a++[r])++w)) i port≠0) :
    ∃ u e f v b mark t, w=u++e::v ∧ PositiveReturn g (clients g target j) (a++[r]) u e f ∧
      ReturnFirst g target j (a++[r]) u b mark t ∧
      mark=incident (ProductionClients.gate g target j) .right ∧
      prescribed (mask g target) b mark=1 ∧
      1≤decisions (prescribed (mask g target)) [] (emit (chooseBy (mask g target)) [] candidates) := by
  obtain ⟨u,e,f,v,W,ret⟩ :=
    post_release_return_of_nonzero g P _ a w r i port receipt own nonzero
  obtain ⟨b,mark,t,first,_⟩ := funded_return_of_miss g P target j (a++[r]) w miss W ret
  obtain ⟨pre,post,U,B,arm,I⟩ := first
  have split : emit (chooseBy (mask g target)) [] candidates=b++mark::(post++e::v) := by
    simp only [tape,W,U,B,List.append_assoc,List.cons_append]
  obtain ⟨right,pay,count⟩ := paid_rival_first g P target j rival candidates b _ mark split arm ⟨t,I⟩
  exact ⟨u,e,f,v,b,mark,t,W,ret,⟨pre,post,U,B,arm,I⟩,right,pay,count⟩

private theorem no_positive_on_miss (P : Production g) (target : Owners h)
    (j : Fin 5) (rival : (clients g target j).val≠target.val)
    (lead w candidates : Word n)
    (tape : emit (chooseBy (mask g target)) [] candidates=lead++w)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 (lead++w))
    {u v : Word n} {e : Fin n} {f : Payload} (W : w=u++e::v)
    (ret : PositiveReturn g (clients g target j) lead u e f) : False := by
  obtain ⟨b,mark,t,first,parity⟩ := funded_return_of_miss g P target j lead w miss W ret
  obtain ⟨pre,post,U,B,arm,I⟩ := first
  have split : emit (chooseBy (mask g target)) [] candidates=b++mark::(post++e::v) := by
    simp only [tape,W,U,B,List.append_assoc,List.cons_append]
  have right := (paid_rival_first g P target j rival candidates b _ mark split arm ⟨t,I⟩).1
  let gate := ProductionClients.gate g target j
  have O := (ProductionClients.gate_address g P target j).1
  have side : t=.right :=
    (BStarAdmitIncidentGeometry.incident_gate_injective h g.hh gate gate false false O O t .right
      (I.symm.trans right)).2.2
  obtain ⟨_,_,_,_,_,_,_,_,_,positive⟩ := ret
  have zero : f.argument.toNat%2=0 := by simpa only [side, show (firstBit Side.right).toNat = 0 from rfl] using parity
  exact (by decide : (1 : Nat)≠0) (positive.symm.trans zero)

/-- Each rival's own receipt clears its owned bits. On every subsequent
unpublished emitted cut they remain zero, and a new ACQUIRE front
cannot make a same-mark writer request at those incidences. -/
theorem rival_clear_on_miss (P : Production g) (target : Owners h)
    (j : Fin 5) (rival : (clients g target j).val≠target.val)
    (a w candidates : Word n) (r : Fin n)
    (receipt : ProductionCycles.accepted g (clients g target j) a r)
    (tape : emit (chooseBy (mask g target)) [] candidates=(a++[r])++w)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 ((a++[r])++w)) :
    ∀ i port,commandOwner h i (slot port)=(clients g target j).val →
      bit (rawRun x ((a++[r])++w)) i port=0 ∧ NoAcquireAt (rawRun x ((a++[r])++w)) i port := by
  intro i port own
  constructor
  · apply Classical.byContradiction
    intro nonzero
    obtain ⟨u,e,f,v,W,ret⟩ :=
      post_release_return_of_nonzero g P _ a w r i port receipt own nonzero
    exact no_positive_on_miss g P target j rival _ w candidates tape miss W ret
  · apply no_acquire_at_owned_of_pc g P _ a w r i port receipt own
    intro active
    obtain ⟨u,e,f,v,W,ret⟩ := post_release_return_of_acquire g P _ a w r receipt active
    exact no_positive_on_miss g P target j rival _ w candidates tape miss W ret

private theorem left_client (target : Owners h) :
    (clients g target 1).val=(target.val-1)%(total h : Int) := by
  change (target.val+1-2)%(total h : Int)=_
  congr 1
  omega

private theorem right_client (target : Owners h) :
    (clients g target 3).val=(target.val+1)%(total h : Int) := by
  change (target.val+3-2)%(total h : Int)=_
  congr 1
  omega

/-- The four physically competing grants belong to clients 1 and 3.
Both clients differ from the target even when the opposite client is
duplicated elsewhere in the five-entry ledger. -/
theorem conflicting_clients (P : Production g) (target : Owners h) :
    let u := (endpoint h g.hh target 0).1
    let v := (endpoint h g.hh target 1).1
    let z := (endpoint h g.hh target 2).1
    let l := (clients g target 1).val
    let r := (clients g target 3).val
    l≠target.val ∧ r≠target.val ∧
      commandOwner h u 1=l ∧ commandOwner h v 2=l ∧
      commandOwner h v 0=r ∧ commandOwner h z 1=r := by
  dsimp only
  rw [left_client g target,right_client g target]
  let m : Int := total h
  have large : (4 : Int)≤m := by
    dsimp only [m]
    exact_mod_cast P.owners
  have lo := target.property.1
  have hi : target.val<m := target.property.2
  refine ⟨?_,?_,FreshAttempt.conflicting_port_owners h g.hh target⟩
  · change (target.val-1)%m≠target.val
    by_cases P : 0<target.val
    · rw [Int.emod_eq_of_lt (by omega : 0≤target.val-1) (by omega : target.val-1<m)]
      omega
    · have E : (target.val-1)%m=(m-1)%m := by
        rw [show target.val-1=(m-1)-m by omega]
        rw [Int.sub_emod,Int.emod_self,Int.sub_zero,Int.emod_emod]
      rw [E,Int.emod_eq_of_lt (by omega : 0≤m-1) (by omega : m-1<m)]
      omega
  · change (target.val+1)%m≠target.val
    by_cases P : target.val+1<m
    · rw [Int.emod_eq_of_lt (by omega : 0≤target.val+1) P]
      omega
    · rw [show target.val+1=m by omega,Int.emod_self]
      omega

#print axioms paid_rival_first
#print axioms funded_at_arrival
#print axioms positive_at_entry
#print axioms post_release_return_of_nonzero
#print axioms charged_of_post_release_nonzero
#print axioms funded_return_of_miss
#print axioms rival_clear_on_miss
#print axioms conflicting_clients

end
end L4.Height.RivalLedger

