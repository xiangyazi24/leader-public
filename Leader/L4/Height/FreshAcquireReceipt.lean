import Leader.L4.Height.ReleaseGrantReceipt
import Leader.L4.Height.FreshAcquireTour

namespace L4.Height.FreshAcquireReceipt
open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles BStarLongWork BStarLongDoor
open BStarLongToken BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarClearanceSource BStarLongCommand BStarSteeredLikelihood
open BStarAcquireLatch BStarSeparatingRail BStarAcquireAnchors
open BStarGeneratedTapeCuts BStarAcquireForwardTrace BStarResetNoAcquire BStarGrantBirth FreshAcquireTour

variable {s n : Nat}
local notation "hp" => (show 0<2 by decide)
local notation "B" => rows s

/-- A launch test uses the old source and its actual incoming physical mark. -/
def ownIssue (x : Raw s n) (root : Fin n) (a : Word n) (e : Fin n) : Prop :=
  let y := rawRun x a
  e=RearTrace.predecessor root ∧ Launch (y root).long (rawNext s y e root).long ∧
    (ctrlOp.read (y root).long).toNat=acquire

def AtMostOneIssue (x : Raw s n) (root : Fin n) (w : Word n) : Prop :=
  ∀ u e v,w=u++e::v → ownIssue x root u e →
    ∀ b f c,u=b++f::c → ¬ownIssue x root b f

private theorem actual_consume {x base : Raw s n} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {m d : Mode} (cur : Current hp base addr len x m) (event : Event hp addr len x e m d)
    (post : Current hp base addr len (rawNext s x e) d)
    (door : e=RearTrace.predecessor (addr 0).1)
    (old : (ctrlOp.read (x (addr 0).1).long).toNat=acquire)
    (left : (ctrlOp.read (rawNext s x e (addr 0).1).long).toNat≠acquire) :
    m=.busy acquire (.back 0) ∧ d=.idle := by
  cases event with
  | idle_hold away => exact (away door).elim
  | bad_issue _ bad =>
    change initial (ctrlOp.read (x (addr 0).1).long).toNat (x (addr 0).1).long=none at bad
    rw [old] at bad
    simp only [initial, beq_self_eq_true, if_true, reduceCtorEq] at bad
  | launch _ _ =>
    exact (left (post.1.2.2.2.trans old)).elim
  | arrived_hold _ away => exact (away door).elim
  | transit op _ _ _ _ =>
    exact (left (post.1.2.2.2.trans (cur.1.2.2.2.symm.trans old))).elim
  | consume op _ _ =>
    have eq : op=acquire := cur.1.2.2.2.symm.trans old
    subst op
    exact ⟨rfl,rfl⟩

/-- A finite output record of the actual all-win outward itinerary, its three
captured incidences, and the matched ISSUE6 receipt on the original tape. -/
def Itinerary (base released : Raw s n) (S : List (Pos n)) (len : Nat) (fall : Pos n)
    (w : Word n) (ack : Fin n) : Prop :=
  ∃ pre launch outward turn ret ps vs,
    w=pre++launch::(outward++turn::ret) ∧ ownIssue released (S.getD 0 fall).1 pre launch ∧
    let start := rawNext s (rawRun released pre) launch
    Trace hp base start (S.getD 0 fall) outward (rawRun start outward) (S.getD len fall) ps vs ∧
    vs.all Visit.wins=true ∧ (∀ j : Fin 3,(vs.filter (fun v=>v.incidence.val==j.val)).length=1) ∧
    BStarResetControllerEntry.snapshot (rawNext s (rawRun released w) ack (S.getD 0 fall).1).long=
      ((.empty,1),BitVec.ofNat 9 6)

set_option maxHeartbeats 1800000 in
theorem production_itinerary {x : Raw s n} {g : CustodyWitness x} (P : Production g)
    (o : Owners (oldH6 B g.base)) (a : Word n) (rrel : Fin n) (paid : accepted g o a rrel) :
    let released := rawNext s (rawRun x a) rrel
    let root := (endpoint (oldH6 B g.base) g.hh o 0).1
    ∃ S len fall, Chart hp g.base g.hh o S len fall ∧ ∀ w ack,
      AtMostOneIssue released root w →
      (∀ u e v,w=u++e::v → ∀ i j,oldH6 B (rawRun released u) i=true →
        commandOwner (oldH6 B g.base) i (slot j)=o.val → RivalsClear (rawRun released u) i j) →
      ack=RearTrace.predecessor root → (ctrlOp.read (rawRun released w root).long).toNat=acquire →
      (ctrlOp.read (rawNext s (rawRun released w) ack root).long).toNat≠acquire →
      Itinerary g.base released S len fall w ack := by
  let released := rawNext s (rawRun x a) rrel
  obtain ⟨S,len,fall,C,idle,cleared⟩ := ReleaseGrantReceipt.released_chart P o a rrel paid
  let addr := fun k => S.getD k fall
  let root := (addr 0).1
  have rootEq : root=(endpoint (oldH6 B g.base) g.hh o 0).1 := congrArg Prod.fst C.root
  refine ⟨S,len,fall,C,?_⟩
  intro w ack one rivals door old left
  rw [←rootEq] at one door old left
  have initial : g.Q released := g.closed _ rrel (ready_run P a).1
  obtain ⟨m,G,q,cur⟩ := generated_word hp C g.Q g.fiber (fun y hy e => g.closed y e hy)
    (separation P) w .idle initial idle
  obtain ⟨d,E,after⟩ := current_step hp C g.Q g.fiber (fun y hy e => g.closed y e hy)
    (separation P) q ack m cur
  obtain ⟨rfl,rfl⟩ := actual_consume cur E after door old left
  obtain ⟨pre,tour,launch,W,atDoor,L,opcode,busy⟩ := from_idle hp G
  have trueIssue : ownIssue released root pre launch := ⟨atDoor,L,opcode⟩
  obtain ⟨source,setup,_⟩ := BStarGeneratedTapeCuts.split hp pre (launch::tour) (W ▸ G)
  have empty := idle_of_issue hp (at_end hp setup) L.1
  subst source
  have noneEarlier (u : Word n) (f : Fin n) (v : Word n) (cut : pre=u++f::v) (b : Mode)
      (H : GeneratedOwner hp g.base addr len released .idle u b) (z : Cursor) : b≠.busy acquire z := by
    intro same
    obtain ⟨prefixMarks,suffixMarks,earlier,F,D,Launched,op,_⟩ := from_idle hp (same ▸ H)
    exact one pre launch tour W trueIssue prefixMarks earlier (suffixMarks++f::v)
      (by rw [cut,F,List.append_assoc,List.cons_append]) ⟨D,Launched,op⟩
  have onTape (u : Word n) : rawRun released (pre++launch::u)=rawRun (rawNext s (rawRun released pre) launch) u :=
    BStarResetSchedule.run_append (rawNext s) released pre (launch::u)
  have visits (u : Word n) (f : Fin n) (v : Word n) (cut : tour=u++f::v) := by
    have mark : w=(pre++launch::u)++f::v := by rw [W,cut,List.append_assoc,List.cons_append]
    have R := rivals _ f v mark
    rw [onTape] at R
    exact R
  have endEq : rawRun released w=rawRun (rawNext s (rawRun released pre) launch) tour :=
    (congrArg (rawRun released) W).trans (onTape tour)
  change Event hp addr len (rawRun released w) ack (.busy acquire (.back 0)) .idle at E
  obtain ⟨out,turn,ret,ps,vs,tape,trace,wins,once,receipt⟩ :=
    completed_fresh_tour hp C (separation P) cleared pre setup noneEarlier launch atDoor L opcode
      tour busy visits ack (endEq ▸ E)
  exact ⟨pre,launch,out,turn,ret,ps,vs,by rw [W,tape],trueIssue,trace,wins,once,endEq.symm ▸ receipt⟩

end L4.Height.FreshAcquireReceipt

