import Leader.L4.Height.FreshConflicts
import Leader.L4.BStarGeneratedPCAncestry
import Leader.L4.BStarOwnerControlHistory

namespace L4.Height.FreshFirstAcquire

open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarLongDoor BStarLongCommand BStarLongToken
open BStarGeneratedOwner BStarResetChartTouch BStarSeparatingRail
open BStarClearanceSource BStarSteeredLikelihood BStarAcquireAnchors
open FreshAcquireReceipt

variable {s n : Nat}
local notation "hp" => (show 0<2 by decide)
local notation "B" => rows s

def PC (z : Raw s n) (root : Fin n) : Nat := (ctrlOp.read (z root).long).toNat

/-- Take the first mark leaving a set of PCs on the original word.
Every old observation on the truncated word, including the exit mark,
then belongs to the set. -/
theorem first_outside (inside : Nat→Prop) (z : Raw s n) (i : Fin n)
    (w : Word n) (start : inside (PC z i)) (stop : ¬inside (PC (rawRun z w) i)) :
    ∃ u e v,w=u++e::v ∧ inside (PC (rawRun z u) i) ∧
      ¬inside (PC (rawNext s (rawRun z u) e) i) ∧
      ∀ a f b,u++[e]=a++f::b → inside (PC (rawRun z a) i) := by
  classical
  induction w generalizing z with
  | nil => exact (stop start).elim
  | cons f w ih =>
    by_cases H : inside (PC (rawNext s z f) i)
    · obtain ⟨u,e,v,W,old,new,previous⟩ := ih (rawNext s z f) H stop
      refine ⟨f::u,e,v,congrArg (List.cons f) W,old,new,?_⟩
      intro a j b eq
      cases a with
      | nil => exact start
      | cons t a =>
        obtain ⟨rfl,tail⟩ := List.cons.inj eq
        exact previous a j b tail
    · refine ⟨[],f,w,rfl,start,H,?_⟩
      intro a j b eq
      cases a with
      | nil => exact start
      | cons t a =>
        have size := congrArg List.length eq
        simp only [List.length_cons,List.length_nil,List.length_append] at size
        omega

private def phase (z : Raw s n) (root : Fin n) : Nat := (ctrlPhase.read (z root).long).toNat

/-- Every internal mark whose old source reads PC5 still reads PC5 after
that mark. A return out of PC5 may occur on the next appended mark. -/
def BeforeFirstReturn (z : Raw s n) (root : Fin n) (w : Word n) : Prop :=
  ∀ u e v,w=u++e::v → PC (rawRun z u) root=acquire →
    PC (rawNext s (rawRun z u) e) root=acquire

private theorem run_join (z : Raw s n) (u v : Word n) :
    rawRun z (u++v)=rawRun (rawRun z u) v :=
  BStarResetSchedule.run_append (rawNext s) z u v

private theorem run_snoc (z : Raw s n) (u : Word n) (e : Fin n) :
    rawRun z (u++[e])=rawNext s (rawRun z u) e :=
  run_join z u [e]

private theorem before_slice {z : Raw s n} {root : Fin n} {w : Word n}
    (stay : BeforeFirstReturn z root w) (lead word tail : Word n)
    (tape : w=(lead++word)++tail) :
    BeforeFirstReturn (rawRun z lead) root word := by
  intro u e v W old
  have E : w=(lead++u)++e::(v++tail) := by
    simp only [tape,W,List.append_assoc,List.cons_append]
  have N := stay _ e _ E (by simpa only [run_join] using old)
  simpa only [run_join] using N

private theorem launch_state {z : Raw s n} {root : Fin n} {u : Word n} {e : Fin n}
    (issue : ownIssue z root u e) :
    phase (rawNext s (rawRun z u) e) root=2 ∧ PC (rawNext s (rawRun z u) e) root=acquire := by
  obtain ⟨_,⟨_,_,_,snapshot⟩,op⟩ := issue
  have ph := congrArg (fun a : (Token×BitVec 2)×BitVec 9=>a.1.2.toNat) snapshot
  have pc := congrArg (fun a : (Token×BitVec 2)×BitVec 9=>a.2.toNat) snapshot
  exact ⟨ph,pc.trans op⟩

private theorem phase_step {x y : Raw s n} {g : CustodyWitness x} (P : Production g)
    {o : Owners (oldH6 B g.base)} {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S L fall) (q : g.Q y) (e : Fin n) {m d : Mode}
    (cur : Current hp g.base (fun k => S.getD k fall) L y m)
    (E : Event hp (fun k => S.getD k fall) L y e m d)
    (after : Current hp g.base (fun k => S.getD k fall) L (rawNext s y e) d)
    (oldPhase : phase y (S.getD 0 fall).1=2)
    (old : PC y (S.getD 0 fall).1=acquire)
    (next : PC (rawNext s y e) (S.getD 0 fall).1=acquire) :
    phase (rawNext s y e) (S.getD 0 fall).1=2 := by
  let addr := fun k => S.getD k fall
  have noIdle (I : Current hp g.base addr L y .idle) : False :=
    (by decide : (1 : Nat)≠2) (I.1.2.symm.trans oldPhase)
  cases E with
  | idle_hold _ => exact (noIdle cur).elim
  | bad_issue _ _ => exact (noIdle cur).elim
  | launch _ _ => exact (noIdle cur).elim
  | transit _ _ _ _ _ => exact after.1.2.2.1
  | arrived_hold _ _ => exact after.1.2.2.1
  | consume op door clear =>
    have E' : Event hp addr L y e (.busy op (.back 0)) .idle := .consume op door clear
    obtain ⟨header,slot⟩ := BStarResetChartService.root_header hp C (g.fiber y q)
    obtain ⟨f,_,successor⟩ := BStarGeneratedPCAncestry.consume_pc
      (k₁:=s) (k₂:=radiusTwo s) (t₂:=ell (radiusTwo s+1)) (J₁:=streak s)
      (J₂:=streak (radiusTwo s)) (r:=radWidth s) (c:=s+11) (c₁:=12)
      (addr:=addr) (e:=e) hp slot header (separation P e) cur E' 
    have stepPC := FreshAttempt.acquire_requires_admit _ f cur.1.2.1 (successor.symm.trans next)
    exact ((by decide : acquire≠admit) (old.symm.trans stepPC.1)).elim

private theorem phase_along {x y : Raw s n} {g : CustodyWitness x} (P : Production g)
    {o : Owners (oldH6 B g.base)} {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S L fall) {w : Word n} {m d : Mode}
    (G : GeneratedOwner hp g.base (fun k=>S.getD k fall) L y m w d)
    (q : g.Q y) (stay : BeforeFirstReturn y (S.getD 0 fall).1 w)
    (oldPhase : phase y (S.getD 0 fall).1=2) (old : PC y (S.getD 0 fall).1=acquire) :
    phase (rawRun y w) (S.getD 0 fall).1=2 := by
  induction G with
  | endpoint _ => exact oldPhase
  | @next z a e v b dest cur event tail ih =>
    have next := stay [] e v rfl old
    have tailStay : BeforeFirstReturn (rawNext s z e) (S.getD 0 fall).1 v := by
      intro u f v W oldPC
      exact stay (e::u) f v (congrArg (List.cons e) W) oldPC
    exact ih (g.closed z e q) tailStay
      (phase_step P C q e cur event (BStarGeneratedTapeCuts.at_start hp tail) oldPhase old next) next

variable {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 B g.base

/-- Before the first exit, a genuine ISSUE5 keeps the source at phase2.
A later ISSUE5 would require phase1 at that exact source. -/
theorem at_most_one_before_return (P : Production g) (o : Owners h)
    (a w : Word n) (r : Fin n) (release : accepted g o a r)
    (stay : BeforeFirstReturn (rawNext s (rawRun x a) r) (RivalLedger.source g o) w) :
    AtMostOneIssue (rawNext s (rawRun x a) r) (RivalLedger.source g o) w := by
  let z := rawNext s (rawRun x a) r
  let root := RivalLedger.source g o
  obtain ⟨S,L,fall,C,idle,_⟩ := ReleaseGrantReceipt.released_chart P o a r release
  let addr := fun k=>S.getD k fall
  have rootID : (addr 0).1=root := congrArg Prod.fst C.root
  have q : g.Q z := g.closed _ r (ready_run P a).1
  obtain ⟨d,G,_,_⟩ := generated_word hp C g.Q g.fiber (fun z q e=>g.closed z e q)
    (separation P) w .idle q idle
  intro u e v W later b f c U earlier
  let lead := b++[f]
  have whole : w=lead++(c++e::v) := by
    simp only [W,U,lead,List.append_assoc,List.nil_append,List.cons_append]
  obtain ⟨m,_,tail⟩ := BStarGeneratedTapeCuts.split hp lead (c++e::v) (whole ▸ G)
  obtain ⟨d,interval,_⟩ := BStarGeneratedTapeCuts.split hp c (e::v) tail
  have through : BeforeFirstReturn (rawRun z lead) root c :=
    before_slice stay lead c (e::v) (by simpa only [List.append_assoc] using whole)
  obtain ⟨ph,next⟩ := launch_state earlier
  have startPhase : phase (rawRun z lead) (addr 0).1=2 := by
    rw [rootID]
    simpa only [lead,run_snoc] using ph
  have startPC : PC (rawRun z lead) (addr 0).1=acquire := by
    rw [rootID]
    simpa only [lead,run_snoc] using next
  have throughAt : BeforeFirstReturn (rawRun z lead) (addr 0).1 c :=
    (congrArg (fun i : Fin n => BeforeFirstReturn (rawRun z lead) i c) rootID).mpr through
  have endpoint : phase (rawRun (rawRun z lead) c) (addr 0).1=2 :=
    phase_along P C interval (ProductionCustody.keep g z lead q) throughAt startPhase startPC
  have oldPhase : phase (rawRun z u) root=2 := by
    rw [rootID,←run_join] at endpoint
    simpa only [U,lead,List.append_assoc,List.singleton_append] using endpoint
  exact (by decide : (1 : Nat)≠2) (later.2.1.1.2.symm.trans oldPhase)

private theorem before_cons {z : Raw s n} {root : Fin n} {e : Fin n} {w : Word n}
    (first : PC z root=acquire → PC (rawNext s z e) root=acquire)
    (rest : BeforeFirstReturn (rawNext s z e) root w) :
    BeforeFirstReturn z root (e::w) := by
  intro u f v W old
  cases u with
  | nil =>
    have same := (List.cons.inj W).1
    subst f
    exact first old
  | cons a u =>
    obtain ⟨A,T⟩ := List.cons.inj W
    subst a
    exact rest u f v T old

private theorem first_exit_or_before (z : Raw s n) (root : Fin n) (w : Word n) :
    BeforeFirstReturn z root w ∨
      ∃ u e v,w=u++e::v ∧ BeforeFirstReturn z root u ∧ PC (rawRun z u) root=acquire ∧
        PC (rawNext s (rawRun z u) e) root≠acquire := by
  classical
  induction w generalizing z with
  | nil =>
    exact .inl (by intro u e v W; cases u <;> cases W)
  | cons e w ih =>
    by_cases H : PC z root=acquire → PC (rawNext s z e) root=acquire
    · rcases ih (rawNext s z e) with clean|⟨u,f,v,W,clean,old,new⟩
      · exact .inl (before_cons H clean)
      · exact .inr ⟨e::u,f,v,congrArg (List.cons e) W,before_cons H clean,old,new⟩
    · have old : PC z root=acquire := Classical.byContradiction (fun N=>H (fun E => (N E).elim))
      exact .inr ⟨[],e,w,rfl,
        (by intro u f v W; cases u <;> cases W),
        old,fun next=>H (fun _=>next)⟩

private theorem stays_at_acquire (z : Raw s n) (root : Fin n) (w : Word n)
    (initial : PC z root=acquire) (stay : BeforeFirstReturn z root w) :
    PC (rawRun z w) root=acquire := by
  induction w generalizing z with
  | nil => exact initial
  | cons e w ih =>
    apply ih _ (stay [] e w rfl initial)
    intro u f v W pc
    exact stay (e::u) f v (congrArg (List.cons e) W) pc

/-- If an actual word visits PC5 and ends off PC5, it has a first exit
mark whose earlier tape satisfies BeforeFirstReturn. -/
theorem first_exit_of_visited (z : Raw s n) (root : Fin n) (w : Word n)
    (seen : ∃ u v,w=u++v ∧ PC (rawRun z u) root=acquire)
    (ended : PC (rawRun z w) root≠acquire) :
    ∃ u e v,w=u++e::v ∧ BeforeFirstReturn z root u ∧ PC (rawRun z u) root=acquire ∧
      PC (rawNext s (rawRun z u) e) root≠acquire := by
  rcases first_exit_or_before z root w with stay|found
  · obtain ⟨u,v,W,old⟩ := seen
    have tail := before_slice stay u v [] (by simpa only [List.append_nil] using W)
    have endPC := stays_at_acquire _ root v old tail
    rw [W,run_join] at ended
    exact (ended endPC).elim
  · exact found

private theorem exit_uses_door {y : Raw s n} (P : Production g)
    {o : Owners h} {S : List (Pos n)} {L : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S L fall) (q : g.Q y) (e : Fin n) {m d : Mode}
    (cur : Current hp g.base (fun k=>S.getD k fall) L y m)
    (E : Event hp (fun k=>S.getD k fall) L y e m d)
    (old : PC y (S.getD 0 fall).1=acquire)
    (left : PC (rawNext s y e) (S.getD 0 fall).1≠acquire)
    (after : Current hp g.base (fun k=>S.getD k fall) L (rawNext s y e) d) :
    e=RearTrace.predecessor (S.getD 0 fall).1 := by
  cases E with
  | idle_hold offsite =>
    rcases BStarOwnerControlHistory.idle_launch_or_hold hp C (g.fiber y q) cur.2
      (separation P) e cur.1 with H|H|H
    · have frame := congrArg (fun a : BitVec 2×BitVec 9=>a.2.toNat) H.2.2.1
      exact (left (frame.trans old)).elim
    · exact (offsite H.1).elim
    · exact (offsite H.1).elim
  | bad_issue _ bad =>
    change initial (PC y (S.getD 0 fall).1) (y (S.getD 0 fall).1).long=none at bad
    rw [old] at bad
    simp only [initial, beq_self_eq_true, if_true, reduceCtorEq] at bad
  | launch _ _ => exact (left (after.1.2.2.2.trans old)).elim
  | transit _ _ _ _ _ => exact (left (after.1.2.2.2.trans (cur.1.2.2.2.symm.trans old))).elim
  | arrived_hold _ _ => exact (left (after.1.2.2.2.trans (cur.1.2.2.2.symm.trans old))).elim
  | consume _ door _ => exact door

/-- On an actual generated post-RREL tape any PC5 exit is the own
incoming ACQUIRE consume. In particular no idle launch can be the exit. -/
theorem first_return_incoming (P : Production g) (o : Owners h)
    (a w : Word n) (r e : Fin n) (release : accepted g o a r)
    (pending : PC (rawRun (rawNext s (rawRun x a) r) w) (RivalLedger.source g o)=acquire)
    (ended : PC (rawNext s (rawRun (rawNext s (rawRun x a) r) w) e) (RivalLedger.source g o)≠acquire) :
    e=RearTrace.predecessor (RivalLedger.source g o) := by
  let y := rawNext s (rawRun x a) r
  obtain ⟨S,L,fall,C,idle,_⟩ := ReleaseGrantReceipt.released_chart P o a r release
  have root : (S.getD 0 fall).1=RivalLedger.source g o := congrArg Prod.fst C.root
  have q0 : g.Q y := g.closed _ r (ready_run P a).1
  obtain ⟨m,_,q,cur⟩ := generated_word hp C g.Q g.fiber (fun z q f=>g.closed z f q)
    (separation P) w .idle q0 idle
  obtain ⟨d,E,after⟩ := current_step hp C g.Q g.fiber (fun z q f=>g.closed z f q)
    (separation P) q e m cur
  have hOld : PC (rawRun y w) (S.getD 0 fall).1=acquire := by simpa only [y,root] using pending
  have hNew : PC (rawNext s (rawRun y w) e) (S.getD 0 fall).1≠acquire := by
    simpa only [y,root] using ended
  have door := exit_uses_door g P C q e cur E hOld hNew after
  simpa only [root] using door

/-- The first ACQUIRE exit on a common unpublished emitted tape has the
physical all-win itinerary. The original prefix supplies issue uniqueness. -/
theorem itinerary_of_first_return (P : Production g) (target : Owners h)
    (base w after candidates : Word n) (cuts : Releases g target 5 base)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=(base++w)++after)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 ((base++w)++after))
    (ack : Fin n)
    (stay : BeforeFirstReturn (rawRun x base) (RivalLedger.source g target) w)
    (pending : PC (rawRun (rawRun x base) w) (RivalLedger.source g target)=acquire)
    (ended : PC (rawNext s (rawRun (rawRun x base) w) ack) (RivalLedger.source g target)≠acquire) :
    ∃ S L fall, Chart hp g.base g.hh target S L fall ∧
      Itinerary g.base (rawRun x base) S L fall w ack := by
  obtain ⟨a,r,same,H⟩ := FreshConflicts.target_release g target cuts
  have eq : rawRun x base=rawNext s (rawRun x a) r := by rw [same,run_snoc]
  have once := at_most_one_before_return g P target a w r H (eq ▸ stay)
  have incoming := first_return_incoming g P target a w r ack H (eq ▸ pending) (eq ▸ ended)
  exact FreshConflicts.itinerary_of_unpublished_prefix g P target base w after candidates cuts tape miss ack
    (eq.symm ▸ once) incoming pending ended

/-- A released unpublished word which visits PC5 and later leaves
contains an actual first ACQUIRE receipt with the all-win itinerary. -/
theorem itinerary_of_visited_acquire (P : Production g) (target : Owners h)
    (base w after candidates : Word n) (cuts : Releases g target 5 base)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=(base++w)++after)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 ((base++w)++after))
    (seen : ∃ u v,w=u++v ∧ PC (rawRun (rawRun x base) u) (RivalLedger.source g target)=acquire)
    (ended : PC (rawRun (rawRun x base) w) (RivalLedger.source g target)≠acquire) :
    ∃ u e v S L fall,w=u++e::v ∧ BeforeFirstReturn (rawRun x base) (RivalLedger.source g target) u ∧
      Chart hp g.base g.hh target S L fall ∧ Itinerary g.base (rawRun x base) S L fall u e := by
  obtain ⟨u,e,v,W,earliest,pending,left⟩ :=
    first_exit_of_visited (rawRun x base) (RivalLedger.source g target) w seen ended
  have full : (base++w)++after=(base++u)++(e::(v++after)) := by
    simp only [W,List.append_assoc,List.cons_append]
  obtain ⟨S,L,fall,C,I⟩ := itinerary_of_first_return g P target base u (e::(v++after))
    candidates cuts (tape.trans full) (full ▸ miss) e earliest pending left
  exact ⟨u,e,v,S,L,fall,W,earliest,C,I⟩

end L4.Height.FreshFirstAcquire

