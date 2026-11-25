import Leader.L4.Height.RivalLedger
import Leader.L4.Height.ProductionCycles
import Leader.L4.Height.FreshAcquireReceipt

namespace L4.Height.FreshConflicts

open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarSteeredLikelihood BStarLongWork BStarResetNoAcquire
open BStarGrantBirth FreshAcquireTour

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 (rows s) g.base

/-- Every indexed receipt in the release sequence remains a physical cut
of that same tape. Repeated client owners may have separate receipts. -/
theorem release_cut (target : Owners h) {k : Nat} {base : Word n}
    (R : Releases g target k base) (j : Nat) (inside : j<k) :
    ∃ a r tail, base=(a++[r])++tail ∧ accepted g (releaseClient g target j) a r := by
  induction R with
  | initial => omega
  | @receipt k a earlier gap e acceptedMark ih =>
    by_cases here : j=k
    · subst j
      exact ⟨a++gap,e,[],(List.append_nil _).symm,acceptedMark⟩
    · obtain ⟨u,r,v,E,H⟩ := ih (by omega)
      refine ⟨u,r,v++gap++[e],?_,H⟩
      simp only [E,List.append_assoc]

/-- The fifth receipt is exactly the target's own physical release. -/
theorem target_release (target : Owners h) {base : Word n} (R : Releases g target 5 base) :
    ∃ a r,base=a++[r] ∧ accepted g target a r := by
  cases R with
  | receipt _ gap e H => exact ⟨_,e,rfl,H⟩

private theorem rival_after_cut (P : Production g) (target : Owners h)
    (j : Fin 5) (diff : (RivalLedger.clients g target j).val≠target.val)
    (base w candidates : Word n)
    (past : ∃ a r v,base=(a++[r])++v ∧ accepted g (RivalLedger.clients g target j) a r)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=base++w)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 (base++w)) :
    ∀ i p,commandOwner h i (slot p)=(RivalLedger.clients g target j).val →
      bit (rawRun x (base++w)) i p=0 ∧ NoAcquireAt (rawRun x (base++w)) i p := by
  obtain ⟨a,r,v,E,H⟩ := past
  have W : (a++[r])++(v++w)=base++w := by simp only [E,List.append_assoc]
  have clear := RivalLedger.rival_clear_on_miss g P target j diff a (v++w) candidates r H
    (tape.trans W.symm) (W.symm ▸ miss)
  rwa [W] at clear

/-- All old competing grants at an unpublished sampled cut are zero
after the five releases. A reader's same-mark writer proposal is absent. -/
theorem sampled_rivals (P : Production g) (target : Owners h)
    (base w candidates : Word n) (cuts : Releases g target 5 base)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=base++w)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 (base++w)) :
    ∀ i p,oldH6 (rows s) (rawRun x (base++w)) i=true →
      commandOwner h i (slot p)=target.val → RivalsClear (rawRun x (base++w)) i p := by
  let u := (endpoint h g.hh target 0).1
  let v := (endpoint h g.hh target 1).1
  let z := (endpoint h g.hh target 2).1
  obtain ⟨leftDiff,rightDiff,uOwn,vLeft,vRight,zOwn⟩ := RivalLedger.conflicting_clients g P target
  have left := rival_after_cut g P target 1 leftDiff base w candidates
    (release_cut g target cuts 1 (by decide)) tape miss
  have right := rival_after_cut g P target 3 rightDiff base w candidates
    (release_cut g target cuts 2 (by decide)) tape miss
  intro i p header owner
  have hI : h i=true :=
    (congrArg Prod.fst (g.fiber _ (ready_run P (base++w)).1 i)).trans header
  have val : p.val=0 ∨ p.val=1 ∨ p.val=2 := by
    have bound := p.isLt
    omega
  rcases val with V|V|V
  · have E : p=(0 : Fin 3) := Fin.ext V
    subst p
    have pos : i=u :=
      congrArg Prod.fst ((endpoint_spec h g.hh target (slot 0)).2.2 i hI owner)
    rw [pos,RivalsClear,if_neg (by decide : (0 : Fin 3)≠1)]
    exact left u 1 uOwn
  · have E : p=(1 : Fin 3) := Fin.ext V
    subst p
    have pos : i=v :=
      congrArg Prod.fst ((endpoint_spec h g.hh target (slot 1)).2.2 i hI owner)
    rw [pos,RivalsClear,if_pos rfl]
    exact ⟨(right v 0 vRight).1,(left v 2 vLeft).1⟩
  · have E : p=(2 : Fin 3) := Fin.ext V
    subst p
    have pos : i=z :=
      congrArg Prod.fst ((endpoint_spec h g.hh target (slot 2)).2.2 i hI owner)
    rw [pos,RivalsClear,if_neg (by decide : (2 : Fin 3)≠1)]
    exact right z 1 zOwn

private theorem emitted_prefix (c : Word n → Fin n → Fin n)
    (a b w : Word n) (E : emit c [] w=a++b) : ∃ u,emit c [] u=a := by
  cases b with
  | nil => exact ⟨w,by simpa only [List.append_nil] using E⟩
  | cons f tail =>
    obtain ⟨u,_,_,_,atPrefix,_,_⟩ := BStarEmittedCut.marked_cut c [] w a tail f E
    exact ⟨u,atPrefix⟩

private theorem misses_prefix (i : Fin n) (a b : Word n)
    (M : ¬RawServiceCore.publishes x i (a++b)) : ¬RawServiceCore.publishes x i a := by
  rintro ⟨u,v,E,H⟩
  exact M ⟨u,v++b,by simp only [E,List.append_assoc,List.cons_append],H⟩

/-- Extract every old arbitration premise from one unpublished emitted
extension. Its actual candidate prefix is used at every sampled cut. -/
theorem common_prefix_rivals (P : Production g) (target : Owners h)
    (base w after candidates : Word n) (cuts : Releases g target 5 base)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=(base++w)++after)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 ((base++w)++after)) :
    ∀ u f v,w=u++f::v → ∀ i p,oldH6 (rows s) (rawRun (rawRun x base) u) i=true →
      commandOwner h i (slot p)=target.val → RivalsClear (rawRun (rawRun x base) u) i p := by
  intro u f v W
  have split : (base++w)++after=(base++u)++(f::(v++after)) := by
    simp only [W,List.append_assoc,List.cons_append]
  obtain ⟨pfx,emitted⟩ := emitted_prefix _ (base++u) _ candidates (tape.trans split)
  have off : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 (base++u) :=
    misses_prefix _ _ _ (split ▸ miss)
  have ready := sampled_rivals g P target base u pfx cuts emitted off
  have runEq : rawRun x (base++u)=rawRun (rawRun x base) u :=
    BStarResetSchedule.run_append (rawNext s) x base u
  rwa [runEq] at ready

/-- The same old-pair premises follow from a consistent terminal
history on the production policy, with its own actual candidate tape. -/
theorem common_prefix_rivals_of_history (P : Production g) (i : Header h)
    (base w after : Word n) (y : History s n)
    (cuts : Releases g (ProductionClients.serviceOwner g i) 5 base)
    (actual : Consistent x (policy g i) i.val y)
    (sameTape : y.emitted=(base++w)++after) (miss : ¬y.published) :
    ∀ u e v,w=u++e::v → ∀ j p,oldH6 (rows s) (rawRun (rawRun x base) u) j=true →
      commandOwner h j (slot p)=(ProductionClients.serviceOwner g i).val →
      RivalsClear (rawRun (rawRun x base) u) j p := by
  let target := ProductionClients.serviceOwner g i
  have tape : emit (chooseBy (RivalLedger.mask g target)) [] y.candidates=(base++w)++after :=
    actual.1.symm.trans sameTape
  have absent : ¬RawServiceCore.publishes x i.val ((base++w)++after) :=
    fun H => miss (actual.2.2.mpr (sameTape.symm ▸ H))
  apply common_prefix_rivals g P target base w after y.candidates cuts tape
  simpa only [target,ProductionClients.service_header] using absent

/-- Install the common-prefix premise in the actual ACQUIRE receipt theorem.
The tape ends at the sampled return or continues past it without publication. -/
theorem itinerary_of_unpublished_prefix (P : Production g) (target : Owners h)
    (base w after candidates : Word n) (cuts : Releases g target 5 base)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=(base++w)++after)
    (miss : ¬RawServiceCore.publishes x (endpoint h g.hh target 1).1 ((base++w)++after))
    (ack : Fin n)
    (once : FreshAcquireReceipt.AtMostOneIssue (rawRun x base) (RivalLedger.source g target) w)
    (incoming : ack=RearTrace.predecessor (RivalLedger.source g target))
    (pending : (BStarLongDoor.ctrlOp.read (rawRun (rawRun x base) w (RivalLedger.source g target)).long).toNat=
      BStarLongCommand.acquire)
    (ended : (BStarLongDoor.ctrlOp.read
      (rawNext s (rawRun (rawRun x base) w) ack (RivalLedger.source g target)).long).toNat≠
      BStarLongCommand.acquire) :
    ∃ S L fall, BStarResetChartTouch.Chart (show 0<2 by decide) g.base g.hh target S L fall ∧
      FreshAcquireReceipt.Itinerary g.base (rawRun x base) S L fall w ack := by
  have rivals := common_prefix_rivals g P target base w after candidates cuts tape miss
  obtain ⟨a,r,E,H⟩ := target_release g target cuts
  have state : rawRun x base=rawNext s (rawRun x a) r := by
    rw [E]
    exact BStarResetSchedule.run_append (rawNext s) x a [r]
  obtain ⟨S,L,fall,C,I⟩ := FreshAcquireReceipt.production_itinerary P target a r H
  rw [state] at once rivals pending ended ⊢
  exact ⟨S,L,fall,C,I w ack once rivals incoming pending ended⟩

#print axioms release_cut
#print axioms target_release
#print axioms sampled_rivals
#print axioms common_prefix_rivals
#print axioms common_prefix_rivals_of_history
#print axioms itinerary_of_unpublished_prefix

end L4.Height.FreshConflicts

