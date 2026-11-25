import Leader.L4.Height.FreshRFinal
import Leader.L4.Height.FreshStageSeal

namespace L4.Height.ProductionCycles
open AllSizeProtocol PhysicalCustody ProductionCustody BStarTrace BStarSteeredLikelihood
open BStarH6WordChart BStarAcquireAnchors BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarAcquireVisitOrder BStarSeparatingRail
open BStarLongLayout BStarLongLiteral BStarLongWork FreshFirstAcquire

set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
local notation "hp" => (show 0<2 by decide)

theorem stage_completion {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (P : Production g) (i : Header (oldH6 (rows s) g.base)) :
    StageCompletion g i := by
  intro S len fall C k K idx a r paid pre post
  dsimp only
  intro hist start stop
  let base := rawNext s (rawRun x a) r
  let y := rawRun base pre
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let o := ProductionClients.serviceOwner g i
  have qbase : g.Q base := g.closed _ r (ready_run P a).1
  have qy : g.Q y := keep g base pre qbase
  have cur : Current hp g.base addr len y .idle := BStarGeneratedTapeCuts.at_end hp hist
  obtain ⟨md,H,_,_⟩ := generated_word hp C g.Q g.fiber (fun y q e => g.closed y e q)
    (separation P) post .idle qy cur
  have joined (u v : Word n) : rawRun base (u++v)=rawRun (rawRun base u) v :=
    BStarResetSchedule.run_append (rawNext s) base u v
  have later : PC (rawRun y post) root=2 := by rw [←joined pre post]; exact stop
  have own : commandOwner (oldH6 (rows s) g.base) i.val 1=o.val := rfl
  obtain ⟨u,v,pay,d,W,G,well,_,_,source,arg,writer,staged,offer⟩ :=
    FreshStageSeal.accepted_seal_facts P o a r paid C i.val k K idx i.property own pre post md
      hist start H later
  refine ⟨u,v,W,G,pay,d,well,?_⟩
  rw [joined pre u]
  exact ⟨source,arg,writer,staged,offer⟩

/-- No unsigned parameters or safety hypotheses remain on the stopped cycle. -/
theorem fresh_cycle_publishes : FreshCyclePublishes :=
  fresh_of_stage_completion stage_completion

end L4.Height.ProductionCycles

namespace L4.Height.ProductionCustody
open AllSizeProtocol PhysicalCustody BStarH6WordChart BStarTrace
open BStarAcquireAnchors BStarSteeredLikelihood Classical

theorem production_block : ProductionBlock :=
  ProductionCycles.strict_block_of_fresh_cycles ProductionCycles.fresh_cycle_publishes

theorem strict_publication_block {s n : Nat} (hn : 4 ≤ n)
    (hs : 6 ≤ s) (hadvice : s = ell (ell n))
    (hspace : 3 * 1024 * radWidth s < n)
    {x : Raw s n} (g : CustodyWitness x) (i : Header (oldH6 (rows s) g.base)) :
    let W := width g
    let D := 2^20 * n * W
    2^(5*longBudget+1) *
      wordSum (fun w => if RawServiceCore.publishes x i.val w then 1 else 0) (2*D) ≥ n^(2*D) :=
  strict_publication_block_of_production_block production_block hn hs hadvice hspace g i

theorem strict_publication_moment {s n : Nat} (_hn : 4 ≤ n)
    (hs : 6 ≤ s) (hadvice : s = ell (ell n))
    (hspace : 3 * 1024 * radWidth s < n)
    {x : Raw s n} (g : CustodyWitness x) (i : Header (oldH6 (rows s) g.base)) (t : Nat) :
    wordSum (fun w => 2^(min (RawServiceCore.strictWait x i.val w) t /
      (2^(5*longBudget+34)*n*radWidth s))) t ≤ 2*n^t :=
  moment_of_production_block production_block g (production_of_space g hs hadvice hspace) i t

#print axioms L4.Height.ProductionCycles.stage_completion
#print axioms L4.Height.ProductionCycles.fresh_cycle_publishes
#print axioms production_block
#print axioms strict_publication_block
#print axioms strict_publication_moment
end L4.Height.ProductionCustody
