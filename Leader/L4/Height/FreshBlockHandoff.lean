import Leader.L4.Height.ProductionConclusion
import Leader.L4.Height.ProductionBlockInterface

namespace L4.Height.ProductionCustody
open AllSizeProtocol PhysicalCustody BStarH6WordChart BStarTrace
open BStarAcquireAnchors BStarSteeredLikelihood Classical

/-- Literal dispatch inequality with the release clock and raw block
reweighting already instantiated. The remaining premise is precisely
the physical fresh-cycle publication on the same emitted tape. -/
theorem strict_publication_block_of_fresh_cycles
    (fresh : ProductionCycles.FreshCyclePublishes)
    {s n : Nat} (hn : 4 ≤ n)
    (hs : 6 ≤ s) (hadvice : s = ell (ell n))
    (hspace : 3 * 1024 * radWidth s < n)
    {x : Raw s n} (g : CustodyWitness x) (i : Header (oldH6 (rows s) g.base)) :
    let W := width g
    let D := 2^20 * n * W
    2^(5*longBudget+1) *
      wordSum (fun w => if RawServiceCore.publishes x i.val w then 1 else 0) (2*D) ≥ n^(2*D) :=
  strict_publication_block_of_production_block
    (ProductionCycles.strict_block_of_fresh_cycles fresh) hn hs hadvice hspace g i

#print axioms strict_publication_block_of_fresh_cycles
end L4.Height.ProductionCustody
