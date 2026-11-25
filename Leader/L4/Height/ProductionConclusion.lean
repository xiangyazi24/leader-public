import Leader.L4.Height.ProductionBlockMoment
import Leader.L4.Height.ReleaseStage

namespace L4.Height.ProductionCycles
open AllSizeProtocol PhysicalCustody ProductionCustody BStarH6WordChart BStarAcquireAnchors

/-- Every fully released fresh target attempt has a strict publication on
the original emitted tape. This statement quantifies only over finite words. -/
def FreshCyclePublishes : Prop :=
  ∀ {s n} {x : Raw s n} (g : CustodyWitness x),Production g → ∀ i : Header (oldH6 (rows s) g.base),
  ∀ y,Consistent x (policy g i) i.val y → Releases g (ProductionClients.serviceOwner g i) 5 y.emitted →
  ∀ z,Consistent x (policy g i) i.val z → ∀ gap e,z.emitted=(y.emitted++gap)++[e] →
    accepted g (ProductionClients.serviceOwner g i) (y.emitted++gap) e → z.published

theorem strict_block_of_fresh_cycles (safe : FreshCyclePublishes) : ProductionBlock := by
  intro s n x g p i
  apply block_of_release_safety g p i
  · intro o y hc
    exact Cycle.mono g (ReleaseStage.release_owner g p i o y hc) (fun _ receipt => .inr receipt)
  · exact safe g p i

theorem g9_of_fresh_cycles (safe : FreshCyclePublishes) {s n : Nat} {Z : Type}
    (step : Z → Fin n → Z) (raw : Z → Raw s n) (served : Z → Prop) (i : Fin n)
    (rawStep : ∀ z e,raw (step z e)=rawNext s (raw z) e)
    (lastMark : ∀ z, ¬BStarGrantWriterHistory.NoPublication (show 0<2 by decide) (raw z) i i →
      served (step z i))
    (g : ∀ z,CustodyWitness (raw z)) (prod : ∀ z,Production (g z))
    (header : ∀ z,oldH6 (rows s) (g z).base i=true) (W : Nat) (fixed : ∀ z,width (g z)=W)
    (z : Z) : Thru.MomentAt step served (2^(5*longBudget+34)*n*radWidth s) z :=
  g9_moment_of_production_block (strict_block_of_fresh_cycles safe)
    step raw served i rawStep lastMark g prod header W fixed z

end L4.Height.ProductionCycles
