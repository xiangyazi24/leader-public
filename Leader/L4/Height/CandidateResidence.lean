import Leader.L4.Height.ProductionBonds
import Leader.L4.Height.FenceLineTransfer

namespace L4.Height.CandidateResidence
open PhysicalCustody ProductionCustody BStarAcquireLiteralChain BStarH6WordChart
open BStarSteeredLikelihood BStarParkedSteering BStarSteeringSupport
open Classical
noncomputable section

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (P : Production g)
    (o : Owners (oldH6 (rows s) g.base))
local notation "hp" => (show 0<2 by decide)

include P in
/-- Initialize both full comparison lines at any stopped candidate prefix.
Their subsequent clock uses the actual five-client controller at that prefix. -/
theorem line_time_at_entry (phase : Fin 5 → Word n → Prop) (pre : Word n)
    {l r H : Nat} (leftPos : 0<l) (rightPos : 0<r) (leftSize : l≤H) (rightSize : r≤H)
    (left right : Nat → Fin n) :
    let R := ProductionClients.redirect g o (live (g:=g) o phase)
    let played := fun a => chooseBy R (emit (chooseBy R) [] (pre++a))
    IIDExpectedHittingTimeAtMost FenceComparison.mark
      (fun a => OpenFenceLine.count l left played a l=0 ∧ OpenFenceLine.count r right played a r=0)
      [] (128*n*H) := by
  dsimp only
  apply FenceLineTransfer.two_open_lines leftPos rightPos leftSize rightSize
  intro a e mid
  obtain ⟨u,f,v,eq,out⟩ := candidates_supply_bonds P o phase (pre++a) e mid
  exact ⟨u,f,v,eq,by simpa only [List.append_assoc] using out⟩

#print axioms line_time_at_entry
#print axioms candidates_supply_bonds
end
end L4.Height.CandidateResidence
