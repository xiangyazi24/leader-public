import Leader.L4.BStarFenceTwoCandidates

namespace L4.BStarFencePhysicalDelivery
open AllSizeProtocol BStarTrace BStarLongWork BStarLongLayout
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarSteeringSupport BStarSteeredLikelihood BStarParkedSteering
open BStarFenceTwoCandidates

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Package the fixed-label receipt for every possible emitted prefix
under the actual fresh-only mask; no scheduler event is discarded.
The prefix is drawn from the original recovered physical base, not
just from the beginning of the FENCE reserve. -/
theorem physical_delivery {base : X} {hh : ∃ i,oldH6 B base i=true}
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e))
    (ready : ∀ x,Q x→BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (start : X) (qstart : Q start)
    {fresh : Word n→Fin n→Prop} {redirect : Word n→Fin n→Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (owners : ∀ a i, fresh a i → Nonempty (GateOwner hp base hh (run start a) i)) :
    ∀ b e u v, (∀ d∈v,d≠e) → e∈emit (chooseBy redirect) b (u++e::(v++[e])) := by
  have closedWords (x : X) (qx : Q x) (b : Word n) : Q (run x b) := by
    induction b generalizing x with
    | nil => exact qx
    | cons e b ih => exact ih _ (closed _ qx e)
  intro b e u v nv
  exact emits_by_second_hit hp Q fiber closed ready distinct start mask
    (fun a i F=>Classical.choice (owners a i F)) b u v e (closedWords start qstart b) nv

#print axioms physical_delivery
end L4.BStarFencePhysicalDelivery
