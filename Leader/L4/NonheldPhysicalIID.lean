import Leader.L4.NonheldPhysical
import Leader.L4.NonheldLaunchIID

namespace L4.NonheldPhysical
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarClearanceSource
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarResetChartTouch BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Physical three-door-hit bound from any nonheld H6 owner on the
unchanged IID raw tape. No intermediate no-reentry assumption. -/
theorem actual_nonheld_launch_expected (root : Fin n)
    (Q : X→Prop) (closed : ∀ y e,Q y→Q (step y e))
    (heads : ∀ y,Q y→oldH6 B y root=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (qx : Q x) (old : ¬Held (x root).long) :
    Height.IIDExpectedHittingTimeAtMost (IssueLaunchIID.observe hp root) (fun z=>z.2=true)
      (x,false) (3*n) :=
  NonheldLaunchIID.expected_of_no_reentry hp root Q closed heads sep
    (fun y e q away h=>no_reentry hp y root e (heads y q) away h) x qx old

/-- Same bound at the canonical K0 source of a fixed owner chart. -/
theorem chart_nonheld_launch_expected {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (qx : Q x)
    (old : ¬Held (x (S.getD 0 fall).1).long) :
    Height.IIDExpectedHittingTimeAtMost (IssueLaunchIID.observe hp (S.getD 0 fall).1)
      (fun z=>z.2=true) (x,false) (3*n) :=
  actual_nonheld_launch_expected hp (S.getD 0 fall).1 Q closed
    (fun y q=>(BStarResetChartService.root_header hp C (fiber y q)).1) sep x qx old

end L4.NonheldPhysical
