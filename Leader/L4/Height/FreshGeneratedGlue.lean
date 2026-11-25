import Leader.L4.BStarGeneratedTapeCuts

namespace L4.Height.FreshGeneratedGlue
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarGeneratedOwner BStarAcquireVisitOrder

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "play" => BStarResetSchedule.run (AllSizeS1Geometry.step (n:=n) B)

/-- Generated language concatenation needs only the generated-history module. -/
theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {u v : List (Fin n)} {a b c : Mode} (U : GeneratedOwner hp base addr len x a u b)
    (V : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u ++ v) c := by
  induction U with
  | endpoint _ => exact V
  | next I E _ ih => exact .next I E (ih V)

end L4.Height.FreshGeneratedGlue
