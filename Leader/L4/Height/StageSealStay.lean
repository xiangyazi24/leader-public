import Leader.L4.Height.StageSealPhaseScope
import Leader.L4.BStarStagePast

namespace L4.Height.StageSealStay
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication BStarLongGrant
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarLongFixedRouting BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetChartService
open BStarSealBitDescriptor BStarAcquireHistoryReturn
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step
open BStarAcquireForwardTrace BStarSeparatingRail
open BStarSeparatingProgress BStarResetChartService BStarAcquireHistoryReturn BStarSealBitDescriptor BStarAcquireHistorySample

open BStarSealPackedFrame BStarAcquireForwardTrace BStarSeparatingRail BStarSeparatorControl
open BStarBankTrace (beforeOutgoing)

-- An actual selected center advance leaves a trail even when its payload is refused.
/-- If the actual post-mark owner still points at this outward position, no selected
old outgoing center row can have written its publication/latch bytes on that mark. -/
theorem no_latch_of_stay {base x : X} {addr : Nat→Pos n} {len k op : Nat}
    {i e : Fin n} (sep : e≠rightNeighbor e) (idx : addr k=(i,1))
    (I : Current hp base addr len (step x e) (.busy op (.out k))) :
    RingNoLatch hp x e i := by
  intro s hs C pay selected side atOne
  dsimp only
  intro _
  obtain ⟨left,trail⟩ := BStarStagePast.departure_trail hp x e sep C pay selected atOne
  have E : i=e := by
    rw [←side,left] at hs
    exact hs
  have F := I.2.1.2.1
  change anyTag.F (atCursor (step x e) (addr k)) at F
  rw [idx,E,trail] at F
  exact (BStarSeparatorParked.forward_not_trail F).elim

#print axioms no_latch_of_stay

/-- Whole real outward SEAL prefix ending at the old center cut.
If already at center, rank trapping forces a stay; its selected-row
absence follows from actual trail/forward disjointness, not mode alone. -/
theorem pre_seal_no_latch {base x : X} {addr : Nat→Pos n} {len k : Nat} {i : Fin n}
    (K : k≤len) (loc : addr k=(i,1)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {z : Cursor} {w : List (Fin n)}
    (T : BusyOnly hp base addr len sealOp x z w (.out k))
    (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (W : w=u++e::v) :
    ∃ m, Current hp base addr len (play x u) m ∧
      (BStarSealOwnerFrame.Excluded k m ∨ RingNoLatch hp (play x u) e i) ∧
      (∀ a,m≠.busy releaseOp a) := by
  subst w
  induction u generalizing x z with
  | nil =>
    cases T with
    | @cons _ z next _ e v I E rest =>
      refine ⟨_,I,?_,?_⟩
      · by_cases C : z=.out k
        · subst z
          have R := StageSealPhaseScope.rank_word hp rest
          have A : Advance len (.out k) next := by
            cases E with
            | transit _ _ _ _ seen =>
              cases seen with
              | cons _ _ h _ tail => cases tail; exact h
          cases A with
          | stay => exact .inr (no_latch_of_stay hp (sep e) loc (busy_start hp rest))
          | forward => simp only [rank] at R; omega
          | turn => simp only [rank] at R; omega
        · left
          intro _ _ H
          cases H
          exact C rfl
      · intro _ H
        cases H
  | cons f u ih =>
    cases T with
    | cons _ _ rest => exact ih rest

#print axioms pre_seal_no_latch
end L4.Height.StageSealStay
