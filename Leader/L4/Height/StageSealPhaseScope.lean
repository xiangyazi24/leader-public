import Leader.L4.Height.StageSealCursorCut
import Leader.L4.Height.StageToSealCenterFrame

namespace L4.Height.StageSealPhaseScope
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

private theorem adv {addr : Nat→Pos n} {len op : Nat} {x : X} {e : Fin n}
    {z d : Cursor} (E : Event hp addr len x e (.busy op z) (.busy op d)) : Advance len z d := by
  cases E with
  | arrived_hold _ _ => exact .stay _
  | transit _ _ _ _ S =>
    cases S with
    | cons _ _ A _ tail => cases tail; exact A

theorem rank_word {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)} (T : BusyOnly hp base addr len op x z w d) :
    rank len d≤rank len z := by
  induction T with
  | nil _ => exact Nat.le_refl _
  | cons I E _ ih => exact Nat.le_trans ih (rank_mono I.2.1 (adv hp E))

/-- All old states of this exact busy replay retain the opcode and have cursor
rank between the two literal endpoints. -/
theorem busy_premark {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)} (T : BusyOnly hp base addr len op x z w d)
    (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (W : w=u++e::v) :
    ∃ j, Current hp base addr len (play x u) (.busy op j) ∧
      rank len d≤rank len j ∧ rank len j≤rank len z := by
  subst w
  induction u generalizing x z with
  | nil =>
    cases T with
    | cons I E rest =>
      exact ⟨z,I,rank_word hp (.cons I E rest),Nat.le_refl _⟩
  | cons f u ih =>
    cases T with
    | cons I E rest =>
      obtain ⟨j,J,H,L⟩ := ih rest
      exact ⟨j,J,H,Nat.le_trans L (rank_mono I.2.1 (adv hp E))⟩

/-- The outbound post-STAGE tail (and its return) cannot revisit the STAGE center. -/
theorem post_stage_scope {base x : X} {addr : Nat→Pos n} {len k : Nat}
    (K : k<len) {w : List (Fin n)}
    (T : BusyOnly hp base addr len stageOp x (.out (k+1)) w (.back 0))
    (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (W : w=u++e::v) :
    ∃ m, Current hp base addr len (play x u) m ∧ BStarSealOwnerFrame.Excluded k m ∧
      (∀ a,m≠.busy releaseOp a) := by
  obtain ⟨j,I,_,HI⟩ := busy_premark hp T u e v W
  refine ⟨_,I,?_,?_⟩
  · intro _ _ E
    cases E
    simp only [rank] at HI
    omega
  · intro _ E
    cases E

/-- The pre-SEAL prefix is latch-free provided it has not yet landed at
center. Holds at center are not covered by this mode-only criterion. -/
theorem before_seal_scope {base x : X} {addr : Nat→Pos n} {len k l : Nat}
    (K : l<k) (KL : k≤len) {w : List (Fin n)}
    (T : BusyOnly hp base addr len sealOp x (.out 0) w (.out l))
    (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (W : w=u++e::v) :
    ∃ m, Current hp base addr len (play x u) m ∧ BStarSealOwnerFrame.Excluded k m ∧
      (∀ a,m≠.busy releaseOp a) := by
  obtain ⟨j,I,LO,_⟩ := busy_premark hp T u e v W
  refine ⟨_,I,?_,?_⟩
  · intro _ _ E
    cases E
    simp only [rank] at LO
    omega
  · intro _ E
    cases E

end L4.Height.StageSealPhaseScope
