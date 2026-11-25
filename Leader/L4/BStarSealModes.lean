import Leader.L4.BStarSealOwnerFrame
import Leader.L4.BStarGeneratedTapeCuts
import Leader.L4.BStarAcquireHistoryReturn

namespace L4.BStarSealModes
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongGrant BStarH6WordChart
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarSealOwnerFrame BStarAcquireVisitOrder BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def Past (center : Nat) (z : Cursor) : Prop :=
  ∀ j, z=.out j → center<j

private theorem past_step {len center : Nat} {a b : Cursor}
    (E : Advance len a b) (old : Past center a) : Past center b := by
  cases E with
  | stay c => exact old
  | forward k =>
    intro j L
    have distinct := old k rfl
    have eq := Cursor.out.inj L
    omega
  | turn =>
    intro _ C
    contradiction
  | reverse =>
    intro _ C
    contradiction

/-- A generated busy tour begun strictly beyond the center never again
has that outward cursor, including while turning and returning. -/
theorem past_prefix {base x : X} {addr : Nat→Pos n} {len op center : Nat}
    {w : List (Fin n)} {a b : Cursor}
    (T : BusyOnly hp base addr len op x a w b) (old : Past center a) :
    ∀ u v,w=u++v →
      ∃ z, Current hp base addr len (play x u) (.busy op z) ∧ Past center z := by
  induction T with
  | nil I =>
    intro u v W
    obtain ⟨rfl,_⟩ := List.append_eq_nil_iff.mp W.symm
    exact ⟨_,I,old⟩
  | @cons x a c b e w I E T ih =>
    intro u v W
    cases u with
    | nil => exact ⟨a,I,old⟩
    | cons f u =>
      obtain ⟨rfl,W'⟩ := List.cons.inj W
      have A : Advance len a c := by
        cases E with
        | transit _ _ _ _ Q =>
          cases Q with
          | cons _ _ A _ Q => cases Q; exact A
        | arrived_hold _ _ => exact .stay _
      exact ih (past_step A old) u v W'

theorem seal_after_center_safe (k : Nat) (z : Cursor) (P : Past k z) :
    Excluded k (.busy sealOp z) ∧ ∀ u, Mode.busy sealOp z≠.busy releaseOp u := by
  refine ⟨?_,?_⟩
  · intro _ _ E
    exact (Nat.lt_irrefl k) (P k (Mode.busy.inj E).2)
  · intro _ E
    exact (by decide : sealOp≠releaseOp) (Mode.busy.inj E).1

theorem bit_safe (k : Nat) (z : Cursor) :
    Excluded k (.busy bitOp z) ∧ ∀ u, Mode.busy bitOp z≠.busy releaseOp u := by
  refine ⟨?_,?_⟩
  · intro op W E
    have same := (Mode.busy.inj E).1
    subst op
    exact (by decide : ¬(bitOp=1 ∨ bitOp=stageOp ∨ bitOp=sealOp ∨ bitOp=commitOp)) W
  · intro _ E
    exact (by decide : bitOp≠releaseOp) (Mode.busy.inj E).1

theorem idle_safe (k : Nat) :
    Excluded k .idle ∧ ∀ u, Mode.idle≠.busy releaseOp u := by
  constructor
  · intro _ _ P; cases P
  · intro _ P; cases P

theorem commit_is_not_release (z : Cursor) :
    ∀ u, Mode.busy commitOp z≠.busy releaseOp u := by
  intro _ E
  exact (by decide : commitOp≠releaseOp) (Mode.busy.inj E).1

end L4.BStarSealModes
