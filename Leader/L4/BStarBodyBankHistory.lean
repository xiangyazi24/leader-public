import Leader.L4.BStarCaptureInterval
import Leader.L4.BStarResetSchedule
import Leader.L4.BStarH6WordChart

namespace L4.BStarBodyBankHistory
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarH6WordChart BStarLongEvents BStarBankTrace BStarCaptureInterval

/-- Nonheader rows cannot commit their own selector. Even forged
payloads are covered; only active STAGE writes require custody. -/
theorem body_no_publication (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (s : Side)
    (body : (BStarLongCommand.geometry g s).axes.h6=false) :
    ∀ e∈(longTrace g raw).publications, e.endpoint≠s := by
  intro e M E
  obtain ⟨C,p,_,side,A⟩ := (literal_event_iff g raw e).mp M
  obtain ⟨_,Hdr,_,_,_,_,_,_⟩ := A
  have Cs : C.source.side=s := side.symm.trans E
  rw [Cs,body] at Hdr
  contradiction

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The remaining proof obligation at a body digit is precisely a
selected STAGE descriptor/center-selector implication. Whole-mark
protection does not assume one row per pair or omit scratch writes. -/
def BodyCustody (x : X) (e i : Fin n) (b : Fin 3) : Prop :=
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  ∀ s : Side, site e s=i →
    (BStarLongCommand.geometry g s).axes.h6=false ∧
    ∀ C p, (C,BStarLongCommand.Offer.advance p)∈offers g raw →
      C.source.side=s → StageLiveAt g raw b C p

theorem body_step (x : X) (e i : Fin n) (b : Fin 3) (he : e≠rightNeighbor e)
    (H : BodyCustody hp x e i b) :
    HeldStep b (x i).long (step x e i).long := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have pair (s : Side) (h : site e s=i) :
      HeldStep b (lane (sideFlag s) (x e,x (rightNeighbor e))).long
        (lane (sideFlag s) (largePair B (x e,x (rightNeighbor e)))).long := by
    obtain ⟨body,own⟩ := H s h
    exact BStarCaptureInterval.bStar_held_step k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) s b
      (safe_from_events g raw s b own (body_no_publication g raw s body))
  by_cases A : i=e
  · subst i
    have Y : step x e e=(largePair B (x e,x (rightNeighbor e))).1 := by
      simp only [AllSizeS1Geometry.step,if_true]
    rw [Y]
    exact pair .left rfl
  · by_cases C : i=rightNeighbor e
    · subst i
      have Y : step x e (rightNeighbor e)=(largePair B (x e,x (rightNeighbor e))).2 := by
        simp only [AllSizeS1Geometry.step,if_neg (Ne.symm he),if_true]
      rw [Y]
      exact pair .right rfl
    · have Y : step x e i=x i := by simp only [AllSizeS1Geometry.step,if_neg A,if_neg C]
      rw [Y]
      exact .noTouch _

private theorem held_concat {b : Fin 3} {x y z : BitVec LW}
    (H : HeldTrace b x y) (G : HeldTrace b y z) : HeldTrace b x z := by
  induction G with
  | empty => exact H
  | next _ one ih => exact .next ih one

/-- Exact physical digit-site lifting through a supplied history. The
caller supplies custody on old states, not equality of the readout. -/
theorem body_interval (sep : ∀ e : Fin n, e≠rightNeighbor e)
    (x : X) (i : Fin n) (b : Fin 3) (w : List (Fin n))
    (H : ∀ pre e tail, w=pre++e::tail → BodyCustody hp (run x pre) e i b) :
    HeldTrace b (x i).long ((run x w) i).long := by
  induction w generalizing x with
  | nil => exact .empty _
  | cons e w ih =>
    have localStep := body_step hp x e i b (sep e) (H [] e w rfl)
    have rest := ih (step x e) (fun pre f tail E => H (e::pre) f tail (congrArg (List.cons e) E))
    exact held_concat (.next (.empty _) localStep) rest

#print axioms body_no_publication
#print axioms body_interval
end L4.BStarBodyBankHistory
