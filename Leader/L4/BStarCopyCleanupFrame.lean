import Leader.L4.BStarCopyActiveEmpty
import Leader.L4.BStarCopyCleanupCoverage
import Leader.L4.BStarCopyPreIssueEmpty
import Leader.L4.BStarClearanceMobileOwner

namespace L4.BStarCopyCleanupFrame
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarLongCommand
open BStarLongFiberOwner BStarH6WordChart BStarClearanceDataChart
open BStarCopyOperand BStarClearanceMobileOwner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "P" => production k₁ k₂ t₂ J₁ J₂ r c p c₁
local notation "X" => Fin n → LargeSite P
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarCopyEntryGates BStarCopyActiveVacancy BStarLongFixedRouting BStarLongLiteral
private theorem fold_field (T : Lane → Prop) (A : List (At Sheet × Leaf))
    (s : At Sheet) (old : At Sheet → Lane)
    (start : T (old s))
    (safe : ∀ a, (s,a)∈A → ∀ L, T L → T (a.put L)) :
    T ((A.foldl update old) s) := by
  induction A generalizing old with
  | nil => exact start
  | cons a A ih =>
    apply ih
    · unfold update
      split
      · rename_i E
        apply safe a.2 _ _ start
        rcases a with ⟨z,t⟩
        change s=z at E
        subst z
        exact List.mem_cons_self
      · exact start
    · exact fun t m => safe t (List.mem_cons_of_mem _ m)


def Drained (v : Lane) : Prop := v.mobile=.empty ∧ v.retained=.empty

private theorem prep_drained (old : At Sheet → Lane) (a : BStarLongPrep.Offer)
    (S : a.claim.op≠.inject) (l : Leaf) (M : l∈(selectedEffects old a).writes)
    (v : Lane) (V : Drained v) : Drained (l.put v) := by
  unfold selectedEffects at M
  cases t : a.claim.op <;> simp [t,effects] at S M
  all_goals rcases M with rfl|M <;> try exact V
  all_goals repeat' first | rcases M with rfl|M
  all_goals simp_all [Drained,Leaf.put]

private theorem prep_closed (old : At Sheet → Lane) (a : BStarLongPrep.Offer)
    (S : a.claim.op≠.enable) (l : Leaf) (M : l∈(selectedEffects old a).writes)
    (v : Lane) (V : v.gate=false) : (l.put v).gate=false := by
  unfold selectedEffects at M
  cases t : a.claim.op <;> simp [t,effects] at S M
  any_goals split at M
  all_goals repeat' first | rcases M with rfl|M
  all_goals first | (rcases M with rfl|rfl <;> exact V) | simp_all [Leaf.put]
  rcases M with rfl|rfl <;> exact V

private theorem data_closed (g : Pair LongGeometry) (old : At Sheet→Lane)
    (d : DataClaim) (a : At Sheet) (l : Leaf) (M : (a,l)∈dataEffects g old d)
    (v : Lane) (V : v.gate=false) : (l.put v).gate=false := by
  cases l <;> try exact V
  unfold dataEffects at M
  rcases d with ⟨kind,src,dst⟩
  cases kind <;> cases dst <;> simp only [endEffects,hopEffects] at M
  all_goals repeat' first | split at M
  all_goals simp_all

private theorem data_drained (g : Pair LongGeometry) (old : At Sheet→Lane)
    (d : DataClaim) (a : At Sheet) (l : Leaf) (M : (a,l)∈dataEffects g old d)
    (safe : (old a).gate=false ∨ (old d.source).mobile=.empty)
    (v : Lane) (V : Drained v) : Drained (l.put v) := by
  rcases safe with closed|empty
  · unfold dataEffects at M
    rcases d with ⟨kind,src,dst⟩
    cases kind <;> cases dst <;> simp only [endEffects,hopEffects] at M
    all_goals repeat' first | split at M
    all_goals simp_all [Leaf.put,Drained]
    all_goals grind
  · rcases d with ⟨kind,src,dst⟩
    cases kind <;> cases dst <;> simp [dataEffects,endEffects,hopEffects,empty] at M

/-- A closed gate is preserved unless its own old-lane ENABLE wins. -/
theorem pair_closed (x : Pair (LargeSite P)) (a : At Sheet) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    (view raw a).gate=false →
    (∀ q∈(arbitration (round g raw).prep).1, q.claim.lane=a → q.claim.op≠.enable) →
    (view (Pair.map LargeSite.long (largePair B x)) a).gate=false := by
  dsimp only
  intro H no
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp,
      BStarLongCommandData.round_transfer]
  apply fold_field (fun v => v.gate=false) _ a _ H
  intro l M v V
  rcases List.mem_append.mp M with prep|data
  · obtain ⟨q,W,Q⟩ := List.mem_flatMap.mp prep
    obtain ⟨t,T,E⟩ := List.mem_map.mp Q
    obtain ⟨A,L⟩ := Prod.mk.inj E
    subst t
    exact prep_closed _ q (no q W A) l T v V
  · obtain ⟨d,_,Q⟩ := List.mem_flatMap.mp data
    exact data_closed _ _ d _ _ Q v V

/-- Closed receiver suffices for drain retention during the CLEAR tour.
After ENABLE, empty old data senders suffice instead. -/
theorem pair_drained (x : Pair (LargeSite P)) (a : At Sheet) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    Drained (view raw a) →
    (∀ q∈(arbitration (round g raw).prep).1, q.claim.lane=a → q.claim.op≠.inject) →
    ((view raw a).gate=false ∨ ∀ d∈orderedData g (reserved (round g raw).prep),
      a∈d.slots → (view raw d.source).mobile=.empty) →
    Drained (view (Pair.map LargeSite.long (largePair B x)) a) := by
  dsimp only
  intro H no safe
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp,
      BStarLongCommandData.round_transfer]
  apply fold_field Drained _ a _ H
  intro l M v V
  rcases List.mem_append.mp M with prep|data
  · obtain ⟨q,W,Q⟩ := List.mem_flatMap.mp prep
    obtain ⟨t,T,E⟩ := List.mem_map.mp Q
    obtain ⟨A,L⟩ := Prod.mk.inj E
    subst t
    exact prep_drained _ q (no q W A) l T v V
  · obtain ⟨d,D,Q⟩ := List.mem_flatMap.mp data
    exact data_drained _ _ d _ _ Q (safe.imp id (fun q => q d D (data_lane_claim _ _ d _ _ Q))) v V


theorem ring_closed (x : X) (e i : Fin n) (sh : Sheet) (sep : e≠rightNeighbor e)
    (H : (readLane (Sheet.index sh) (x i).long).gate=false)
    (no : ∀ q∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1,
      site e q.claim.lane.side=i → q.claim.lane.occurrence=sh → q.claim.op≠.enable)
 :
    (readLane (Sheet.index sh) (step x e i).long).gate=false := by
  have touch (s : Side) (E : site e s=i) : (readLane (Sheet.index sh) (step x e i).long).gate=false := by
    subst i
    have q := pair_closed hp (x e,x (rightNeighbor e)) (⟨s,sh⟩ : At Sheet)
      (by cases s <;> exact H) (fun a M Q => no a M
        (congrArg (fun z : At Sheet => site e z.side) Q) (congrArg At.occurrence Q))
      
    cases s <;> simpa [view,site,lane,BStarTrace.lane,Pair.map,AllSizeS1Geometry.step,Ne.symm sep] using q
  by_cases hL : i=e
  · exact touch .left hL.symm
  · by_cases hR : i=rightNeighbor e
    · exact touch .right hR.symm
    · simpa [AllSizeS1Geometry.step,hL,hR] using H

#print axioms ring_closed

theorem ring_drained (x : X) (e i : Fin n) (sh : Sheet) (sep : e≠rightNeighbor e)
    (H : Drained (readLane (Sheet.index sh) (x i).long))
    (no : ∀ q∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1,
      site e q.claim.lane.side=i → q.claim.lane.occurrence=sh → q.claim.op≠.inject)
    (safe : (readLane (Sheet.index sh) (x i).long).gate=false ∨
      let g := oldPair B x e
      let raw := ((x e).long,(x (rightNeighbor e)).long)
      ∀ d∈orderedData g (reserved (round g raw).prep),
        ∀ a∈d.slots, site e a.side=i → a.occurrence=sh → (view raw d.source).mobile=.empty) :
    Drained (readLane (Sheet.index sh) (step x e i).long) := by
  have touch (s : Side) (E : site e s=i) : Drained (readLane (Sheet.index sh) (step x e i).long) := by
    subst i
    have q := pair_drained hp (x e,x (rightNeighbor e)) (⟨s,sh⟩ : At Sheet)
      (by cases s <;> exact H) (fun a M Q => no a M
        (congrArg (fun z : At Sheet => site e z.side) Q) (congrArg At.occurrence Q))
      (safe.imp (by cases s <;> exact id) (fun N d M D => N d M _ D rfl rfl))
    cases s <;> simpa [view,site,lane,BStarTrace.lane,Pair.map,AllSizeS1Geometry.step,Ne.symm sep] using q
  by_cases hL : i=e
  · exact touch .left hL.symm
  · by_cases hR : i=rightNeighbor e
    · exact touch .right hR.symm
    · simpa [AllSizeS1Geometry.step,hL,hR] using H

#print axioms ring_drained
#print axioms pair_closed
#print axioms pair_drained
end L4.BStarCopyCleanupFrame
