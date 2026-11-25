import Leader.L4.BStarRawCausalCrossing
import Leader.L4.BStarRawStopMax

/-! The literal clock-height threshold is the chronological raw stop
used by the finite-tape conditional moment interface. -/

namespace L4.BStarRawCausalCut
open BStarRawCausalCrossing BStarRawStopMax BStarRawStopCut BStarRawStopMoment BStarRawPublicationHistory Height
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireAnchors BStarLongFixedRouting BStarCycleGeometry
open BStarPhysicalIncrementLedger BStarIncrementLedger BStarPhysicalLiftAlignment
open BStarPhysicalLegitimate BStarPhysicalCoset BStarEpochLift BStarGrantWriterHistory
open BStarNativePointwise BStarNativePortGeometry BStarNativeNeedLift Compiler.Native
open Classical

/-- The list-indexed and prefix-recursive scanners select the same
threshold entrance time, including clipping to the horizon. -/
theorem firstTime_eq_firstCrossing {n : Nat} (height : List (Fin n)→Nat)
    (level : Nat) (h w : List (Fin n)) :
    firstTime (fun u=>decide (level≤height u)) h w =
      firstCrossing w.length (fun t=>height (h++w.take t)) level := by
  let s := fun u=>decide (level≤height u)
  let a := firstTime s h w
  let b := firstCrossing w.length (fun t=>height (h++w.take t)) level
  have ale : a≤w.length := firstTime_length s h w
  have ble : b≤w.length := firstCrossing_le _ _ _
  change a=b
  apply Nat.le_antisymm
  · by_cases H : b<w.length
    · apply firstTime_le
      exact decide_eq_true_eq.mpr (firstCrossing_reached _ _ _ H)
    · omega
  · by_cases H : a<w.length
    · obtain ⟨eq,term,_⟩ := split_spec s h w
      let split := splitStop s h w
      change w=split.1++split.2 at eq
      change s (h++split.1)=true ∨ split.2=[] at term
      have stopped : s (h++split.1)=true := by
        apply term.resolve_right
        intro E
        rw [E,List.append_nil] at eq
        exact (Nat.ne_of_lt H) (congrArg List.length eq).symm
      have E : w.take a=split.1 := by
        change w.take split.1.length=_
        rw [eq,List.take_append_of_le_length (Nat.le_refl _),List.take_length]
      apply firstCrossing_min _ _ _ a
      rw [E]
      exact decide_eq_true_eq.mp stopped
    · omega

/-- The tested prefix and remaining suffix are exactly the original
word's take/drop at the clipped first time. -/
theorem splitStop_eq_take_drop {n : Nat} (test : List (Fin n)→Bool) (h w : List (Fin n)) :
    splitStop test h w=(w.take (firstTime test h w),w.drop (firstTime test h w)) := by
  have eq := (split_spec test h w).1
  let s := splitStop test h w
  change w=s.1++s.2 at eq
  change s=(w.take s.1.length,w.drop s.1.length)
  rw [eq,List.take_append_of_le_length (Nat.le_refl _),List.take_length,List.drop_append,
    List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

noncomputable def rawLevelTest {base initial : X} (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (i : Header (oldH6 B base)) (level : Nat) (a : List (Fin n)) : Bool :=
  decide (level≤traceCount hp base initial hh start a i.val)

theorem rawLevelTest_mono {base initial : X} (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (i : Header (oldH6 B base)) (level : Nat)
    (a b : List (Fin n)) (hit : rawLevelTest hp (initial:=initial) hh start i level a=true) :
    rawLevelTest hp (initial:=initial) hh start i level (a++b)=true := by
  unfold rawLevelTest at hit ⊢
  apply decide_eq_true_eq.mpr
  have mono : traceCount hp base initial hh start a i.val≤traceCount hp base initial hh start (a++b) i.val := by
    rw [count_concat]
    unfold traceCount
    exact count_monotone (traceCount hp base initial hh start a)
      (tapeInc hp base hh (run initial a) b) i.val (Nat.zero_le b.length)
  exact Nat.le_trans (decide_eq_true_eq.mp hit) mono


noncomputable def rawReady {base initial : X} (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (i : Header (oldH6 B base)) (level : Nat) :
    List (Fin n)→Bool :=
  threeReady (rawLevelTest hp (initial:=initial) hh start (neighborHeader hh i 0) level)
    (rawLevelTest hp (initial:=initial) hh start (neighborHeader hh i 1) level)
    (rawLevelTest hp (initial:=initial) hh start (neighborHeader hh i 2) level)

theorem rawReady_firstTime {base initial : X} (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (i : Header (oldH6 B base)) (level : Nat)
    (history w : List (Fin n)) :
    let T := fun j : Header (oldH6 B base) =>
      firstCrossing w.length (fun t=>traceCount hp base initial hh start (history++w.take t) j.val) level
    firstTime (rawReady hp (initial:=initial) hh start i level) history w =
      max (T (neighborHeader hh i 0)) (max (T (neighborHeader hh i 1)) (T (neighborHeader hh i 2))) := by
  dsimp only [rawReady]
  rw [firstTime_threeReady _ _ _
    (rawLevelTest_mono hp (initial:=initial) hh start _ _)
    (rawLevelTest_mono hp (initial:=initial) hh start _ _)
    (rawLevelTest_mono hp (initial:=initial) hh start _ _)]
  unfold rawLevelTest
  rw [firstTime_eq_firstCrossing,firstTime_eq_firstCrossing,firstTime_eq_firstCrossing]


theorem rawLevelTest_initial {base initial : X} (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (i : Header (oldH6 B base)) (level : Nat) (history w : List (Fin n))
    (hit : level≤traceCount hp base initial hh start history i.val) :
    firstTime (rawLevelTest hp (initial:=initial) hh start i level) history w=0 := by
  have T := firstTime_le (rawLevelTest hp (initial:=initial) hh start i level)
    history w 0 (by simpa [rawLevelTest] using hit)
  omega

/-- A genuine missed threshold charges the entire horizon; an
attainment on the very last letter can also have this same time. -/
theorem rawLevelTest_horizon_of_miss {base initial : X} (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (i : Header (oldH6 B base)) (level : Nat) (history w : List (Fin n))
    (miss : traceCount hp base initial hh start (history++w) i.val < level) :
    firstTime (rawLevelTest hp (initial:=initial) hh start i level) history w=w.length := by
  let f := rawLevelTest hp (initial:=initial) hh start i level
  have le := firstTime_length f history w
  apply Nat.le_antisymm le
  apply Nat.le_of_not_gt
  intro h
  have H := true_after_time f (rawLevelTest_mono hp (initial:=initial) hh start i level)
    history w w.length h le
  have T : level≤traceCount hp base initial hh start (history++w) i.val := by
    simpa [f,rawLevelTest] using H
  omega

/-- Exact input to stopped moment composition: the child first time
is bounded by the stopped predecessor time plus a publication wait
charged on the true retained suffix and original old state. -/
theorem crossing_le_stopped_publication {base initial : X}
    (hh : ∃ i,oldH6 B base i=true)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (period : 32∣P) (start : Fin n→Nat)
    (history w : List (Fin n))
    (good : ∀ a : List (Fin n), a <+: w →
      let z := history++a
      ClockLegit hp base hh (run initial z) ∧
      RepresentsCoset hp base (run initial z) P (traceCount hp base initial hh start z) ∧
      Coherent hh (traceCount hp base initial hh start z))
    (i : Header (oldH6 B base)) (level : Nat) :
    firstTime (rawLevelTest hp (initial:=initial) hh start i (level+1)) history w ≤
      atStop (rawReady hp (initial:=initial) hh start i level)
        (fun h t rest=>t+publicationWait hp (run initial h) i.val rest) history 0 w := by
  unfold rawLevelTest
  rw [firstTime_eq_firstCrossing,atStop_eq_split,splitStop_eq_take_drop,Nat.zero_add]
  dsimp only
  rw [List.length_take,Nat.min_eq_left (firstTime_length _ _ _),rawReady_firstTime]
  exact crossing_le_ready_add_publicationWait hp hh P M pos period start history w good i level

#print axioms firstTime_eq_firstCrossing
#print axioms splitStop_eq_take_drop
#print axioms rawLevelTest_mono
#print axioms rawReady_firstTime
#print axioms crossing_le_stopped_publication
#print axioms rawLevelTest_horizon_of_miss

end L4.BStarRawCausalCut
