import Leader.L4.BStarRawCausalCut
import Leader.L4.BStarRawStopMax

namespace L4.BStarRawActualChildMoment
open Height BStarRawStopMax BStarRawStopCut BStarRawStopMoment
open BStarRawCausalCut BStarRawPublicationHistory
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireAnchors BStarLongFixedRouting
open BStarPhysicalLegitimate BStarPhysicalCoset BStarEpochLift
open BStarNativePortGeometry BStarNativeNeedLift Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- An actual first-crossing moment follows the maximum of the two
neighbor and one self predecessor crossings. Service is conditional on
the exact old raw prefix, even for an inherited in-flight controller. -/
theorem actual_child_moment {base initial : X}
    (hh : ∃ i,oldH6 B base i=true)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (period : 32∣P) (start : Fin n→Nat)
    (history : List (Fin n))
    (good : ∀ a : List (Fin n),
      let z := history++a
      ClockLegit hp base hh (run initial z) ∧
      RepresentsCoset hp base (run initial z) P (traceCount hp base initial hh start z) ∧
      Coherent hh (traceCount hp base initial hh start z))
    (i : Header (oldH6 B base)) (level L D : Nat) (positive : 0<L)
    (service : ∀ a K,
      rawReady hp (initial:=initial) hh start i level (history++a)=true →
      wordSum (fun w=>2^(publicationWait hp (run initial (history++a)) i.val w/L)) K≤2*n^K) :
    let T := fun (k : Nat) (j : Header (oldH6 B base)) =>
      firstTime (rawLevelTest hp (initial:=initial) hh start j k) history
    wordSum (fun w=>2^(T (level+1) i w/L)) D≤
      4*wordSum (fun w=>2^(max (T level i w)
        (max (T level (neighborHeader hh i 0) w) (T level (neighborHeader hh i 2) w))/L)) D := by
  dsimp only
  let test := fun j a=>rawLevelTest hp (initial:=initial) hh start j level (history++a)
  let W := fun a w=>publicationWait hp (run initial (history++a)) i.val w
  have mono (j) (a b) (H : test j a=true) : test j (a++b)=true := by
    unfold test at H ⊢
    rw [←List.append_assoc]
    exact rawLevelTest_mono hp hh start j level _ _ H
  let child := firstTime (rawLevelTest hp (initial:=initial) hh start i (level+1)) history
  have S : ∀ a K, threeReady (test (neighborHeader hh i 0)) (test (neighborHeader hh i 1))
      (test (neighborHeader hh i 2)) a=true →
      wordSum (fun w=>2^(W a w/L)) K≤2*n^K := service
  have zero (a : List (Fin n)) : W a []=0 := rfl
  have E (w : List (Fin n)) (_ : w.length=D) :
      child w≤atStop (threeReady (test (neighborHeader hh i 0)) (test (neighborHeader hh i 1))
        (test (neighborHeader hh i 2))) (fun h t v=>t+W h v) [] 0 w := by
    change child w≤atStop (fun h=>rawReady hp (initial:=initial) hh start i level (history++h))
      (fun h t v=>t+publicationWait hp (run initial (history++h)) i.val v) [] 0 w
    have shift := atStop_rebase (rawReady hp (initial:=initial) hh start i level)
      (fun h t v=>t+publicationWait hp (run initial h) i.val v) history [] 0 w
    rw [List.append_nil] at shift
    rw [shift]
    exact crossing_le_stopped_publication hp hh P M pos period start history w (fun a _=>good a) i level
  have cmp := child_moment _ _ _ (mono _) (mono _) (mono _) W L D positive S zero child E
  apply Nat.le_trans cmp
  apply Nat.mul_le_mul_left
  apply wordSum_mono
  intro w
  have shift (j) : firstTime (test j) [] w =
      firstTime (rawLevelTest hp (initial:=initial) hh start j level) history w := by
    unfold test
    simpa only [List.append_nil] using
      firstTime_rebase (rawLevelTest hp (initial:=initial) hh start j level) history [] w
  rw [shift,shift,shift,self_port hh i,Nat.max_left_comm]
  exact Nat.le_refl _

end L4.BStarRawActualChildMoment
