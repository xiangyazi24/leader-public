import Leader.Wu.Elimination.LabelFreeElimination
import Leader.Wu.RaceEntrance.UniformConsequences
import Leader.Core.LeaderCountDyadicTail
import Leader.Wu.Elimination.CyclicLayout
import Leader.Wu.Elimination.MinimumAttackGap

/-!
# Actual finite-carrier leader-count progress

The stopped tagged-deletion tree is compared, on the same raw scheduler
words, with the unstopped label-free transition on the existing `UCell`.
Every successful word loses an actual initial endpoint leader. Since this
row never creates leaders, the true physical leader count strictly drops
at its full physical endpoint, including every terminal padding symbol.

The ordered-pair mass keeps both physical gap lengths in its clock. This
module does not supply a bound of order `n^2/k` for that clock.
-/

namespace K2FiniteProgress

open StateBoundUnifiedCell LDSinkBoundedKernel LDTwoGapFrame
  LDSinkTwoGapNoResetKernel LDSinkTwoGapReachInvariant LDSinkGapCleanup
  FiniteUniformStoppingTree LabelFreeElimination

set_option autoImplicit false

variable {n ψ κ : Nat}

/-- The existing physical count, applied to the actual finite configuration. -/
abbrev count (C : Fin n → UCell ψ κ) : Nat :=
  K2GlobalGapClosure.physicalLeaderCount (physicalConfig C)

/-- The counted bits are precisely the output bits stored in the cells. -/
theorem count_eq_sum (C : Fin n → UCell ψ κ) :
    count C = (List.ofFn (fun i => if (C i).legacy.leader then 1 else 0)).sum := rfl

/-- The proof observation retains the exact physical count. -/
theorem count_eq_observe (C : Fin n → UCell ψ κ) :
    count C = K2GlobalGapClosure.physicalLeaderCount (observe C) := rfl

/-- A pointwise statement about the actual old and new leader bits. -/
def NoNewLeaders (C D : Fin n → UCell ψ κ) : Prop :=
  ∀ i, (C i).legacy.leader = false → (D i).legacy.leader = false

theorem noNew_refl (C : Fin n → UCell ψ κ) : NoNewLeaders C C := fun _ h => h

theorem noNew_trans {C D E : Fin n → UCell ψ κ}
    (hCD : NoNewLeaders C D) (hDE : NoNewLeaders D E) : NoNewLeaders C E :=
  fun i h => hDE i (hCD i h)

/-- Every input of the actual finite row preserves followers. -/
theorem step_noNew (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) : NoNewLeaders C (step hψ ring C e) := by
  intro i hi
  have h := K2GlobalGapClosure.rawStep_follower (by decide) ring (observe C) e i hi
  rw [← observe_step hψ ring C e] at h
  exact h

/-- Actual leader count is nonincreasing on all finite configurations. -/
theorem step_count_nonincrease (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) :
    count (step hψ ring C e) ≤ count C := by
  rw [count_eq_observe, count_eq_observe, observe_step]
  exact K2GlobalGapClosure.physical_count_nonincrease (by decide) ring (observe C) e

/-- No padding word can restore a deleted old leader. -/
theorem run_noNew (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) :
    NoNewLeaders C (run (step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact noNew_refl C
  | cons e es ih => exact noNew_trans (step_noNew hψ ring C e) (ih _)

/-- Count monotonicity follows along the literal physical scheduler word. -/
theorem run_count_nonincrease (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) :
    count (run (step hψ ring) C es) ≤ count C := by
  induction es generalizing C with
  | nil => exact Nat.le_refl _
  | cons e es ih => exact Nat.le_trans (ih _) (step_count_nonincrease hψ ring C e)

private theorem ofFn_sum_lt {m : Nat} (f g : Fin m → Nat)
    (hle : ∀ i, f i ≤ g i) (v : Fin m) (hv : f v < g v) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction m with
  | zero => exact Fin.elim0 v
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
    revert hv
    refine Fin.cases ?_ (fun j => ?_) v
    · intro hv
      have ht := ofFn_sum_le (fun i => f i.succ) (fun i => g i.succ)
        (fun i => hle i.succ)
      omega
    · intro hv
      have ht := ih (fun i => f i.succ) (fun i => g i.succ)
        (fun i => hle i.succ) j hv
      have hh := hle 0
      omega

/-- Losing one real old leader strictly lowers the physical sum when no
new leader bit appears anywhere else. -/
theorem lost_leader_count_lt {C D : Fin n → UCell ψ κ}
    (hnew : NoNewLeaders C D) (v : Fin n)
    (hp : (C v).legacy.leader = true) (hd : (D v).legacy.leader = false) :
    count D < count C := by
  rw [count_eq_sum, count_eq_sum]
  refine ofFn_sum_lt _ _ ?_ v ?_
  · intro i
    cases hc : (C i).legacy.leader
    · rw [hnew i hc]
      simp
    · cases (D i).legacy.leader <;> decide
  · simp [hp, hd]

/-- The three physically tagged endpoints are initially leaders. -/
def PairPresent (F : TwoGapFrame n) (C : Fin n → UCell ψ κ) : Prop :=
  GapEndpointsPresent F.recovery (physicalConfig C) ∧
    GapEndpointsPresent F.attack (physicalConfig C)

theorem pairPresent_of_gapPair (F : TwoGapFrame n) (C : Fin n → UCell ψ κ)
    (phase : APhase) (hg : GapPair (by decide) F ⟨observe C, phase⟩) :
    PairPresent F C := ⟨hg.recovery.1, hg.attack.1⟩

/-- Tagged success names a real initial leader that is now absent. -/
theorem success2_lost_initial (F : TwoGapFrame n) {C D : Fin n → UCell ψ κ}
    (hp : PairPresent F C) (hs : NoResetSuccess F (physicalConfig D)) :
    ∃ v : Fin n,
      (v = F.recovery.pos 0 ∨ v = F.attack.pos 0 ∨ v = F.attack.pos F.attack.d) ∧
      (C v).legacy.leader = true ∧ (D v).legacy.leader = false := by
  rcases (success2_covers_three F (physicalConfig D) F.shared).mp hs with hi | hj | hk
  · exact ⟨F.recovery.pos 0, Or.inl rfl, hp.1.1, hi⟩
  · exact ⟨F.attack.pos 0, Or.inr (Or.inl rfl), hp.2.1, hj⟩
  · exact ⟨F.attack.pos F.attack.d, Or.inr (Or.inr rfl), hp.2.2, hk⟩

theorem success2_count_lt (F : TwoGapFrame n) {C D : Fin n → UCell ψ κ}
    (hp : PairPresent F C) (hnew : NoNewLeaders C D)
    (hs : NoResetSuccess F (physicalConfig D)) : count D < count C := by
  obtain ⟨v, _, hv, hd⟩ := success2_lost_initial F hp hs
  exact lost_leader_count_lt hnew v hv hd

theorem success2_step (hψ : 0 < ψ) (F : TwoGapFrame n)
    (D : Fin n → UCell ψ κ) (e : Fin n)
    (hs : NoResetSuccess F (physicalConfig D)) :
    NoResetSuccess F (physicalConfig (step hψ F.attack.ring D e)) := by
  rw [success2_covers_three F _ F.shared] at hs ⊢
  rcases hs with hi | hj | hk
  · exact Or.inl (step_noNew hψ F.attack.ring D e _ hi)
  · exact Or.inr (Or.inl (step_noNew hψ F.attack.ring D e _ hj))
  · exact Or.inr (Or.inr (step_noNew hψ F.attack.ring D e _ hk))

noncomputable section

/-- Relate a stopped tagged tree to its unstopped physical endpoint. Even
after success, actual physical states and every remaining raw edge remain. -/
def Tracks (F : TwoGapFrame n) (C : Fin n → UCell ψ κ)
    (u : StopNode (Fin n → UCell ψ κ)) (D : Fin n → UCell ψ κ) : Prop :=
  NoNewLeaders C D ∧ match u with
    | .active E => E = D
    | .success => NoResetSuccess F (physicalConfig D)
    | .failure => True

theorem tracks_initial (F : TwoGapFrame n) (C : Fin n → UCell ψ κ) :
    Tracks F C (.active C) C := ⟨noNew_refl C, rfl⟩

/-- One original edge advances both representations with the same symbol. -/
theorem tracks_step (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (u : StopNode (Fin n → UCell ψ κ))
    (D : Fin n → UCell ψ κ) (ht : Tracks F C u D) (e : Fin n) :
    Tracks F C (stepNode (blockStep hψ F) u e) (step hψ F.attack.ring D e) := by
  rcases ht with ⟨hnew, ht⟩
  refine ⟨noNew_trans hnew (step_noNew hψ F.attack.ring D e), ?_⟩
  cases u with
  | active E =>
    change E = D at ht
    subst E
    by_cases hs : NoResetSuccess F (physicalConfig (step hψ F.attack.ring D e))
    · simpa only [stepNode, blockStep, if_pos hs] using hs
    · simp only [stepNode, blockStep, if_neg hs]
  | success => exact success2_step hψ F D e ht
  | failure => trivial

/-- The entire same raw word tracks the actual finite configuration,
including any suffix after the stopped process has already succeeded. -/
theorem tracks_word (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (u : StopNode (Fin n → UCell ψ κ))
    (D : Fin n → UCell ψ κ) (ht : Tracks F C u D) (es : List (Fin n)) :
    Tracks F C (ControlledSchedulerMass.runWord (blockStep hψ F) u es)
      (run (step hψ F.attack.ring) D es) := by
  induction es generalizing u D with
  | nil => exact ht
  | cons e es ih => exact ih _ _ (tracks_step hψ F C u D ht e)

/-- Each successful literal word removes a particular original endpoint
leader in the actual finite execution, with no restart or clock change. -/
theorem successful_word_deletes_initial_leader (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (hp : PairPresent F C) (es : List (Fin n))
    (hs : ControlledSchedulerMass.runWord (blockStep hψ F) (.active C) es = .success) :
    ∃ v : Fin n,
      (v = F.recovery.pos 0 ∨ v = F.attack.pos 0 ∨ v = F.attack.pos F.attack.d) ∧
      (C v).legacy.leader = true ∧
      (run (step hψ F.attack.ring) C es v).legacy.leader = false := by
  have ht := tracks_word hψ F C (.active C) C (tracks_initial F C) es
  rw [hs] at ht
  exact success2_lost_initial F hp ht.2

theorem successful_word_count_strict (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (hp : PairPresent F C) (es : List (Fin n))
    (hs : ControlledSchedulerMass.runWord (blockStep hψ F) (.active C) es = .success) :
    count (run (step hψ F.attack.ring) C es) < count C := by
  obtain ⟨v, _, hv, hd⟩ := successful_word_deletes_initial_leader hψ F C hp es hs
  exact lost_leader_count_lt (run_noNew hψ F.attack.ring C es) v hv hd

private theorem tracked_tree_le (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (hp : PairPresent F C) (T : Nat)
    (u : StopNode (Fin n → UCell ψ κ)) (D : Fin n → UCell ψ κ)
    (ht : Tracks F C u D) :
    treeWeight (blockStep hψ F) successWeight u T ≤
      LeaderCountDyadicTail.wordSum (step hψ F.attack.ring)
        (fun E => if count E < count C then 1 else 0) D T := by
  induction T generalizing u D with
  | zero =>
    cases u with
    | active E => exact Nat.zero_le _
    | failure => exact Nat.zero_le _
    | success =>
      have hdrop := success2_count_lt F hp ht.1 ht.2
      simp only [treeWeight, successWeight, LeaderCountDyadicTail.wordSum_zero, if_pos hdrop]
      exact Nat.le_refl _
  | succ T ih =>
    exact ofFn_sum_le _ _ (fun e => ih _ _ (tracks_step hψ F C u D ht e))

/-- Convert the actual stopped success numerator to the exact strict-count
drop numerator consumed by the dyadic theorem, at the same physical time. -/
theorem successCount_le_physical_count_drop (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (hp : PairPresent F C) (T : Nat) :
    successCount (blockStep hψ F) (.active C) T ≤
      LeaderCountDyadicTail.wordSum (step hψ F.attack.ring)
        (fun D => if count D < count C then 1 else 0) C T :=
  tracked_tree_le hψ F C hp T (.active C) C (tracks_initial F C)

/-- Ordered physical GapPairs give a strict drop of the actual finite-cell
leader count with constant raw-word mass. Both gap costs remain explicit. -/
theorem ordered_pair_count_drop_mass (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ)
    (hg : GapPair (by decide) F ⟨observe C, .transit⟩)
    (hab : F.attack.d ≤ F.recovery.d) :
    n ^ (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) ≤
      (16 * 2 ^ LDSinkTwoGapRaceEntranceUniformMass.uniformCollapseBudget) *
        LeaderCountDyadicTail.wordSum (step hψ F.attack.ring)
          (fun D => if count D < count C then 1 else 0) C
          (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) := by
  have hm := LDSinkTwoGapRaceEntranceUniformMass.gapPair_uniform_deletion_mass
    (by decide) F ⟨observe C, .transit⟩ hg hab
  rw [← successCount_eq hψ F C .transit] at hm
  exact Nat.le_trans hm (Nat.mul_le_mul_left _
    (successCount_le_physical_count_drop hψ F C (pairPresent_of_gapPair F C .transit hg) _))

/-- The simple pair-span clock is still the original scheduler clock. -/
theorem ordered_pair_count_drop_at_span (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ)
    (hg : GapPair (by decide) F ⟨observe C, .transit⟩)
    (hab : F.attack.d ≤ F.recovery.d) :
    n ^ (19 * n * (F.recovery.d + F.attack.d)) ≤
      (16 * 2 ^ LDSinkTwoGapRaceEntranceUniformMass.uniformCollapseBudget) *
        LeaderCountDyadicTail.wordSum (step hψ F.attack.ring)
          (fun D => if count D < count C then 1 else 0) C
          (19 * n * (F.recovery.d + F.attack.d)) := by
  have hm := LDSinkTwoGapRaceEntranceUniformConsequences.gapPair_uniform_deletion_at_span
    (by decide) F ⟨observe C, .transit⟩ hg hab
  rw [← successCount_eq hψ F C .transit] at hm
  exact Nat.le_trans hm (Nat.mul_le_mul_left _
    (successCount_le_physical_count_drop hψ F C (pairPresent_of_gapPair F C .transit hg) _))

/-- The global signal invariant produces the required actual GapPair from
the selected physical endpoints and interiors. No labels or ready race are
required; only the ordering of the two physical gap lengths remains. -/
theorem selected_pair_count_drop_at_span (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (F : TwoGapFrame n)
    (hrE : GapEndpointsPresent F.recovery (physicalConfig C))
    (hrI : GapInteriorFollowers F.recovery (physicalConfig C))
    (haE : GapEndpointsPresent F.attack (physicalConfig C))
    (haI : GapInteriorFollowers F.attack (physicalConfig C))
    (hab : F.attack.d ≤ F.recovery.d) :
    n ^ (19 * n * (F.recovery.d + F.attack.d)) ≤
      (16 * 2 ^ LDSinkTwoGapRaceEntranceUniformMass.uniformCollapseBudget) *
        LeaderCountDyadicTail.wordSum (step hψ F.attack.ring)
          (fun D => if count D < count C then 1 else 0) C
          (19 * n * (F.recovery.d + F.attack.d)) :=
  ordered_pair_count_drop_at_span hψ F C
    (selected_gapPair ring C hC F hrE hrI haE haI .transit) hab

/-- The actual physical leader enumeration and minimum-attack selector
produce an ordered pair from every global state with at least three leaders.
The recovered gap length is not discarded by the average attack bound. -/
theorem signalGlobal_ordered_pair (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (hk : 3 ≤ count C) :
    ∃ F : TwoGapFrame n,
      F.attack.d ≤ F.recovery.d ∧ count C * F.attack.d ≤ n ∧
      ∀ phase : APhase, GapPair (by decide) F ⟨observe C, phase⟩ := by
  have hG : K2GlobalGapClosure.GlobalClass (by decide) ring (count C) (observe C) :=
    ⟨by omega, (count_eq_observe C).symm, hC⟩
  obtain ⟨L, hE, hI, _⟩ := K2CyclicLayout.exists_realizing_layout (by decide) ring (observe C) hG
  exact K2MinimumAttack.select_minimum_attack (by decide) ring (count C) hk
    (observe C) hC L hE hI

/-- A state-uniform physical count-drop block on the closed signal domain.
The derived clock is the coarse `19*n*n`; no inverse-count improvement is
asserted. Pair selection and the success-to-count conversion are both proved. -/
theorem signalGlobal_count_drop_mass (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (hk : 3 ≤ count C) :
    n ^ (19 * n * n) ≤
      (16 * 2 ^ LDSinkTwoGapRaceEntranceUniformMass.uniformCollapseBudget) *
        LeaderCountDyadicTail.wordSum (step hψ ring)
          (fun D => if count D < count C then 1 else 0) C (19 * n * n) := by
  obtain ⟨F, hab, _, hg⟩ := signalGlobal_ordered_pair ring C hC hk
  have htime : 19 * n * (F.recovery.d + F.attack.d) ≤ 19 * n * n :=
    Nat.mul_le_mul_left (19 * n) (Nat.le_of_lt F.length_lt)
  exact LeaderCountDyadicTail.pad_deletion_mass (step hψ F.attack.ring) count
    (step_count_nonincrease hψ F.attack.ring) C _
    (19 * n * (F.recovery.d + F.attack.d)) (19 * n * n) htime
    (ordered_pair_count_drop_at_span hψ F C (hg .transit) hab)

/-- Direct consumption by the proved dyadic-bin theorem on the actual
closed finite carrier. The displayed numerator is still the original
physical word sum, with a coarse quadratic cost for each deletion block. -/
theorem signalGlobal_bin_tail (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C)
    (m s : Nat) (hm : 2 ≤ m) (hk : count C ≤ 2 * m) :
    2 ^ s * LeaderCountDyadicTail.wordSum (step hψ ring)
      (fun D => LeaderCountDyadicTail.binMiss m (count D)) C
      ((m + s) * (2 * (16 * 2 ^ LDSinkTwoGapRaceEntranceUniformMass.uniformCollapseBudget) *
        (19 * n * n))) ≤
      n ^ ((m + s) * (2 * (16 * 2 ^ LDSinkTwoGapRaceEntranceUniformMass.uniformCollapseBudget) *
        (19 * n * n))) := by
  let Q := 16 * 2 ^ LDSinkTwoGapRaceEntranceUniformMass.uniformCollapseBudget
  let closed : ∀ (D : Fin n → UCell ψ κ) (e : Fin n),
      SignalGlobal ring D → SignalGlobal ring (step hψ ring D e) :=
    fun D e hD => signalGlobal_step hψ ring D hD e
  let stepP := LeaderCountDyadicTail.restrictedStep (step hψ ring) (SignalGlobal ring) closed
  have hmass : ∀ D : {D : Fin n → UCell ψ κ // SignalGlobal ring D},
      m < count D.val → count D.val ≤ 2 * m →
      n ^ (19 * n * n) ≤ Q * LeaderCountDyadicTail.wordSum stepP
        (fun E => if count E.val < count D.val then 1 else 0) D (19 * n * n) := by
    intro D hD _
    rw [LeaderCountDyadicTail.wordSum_restrict (step hψ ring) (SignalGlobal ring) closed
      (fun E : Fin n → UCell ψ κ => if count E < count D.val then 1 else 0)
      (19 * n * n) D]
    exact signalGlobal_count_drop_mass hψ ring D.val D.property (by omega)
  have hQ : 1 ≤ Q := Nat.mul_pos (by decide) (Nat.two_pow_pos _)
  have ht := LeaderCountDyadicTail.bin_tail stepP (fun D => count D.val)
    m (19 * n * n) Q s hQ
    (fun D e => step_count_nonincrease hψ ring D.val e) hmass ⟨C, hC⟩ hk
  rw [LeaderCountDyadicTail.wordSum_restrict (step hψ ring) (SignalGlobal ring) closed
    (fun D : Fin n → UCell ψ κ => LeaderCountDyadicTail.binMiss m (count D))
    ((m + s) * (2 * Q * (19 * n * n))) ⟨C, hC⟩] at ht
  exact ht

/-- A nondivisible finite-carrier example has three actual initial leaders
and consumes the proved count-drop mass without any ready-state premise. -/
theorem seed7_count_drop :
    count NondivisibleExample.seed7 = 3 ∧
    7 ^ (19 * 7 * (NondivisibleExample.frame7.recovery.d + NondivisibleExample.frame7.attack.d)) ≤
      (16 * 2 ^ LDSinkTwoGapRaceEntranceUniformMass.uniformCollapseBudget) *
        LeaderCountDyadicTail.wordSum
          (step (by decide) NondivisibleExample.frame7.attack.ring)
          (fun D => if count D < count NondivisibleExample.seed7 then 1 else 0)
          NondivisibleExample.seed7
          (19 * 7 * (NondivisibleExample.frame7.recovery.d + NondivisibleExample.frame7.attack.d)) :=
  ⟨by decide, ordered_pair_count_drop_at_span (by decide) NondivisibleExample.frame7
    NondivisibleExample.seed7 NondivisibleExample.seed7_gapPair (by decide)⟩

/-- A literal two-edge execution reduces the physical output count from
two to one on a ring whose physical label modulus does not divide its size. -/
theorem seed5_true_count_deletion :
    count NondivisibleExample.seed5 = 2 ∧
    count (run (step (by decide) NondivisibleExample.ring5)
      NondivisibleExample.seed5 [3, 2]) = 1 := by decide

/-- A real three-leader finite state with arbitrary physical labels and
zero signal bits. It witnesses the domain of the state-uniform theorem. -/
def threeLeaderSeed (i : Fin 7) : UCell 2 1 :=
  { NondivisibleExample.seed7 i with
    legacy := { (NondivisibleExample.seed7 i).legacy with signal_B := 0 } }

theorem threeLeaderSeed_global :
    SignalGlobal NondivisibleExample.frame7.attack.ring threeLeaderSeed := by
  apply signalGlobal_of_signals_zero
  · unfold K2GlobalGapClosure.Separated
    decide
  · intro i
    rfl

theorem signalGlobal_three_domain_nonempty :
    ∃ C : Fin 7 → UCell 2 1,
      SignalGlobal NondivisibleExample.frame7.attack.ring C ∧ count C = 3 :=
  ⟨threeLeaderSeed, threeLeaderSeed_global, by decide⟩

end

end K2FiniteProgress

#print axioms K2FiniteProgress.step_count_nonincrease
#print axioms K2FiniteProgress.run_count_nonincrease
#print axioms K2FiniteProgress.successful_word_deletes_initial_leader
#print axioms K2FiniteProgress.successful_word_count_strict
#print axioms K2FiniteProgress.successCount_le_physical_count_drop
#print axioms K2FiniteProgress.ordered_pair_count_drop_mass
#print axioms K2FiniteProgress.ordered_pair_count_drop_at_span
#print axioms K2FiniteProgress.selected_pair_count_drop_at_span
#print axioms K2FiniteProgress.signalGlobal_ordered_pair
#print axioms K2FiniteProgress.signalGlobal_count_drop_mass
#print axioms K2FiniteProgress.signalGlobal_bin_tail
#print axioms K2FiniteProgress.seed7_count_drop
#print axioms K2FiniteProgress.seed5_true_count_deletion
#print axioms K2FiniteProgress.signalGlobal_three_domain_nonempty
