import Leader.Wu.Seal.UniformScheduler

/-!
# Mixed-state restart producer for the seal sweep

The five-case seal overlay has a conserved token balance.  Write `B` for an
open leader and `D` for an open follower.  Every launch creates one `B` and
one `D`, every return consumes one of each, and the two propagation rules move
one `D` without changing the number of `B` tokens.  Thus every descendant of
a positive all-closed start satisfies `#B = #D` and still contains a leader.

For a mixed balanced state, choose a `D`--`B` pair of minimum positive
clockwise distance.  If the distance is one, the return transition closes the
pair.  Otherwise the successor of that `D` is closed: an intervening `B` or
`D` would contradict minimality.  One propagation interaction therefore
reduces the minimum distance.  The lexicographic potential

`(# open leaders, minimum positive D--B distance)`

strictly decreases until every seal is closed.  The existing positive
all-closed landing theorem then reaches semantic safety.  The proof below is
about the exact `P_partialSealSweep` transition and adds no carrier state.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepMixedNormalizerSol

open PPLL PPLLResearchFormulation
open PPLLNoCheckBirthConditionTwoGeometry
open PPartialDynamicSweepLockSol
open PPartialDynamicSweepResetSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol
open PPartialSealSweepUniformSchedulerSol
open PPLLClosedDomainSchedulerAmplificationSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Finite counts and the conserved open-token balance -/

private def finNatSum {m : Nat} (f : Fin m → Nat) : Nat :=
  (List.ofFn f).sum

private theorem finNatSum_succ {m : Nat} (f : Fin (m + 1) → Nat) :
    finNatSum f = f 0 + finNatSum (fun i : Fin m => f i.succ) := by
  unfold finNatSum
  rw [List.ofFn_succ, List.sum_cons]

/-- Replacing one coordinate gives the exact additive accounting identity. -/
private theorem finNatSum_single_change {m : Nat}
    (before after : Fin m → Nat) (victim : Fin m)
    (hother : ∀ i : Fin m, i ≠ victim → after i = before i) :
    finNatSum after + before victim =
      finNatSum before + after victim := by
  induction m with
  | zero => exact Fin.elim0 victim
  | succ m ih =>
      rw [finNatSum_succ, finNatSum_succ]
      cases victim using Fin.cases with
      | zero =>
          have htail :
              (fun i : Fin m => after i.succ) =
                fun i : Fin m => before i.succ := by
            funext i
            exact hother i.succ (Fin.succ_ne_zero i)
          rw [htail]
          omega
      | succ victim =>
          have hhead : after 0 = before 0 :=
            hother 0 (fun h => Fin.succ_ne_zero victim h.symm)
          have htail := ih
            (fun i : Fin m => before i.succ)
            (fun i : Fin m => after i.succ)
            victim
            (fun i hi => hother i.succ (fun h => hi (Fin.succ_inj.mp h)))
          rw [hhead]
          omega

/-- Two-coordinate replacement accounting, used for every nontrivial local
interaction on a ring with at least two sites. -/
private theorem finNatSum_pair_change {m : Nat}
    (before after : Fin m → Nat) (left right : Fin m)
    (hne : left ≠ right)
    (hother : ∀ i : Fin m, i ≠ left → i ≠ right →
      after i = before i) :
    finNatSum after + before left + before right =
      finNatSum before + after left + after right := by
  let middle : Fin m → Nat := fun i =>
    if i = left then after i else before i
  have hfirst := finNatSum_single_change before middle left (by
    intro i hi
    simp [middle, hi])
  have hfirst' : finNatSum middle + before left =
      finNatSum before + after left := by
    simpa [middle] using hfirst
  have hmiddleRight : middle right = before right := by
    have hrne : right ≠ left := fun h : right = left => hne h.symm
    simp [middle, hrne]
  have hsecond := finNatSum_single_change middle after right (by
    intro i hi
    by_cases hil : i = left
    · subst i
      simp [middle]
    · rw [hother i hil hi]
      simp [middle, hil])
  rw [hmiddleRight] at hsecond
  omega

private def openLeaderBit (u : SealSweepState psi kappa tau) : Bool :=
  sweepLockLeader u && !u.2

private def openFollowerBit (u : SealSweepState psi kappa tau) : Bool :=
  !sweepLockLeader u && !u.2

/-- Number of open leaders (`B` tokens). -/
def sealSweepOpenLeaderCount
    (C : SealSweepConfig n psi kappa tau) : Nat :=
  finNatSum (fun i => if openLeaderBit (C i) then 1 else 0)

/-- Number of open followers (`D` tokens). -/
def sealSweepOpenFollowerCount
    (C : SealSweepConfig n psi kappa tau) : Nat :=
  finNatSum (fun i => if openFollowerBit (C i) then 1 else 0)

/-- The launch/return conservation law visible in every reachable mixed
configuration. -/
def SealSweepOpenBalanced
    (C : SealSweepConfig n psi kappa tau) : Prop :=
  sealSweepOpenLeaderCount C = sealSweepOpenFollowerCount C

private theorem openLeaderBit_eq_true_iff
    (u : SealSweepState psi kappa tau) :
    openLeaderBit u = true ↔
      sweepLockLeader u = true ∧ u.2 = false := by
  simp [openLeaderBit]

private theorem openFollowerBit_eq_true_iff
    (u : SealSweepState psi kappa tau) :
    openFollowerBit u = true ↔
      sweepLockLeader u = false ∧ u.2 = false := by
  simp [openFollowerBit]

private theorem finNatSum_bool_eq_zero_iff {m : Nat}
    (bits : Fin m → Bool) :
    finNatSum (fun i => if bits i then 1 else 0) = 0 ↔
      ∀ i, bits i = false := by
  induction m with
  | zero => simp [finNatSum]
  | succ m ih =>
      rw [finNatSum_succ]
      constructor
      · intro h
        have hhead : bits 0 = false := by
          cases hbit : bits 0 <;> simp_all
        have htail : finNatSum
            (fun i : Fin m => if bits i.succ then 1 else 0) = 0 := by
          simp [hhead] at h
          omega
        have hall := (ih (fun i : Fin m => bits i.succ)).1 htail
        intro i
        cases i using Fin.cases with
        | zero => exact hhead
        | succ i => exact hall i
      · intro hall
        have hhead := hall (0 : Fin (m + 1))
        have htail : ∀ i : Fin m, bits i.succ = false :=
          fun i => hall i.succ
        rw [(ih (fun i : Fin m => bits i.succ)).2 htail]
        simp [hhead]

private theorem finNatSum_bool_pos_iff {m : Nat}
    (bits : Fin m → Bool) :
    0 < finNatSum (fun i => if bits i then 1 else 0) ↔
      ∃ i, bits i = true := by
  constructor
  · intro hpos
    apply Classical.byContradiction
    intro hnone
    have hall : ∀ i, bits i = false := by
      intro i
      cases h : bits i
      · rfl
      · exact False.elim (hnone ⟨i, h⟩)
    have hzero := (finNatSum_bool_eq_zero_iff bits).2 hall
    omega
  · rintro ⟨i, hi⟩
    apply Nat.pos_of_ne_zero
    intro hzero
    have hall := (finNatSum_bool_eq_zero_iff bits).1 hzero
    have hfalse := hall i
    rw [hi] at hfalse
    exact Bool.noConfusion hfalse

theorem openLeaderCount_pos_iff
    (C : SealSweepConfig n psi kappa tau) :
    0 < sealSweepOpenLeaderCount C ↔
      ∃ i : Fin n,
        sweepLockLeader (C i) = true ∧ (C i).2 = false := by
  rw [sealSweepOpenLeaderCount, finNatSum_bool_pos_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (openLeaderBit_eq_true_iff (C i)).1 hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (openLeaderBit_eq_true_iff (C i)).2 hi⟩

theorem openFollowerCount_pos_iff
    (C : SealSweepConfig n psi kappa tau) :
    0 < sealSweepOpenFollowerCount C ↔
      ∃ i : Fin n,
        sweepLockLeader (C i) = false ∧ (C i).2 = false := by
  rw [sealSweepOpenFollowerCount, finNatSum_bool_pos_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (openFollowerBit_eq_true_iff (C i)).1 hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (openFollowerBit_eq_true_iff (C i)).2 hi⟩

theorem sealSweepOpenLeaderCount_le
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepOpenLeaderCount C ≤ n := by
  induction n with
  | zero => simp [sealSweepOpenLeaderCount, finNatSum]
  | succ n ih =>
      rw [sealSweepOpenLeaderCount, finNatSum_succ]
      have htail := ih (C := fun i : Fin n => C i.succ)
      unfold sealSweepOpenLeaderCount at htail
      have htail' : finNatSum
          (fun i : Fin n =>
            if openLeaderBit (C i.succ) then 1 else 0) ≤ n := by
        simpa using htail
      split <;> omega

private theorem sealSweep_localStep_eq_self_of_one
    (ring : DirectedRing n) (hn : n = 1)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) :
    localStep ring P_partialSealSweep C e = C := by
  have hall : ∀ a b : Fin n, a = b := by
    intro a b
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    omega
  have hj : ring.rightNeighbor e = e := hall _ _
  funext i
  have hi : i = e := hall _ _
  subst i
  simp only [localStep, if_pos]
  rw [hj]
  cases hl : sweepLockLeader (C e) <;>
    cases hc : (C e).2
  all_goals
    apply Prod.ext
    · simp [P_partialSealSweep, hl, hc]
    · simp [P_partialSealSweep, hl, hc]

private theorem openLeaderCount_pair_change
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) :
    let j := ring.rightNeighbor e
    let D := localStep ring P_partialSealSweep C e
    sealSweepOpenLeaderCount D +
        (if openLeaderBit (C e) then 1 else 0) +
        (if openLeaderBit (C j) then 1 else 0) =
      sealSweepOpenLeaderCount C +
        (if openLeaderBit (D e) then 1 else 0) +
        (if openLeaderBit (D j) then 1 else 0) := by
  let j := ring.rightNeighbor e
  let D := localStep ring P_partialSealSweep C e
  have hne : e ≠ j := by
    intro h
    exact rightNeighbor_ne_self_of_one_lt ring hn e h.symm
  dsimp only
  unfold sealSweepOpenLeaderCount
  exact finNatSum_pair_change
    (fun i => if openLeaderBit (C i) then 1 else 0)
    (fun i => if openLeaderBit (D i) then 1 else 0)
    e j hne (by
      intro i hie hij
      have hstate : D i = C i := by
        simp [D, localStep, j, hie, hij]
      rw [hstate])

private theorem openFollowerCount_pair_change
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) :
    let j := ring.rightNeighbor e
    let D := localStep ring P_partialSealSweep C e
    sealSweepOpenFollowerCount D +
        (if openFollowerBit (C e) then 1 else 0) +
        (if openFollowerBit (C j) then 1 else 0) =
      sealSweepOpenFollowerCount C +
        (if openFollowerBit (D e) then 1 else 0) +
        (if openFollowerBit (D j) then 1 else 0) := by
  let j := ring.rightNeighbor e
  let D := localStep ring P_partialSealSweep C e
  have hne : e ≠ j := by
    intro h
    exact rightNeighbor_ne_self_of_one_lt ring hn e h.symm
  dsimp only
  unfold sealSweepOpenFollowerCount
  exact finNatSum_pair_change
    (fun i => if openFollowerBit (C i) then 1 else 0)
    (fun i => if openFollowerBit (D i) then 1 else 0)
    e j hne (by
      intro i hie hij
      have hstate : D i = C i := by
        simp [D, localStep, j, hie, hij]
      rw [hstate])

/-- Every exact local interaction preserves the equality between open anchors
and open probes. -/
theorem sealSweepOpenBalanced_localStep
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C) (e : Fin n) :
    SealSweepOpenBalanced
      (localStep ring P_partialSealSweep C e) := by
  by_cases hn : n = 1
  · rw [sealSweep_localStep_eq_self_of_one ring hn C e]
    exact hbalanced
  · have hnTwo : 1 < n := by
      have hnPos := ring.hn
      omega
    let j := ring.rightNeighbor e
    let D := localStep ring P_partialSealSweep C e
    have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hnTwo e
    have hej : e ≠ j := fun h => hje h.symm
    have hDe : D e = (P_partialSealSweep (C e) (C j)).1 := by
      simp [D, localStep, j]
    have hDj : D j = (P_partialSealSweep (C e) (C j)).2 := by
      simp [D, localStep, j, hje]
    have hleaders := openLeaderCount_pair_change ring hnTwo C e
    have hfollowers := openFollowerCount_pair_change ring hnTwo C e
    change SealSweepOpenBalanced D
    change sealSweepOpenLeaderCount C =
      sealSweepOpenFollowerCount C at hbalanced
    change sealSweepOpenLeaderCount D =
      sealSweepOpenFollowerCount D
    change sealSweepOpenLeaderCount D +
        (if openLeaderBit (C e) then 1 else 0) +
        (if openLeaderBit (C j) then 1 else 0) =
      sealSweepOpenLeaderCount C +
        (if openLeaderBit (D e) then 1 else 0) +
        (if openLeaderBit (D j) then 1 else 0) at hleaders
    change sealSweepOpenFollowerCount D +
        (if openFollowerBit (C e) then 1 else 0) +
        (if openFollowerBit (C j) then 1 else 0) =
      sealSweepOpenFollowerCount C +
        (if openFollowerBit (D e) then 1 else 0) +
        (if openFollowerBit (D j) then 1 else 0) at hfollowers
    rw [hDe, hDj] at hleaders hfollowers
    cases hl : sweepLockLeader (C e) <;>
      cases hlc : (C e).2 <;>
      cases hr : sweepLockLeader (C j) <;>
      cases hrc : (C j).2
    all_goals
      simp only [sweepLockLeader] at hl hr
      simp [P_partialSealSweep, openLeaderBit,
        openFollowerBit, hl, hlc, hr, hrc, sweepLockLeader] at hleaders hfollowers
      omega

theorem allClosed_openBalanced
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C) :
    SealSweepOpenBalanced C := by
  have hleaders : sealSweepOpenLeaderCount C = 0 := by
    unfold sealSweepOpenLeaderCount
    apply (finNatSum_bool_eq_zero_iff
      (fun i => openLeaderBit (C i))).2
    intro i
    simp [openLeaderBit, hclosed i]
  have hfollowers : sealSweepOpenFollowerCount C = 0 := by
    unfold sealSweepOpenFollowerCount
    apply (finNatSum_bool_eq_zero_iff
      (fun i => openFollowerBit (C i))).2
    intro i
    simp [openFollowerBit, hclosed i]
  exact hleaders.trans hfollowers.symm

theorem sealSweepOpenBalanced_closed
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialSealSweepProtocol psi kappa tau) ring
      SealSweepOpenBalanced := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  change SealSweepOpenBalanced
    (localStep ring P_partialSealSweep C e)
  exact sealSweepOpenBalanced_localStep ring C hC e

def SealSweepHasLeader
    (C : SealSweepConfig n psi kappa tau) : Prop :=
  ∃ i : Fin n, sweepLockLeader (C i) = true

theorem sealSweep_hasLeader_iff_leaderCount_pos
    (C : SealSweepConfig n psi kappa tau) :
    SealSweepHasLeader C ↔ 0 < sealSweepLeaderCount C := by
  unfold SealSweepHasLeader sealSweepLeaderCount
  change (∃ i, sweepLockLeader (C i) = true) ↔
    0 < finNatSum (fun i => if sweepLockLeader (C i) then 1 else 0)
  rw [finNatSum_bool_pos_iff]

private theorem sealSweep_leftLeader_after
    (l r : SealSweepState psi kappa tau)
    (hl : sweepLockLeader l = true) :
    sweepLockLeader (P_partialSealSweep l r).1 = true := by
  cases hlc : l.2 <;>
    cases hr : sweepLockLeader r <;>
    cases hrc : r.2
  all_goals
    simp only [sweepLockLeader] at hl hr
    simp [P_partialSealSweep, sweepLockLeader, hl, hlc, hr, hrc]

/-- The exact transition cannot remove the final leader from a balanced
configuration.  The only delicate branch is `D A → C D`: balance supplies
an open leader elsewhere, and that site is framed. -/
theorem sealSweepHasLeader_localStep
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hleader : SealSweepHasLeader C) (e : Fin n) :
    SealSweepHasLeader
      (localStep ring P_partialSealSweep C e) := by
  by_cases hn : n = 1
  · rw [sealSweep_localStep_eq_self_of_one ring hn C e]
    exact hleader
  · have hnTwo : 1 < n := by
      have hnPos := ring.hn
      omega
    let j := ring.rightNeighbor e
    let D := localStep ring P_partialSealSweep C e
    have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hnTwo e
    have hej : e ≠ j := fun h => hje h.symm
    cases hl : sweepLockLeader (C e) with
    | true =>
        refine ⟨e, ?_⟩
        change sweepLockLeader (D e) = true
        have hp := sealSweep_leftLeader_after (C e) (C j) hl
        have hDe : D e = (P_partialSealSweep (C e) (C j)).1 := by
          simp [D, localStep, j]
        rw [hDe]
        exact hp
    | false =>
        cases hlc : (C e).2 with
        | true =>
            obtain ⟨root, hroot⟩ := hleader
            have hpair : P_partialSealSweep (C e) (C j) =
                (C e, C j) :=
              P_partialSealSweep_eq_self_of_leftClosedFollower
                (C e) (C j) hl hlc
            refine ⟨root, ?_⟩
            by_cases hre : root = e
            · subst root
              simp [D, localStep, j, hpair]
              exact hroot
            · by_cases hrj : root = j
              · subst root
                simp [D, localStep, j, hpair, hje]
                exact hroot
              · have hframe : D root = C root := by
                  simp [D, localStep, j, hre, hrj]
                change sweepLockLeader (D root) = true
                rw [hframe]
                exact hroot
        | false =>
            cases hr : sweepLockLeader (C j) with
            | false =>
                obtain ⟨root, hroot⟩ := hleader
                have hre : root ≠ e := by
                  intro h
                  subst root
                  rw [hl] at hroot
                  exact Bool.noConfusion hroot
                have hrj : root ≠ j := by
                  intro h
                  subst root
                  rw [hr] at hroot
                  exact Bool.noConfusion hroot
                refine ⟨root, ?_⟩
                have hframe : D root = C root := by
                  simp [D, localStep, j, hre, hrj]
                change sweepLockLeader (D root) = true
                rw [hframe]
                exact hroot
            | true =>
                cases hrc : (C j).2 with
                | false =>
                    refine ⟨j, ?_⟩
                    change sweepLockLeader (D j) = true
                    have hpair := P_partialSealSweep_return
                      (C e) (C j) hl hlc hr hrc
                    have hDj : D j = ((C j).1, true) := by
                      simp [D, localStep, j, hpair, hje]
                    rw [hDj]
                    simpa [sweepLockLeader] using hr
                | true =>
                    have hFollowerPositive :
                        0 < sealSweepOpenFollowerCount C :=
                      (openFollowerCount_pos_iff C).2 ⟨e, hl, hlc⟩
                    have hLeaderPositive :
                        0 < sealSweepOpenLeaderCount C := by
                      change sealSweepOpenLeaderCount C =
                        sealSweepOpenFollowerCount C at hbalanced
                      omega
                    obtain ⟨anchor, hAnchorLeader, hAnchorOpen⟩ :=
                      (openLeaderCount_pos_iff C).1 hLeaderPositive
                    have hae : anchor ≠ e := by
                      intro h
                      subst anchor
                      rw [hl] at hAnchorLeader
                      exact Bool.noConfusion hAnchorLeader
                    have haj : anchor ≠ j := by
                      intro h
                      subst anchor
                      rw [hrc] at hAnchorOpen
                      exact Bool.noConfusion hAnchorOpen
                    refine ⟨anchor, ?_⟩
                    have hframe : D anchor = C anchor := by
                      simp [D, localStep, j, hae, haj]
                    change sweepLockLeader (D anchor) = true
                    rw [hframe]
                    exact hAnchorLeader

/-- Balance and positive leader existence form a genuine step-closed invariant,
not a renamed restart hypothesis. -/
theorem sealSweepBalancedPositive_closed
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialSealSweepProtocol psi kappa tau) ring
      (fun C => SealSweepOpenBalanced C ∧ SealSweepHasLeader C) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  change SealSweepOpenBalanced
      (localStep ring P_partialSealSweep C e) ∧
    SealSweepHasLeader (localStep ring P_partialSealSweep C e)
  exact ⟨sealSweepOpenBalanced_localStep ring C hC.1 e,
    sealSweepHasLeader_localStep ring C hC.1 hC.2 e⟩

/-- Every state in the R87 reachability closure satisfies the two primitive
normalizer invariants. -/
theorem positiveDescendant_balanced_hasLeader
    (ring : DirectedRing n)
    (D : SealSweepConfig n psi kappa tau)
    (hD : SealSweepPositiveDescendant ring D) :
    SealSweepOpenBalanced D ∧ SealSweepHasLeader D := by
  obtain ⟨C, hC, hreach⟩ := hD
  apply PopulationProtocol.ClosedPred.reachable
    (sealSweepBalancedPositive_closed ring)
    ⟨allClosed_openBalanced C hC.1,
      (sealSweep_hasLeader_iff_leaderCount_pos C).2 hC.2⟩
    hreach

/-! ## Minimum clockwise open-probe/open-anchor gap -/

/-- A positive bounded clockwise distance from an open follower probe to an
open leader anchor. -/
def SealSweepOpenGapWitness
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (d : Nat) : Prop :=
  ∃ probe anchor : Fin n,
    sweepLockLeader (C probe) = false ∧
      (C probe).2 = false ∧
      sweepLockLeader (C anchor) = true ∧
      (C anchor).2 = false ∧
      0 < d ∧ d < n ∧
      cwPos ring probe d = anchor

/-- Least positive clockwise gap between an open follower and an open leader;
zero is used only when no such pair exists. -/
private theorem nat_minimal_of_exists {P : Nat → Prop}
    (hex : ∃ d, P d) :
    ∃ d, P d ∧ ∀ k, P k → d ≤ k := by
  obtain ⟨seed, hseed⟩ := hex
  have go : ∀ d : Nat, P d →
      ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
        intro hd
        by_cases hsmaller : ∃ k : Nat, k < d ∧ P k
        · obtain ⟨k, hklt, hk⟩ := hsmaller
          exact ih k hklt hk
        · refine ⟨d, hd, ?_⟩
          intro k hk
          by_cases hle : d ≤ k
          · exact hle
          · exact False.elim (hsmaller ⟨k, by omega, hk⟩)
  exact go seed hseed

noncomputable def sealSweepOpenGap
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) : Nat := by
  classical
  exact if h : ∃ d, SealSweepOpenGapWitness ring C d
    then Classical.choose (nat_minimal_of_exists h)
    else 0

theorem balanced_not_allClosed_openCounts_pos
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hnotClosed : ¬ SealSweepAllClosed C) :
    0 < sealSweepOpenLeaderCount C ∧
      0 < sealSweepOpenFollowerCount C := by
  have hopen : ∃ i : Fin n, (C i).2 = false := by
    apply Classical.byContradiction
    intro hnone
    apply hnotClosed
    intro i
    cases hi : (C i).2
    · exact False.elim (hnone ⟨i, hi⟩)
    · rfl
  obtain ⟨i, hi⟩ := hopen
  cases hl : sweepLockLeader (C i) with
  | false =>
      have hfollower : 0 < sealSweepOpenFollowerCount C :=
        (openFollowerCount_pos_iff C).2 ⟨i, hl, hi⟩
      change sealSweepOpenLeaderCount C =
        sealSweepOpenFollowerCount C at hbalanced
      exact ⟨by omega, hfollower⟩
  | true =>
      have hleader : 0 < sealSweepOpenLeaderCount C :=
        (openLeaderCount_pos_iff C).2 ⟨i, hl, hi⟩
      change sealSweepOpenLeaderCount C =
        sealSweepOpenFollowerCount C at hbalanced
      exact ⟨hleader, by omega⟩

theorem balanced_not_allClosed_gap_exists
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hnotClosed : ¬ SealSweepAllClosed C) :
    ∃ d, SealSweepOpenGapWitness ring C d := by
  obtain ⟨hleaderPos, hfollowerPos⟩ :=
    balanced_not_allClosed_openCounts_pos C hbalanced hnotClosed
  obtain ⟨anchor, hAnchorLeader, hAnchorOpen⟩ :=
    (openLeaderCount_pos_iff C).1 hleaderPos
  obtain ⟨probe, hProbeLeader, hProbeOpen⟩ :=
    (openFollowerCount_pos_iff C).1 hfollowerPos
  let d := cwDist ring probe anchor
  have hdlt : d < n := cwDist_lt ring probe anchor
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hdzero
    have heq : probe = anchor := by
      have hpos := cwPos_cwDist ring probe anchor
      simpa [d, hdzero] using hpos
    subst anchor
    rw [hProbeLeader] at hAnchorLeader
    exact Bool.noConfusion hAnchorLeader
  exact ⟨d, probe, anchor,
    hProbeLeader, hProbeOpen, hAnchorLeader, hAnchorOpen,
    hdpos, hdlt, cwPos_cwDist ring probe anchor⟩

private theorem sealSweepOpenGap_spec
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hex : ∃ d, SealSweepOpenGapWitness ring C d) :
    SealSweepOpenGapWitness ring C (sealSweepOpenGap ring C) := by
  classical
  simp only [sealSweepOpenGap, dif_pos hex]
  exact (Classical.choose_spec (nat_minimal_of_exists hex)).1

private theorem sealSweepOpenGap_le_of_witness
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (d : Nat)
    (hd : SealSweepOpenGapWitness ring C d) :
    sealSweepOpenGap ring C ≤ d := by
  classical
  have hex : ∃ k, SealSweepOpenGapWitness ring C k := ⟨d, hd⟩
  simp only [sealSweepOpenGap, dif_pos hex]
  exact (Classical.choose_spec (nat_minimal_of_exists hex)).2 d hd

theorem sealSweepOpenGap_pos_lt
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hnotClosed : ¬ SealSweepAllClosed C) :
    0 < sealSweepOpenGap ring C ∧ sealSweepOpenGap ring C < n := by
  have hex := balanced_not_allClosed_gap_exists ring C hbalanced hnotClosed
  obtain ⟨probe, anchor, hpl, hpo, hal, hao, hpos, hlt, hcw⟩ :=
    sealSweepOpenGap_spec ring C hex
  exact ⟨hpos, hlt⟩

theorem sealSweepOpenGap_le
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepOpenGap ring C ≤ n := by
  classical
  by_cases hex : ∃ d, SealSweepOpenGapWitness ring C d
  · obtain ⟨probe, anchor, hpl, hpo, hal, hao, hpos, hlt, hcw⟩ :=
      sealSweepOpenGap_spec ring C hex
    omega
  · simp [sealSweepOpenGap, hex]

theorem balanced_openLeaderCount_zero_allClosed
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hzero : sealSweepOpenLeaderCount C = 0) :
    SealSweepAllClosed C := by
  intro i
  cases hi : (C i).2 with
  | true => rfl
  | false =>
      cases hl : sweepLockLeader (C i) with
      | true =>
          have hpos : 0 < sealSweepOpenLeaderCount C :=
            (openLeaderCount_pos_iff C).2 ⟨i, hl, hi⟩
          omega
      | false =>
          have hpos : 0 < sealSweepOpenFollowerCount C :=
            (openFollowerCount_pos_iff C).2 ⟨i, hl, hi⟩
          change sealSweepOpenLeaderCount C =
            sealSweepOpenFollowerCount C at hbalanced
          omega

/-! ## Exact one-step potential decrease -/

/-- The scalar encoding of the lexicographic potential. -/
noncomputable def sealSweepMixedRank
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) : Nat :=
  sealSweepOpenLeaderCount C * n + sealSweepOpenGap ring C

private theorem openLeaderCount_return_drop
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hl : sweepLockLeader (C e) = false)
    (hlc : (C e).2 = false)
    (hr : sweepLockLeader (C (ring.rightNeighbor e)) = true)
    (hrc : (C (ring.rightNeighbor e)).2 = false) :
    let D := localStep ring P_partialSealSweep C e
    sealSweepOpenLeaderCount D + 1 =
      sealSweepOpenLeaderCount C := by
  let j := ring.rightNeighbor e
  let D := localStep ring P_partialSealSweep C e
  have hstep := sealSweep_localStep_return ring hn C e hl hlc hr hrc
  change D e = ((C e).1, true) ∧
      D j = ((C j).1, true) ∧
      ∀ i : Fin n, i ≠ e → i ≠ j → D i = C i at hstep
  have hcount := openLeaderCount_pair_change ring hn C e
  change sealSweepOpenLeaderCount D +
        (if openLeaderBit (C e) then 1 else 0) +
        (if openLeaderBit (C j) then 1 else 0) =
      sealSweepOpenLeaderCount C +
        (if openLeaderBit (D e) then 1 else 0) +
        (if openLeaderBit (D j) then 1 else 0) at hcount
  have hCebit : openLeaderBit (C e) = false := by
    simp [openLeaderBit, hl]
  have hr' : sweepLockLeader (C j) = true := by
    simpa [j] using hr
  have hrc' : (C j).2 = false := by
    simpa [j] using hrc
  have hCjbit : openLeaderBit (C j) = true := by
    simp [openLeaderBit, hr', hrc']
  have hDeb : openLeaderBit (D e) = false := by
    rw [hstep.1]
    simp [openLeaderBit, sweepLockLeader]
  have hDjb : openLeaderBit (D j) = false := by
    rw [hstep.2.1]
    simp [openLeaderBit]
  simp [hCebit, hCjbit, hDeb, hDjb] at hcount
  exact hcount

private theorem openLeaderCount_probe_closed_same
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hl : sweepLockLeader (C e) = false)
    (hlc : (C e).2 = false)
    (hrc : (C (ring.rightNeighbor e)).2 = true) :
    let D := localStep ring P_partialSealSweep C e
    sealSweepOpenLeaderCount D = sealSweepOpenLeaderCount C := by
  let j := ring.rightNeighbor e
  let D := localStep ring P_partialSealSweep C e
  have hstep := sealSweep_localStep_probe_closed ring hn C e hl hlc hrc
  change D e = ((C e).1, true) ∧
      (D j).2 = false ∧
      sweepLockLeader (D j) = false ∧
      ∀ i : Fin n, i ≠ e → i ≠ j → D i = C i at hstep
  have hcount := openLeaderCount_pair_change ring hn C e
  change sealSweepOpenLeaderCount D +
        (if openLeaderBit (C e) then 1 else 0) +
        (if openLeaderBit (C j) then 1 else 0) =
      sealSweepOpenLeaderCount C +
        (if openLeaderBit (D e) then 1 else 0) +
        (if openLeaderBit (D j) then 1 else 0) at hcount
  have hCebit : openLeaderBit (C e) = false := by
    simp [openLeaderBit, hl]
  have hrc' : (C j).2 = true := by
    simpa [j] using hrc
  have hCjbit : openLeaderBit (C j) = false := by
    simp [openLeaderBit, hrc']
  have hDeb : openLeaderBit (D e) = false := by
    rw [hstep.1]
    simp [openLeaderBit, sweepLockLeader]
  have hDjb : openLeaderBit (D j) = false := by
    simp [openLeaderBit, hstep.2.1, hstep.2.2.1]
  simp [hCebit, hCjbit, hDeb, hDjb] at hcount
  exact hcount

private theorem cwPos_one_eq_rightNeighbor
    (ring : DirectedRing n) (i : Fin n) :
    cwPos ring i 1 = ring.rightNeighbor i := by
  simpa using cwPos_succ ring i 0

/-- Every mixed balanced positive configuration has one exact edge whose
execution strictly lowers `sealSweepMixedRank`. -/
theorem sealSweep_mixedRank_descent
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hleader : SealSweepHasLeader C)
    (hnotClosed : ¬ SealSweepAllClosed C) :
    ∃ e : Fin n,
      let D := localStep ring P_partialSealSweep C e
      SealSweepOpenBalanced D ∧
        SealSweepHasLeader D ∧
        sealSweepMixedRank ring D < sealSweepMixedRank ring C := by
  have hex := balanced_not_allClosed_gap_exists ring C hbalanced hnotClosed
  let k := sealSweepOpenGap ring C
  have hgap := sealSweepOpenGap_spec ring C hex
  change SealSweepOpenGapWitness ring C k at hgap
  obtain ⟨probe, anchor, hProbeLeader, hProbeOpen,
      hAnchorLeader, hAnchorOpen, hkpos, hklt, hcw⟩ := hgap
  have hnTwo : 1 < n := by omega
  let j := ring.rightNeighbor probe
  have hje : j ≠ probe :=
    rightNeighbor_ne_self_of_one_lt ring hnTwo probe
  have hej : probe ≠ j := fun h => hje h.symm
  by_cases hkOne : k = 1
  · have hja : j = anchor := by
      calc
        j = cwPos ring probe 1 := by
          simpa [j] using (cwPos_one_eq_rightNeighbor ring probe).symm
        _ = cwPos ring probe k := by rw [hkOne]
        _ = anchor := hcw
    have hRightLeader : sweepLockLeader (C j) = true := by
      rw [hja]
      exact hAnchorLeader
    have hRightOpen : (C j).2 = false := by
      rw [hja]
      exact hAnchorOpen
    let D := localStep ring P_partialSealSweep C probe
    refine ⟨probe, ?_⟩
    dsimp only
    refine ⟨sealSweepOpenBalanced_localStep ring C hbalanced probe,
      sealSweepHasLeader_localStep ring C hbalanced hleader probe, ?_⟩
    have hcount := openLeaderCount_return_drop ring hnTwo C probe
      hProbeLeader hProbeOpen
      (by simpa [j] using hRightLeader)
      (by simpa [j] using hRightOpen)
    change sealSweepOpenLeaderCount D + 1 =
      sealSweepOpenLeaderCount C at hcount
    have hgapD := sealSweepOpenGap_le ring D
    have hgapC : sealSweepOpenGap ring C = 1 := by
      simpa [k] using hkOne
    change sealSweepMixedRank ring D < sealSweepMixedRank ring C
    unfold sealSweepMixedRank
    rw [← hcount, hgapC, Nat.add_mul]
    omega
  · have hkgt : 1 < k := by omega
    have hjNotOpenLeader : ¬
        (sweepLockLeader (C j) = true ∧ (C j).2 = false) := by
      rintro ⟨hjl, hjo⟩
      have hone : SealSweepOpenGapWitness ring C 1 :=
        ⟨probe, j, hProbeLeader, hProbeOpen, hjl, hjo,
          by omega, by omega, by
            simpa [j] using cwPos_one_eq_rightNeighbor ring probe⟩
      have hmin := sealSweepOpenGap_le_of_witness ring C 1 hone
      change k ≤ 1 at hmin
      omega
    have hjNotOpenFollower : ¬
        (sweepLockLeader (C j) = false ∧ (C j).2 = false) := by
      rintro ⟨hjl, hjo⟩
      have hmove : cwPos ring j (k - 1) = anchor := by
        calc
          cwPos ring j (k - 1) =
              cwPos ring probe ((k - 1) + 1) := by
            simpa [j] using cwPos_rightNeighbor ring probe (k - 1)
          _ = cwPos ring probe k := by
            rw [show k - 1 + 1 = k by omega]
          _ = anchor := hcw
      have hprev : SealSweepOpenGapWitness ring C (k - 1) :=
        ⟨j, anchor, hjl, hjo, hAnchorLeader, hAnchorOpen,
          by omega, by omega, hmove⟩
      have hmin := sealSweepOpenGap_le_of_witness ring C (k - 1) hprev
      change k ≤ k - 1 at hmin
      omega
    have hjClosed : (C j).2 = true := by
      cases hjc : (C j).2 with
      | true => rfl
      | false =>
          cases hjl : sweepLockLeader (C j) with
          | true => exact False.elim (hjNotOpenLeader ⟨hjl, hjc⟩)
          | false => exact False.elim (hjNotOpenFollower ⟨hjl, hjc⟩)
    let D := localStep ring P_partialSealSweep C probe
    have hstep := sealSweep_localStep_probe_closed ring hnTwo C probe
      hProbeLeader hProbeOpen (by simpa [j] using hjClosed)
    change D probe = ((C probe).1, true) ∧
        (D j).2 = false ∧
        sweepLockLeader (D j) = false ∧
        ∀ i : Fin n, i ≠ probe → i ≠ j → D i = C i at hstep
    have hae : anchor ≠ probe := by
      intro h
      have hbad : sweepLockLeader (C probe) = true := by
        rw [← h]
        exact hAnchorLeader
      rw [hProbeLeader] at hbad
      exact Bool.noConfusion hbad
    have haj : anchor ≠ j := by
      intro h
      apply hjNotOpenLeader
      constructor
      · rw [← h]
        exact hAnchorLeader
      · rw [← h]
        exact hAnchorOpen
    have hframe : D anchor = C anchor :=
      hstep.2.2.2 anchor hae haj
    have hmove : cwPos ring j (k - 1) = anchor := by
      calc
        cwPos ring j (k - 1) =
            cwPos ring probe ((k - 1) + 1) := by
          simpa [j] using cwPos_rightNeighbor ring probe (k - 1)
        _ = cwPos ring probe k := by
          rw [show k - 1 + 1 = k by omega]
        _ = anchor := hcw
    have hnewWitness : SealSweepOpenGapWitness ring D (k - 1) := by
      refine ⟨j, anchor, hstep.2.2.1, hstep.2.1, ?_, ?_,
        by omega, by omega, hmove⟩
      · rw [hframe]
        exact hAnchorLeader
      · rw [hframe]
        exact hAnchorOpen
    have hgapDle :=
      sealSweepOpenGap_le_of_witness ring D (k - 1) hnewWitness
    have hgapDlt : sealSweepOpenGap ring D < sealSweepOpenGap ring C := by
      change sealSweepOpenGap ring D < k
      omega
    have hcount := openLeaderCount_probe_closed_same ring hnTwo C probe
      hProbeLeader hProbeOpen (by simpa [j] using hjClosed)
    change sealSweepOpenLeaderCount D = sealSweepOpenLeaderCount C at hcount
    refine ⟨probe, ?_⟩
    dsimp only
    refine ⟨sealSweepOpenBalanced_localStep ring C hbalanced probe,
      sealSweepHasLeader_localStep ring C hbalanced hleader probe, ?_⟩
    change sealSweepMixedRank ring D < sealSweepMixedRank ring C
    unfold sealSweepMixedRank
    rw [hcount]
    exact Nat.add_lt_add_left hgapDlt _

/-! ## Bounded normalization and safe landing -/

theorem sealSweepMixedRank_le
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepMixedRank ring C ≤ n * n + n := by
  have hcount := sealSweepOpenLeaderCount_le C
  have hgap := sealSweepOpenGap_le ring C
  unfold sealSweepMixedRank
  exact Nat.add_le_add (Nat.mul_le_mul_right n hcount) hgap

/-- Strong induction on the exact mixed-state potential produces an
all-closed positive endpoint. -/
theorem sealSweep_balancedPositive_normalizes_rankBound
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hleader : SealSweepHasLeader C) :
    ∃ word : DetSchedule n,
      word.length ≤ sealSweepMixedRank ring C ∧
      SealSweepAllClosed
        (runLocalSchedule ring P_partialSealSweep C word) ∧
      SealSweepHasLeader
        (runLocalSchedule ring P_partialSealSweep C word) := by
  generalize hr : sealSweepMixedRank ring C = r
  induction r using Nat.strongRecOn generalizing C with
  | ind r ih =>
      by_cases hclosed : SealSweepAllClosed C
      · refine ⟨[], by simp, ?_, ?_⟩
        · change SealSweepAllClosed C
          exact hclosed
        · change SealSweepHasLeader C
          exact hleader
      · obtain ⟨e, hDbalanced, hDleader, hdecrease⟩ :=
          sealSweep_mixedRank_descent ring C hbalanced hleader hclosed
        let D := localStep ring P_partialSealSweep C e
        change SealSweepOpenBalanced D at hDbalanced
        change SealSweepHasLeader D at hDleader
        change sealSweepMixedRank ring D < sealSweepMixedRank ring C
          at hdecrease
        have hDr : sealSweepMixedRank ring D < r := by omega
        obtain ⟨tail, htailLength, htailClosed, htailLeader⟩ :=
          ih (sealSweepMixedRank ring D) hDr D hDbalanced hDleader rfl
        refine ⟨e :: tail, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · simpa only [runLocalSchedule] using htailClosed
        · simpa only [runLocalSchedule] using htailLeader

theorem sealSweep_balancedPositive_normalizes_poly
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hleader : SealSweepHasLeader C) :
    ∃ word : DetSchedule n,
      word.length ≤ n * n + n ∧
      SealSweepAllClosed
        (runLocalSchedule ring P_partialSealSweep C word) ∧
      0 < sealSweepLeaderCount
        (runLocalSchedule ring P_partialSealSweep C word) := by
  obtain ⟨word, hlength, hclosed, hhasLeader⟩ :=
    sealSweep_balancedPositive_normalizes_rankBound
      ring C hbalanced hleader
  refine ⟨word, ?_, hclosed,
    (sealSweep_hasLeader_iff_leaderCount_pos _).1 hhasLeader⟩
  have hrankBound := sealSweepMixedRank_le ring C
  omega

/-- The normalizer followed by the existing all-closed positive landing word
reaches genuine semantic safety in a uniform quadratic number of steps. -/
theorem sealSweep_balancedPositive_reaches_isSafe_poly
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hleader : SealSweepHasLeader C) :
    ∃ word : DetSchedule n,
      word.length ≤ n * n + 3 * n ∧
      PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealSweep C word)
        isLeaderOutput := by
  obtain ⟨pre, hpreLength, hDclosed, hDpositive⟩ :=
    sealSweep_balancedPositive_normalizes_poly ring C hbalanced hleader
  let D := runLocalSchedule ring P_partialSealSweep C pre
  change SealSweepAllClosed D at hDclosed
  change 0 < sealSweepLeaderCount D at hDpositive
  obtain ⟨tail, htailLength, htailReach, htailSafe⟩ :=
    sealSweep_allClosedPositive_reaches_isSafe_two_mul_sub_two
      ring D hDclosed hDpositive
  refine ⟨pre ++ tail, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · have hrun :
        runLocalSchedule ring P_partialSealSweep C (pre ++ tail) =
          runLocalSchedule ring P_partialSealSweep D tail := by
      rw [PPLLSchedulerBlocks.runLocalSchedule_append]
    have hsafeEq := congrArg
      (fun X : SealSweepConfig n psi kappa tau =>
        PopulationProtocol.IsSafe
          (P_partialSealSweepProtocol psi kappa tau) ring X
          isLeaderOutput)
      hrun
    exact Eq.mpr hsafeEq htailSafe

/-- This closes the R87/R88 restart hypothesis on the exact reachable
descendant domain. -/
theorem positiveDescendant_boundedLanding_poly
    (ring : DirectedRing n) :
    PositiveDescendantBoundedLanding
      (psi := psi) (kappa := kappa) (tau := tau)
      ring (n * n + 3 * n) := by
  intro C hdesc hnotSafe
  obtain ⟨hbalanced, hleader⟩ :=
    positiveDescendant_balanced_hasLeader ring C hdesc
  obtain ⟨word, hlength, hsafe⟩ :=
    sealSweep_balancedPositive_reaches_isSafe_poly
      ring C hbalanced hleader
  exact ⟨word, hlength, hsafe⟩

/-- Assumption-free repeated-block exact scheduler bound obtained by supplying
the proved quadratic restart producer. -/
theorem positiveDescendant_repeatedBlockSSLEOn_mixedPoly
    (ring : DirectedRing n) :
    ∀ blocks,
      UniformFiniteHorizonSSLEOn
        (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
        (SealSweepPositiveDescendant ring)
        (blocks * (n * n + 3 * n))
        ((n ^ (n * n + 3 * n) - 1) ^ blocks) := by
  exact positiveDescendant_repeatedBlockSSLEOn
    ring (n * n + 3 * n)
    (positiveDescendant_boundedLanding_poly ring)

end PPartialSealSweepMixedNormalizerSol
end PPLLCompleteMultiLeaderCleanup
