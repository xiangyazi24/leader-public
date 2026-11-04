import Leader.PPL.Modes.MidEntrySweepSplice

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-!
# Lemma 5(i): corrected traversal suffix projection

Truth repair.

The residual used reachesAux maxResetSignalB on the arm prefix.
That test is historical: it remains true after the reset lineage has already
disappeared.  Phase C, however, begins at the arm/sweep boundary and can only
charge a clockwise traversal word when a reset signal is live there.

We therefore split the old traversal event into

* stale arm: the historical arm event occurred, but no max-TTL reset is live
  at the boundary;
* live traversal: a max-TTL reset is live at the boundary and the paper sweep
  still fails to reset every clock.

The old traversal event is dominated by the union of these two events.
The stale term has to be charged by the arm/reset phase.  It cannot be hidden
inside the fixed-word miss numerator.
-/

/-- Historical arm success whose max reset is no longer present at the
arm/sweep boundary. -/
def lemma5iTraversalStaleArmBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Bool :=
  let arm := lemma5iArmPrefix word
  let D := runPPL ring C arm
  reachesAux ring maxResetSignalB C arm &&
    !maxResetSignalB D

/-- Corrected phase-C event: the arm event occurred, a max reset is still
live at the arm/sweep boundary, and the paper sweep fails to reset every
clock. -/
def lemma5iTraversalLiveBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Bool :=
  let arm := lemma5iArmPrefix word
  let D := runPPL ring C arm
  let sweep := lemma5iPaperSweepSuffix word
  reachesAux ring maxResetSignalB C arm &&
    maxResetSignalB D &&
    !allClockResetsSeenB ring D sweep

def lemma5iTraversalStaleArmFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma5iHorizon n)).countP
    (lemma5iTraversalStaleArmBadB ring C)

def lemma5iTraversalLiveFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma5iHorizon n)).countP
    (lemma5iTraversalLiveBadB ring C)

def lemma5iTraversalLiveSuffixFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n) : Nat :=
  ((allSchedules n (lemma5SweepHorizon n)).map
      (fun suf => pre ++ suf)).countP
    (lemma5iTraversalLiveBadB ring C)

private def traversalCountP_mono
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq : forall x, p x = true -> q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx : q x = true := hpq x hp
          simp [hp, hqx]
          omega

private def traversalCountP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A -> Bool) :
    xs.countP (fun x => p x || q x) <=
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons]
      cases hp : p x <;>
        cases hq : q x <;>
        simp [hp, hq] at * <;>
        omega

private def traversalBad_to_stale_or_live
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hbad : lemma5iTraversalBadB ring C word = true) :
    (lemma5iTraversalStaleArmBadB ring C word ||
      lemma5iTraversalLiveBadB ring C word) = true := by
  unfold lemma5iTraversalBadB at hbad
  unfold lemma5iTraversalStaleArmBadB
    lemma5iTraversalLiveBadB
  dsimp only at hbad ⊢
  cases hr :
      reachesAux ring maxResetSignalB C
        (lemma5iArmPrefix word) <;>
    cases hm :
      maxResetSignalB
        (runPPL ring C (lemma5iArmPrefix word)) <;>
    cases hs :
      allClockResetsSeenB ring
        (runPPL ring C (lemma5iArmPrefix word))
        (lemma5iPaperSweepSuffix word) <;>
    simp_all

/-- The frozen phase-C event is covered by the stale-arm event plus the
corrected live-boundary traversal event. -/
theorem lemma5iTraversalFailureCount_le_stale_add_live
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma5iTraversalFailureCount ring C <=
      lemma5iTraversalStaleArmFailureCount ring C +
        lemma5iTraversalLiveFailureCount ring C := by
  unfold lemma5iTraversalFailureCount
    lemma5iTraversalStaleArmFailureCount
    lemma5iTraversalLiveFailureCount
  have hmono :
      (allSchedules n (lemma5iHorizon n)).countP
          (lemma5iTraversalBadB ring C) <=
        (allSchedules n (lemma5iHorizon n)).countP
          (fun word =>
            lemma5iTraversalStaleArmBadB ring C word ||
              lemma5iTraversalLiveBadB ring C word) := by
    exact
      traversalCountP_mono
        (allSchedules n (lemma5iHorizon n))
        (lemma5iTraversalBadB ring C)
        (fun word =>
          lemma5iTraversalStaleArmBadB ring C word ||
            lemma5iTraversalLiveBadB ring C word)
        (fun word hbad =>
          traversalBad_to_stale_or_live ring C word hbad)
  exact
    Nat.le_trans hmono
      (traversalCountP_or_le_add
        (allSchedules n (lemma5iHorizon n))
        (lemma5iTraversalStaleArmBadB ring C)
        (lemma5iTraversalLiveBadB ring C))

private def traversalTakeArm_append
    {n : Nat}
    (pre suf : DetSchedule n)
    (hlen : pre.length = lemma5ArmHorizon n) :
    lemma5iArmPrefix (pre ++ suf) = pre := by
  unfold lemma5iArmPrefix
  rw [List.take_append, ← hlen]
  simp

/-- The controller's first concern is harmless after the repair: if no max
reset is live at the arm/sweep boundary, the corrected live-traversal suffix
count is literally zero. -/
theorem lemma5iTraversalLiveSuffix_zero_of_endpoint_no_max
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n)
    (hpre :
      pre ∈ allSchedules n (lemma5ArmHorizon n))
    (hmax :
      maxResetSignalB (runPPL ring C pre) = false) :
    lemma5iTraversalLiveSuffixFailureCount
      ring C pre = 0 := by
  have hlen :
      pre.length = lemma5ArmHorizon n :=
    allSchedules_schedule_length
      n (lemma5ArmHorizon n) pre hpre
  unfold lemma5iTraversalLiveSuffixFailureCount
  apply List.countP_eq_zero.mpr
  intro word hword hbad
  rcases List.mem_map.mp hword with
    ⟨suf, _hsuf, hwordEq⟩
  rw [← hwordEq] at hbad
  have htake :
      lemma5iArmPrefix (pre ++ suf) = pre :=
    traversalTakeArm_append pre suf hlen
  unfold lemma5iTraversalLiveBadB at hbad
  dsimp only at hbad
  rw [htake] at hbad
  simp [hmax] at hbad

/-!
Smallest new physical residual.

Unlike the earlier statement, the reset is required to be live at the arm/sweep boundary.
The false historical case has been removed.  On hmax=true a proof selects a
current max-TTL owner, uses SignalLineageOwnership to follow that owner (or a
fresh max-TTL re-arm) around the ring, and charges failure to a rotated copy
of lemma5ClockwiseSweepWord.  FixedWord supplies the scheduler count; the
stopped MarkedWord/Lemma9 encounter machinery is only needed when the lineage
dies, and that outcome belongs to the stale/reset phase rather than phase C.
-/
def Lemma5iTraversalLiveSuffixPhysicalProjection : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    forall pre : DetSchedule n,
      pre ∈ allSchedules n (lemma5ArmHorizon n) ->
      maxResetSignalB (runPPL ring C pre) = true ->
      lemma5iTraversalLiveSuffixFailureCount ring C pre <=
        n ^ (2 * n * n) *
          fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n)

private def traversalAllSchedules_add
    (n a b : Nat) :
    allSchedules n (a + b) =
      (allSchedules n a).flatMap (fun pre =>
        (allSchedules n b).map
          (fun suf => pre ++ suf)) := by
  induction b with
  | zero =>
      simp [allSchedules]
  | succ b ih =>
      rw [Nat.add_succ, allSchedules, ih]
      simp only [allSchedules, List.flatMap_assoc,
        List.map_flatMap, List.flatMap_map]
      congr
      funext pre
      congr
      funext suf
      rw [List.map_ofFn]
      congr 1
      funext e
      simp [List.append_assoc]

private def traversalSum_map_le
    {A : Type}
    (xs : List A)
    (f g : A -> Nat)
    (hfg : forall x, x ∈ xs -> f x <= g x) :
    (xs.map f).sum <= (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons]
      exact
        Nat.add_le_add
          (hfg x (by simp))
          (ih (fun y hy => hfg y (by simp [hy])))

private def traversalSum_map_const
    {A : Type}
    (xs : List A)
    (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.succ_mul, Nat.add_comm]

private def traversalLiveFailureCount_eq_suffixSum
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma5iTraversalLiveFailureCount ring C =
      ((allSchedules n (lemma5ArmHorizon n)).map
        (lemma5iTraversalLiveSuffixFailureCount
          ring C)).sum := by
  unfold lemma5iTraversalLiveFailureCount
    lemma5iTraversalLiveSuffixFailureCount
  rw [show
      lemma5iHorizon n =
        lemma5ArmHorizon n +
          lemma5SweepHorizon n by rfl]
  rw [traversalAllSchedules_add,
    List.countP_flatMap]
  rfl

/-- The corrected live-boundary traversal count has exactly the
fixed-word outer splice.  Prefixes with no live max reset contribute zero. -/
theorem lemma5iTraversalLiveCountSplice
    (hprojection :
      Lemma5iTraversalLiveSuffixPhysicalProjection) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    lemma5iTraversalLiveFailureCount ring C <=
      n ^ (lemma5ArmHorizon n + 2 * n * n) *
        fixedWordMissCount
          (lemma5ClockwiseSweepWord n)
          (lemma5PaperSweepHorizon n) := by
  intro n psi kappa
  intro hn3 hpsi hkappa ring C hlineage

  let P : Nat :=
    n ^ (2 * n * n) *
      fixedWordMissCount
        (lemma5ClockwiseSweepWord n)
        (lemma5PaperSweepHorizon n)

  have hpoint :
      forall pre : DetSchedule n,
        pre ∈ allSchedules n (lemma5ArmHorizon n) ->
        lemma5iTraversalLiveSuffixFailureCount
            ring C pre <= P := by
    intro pre hpre
    cases hm :
        maxResetSignalB (runPPL ring C pre) with
    | false =>
        have hz :=
          lemma5iTraversalLiveSuffix_zero_of_endpoint_no_max
            ring C pre hpre hm
        rw [hz]
        exact Nat.zero_le P
    | true =>
        exact
          hprojection
            hn3 hpsi hkappa ring C hlineage
            pre hpre hm

  have hsum :
      ((allSchedules n (lemma5ArmHorizon n)).map
        (lemma5iTraversalLiveSuffixFailureCount
          ring C)).sum <=
      ((allSchedules n (lemma5ArmHorizon n)).map
        (fun _ => P)).sum :=
    traversalSum_map_le
      (allSchedules n (lemma5ArmHorizon n))
      (lemma5iTraversalLiveSuffixFailureCount ring C)
      (fun _ => P)
      hpoint

  calc
    lemma5iTraversalLiveFailureCount ring C =
        ((allSchedules n (lemma5ArmHorizon n)).map
          (lemma5iTraversalLiveSuffixFailureCount
            ring C)).sum :=
      traversalLiveFailureCount_eq_suffixSum ring C
    _ <=
        ((allSchedules n (lemma5ArmHorizon n)).map
          (fun _ => P)).sum :=
      hsum
    _ =
        (allSchedules n
          (lemma5ArmHorizon n)).length * P :=
      traversalSum_map_const
        (allSchedules n (lemma5ArmHorizon n)) P
    _ =
        n ^ lemma5ArmHorizon n * P := by
      rw [allSchedules_length]
    _ =
        n ^ (lemma5ArmHorizon n + 2 * n * n) *
          fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n) := by
      dsimp [P]
      rw [Nat.pow_add]
      ac_rfl

/-- Corrected replacement for the false first conjunct of the earlier statement.
The stale-arm term is explicit and must be paid by the arm/reset phase. -/
theorem lemma5iTraversalCountSplice_corrected
    (hprojection :
      Lemma5iTraversalLiveSuffixPhysicalProjection) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    lemma5iTraversalFailureCount ring C <=
      lemma5iTraversalStaleArmFailureCount ring C +
        n ^ (lemma5ArmHorizon n + 2 * n * n) *
          fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n) := by
  intro n psi kappa
  intro hn3 hpsi hkappa ring C hlineage
  have hsplit :=
    lemma5iTraversalFailureCount_le_stale_add_live
      ring C
  have hlive :=
    lemma5iTraversalLiveCountSplice
      hprojection
      hn3 hpsi hkappa ring C hlineage
  exact
    Nat.le_trans hsplit
      (Nat.add_le_add_left hlive
        (lemma5iTraversalStaleArmFailureCount
          ring C))

/-- The corrected sweep/mid splice.  The phase-D clause is unchanged and is
still supplied by the earlier independent latest-reset residual. -/
def Lemma5iSweepMidPhysicalCountSpliceCorrected : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    StoppedClockSuffixBoundsCorrected ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    And
      (lemma5iTraversalFailureCount ring C <=
        lemma5iTraversalStaleArmFailureCount ring C +
          n ^ (lemma5ArmHorizon n + 2 * n * n) *
            fixedWordMissCount
              (lemma5ClockwiseSweepWord n)
              (lemma5PaperSweepHorizon n))
      (lemma5iMidClockFailureCount ring C * 2 ^ psi <=
        n ^ lemma5iHorizon n)

/-- The earlier outer algebra remains valid after the truth repair; only the
stale-arm mass is exposed instead of being incorrectly hidden in the
fixed-word term. -/
theorem lemma5iSweepMidPhysicalCountSplice_corrected
    (hTraversal :
      Lemma5iTraversalLiveSuffixPhysicalProjection)
    (hMid : Lemma5iMidLatestResetSuffixBound) :
    Lemma5iSweepMidPhysicalCountSpliceCorrected := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro hcnz hlineage hclock hmarked
  intro hpredict hhead hlottery
  exact
    And.intro
      (lemma5iTraversalCountSplice_corrected
        hTraversal
        hn3 hpsi hkappa
        ring C hlineage)
      (lemma5iMidClockCountSplice
        hMid
        hn3 hpsi hkappa hnpow
        ring C hcnz hclock hmarked
        hpredict hhead hlottery)

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iTraversalFailureCount_le_stale_add_live
#print axioms PPL.Modes.Lemma5.lemma5iTraversalLiveSuffix_zero_of_endpoint_no_max
#print axioms PPL.Modes.Lemma5.lemma5iTraversalLiveCountSplice
#print axioms PPL.Modes.Lemma5.lemma5iTraversalCountSplice_corrected
#print axioms PPL.Modes.Lemma5.lemma5iSweepMidPhysicalCountSplice_corrected
