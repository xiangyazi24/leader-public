import Leader.PPL.ReachCPB.Forcing
import Leader.PPL.Modes.DetectionEntryClockRise

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability

/-!
# Lemma 16 with capped Detect states

The literal counterexamples in ReachCPBForcing show that a stored Detect bit is
not enough: DetermineMode recomputes mode from clock.  The stable target is
therefore CPB or DetectReadyCapped.

There is one quantitative interface that current Lemma 6 does not provide.
Its success predicate lemma6GoodB stops on signalFreeB && allDetectB, and can
already be true at time zero with stale mode=true and clock<kappa.  Consequently
Lemma6WordBound cannot, by itself, bound failure to reach the capped target.

Lemma16ModeCappedReachCountSpec below is exactly that missing strengthening of
the Lemma-6 mode block.  It keeps the same H6 and coefficient 8 and explicitly
takes the now-proved Lemma6ClockRiseCount.  No false uncapped forcing premise is
used below.
-/

/-! ## Capped Boolean predicates -/

instance instDecidableDetectReadyCappedLocal
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Decidable (DetectReadyCapped ring C) := by
  unfold DetectReadyCapped
  infer_instance

instance instDecidableDistReadyCappedLocal
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Decidable (DistReadyCapped ring C) := by
  unfold DistReadyCapped
  infer_instance

instance instDecidableLastReadyCappedLocal
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Decidable (LastReadyCapped ring C) := by
  unfold LastReadyCapped
  infer_instance

def detectCappedOrCPBB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (Or (PPL.CPB ring C) (DetectReadyCapped ring C))

def distCappedOrCPBB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (Or (PPL.CPB ring C) (DistReadyCapped ring C))

def lastCappedOrCPBB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (Or (PPL.CPB ring C) (LastReadyCapped ring C))

/-- Prefix success predicate for the repaired Lemma-6 handoff. -/
def reachesDetectCappedOrCPB
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa -> DetSchedule n -> Bool
  | C, [] =>
      detectCappedOrCPBB ring C
  | C, e :: rest =>
      detectCappedOrCPBB ring C ||
        reachesDetectCappedOrCPB ring
          (PopulationProtocol.step
            (PPL.protocol psi kappa) ring C e)
          rest

def lemma16ModeCappedReachFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (T : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word =>
      !(reachesDetectCappedOrCPB ring C word))

/-! ## Corrected deterministic interfaces -/

/-- C_det persistence with the missing clock-cap invariant made explicit. -/
def Lemma16DetectPersistenceCapped : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (word : DetSchedule n),
    DetectReadyCapped ring C ->
      Or
        (PPL.CPB ring
          (PPL.Probability.runPPL ring C word))
        (DetectReadyCapped ring
          (PPL.Probability.runPPL ring C word))

/--
Semantic endpoint bridge for the capped mode target.

Unlike the old Lemma16ModeEndpointSpec, the scanned predicate itself is the
closed target CPB-or-DetectReadyCapped.  Thus once it is hit, capped Detect
persistence or CPB closure carries it to the full endpoint.
-/
def Lemma16ModeEndpointCappedSpec : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (word : DetSchedule n),
    reachesDetectCappedOrCPB ring C word = true ->
      Or
        (PPL.CPB ring
          (PPL.Probability.runPPL ring C word))
        (DetectReadyCapped ring
          (PPL.Probability.runPPL ring C word))

/--
Quantitative repair required at the Lemma-6 handoff.

Current Lemma6WordBound does not imply this statement because lemma6GoodB can
be true initially on a stale Detect bit.  A strengthened clock-phase proof must
charge those uncapped stale-Detect words.  The desired repair has exactly the
old H6 and coefficient 8.
-/
def Lemma16ModeCappedReachCountSpec : Prop :=
  forall {n psi kappa modeC : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hc : 6 <= modeC)
      (hkappa : kappa = 8 * modeC * psi)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    AllLivePeaceful ring C ->
    PPL.Modes.Lemma6.Lemma6ClockRiseCount ->
      n *
          lemma16ModeCappedReachFailureCount
            ring C (lemma16H6 n psi kappa) <=
        8 * n ^ lemma16H6 n psi kappa

/--
Mismatch extraction with the stable Detect invariant.

The geometric Cd witness is unchanged; cappedness is needed by the completion
implication so that a target mismatch takes the Detect leader-birth branch
rather than the Construct ID-write branch.
-/
def Lemma16MismatchWitnessCappedSpec : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    LastReadyCapped ring C ->
    Not (PPL.Perfect ring C) ->
      exists k : Fin n, exists kind : PPL.TokenKind,
        And
          (PPL.Cd ring k kind C)
          (forall schedule : DetSchedule n,
            PPL.HasFreshCompletion kind k
                (PPL.ghostRun hpsi ring 0
                  (PPL.initialGhost C) schedule) ->
              PPL.CPB ring
                (PPL.Probability.runPPL ring C schedule))

/--
Capped wrapper for the trace statement.  The underlying trace fact itself does
not need the cap; LastReadyCapped simply supplies the old LastReady premise.
-/
def Lemma16CdTraceUntilSuccessCappedSpec : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (k : Fin n)
      (kind : PPL.TokenKind),
    LastReadyCapped ring C ->
    PPL.Cd ring k kind C ->
      forall schedule : DetSchedule n,
        Or
          (PPL.CPB ring
            (PPL.Probability.runPPL ring C schedule))
          (PPL.CdTrace hpsi ring k kind C schedule)

/-! ## Forgetting the clock cap -/

private theorem distReady_of_capped
    {n psi kappa : Nat}
    {ring : DirectedRing n}
    {C : Config n psi kappa}
    (h : DistReadyCapped ring C) :
    DistReady ring C := by
  unfold DistReadyCapped at h
  unfold DistReady
  exact And.intro h.1.1 h.2

private theorem lastReady_of_capped
    {n psi kappa : Nat}
    {ring : DirectedRing n}
    {C : Config n psi kappa}
    (h : LastReadyCapped ring C) :
    LastReady ring C := by
  unfold LastReadyCapped at h
  unfold LastReady
  exact And.intro (distReady_of_capped h.1) h.2

theorem lemma16CdTraceUntilSuccessCapped_of_uncapped
    (htrace : Lemma16CdTraceUntilSuccessSpec) :
    Lemma16CdTraceUntilSuccessCappedSpec := by
  intro n psi kappa hn3 hpsi ring C k kind
  intro hlast hCd schedule
  exact
    htrace hn3 hpsi ring C k kind
      (lastReady_of_capped hlast) hCd schedule

/-! ## Capped endpoint persistence -/

theorem lemma16ModeEndpointCappedSpec_of_persistence
    (hpersist : Lemma16DetectPersistenceCapped) :
    Lemma16ModeEndpointCappedSpec := by
  intro n psi kappa hn3 hpsi ring C word hreach
  induction word generalizing C with
  | nil =>
      have hgood :
          detectCappedOrCPBB ring C = true := by
        simpa [reachesDetectCappedOrCPB] using hreach
      have hnow :
          Or (PPL.CPB ring C)
            (DetectReadyCapped ring C) := by
        exact of_decide_eq_true hgood
      simpa [PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule] using hnow
  | cons e rest ih =>
      cases hgood :
          detectCappedOrCPBB ring C with
      | true =>
          have hnow :
              Or (PPL.CPB ring C)
                (DetectReadyCapped ring C) := by
            exact of_decide_eq_true hgood
          rcases hnow with hcpb | hdet
          · exact
              Or.inl
                (cpb_run_closed
                  hn3 hpsi ring C
                  (e :: rest) hcpb)
          · exact
              hpersist
                hn3 hpsi ring C
                (e :: rest) hdet
      | false =>
          have htail :
              reachesDetectCappedOrCPB ring
                  (PopulationProtocol.step
                    (PPL.protocol psi kappa) ring C e)
                  rest = true := by
            simpa [reachesDetectCappedOrCPB,
              hgood] using hreach
          simp only [PPL.Probability.runPPL,
            PPL.Probability.runPopulationSchedule]
          exact
            ih
              (C :=
                PopulationProtocol.step
                  (PPL.protocol psi kappa) ring C e)
              htail

/-! ## Local finite-word counting helpers copied from ReachCPB -/

private theorem cappedAllSchedules_add
    (n a b : Nat) :
    allSchedules n (a + b) =
      (allSchedules n a).flatMap
        (fun pre =>
          (allSchedules n b).map
            (fun suf => pre ++ suf)) := by
  induction b with
  | zero =>
      simp [allSchedules]
  | succ b ih =>
      rw [Nat.add_succ, allSchedules, ih]
      simp only [allSchedules,
        List.flatMap_assoc,
        List.map_flatMap,
        List.flatMap_map]
      congr
      funext pre
      congr
      funext suf
      rw [List.map_ofFn]
      congr 1
      funext e
      simp [List.append_assoc]

private theorem cappedRunPPL_append
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    PPL.Probability.runPPL ring C (u ++ v) =
      PPL.Probability.runPPL ring
        (PPL.Probability.runPPL ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append,
        PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule]
      exact
        ih
          (C :=
            PPL.Probability.pplStep ring C e)

private theorem cappedCountP_mono
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq :
      forall x, p x = true -> q x = true) :
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
          have hqx : q x = true :=
            hpq x hp
          simp [hp, hqx]
          omega

private theorem cappedScaled_sum
    {A : Type}
    (xs : List A)
    (p : A -> Bool)
    (f : A -> Nat)
    (scale u v : Nat)
    (hpoint :
      forall x, x ∈ xs ->
        scale * f x <=
          (if p x then u else 0) + v) :
    scale * (xs.map f).sum <=
      xs.countP p * u + xs.length * v := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx := hpoint x (by simp)
      have ht :=
        ih
          (fun y hy =>
            hpoint y (by simp [hy]))
      rw [List.map_cons, List.sum_cons,
        List.countP_cons, List.length_cons,
        Nat.mul_add, Nat.succ_mul]
      cases hp : p x <;>
        simp [hp, Nat.add_mul] at hx ⊢ <;>
        omega

private def cappedChildEndpointFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (U : Nat)
    (pre : DetSchedule n) : Nat :=
  ((allSchedules n U).map
    (fun suf => pre ++ suf)).countP
      (fun word =>
        !good
          (PPL.Probability.runPPL
            ring C word))

private theorem cappedChildEndpointFailureCount_le_full
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (U : Nat)
    (pre : DetSchedule n) :
    cappedChildEndpointFailureCount
        ring good C U pre <=
      n ^ U := by
  unfold cappedChildEndpointFailureCount
  calc
    ((allSchedules n U).map
      (fun suf => pre ++ suf)).countP
        (fun word =>
          !good
            (PPL.Probability.runPPL
              ring C word))
        <=
      ((allSchedules n U).map
        (fun suf => pre ++ suf)).length :=
      List.countP_le_length
    _ = (allSchedules n U).length := by
      rw [List.length_map]
    _ = n ^ U :=
      allSchedules_length n U

private theorem cappedChildEndpointFailureCount_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (U : Nat)
    (pre : DetSchedule n) :
    cappedChildEndpointFailureCount
        ring good C U pre =
      endpointFailureCount
        ring good
        (PPL.Probability.runPPL
          ring C pre) U := by
  unfold cappedChildEndpointFailureCount
    endpointFailureCount
  rw [List.countP_map]
  simp only [Function.comp_def]
  apply congrArg
    (fun p =>
      (allSchedules n U).countP p)
  funext suf
  rw [cappedRunPPL_append]

private theorem cappedEndpointFailureCount_eq_child_sum
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (T U : Nat) :
    endpointFailureCount ring good C (T + U) =
      ((allSchedules n T).map
        (cappedChildEndpointFailureCount
          ring good C U)).sum := by
  unfold endpointFailureCount
    cappedChildEndpointFailureCount
  rw [cappedAllSchedules_add,
    List.countP_flatMap]
  rfl

private theorem cappedPhaseBind
    {n psi kappa T U A B : Nat}
    (ring : DirectedRing n)
    (mid final : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (hmid :
      n * endpointFailureCount
            ring mid C T <=
        A * n ^ T)
    (hnext :
      forall D : Config n psi kappa,
        mid D = true ->
          n * endpointFailureCount
                ring final D U <=
            B * n ^ U) :
    n * endpointFailureCount
          ring final C (T + U) <=
      (A + B) * n ^ (T + U) := by
  let badPre : DetSchedule n -> Bool :=
    fun pre =>
      !mid
        (PPL.Probability.runPPL
          ring C pre)
  let child : DetSchedule n -> Nat :=
    cappedChildEndpointFailureCount
      ring final C U

  have hpoint :
      forall pre, pre ∈ allSchedules n T ->
        n * child pre <=
          (if badPre pre
            then n * n ^ U else 0) +
            B * n ^ U := by
    intro pre hpre
    let D :=
      PPL.Probability.runPPL
        ring C pre
    by_cases hm : mid D = true
    · have hbad : badPre pre = false := by
        show (!mid D) = false
        rw [hm]
        rfl
      rw [hbad]
      simp only [Bool.false_eq_true,
        ↓reduceIte, Nat.zero_add]
      have heq :
          child pre =
            endpointFailureCount
              ring final D U := by
        dsimp [child, D]
        exact
          cappedChildEndpointFailureCount_eq
            ring final C U pre
      rw [heq]
      exact hnext D hm
    · have hmfalse : mid D = false := by
        cases h : mid D with
        | false =>
            rfl
        | true =>
            exact False.elim (hm h)
      have hbad : badPre pre = true := by
        show (!mid D) = true
        rw [hmfalse]
        rfl
      rw [hbad]
      simp only [if_true]
      have hfull :
          child pre <= n ^ U := by
        dsimp [child]
        exact
          cappedChildEndpointFailureCount_le_full
            ring final C U pre
      have hmul :=
        Nat.mul_le_mul_left n hfull
      omega

  have hsum :=
    cappedScaled_sum
      (allSchedules n T)
      badPre child
      n (n * n ^ U) (B * n ^ U)
      hpoint

  have hbadCount :
      (allSchedules n T).countP badPre =
        endpointFailureCount
          ring mid C T := by
    rfl
  have hlen :
      (allSchedules n T).length =
        n ^ T :=
    allSchedules_length n T
  rw [hbadCount, hlen] at hsum

  have hfirst :
      endpointFailureCount ring mid C T *
          (n * n ^ U) <=
        (A * n ^ T) * n ^ U := by
    calc
      endpointFailureCount ring mid C T *
            (n * n ^ U) =
          (n *
            endpointFailureCount ring mid C T) *
              n ^ U := by
        ac_rfl
      _ <=
          (A * n ^ T) * n ^ U :=
        Nat.mul_le_mul_right
          (n ^ U) hmid

  have hdecomp :=
    cappedEndpointFailureCount_eq_child_sum
      ring final C T U
  rw [hdecomp]
  calc
    n *
        ((allSchedules n T).map child).sum
        <=
      endpointFailureCount ring mid C T *
          (n * n ^ U) +
        n ^ T * (B * n ^ U) :=
      hsum
    _ <=
      (A * n ^ T) * n ^ U +
        n ^ T * (B * n ^ U) :=
      Nat.add_le_add
        hfirst (Nat.le_refl _)
    _ =
      (A + B) * n ^ (T + U) := by
      rw [Nat.pow_add, Nat.add_mul]
      simp only [Nat.mul_comm,
        Nat.mul_assoc, Nat.mul_left_comm]

private theorem cappedEndpointFailureCount_zero
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (T : Nat)
    (hall :
      forall word : DetSchedule n,
        good
          (PPL.Probability.runPPL
            ring C word) = true) :
    endpointFailureCount
      ring good C T = 0 := by
  unfold endpointFailureCount
  apply List.countP_eq_zero.mpr
  intro word hword hbad
  have hg := hall word
  simp [hg] at hbad

private theorem cappedFixedWordPhaseBound
    {n psi kappa : Nat}
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= lemma16K n)
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (L : Nat)
    (hlen : word.length = L)
    (hforce :
      forall schedule : DetSchedule n,
        word.Sublist schedule ->
          good
            (PPL.Probability.runPPL
              ring C schedule) = true) :
    n *
        endpointFailureCount ring good C
          (2 * n *
            (L + 4 * lemma16K n)) <=
      n ^ (2 * n *
        (L + 4 * lemma16K n)) := by
  let H :=
    2 * n *
      (L + 4 * lemma16K n)
  have hmono :
      endpointFailureCount ring good C H <=
        PPL.Probability.fixedWordMissCount
          word H := by
    unfold endpointFailureCount
    change
      (allSchedules n H).countP
          (fun schedule =>
            !good
              (PPL.Probability.runPPL
                ring C schedule)) <=
        (allSchedules n H).countP
          (fun schedule =>
            decide (Not (word.Sublist schedule)))
    apply cappedCountP_mono
    intro schedule hbad
    by_cases hsub : word.Sublist schedule
    · have hg :=
        hforce schedule hsub
      simp [hg] at hbad
    · simp [hsub]

  have hpsiPow :
      2 ^ psi <=
        2 ^ lemma16K n :=
    Nat.pow_le_pow_right
      (by decide) hpsiK
  have hK4 :
      lemma16K n <=
        4 * lemma16K n := by
    omega
  have h4Pow :
      2 ^ lemma16K n <=
        2 ^ (4 * lemma16K n) :=
    Nat.pow_le_pow_right
      (by decide) hK4
  have hnscale :
      n <= 2 ^ (4 * lemma16K n) :=
    Nat.le_trans hnpow
      (Nat.le_trans hpsiPow h4Pow)

  have hfixed :=
    PPL.Probability.fixedWordMissCount_mul_twoPow_le_of_length
      word L (4 * lemma16K n) hlen
  change
    PPL.Probability.fixedWordMissCount
          word H *
        2 ^ (4 * lemma16K n) <=
      n ^ H at hfixed

  have hscaled :
      n *
          PPL.Probability.fixedWordMissCount
            word H <=
        n ^ H := by
    calc
      n *
          PPL.Probability.fixedWordMissCount
            word H =
        PPL.Probability.fixedWordMissCount
            word H * n := by
          ac_rfl
      _ <=
        PPL.Probability.fixedWordMissCount
            word H *
          2 ^ (4 * lemma16K n) :=
        Nat.mul_le_mul_left _ hnscale
      _ <= n ^ H :=
        hfixed

  exact
    Nat.le_trans
      (Nat.mul_le_mul_left n hmono)
      hscaled

/-! ## Repaired per-phase bounds -/

private theorem modePhaseBoundCapped
    (hclock :
      PPL.Modes.Lemma6.Lemma6ClockRiseCount)
    (hmode :
      Lemma16ModeEndpointCappedSpec)
    (hmodeCount :
      Lemma16ModeCappedReachCountSpec)
    {n psi kappa modeC : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 6 <= modeC)
    (hkappa : kappa = 8 * modeC * psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hclean :
      allLivePeacefulB ring C = true) :
    n *
        endpointFailureCount
          ring (detectCappedOrCPBB ring) C
          (lemma16H6 n psi kappa) <=
      8 * n ^ lemma16H6 n psi kappa := by
  have hcleanP :
      AllLivePeaceful ring C :=
    of_decide_eq_true hclean

  have hmono :
      endpointFailureCount
          ring (detectCappedOrCPBB ring) C
          (lemma16H6 n psi kappa) <=
        lemma16ModeCappedReachFailureCount
          ring C (lemma16H6 n psi kappa) := by
    unfold endpointFailureCount
      lemma16ModeCappedReachFailureCount
    apply cappedCountP_mono
    intro word hbad
    cases hr :
        reachesDetectCappedOrCPB
          ring C word with
    | false =>
        simp [hr]
    | true =>
        have hor :=
          hmode hn3 hpsi ring C word hr
        have hgood :
            detectCappedOrCPBB ring
              (PPL.Probability.runPPL
                ring C word) = true := by
          simp [detectCappedOrCPBB, hor]
        simp [hgood] at hbad

  have hreach :=
    hmodeCount
      hn3 hpsi hc hkappa hnpow
      ring C hcleanP hclock

  exact
    Nat.le_trans
      (Nat.mul_le_mul_left n hmono)
      hreach

private theorem distPhaseBoundCapped
    (hdist : Lemma16DistForcingCappedSpec)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= lemma16K n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hstart :
      detectCappedOrCPBB ring C = true) :
    n *
        endpointFailureCount
          ring (distCappedOrCPBB ring) C
          (lemma16HDist n) <=
      n ^ lemma16HDist n := by
  have hstartP :
      Or (PPL.CPB ring C)
        (DetectReadyCapped ring C) :=
    of_decide_eq_true hstart
  rcases hstartP with hcpb | hdet
  · have hz :=
      cappedEndpointFailureCount_zero
        ring (distCappedOrCPBB ring) C
        (lemma16HDist n)
        (fun word => by
          have hend :=
            cpb_run_closed
              hn3 hpsi ring C word hcpb
          simp [distCappedOrCPBB, hend])
    rw [hz]
    simp
  · obtain ⟨word, hlen, hforce⟩ :=
      hdist hn3 hpsi ring C hdet
    have hb :=
      cappedFixedWordPhaseBound
        hnpow hpsiK
        ring (distCappedOrCPBB ring) C
        word 1 hlen
        (fun schedule hsub => by
          have hor :=
            hforce schedule hsub
          simp [distCappedOrCPBB, hor])
    simpa [lemma16HDist] using hb

private theorem lastPhaseBoundCapped
    (hlast : Lemma16LastForcingCappedSpec)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= lemma16K n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hstart :
      distCappedOrCPBB ring C = true) :
    n *
        endpointFailureCount
          ring (lastCappedOrCPBB ring) C
          (lemma16HLast n) <=
      n ^ lemma16HLast n := by
  have hstartP :
      Or (PPL.CPB ring C)
        (DistReadyCapped ring C) :=
    of_decide_eq_true hstart
  rcases hstartP with hcpb | hdistReady
  · have hz :=
      cappedEndpointFailureCount_zero
        ring (lastCappedOrCPBB ring) C
        (lemma16HLast n)
        (fun word => by
          have hend :=
            cpb_run_closed
              hn3 hpsi ring C word hcpb
          simp [lastCappedOrCPBB, hend])
    rw [hz]
    simp
  · obtain ⟨word, hlen, hforce⟩ :=
      hlast hn3 hpsi ring C hdistReady
    have hb :=
      cappedFixedWordPhaseBound
        hnpow hpsiK
        ring (lastCappedOrCPBB ring) C
        word n hlen
        (fun schedule hsub => by
          have hor :=
            hforce schedule hsub
          simp [lastCappedOrCPBB, hor])
    simpa [lemma16HLast] using hb

private theorem tokenPhaseBoundCapped
    (hmismatch : Lemma16MismatchWitnessCappedSpec)
    (htrace : Lemma16CdTraceUntilSuccessSpec)
    (hcore : PPL.lemma4_deterministic_core)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= lemma16K n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hstart :
      lastCappedOrCPBB ring C = true) :
    n *
        endpointFailureCount
          ring (cpbB ring) C
          (lemma16HToken n psi) <=
      n ^ lemma16HToken n psi := by
  have hstartP :
      Or (PPL.CPB ring C)
        (LastReadyCapped ring C) :=
    of_decide_eq_true hstart
  rcases hstartP with hcpb | hlastCapped
  · have hz :=
      cappedEndpointFailureCount_zero
        ring (cpbB ring) C
        (lemma16HToken n psi)
        (fun word => by
          have hend :=
            cpb_run_closed
              hn3 hpsi ring C word hcpb
          simp [cpbB, hend])
    rw [hz]
    simp
  · have hlast :
        LastReady ring C :=
      lastReady_of_capped hlastCapped
    have hnotPerfect :=
      lemma16LastReady_not_perfect
        hn3 hnpow ring C hlast
    obtain
        ⟨k, kind, hCd, hcompletion⟩ :=
      hmismatch
        hn3 hpsi hnpow
        ring C hlastCapped hnotPerfect
    have hforce :
        forall schedule : DetSchedule n,
          (PPL.lemma4Word ring k psi).Sublist
              schedule ->
            cpbB ring
              (PPL.Probability.runPPL
                ring C schedule) = true := by
      intro schedule hsub
      by_cases hcpbEnd :
          PPL.CPB ring
            (PPL.Probability.runPPL
              ring C schedule)
      · simp [cpbB, hcpbEnd]
      · have htraceOr :=
          htrace
            hn3 hpsi ring C k kind
            hlast hCd schedule
        rcases htraceOr with hcpbNow | hCdTrace
        · exact False.elim (hcpbEnd hcpbNow)
        · have hcompleted :=
            hcore
              hpsi ring k kind
              C schedule hCdTrace hsub
          have hcpbNow :=
            hcompletion schedule hcompleted
          exact False.elim (hcpbEnd hcpbNow)
    have hlen0 :=
      PPL.lemma4Word_length
        hpsi ring k
    have hlen :
        (PPL.lemma4Word ring k psi).length =
          lemma16L4 psi := by
      simpa [lemma16L4] using hlen0
    have hb :=
      cappedFixedWordPhaseBound
        hnpow hpsiK
        ring (cpbB ring) C
        (PPL.lemma4Word ring k psi)
        (lemma16L4 psi) hlen hforce
    simpa [lemma16HToken] using hb

/-! ## Capped Lemma 16 assembly -/

/--
Same Lemma-16 horizon and coefficient 12 as ReachCPB.lean, but with the
false uncapped Detect/Dist/Last chain removed.

The only new quantitative premise is Lemma16ModeCappedReachCountSpec, because
the currently proved Lemma6WordBound stops on stale allDetect states and
therefore cannot imply a capped endpoint bound.
-/
theorem lemma16_wordBound_capped
    (h15 : Lemma16BulletSweepNatBound)
    (hpersist : Lemma16DetectPersistenceCapped)
    (hmodeCount : Lemma16ModeCappedReachCountSpec)
    (hdist : Lemma16DistForcingCappedSpec)
    (hlast : Lemma16LastForcingCappedSpec)
    (hmismatch : Lemma16MismatchWitnessCappedSpec)
    (htrace : Lemma16CdTraceUntilSuccessSpec)
    (hcore : PPL.lemma4_deterministic_core)
    {n psi kappa modeC : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 6 <= modeC)
    (hkappa : kappa = 8 * modeC * psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= lemma16K n)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Lemma16WordBound ring C := by
  have hclock :
      PPL.Modes.Lemma6.Lemma6ClockRiseCount :=
    PPL.Modes.Lemma6.lemma6ClockRiseCount

  have hmode :
      Lemma16ModeEndpointCappedSpec :=
    lemma16ModeEndpointCappedSpec_of_persistence
      hpersist

  have h0 :
      n *
          endpointFailureCount
            ring (allLivePeacefulB ring) C
            (lemma16H15 n) <=
        1 * n ^ lemma16H15 n := by
    simpa using
      h15 hn3 hpsi ring C

  have h01 :=
    cappedPhaseBind
      ring
      (allLivePeacefulB ring)
      (detectCappedOrCPBB ring)
      C h0
      (fun D hD =>
        modePhaseBoundCapped
          hclock hmode hmodeCount
          hn3 hpsi hc hkappa hnpow
          ring D hD)

  have h012 :=
    cappedPhaseBind (B := 1)
      ring
      (detectCappedOrCPBB ring)
      (distCappedOrCPBB ring)
      C h01
      (fun D hD =>
        Nat.le_trans
          (distPhaseBoundCapped
            hdist
            hn3 hpsi hnpow hpsiK
            ring D hD)
          (Nat.le_of_eq (Nat.one_mul _).symm))

  have h0123 :=
    cappedPhaseBind (B := 1)
      ring
      (distCappedOrCPBB ring)
      (lastCappedOrCPBB ring)
      C h012
      (fun D hD =>
        Nat.le_trans
          (lastPhaseBoundCapped
            hlast
            hn3 hpsi hnpow hpsiK
            ring D hD)
          (Nat.le_of_eq (Nat.one_mul _).symm))

  have hfinal :=
    cappedPhaseBind (B := 1)
      ring
      (lastCappedOrCPBB ring)
      (cpbB ring)
      C h0123
      (fun D hD =>
        Nat.le_trans
          (tokenPhaseBoundCapped
            hmismatch htrace hcore
            hn3 hpsi hnpow hpsiK
            ring D hD)
          (Nat.le_of_eq (Nat.one_mul _).symm))

  have hfailEq :=
    lemma16FailureCount_eq_endpoint
      hn3 hpsi ring C
  unfold Lemma16WordBound
  rw [hfailEq]
  simpa [lemma16Horizon] using hfinal

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16ModeEndpointCappedSpec_of_persistence
#print axioms PPL.Convergence.ReachCPB.lemma16CdTraceUntilSuccessCapped_of_uncapped
#print axioms PPL.Convergence.ReachCPB.lemma16_wordBound_capped
