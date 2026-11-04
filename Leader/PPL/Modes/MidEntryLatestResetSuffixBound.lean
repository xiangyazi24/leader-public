import Leader.PPL.Modes.MidEntrySweepSplice
import Leader.PPL.Modes.StoppedClockSuffixFreeze
import Leader.PPL.Probability.MarkedWordTransfer
import Leader.PPL.Probability.EncounterProjection
import Leader.PPL.Probability.LotteryMoment
import Leader.Core.FiniteUniformStoppingTree

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-!
# Lemma 5(i): latest-reset C_mid suffix bound

Truth audit.

The frozen per-arm statement is true.  If the fixed arm prefix never reaches
maxResetSignalB, lemma5iMidClockBadB is false for every suffix.  Otherwise a
bad paper sweep has allClockResetsSeenB=true and no C_mid prefix.  Because
neverLeaderless is reachability-closed, the final paper-prefix configuration
still has a leader.  Hence some agent fails the local C_mid clock/mode clause.
That agent has undergone a real Algorithm-4 reset during the sweep.

The only bounded-round residual below is the wordwise extraction of the
latest reset for that witness.  From the latest reset to the final paper
boundary, no later reset occurs; the reset starts clock at zero, and a final
clock above kappa/2 (or Detect, which is backed by clock=kappa) forces more
than 24*psi clock ticks.  clockSuffixTickLotteryBridge maps those ticks to the
fixed-agent H/T parser.  If the whole fixed-agent sweep has at most 24*n
incidents, the parser event below follows; otherwise the word is charged to
the accepted 24*n encounter upper tail.

No scheduler count is hidden in the residual.
-/

/-! ## Literal reset row from the closed corrected suffix theorem -/

theorem lemma5iMidResetClockZero
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (x e : Fin n)
    (hreset : clockResetAt ring C x e = true) :
    (pplStep ring C e x).clock.val = 0 := by
  exact
    PPL.Probability.stoppedClockSuffixBoundsCorrected.1
      n psi kappa ring C x e hpsi hreset

/-! ## Paper-sweep fixed-agent bad events -/

def lemma5iMidEncounterAgentBadB
    {n : Nat}
    (ring : DirectedRing n)
    (x : Fin n)
    (sweep : DetSchedule n) : Bool :=
  decide
    (24 * n <
      predictableHostHits ring (fun _ => x) sweep)

def lemma5iMidEncounterAgentFailureCount
    {n : Nat}
    (ring : DirectedRing n)
    (x : Fin n) : Nat :=
  (allSchedules n (lemma5PaperSweepHorizon n)).countP
    (lemma5iMidEncounterAgentBadB ring x)

def lemma5iMidLotteryAgentBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (x : Fin n)
    (sweep : DetSchedule n) : Bool :=
  let bits :=
    stoppedEncounterBits ring
      (fun _ => x) (fun _ => false) sweep
  decide
    (And
      (bits.length <= lotteryL7Horizon psi 2)
      (24 * psi <=
        (lotteryRun psi
          (lotteryOffset (D x).hits.val) bits).wins))

def lemma5iMidLotteryAgentFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (x : Fin n) : Nat :=
  (allSchedules n (lemma5PaperSweepHorizon n)).countP
    (lemma5iMidLotteryAgentBadB ring D x)

def lemma5iMidAgentBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (x : Fin n)
    (sweep : DetSchedule n) : Bool :=
  lemma5iMidEncounterAgentBadB ring x sweep ||
    lemma5iMidLotteryAgentBadB ring D x sweep

def lemma5iMidPaperFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n) : Nat :=
  (allSchedules n (lemma5PaperSweepHorizon n)).countP
    (fun sweep =>
      lemma5iMidClockBadB ring C (pre ++ sweep))

/--
Smallest remaining physical residual.

It is wordwise: there is no count or probability statement here.  The
corrected reset theorem and clockSuffixTickLotteryBridge are the intended
physical inputs.  The 3 <= psi and psi <= n conclusions are harmless
consequences of a bad sweep: after the latest reset, more than 24*psi wins are
needed inside a raw window of only 6*n^2 letters.  In particular psi=2 cannot
produce a C_mid-bad word under the all-resets-seen conjunct.
-/
def Lemma5iMidLatestResetWordProjection : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    StoppedClockSuffixBoundsCorrected ->
    forall
      (pre : DetSchedule n)
      (sweep : DetSchedule n),
      pre ∈ allSchedules n (lemma5ArmHorizon n) ->
      sweep ∈ allSchedules n (lemma5PaperSweepHorizon n) ->
      lemma5iMidClockBadB ring C (pre ++ sweep) = true ->
      And
        (3 <= psi)
        (And
          (psi <= n)
          (exists x : Fin n,
            lemma5iMidAgentBadB
              ring (runPPL ring C pre) x sweep = true))

/-! ## Small list/count helpers -/

private def midAnyPred {A : Type} :
    List (A -> Bool) -> A -> Bool
  | [], _ => false
  | p :: ps, x => p x || midAnyPred ps x

private def midAnyPred_true_of_mem
    {A : Type}
    (ps : List (A -> Bool))
    (p : A -> Bool)
    (x : A)
    (hmem : p ∈ ps)
    (hp : p x = true) :
    midAnyPred ps x = true := by
  induction ps with
  | nil =>
      simp at hmem
  | cons q qs ih =>
      rcases List.mem_cons.mp hmem with hq | hq
      · subst q
        simp [midAnyPred, hp]
      · have ht := ih hq
        simp [midAnyPred, ht]

private def midCountP_mono
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

private def midCountP_mono_mem
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq :
      forall x,
        x ∈ xs ->
        p x = true ->
        q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have htail :
          forall y,
            y ∈ xs ->
            p y = true ->
            q y = true := by
        intro y hy
        exact hpq y (by simp [hy])
      have hi := ih htail
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases q x <;>
            simp_all <;>
            omega
      | true =>
          have hq :
              q x = true :=
            hpq x (by simp) hp
          simpa [hp, hq] using hi

private def midCountP_or_le_add
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

private def midCountP_anyPred_le_sum
    {A : Type}
    (xs : List A)
    (ps : List (A -> Bool)) :
    xs.countP (midAnyPred ps) <=
      (ps.map (fun p => xs.countP p)).sum := by
  induction ps with
  | nil =>
      simp [midAnyPred]
  | cons p ps ih =>
      calc
        xs.countP (midAnyPred (p :: ps)) =
            xs.countP
              (fun x => p x || midAnyPred ps x) := by
          rfl
        _ <=
            xs.countP p +
              xs.countP (midAnyPred ps) :=
          midCountP_or_le_add xs p (midAnyPred ps)
        _ <=
            xs.countP p +
              (ps.map (fun q => xs.countP q)).sum :=
          Nat.add_le_add_left ih _
        _ =
            ((p :: ps).map
              (fun q => xs.countP q)).sum := by
          simp

private def midNatLeTwoPowSelf (n : Nat) :
    n <= 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have hp : 0 < 2 ^ n :=
        Nat.pow_pos (by omega)
      omega

/-! ## Exact arm/paper/padding projections -/

private def midTakeLengthAppend
    {A : Type}
    (xs ys : List A) :
    (xs ++ ys).take xs.length = xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]

private def midDropLengthAppend
    {A : Type}
    (xs ys : List A) :
    (xs ++ ys).drop xs.length = ys := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]

private def midArmPrefix_append
    {n : Nat}
    (pre tail : DetSchedule n)
    (hpre :
      pre.length = lemma5ArmHorizon n) :
    lemma5iArmPrefix (pre ++ tail) = pre := by
  unfold lemma5iArmPrefix
  rw [← hpre]
  exact midTakeLengthAppend pre tail

private def midPaperSweep_append
    {n : Nat}
    (pre sweep pad : DetSchedule n)
    (hpre :
      pre.length = lemma5ArmHorizon n)
    (hsweep :
      sweep.length = lemma5PaperSweepHorizon n) :
    lemma5iPaperSweepSuffix
        (pre ++ sweep ++ pad) =
      sweep := by
  unfold lemma5iPaperSweepSuffix
  have hdrop :
      (pre ++ sweep ++ pad).drop
          (lemma5ArmHorizon n) =
        sweep ++ pad := by
    simpa only [List.append_assoc, hpre] using
      (midDropLengthAppend pre (sweep ++ pad))
  rw [hdrop, ← hsweep]
  exact midTakeLengthAppend sweep pad

private def midPaperSweep_append_short
    {n : Nat}
    (pre sweep : DetSchedule n)
    (hpre :
      pre.length = lemma5ArmHorizon n)
    (hsweep :
      sweep.length = lemma5PaperSweepHorizon n) :
    lemma5iPaperSweepSuffix
        (pre ++ sweep) =
      sweep := by
  have h :=
    midPaperSweep_append
      pre sweep ([] : DetSchedule n)
      hpre hsweep
  simpa using h

private def midPaperPrefix_append
    {n : Nat}
    (pre sweep pad : DetSchedule n)
    (hpre :
      pre.length = lemma5ArmHorizon n)
    (hsweep :
      sweep.length = lemma5PaperSweepHorizon n) :
    lemma5iPaperPrefix
        (pre ++ sweep ++ pad) =
      pre ++ sweep := by
  unfold lemma5iPaperPrefix
  have ha :
      lemma5iArmPrefix (pre ++ sweep ++ pad) = pre := by
    simpa only [List.append_assoc] using
      (midArmPrefix_append
        pre (sweep ++ pad) hpre)
  rw [ha]
  rw [midPaperSweep_append
        pre sweep pad hpre hsweep]

private def midPaperPrefix_append_short
    {n : Nat}
    (pre sweep : DetSchedule n)
    (hpre :
      pre.length = lemma5ArmHorizon n)
    (hsweep :
      sweep.length = lemma5PaperSweepHorizon n) :
    lemma5iPaperPrefix
        (pre ++ sweep) =
      pre ++ sweep := by
  unfold lemma5iPaperPrefix
  rw [midArmPrefix_append pre sweep hpre]
  rw [midPaperSweep_append_short
        pre sweep hpre hsweep]

private def midBad_padding
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre sweep pad : DetSchedule n)
    (hpre :
      pre.length = lemma5ArmHorizon n)
    (hsweep :
      sweep.length = lemma5PaperSweepHorizon n) :
    lemma5iMidClockBadB
        ring C (pre ++ sweep ++ pad) =
      lemma5iMidClockBadB
        ring C (pre ++ sweep) := by
  have haLong :
      lemma5iArmPrefix (pre ++ sweep ++ pad) = pre := by
    simpa only [List.append_assoc] using
      (midArmPrefix_append
        pre (sweep ++ pad) hpre)
  have hsLong :=
    midPaperSweep_append
      pre sweep pad hpre hsweep
  have hpLong :=
    midPaperPrefix_append
      pre sweep pad hpre hsweep
  have haShort :=
    midArmPrefix_append pre sweep hpre
  have hsShort :=
    midPaperSweep_append_short
      pre sweep hpre hsweep
  have hpShort :=
    midPaperPrefix_append_short
      pre sweep hpre hsweep
  unfold lemma5iMidClockBadB
  dsimp only
  rw [haLong, hsLong, hpLong,
    haShort, hsShort, hpShort]

private def midSweepHorizon_split (n : Nat) :
    lemma5PaperSweepHorizon n +
        2 * n * n =
      lemma5SweepHorizon n := by
  unfold lemma5PaperSweepHorizon
    lemma5SweepHorizon
  calc
    6 * n * n + 2 * n * n =
        6 * (n * n) + 2 * (n * n) := by
      rw [Nat.mul_assoc, Nat.mul_assoc]
    _ = (6 + 2) * (n * n) :=
      (Nat.add_mul 6 2 (n * n)).symm
    _ = 8 * n * n := by
      rw [Nat.mul_assoc]

private def allSchedules_add_mid
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

private def midSumIfCount
    {A : Type}
    (xs : List A)
    (p : A -> Bool)
    (c : Nat) :
    (xs.map
      (fun x => if p x then c else 0)).sum =
      xs.countP p * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons,
        List.countP_cons]
      cases hp : p x <;>
        simp [hp, ih, Nat.succ_mul, Nat.add_comm]

private def countP_prefixInvariant
    {n H P : Nat}
    (p : DetSchedule n -> Bool)
    (hinv :
      forall sweep : DetSchedule n,
        sweep.length = H ->
        forall pad : DetSchedule n,
          p (sweep ++ pad) = p sweep) :
    (allSchedules n (H + P)).countP p =
      (allSchedules n H).countP p *
        n ^ P := by
  rw [allSchedules_add_mid,
    List.countP_flatMap]
  simp only [Function.comp_def]
  have hmap :
      ((allSchedules n H).map
        (fun sweep =>
          ((allSchedules n P).map
            (fun pad => sweep ++ pad)).countP p)) =
      (allSchedules n H).map
        (fun sweep =>
          if p sweep then n ^ P else 0) := by
    apply List.map_congr_left
    intro sweep hsweep
    rw [List.countP_map]
    simp only [Function.comp_def]
    have hlen :=
      allSchedules_schedule_length
        n H sweep hsweep
    have hfun :
        (fun pad : DetSchedule n =>
          p (sweep ++ pad)) =
        (fun _ : DetSchedule n =>
          p sweep) := by
      funext pad
      exact hinv sweep hlen pad
    rw [hfun]
    cases hp : p sweep <;>
      simp [hp, allSchedules_length]
  rw [hmap]
  exact midSumIfCount
    (allSchedules n H) p (n ^ P)

private def lemma5iMidSuffix_eq_paper_pad
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n)
    (hpre :
      pre ∈ allSchedules n
        (lemma5ArmHorizon n)) :
    lemma5iMidSuffixFailureCount
        ring C pre =
      lemma5iMidPaperFailureCount
          ring C pre *
        n ^ (2 * n * n) := by
  let p : DetSchedule n -> Bool :=
    fun suf =>
      lemma5iMidClockBadB
        ring C (pre ++ suf)
  have hpreLen :=
    allSchedules_schedule_length
      n (lemma5ArmHorizon n)
      pre hpre
  have hinv :
      forall sweep : DetSchedule n,
        sweep.length =
            lemma5PaperSweepHorizon n ->
        forall pad : DetSchedule n,
          p (sweep ++ pad) =
            p sweep := by
    intro sweep hsweep pad
    dsimp [p]
    simpa [List.append_assoc] using
      midBad_padding
        ring C pre sweep pad
        hpreLen hsweep
  have hcount :=
    countP_prefixInvariant
      (n := n)
      (H := lemma5PaperSweepHorizon n)
      (P := 2 * n * n)
      p hinv
  rw [midSweepHorizon_split n] at hcount
  unfold lemma5iMidSuffixFailureCount
    lemma5iMidPaperFailureCount
  rw [List.countP_map]
  simpa [p, Function.comp_def]
    using hcount

/-!
The controller's first concern, formally: if the arm event never occurred,
the paper-sweep failure count is zero, uniformly in arbitrary C.
-/
theorem lemma5iMidPaperFailureCount_zero_of_noArm
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n)
    (hpre :
      pre ∈ allSchedules n
        (lemma5ArmHorizon n))
    (harm :
      reachesAux ring maxResetSignalB
        C pre = false) :
    lemma5iMidPaperFailureCount
      ring C pre = 0 := by
  unfold lemma5iMidPaperFailureCount
  apply List.countP_eq_zero.mpr
  intro sweep hsweep
  have hpreLen :=
    allSchedules_schedule_length
      n (lemma5ArmHorizon n)
      pre hpre
  have ha :=
    midArmPrefix_append
      pre sweep hpreLen
  simp [lemma5iMidClockBadB, ha, harm]

/-! ## Encounter and lottery counting -/

/-- Accepted 24n fixed-agent encounter tail, in the paper 6n² window. -/
theorem lemma5iMidEncounterAgentCount
    {n : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (x : Fin n) :
    2 ^ (4 * n) *
        lemma5iMidEncounterAgentFailureCount
          ring x <=
      n ^ lemma5PaperSweepHorizon n := by
  have h :=
    predictableHost24nBound
      n (by omega) ring (fun _ => x)
  change
    2 ^ (4 * n) *
        predictableHostUpperTailCount
          ring (fun _ => x)
          (lemma5PaperSweepHorizon n)
          (24 * n) <=
      n ^ lemma5PaperSweepHorizon n
  simpa [lemma5PaperSweepHorizon,
    Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm]
    using h

/-!
A stronger binary bound than the frozen target needs.

At E = L7(psi,2), the proved moment bound has fresh target 16*psi.
Markov at 24*psi-1 therefore leaves nine full psi bits of dyadic slack.
-/
theorem lemma5iMidFreshLottery24Count
    {psi : Nat}
    (hpsi : 2 <= psi) :
    2 ^ (9 * psi) *
        lotteryAtLeastWordCount
          psi 0
          (lotteryL7Horizon psi 2)
          (24 * psi - 1) <=
      2 ^ (lotteryL7Horizon psi 2) := by
  let E : Nat :=
    lotteryL7Horizon psi 2
  let M : Nat :=
    24 * psi - 1
  let B : Nat :=
    lotteryAtLeastWordCount
      psi 0 E M
  let DP : Nat :=
    lotteryNatDP psi
      (fun s => 2 ^ s.wins)
      E lotteryFresh

  have hm0 :=
    (lotteryTailMomentArithmetic
      psi 2 (by omega) (by omega)).1
  have hm :
      2 ^ (2 * psi) * DP <=
        2 ^ (E + 16 * psi) := by
    simpa [E, DP, lotteryTarget,
      Nat.mul_assoc]
      using hm0

  have hmark0 :=
    lotteryAtLeast_mul_twoPow_le_upperMoment
      psi E M
  rw [lotteryUpperMoment_eq_dp] at hmark0
  have hmark :
      B * 2 ^ M <= DP := by
    simpa [B, DP] using hmark0

  have hexp :
      25 * psi <= 2 * psi + M := by
    dsimp [M]
    omega

  have hpow :
      2 ^ (25 * psi) <=
        2 ^ (2 * psi + M) :=
    Nat.pow_le_pow_right
      (by omega : 0 < 2) hexp

  have hcore :
      B * 2 ^ (25 * psi) <=
        2 ^ (E + 16 * psi) := by
    calc
      B * 2 ^ (25 * psi) <=
          B * 2 ^ (2 * psi + M) :=
        Nat.mul_le_mul_left B hpow
      _ =
          2 ^ (2 * psi) *
            (B * 2 ^ M) := by
        rw [Nat.pow_add]
        ac_rfl
      _ <=
          2 ^ (2 * psi) * DP :=
        Nat.mul_le_mul_left
          (2 ^ (2 * psi)) hmark
      _ <= 2 ^ (E + 16 * psi) :=
        hm

  have hcancel :
      2 ^ (16 * psi) *
          (2 ^ (9 * psi) * B) <=
        2 ^ (16 * psi) * 2 ^ E := by
    calc
      2 ^ (16 * psi) *
            (2 ^ (9 * psi) * B) =
          B *
            (2 ^ (16 * psi) *
              2 ^ (9 * psi)) := by
        ac_rfl
      _ = B * 2 ^ (25 * psi) := by
        rw [← Nat.pow_add]
        congr 2
        omega
      _ <= 2 ^ (E + 16 * psi) :=
        hcore
      _ = 2 ^ (16 * psi) * 2 ^ E := by
        rw [Nat.add_comm, Nat.pow_add]

  have hfinal :
      2 ^ (9 * psi) * B <=
        2 ^ E :=
    Nat.le_of_mul_le_mul_left
      hcancel
      (Nat.pow_pos (by omega))

  simpa [B, E] using hfinal

/--
One fixed agent's lottery branch.  The arbitrary incoming hits offset loses
one win, so offset >= 24psi is compared with fresh >= 24psi-1.
-/
theorem lemma5iMidLotteryAgentCount
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (x : Fin n)
    (hoffset : WLGHeadOffsetBounds) :
    2 ^ (9 * psi) *
        lemma5iMidLotteryAgentFailureCount
          ring D x <=
      n ^ lemma5PaperSweepHorizon n := by
  let T : Nat :=
    lemma5PaperSweepHorizon n
  let E : Nat :=
    lotteryL7Horizon psi 2
  let M : Nat :=
    24 * psi
  let M0 : Nat :=
    24 * psi - 1
  let h : Nat :=
    (D x).hits.val
  let A : Nat :=
    lemma5iMidLotteryAgentFailureCount
      ring D x
  let B : Nat :=
    lotteryAtLeastWordCount
      psi h E M
  let B0 : Nat :=
    lotteryAtLeastWordCount
      psi 0 E M0
  let scale : Nat :=
    2 ^ (9 * psi)

  have hh : h <= psi := by
    dsimp [h]
    have hlt := (D x).hits.isLt
    omega

  have htransfer0 :=
    stoppedEncounterLotteryAtLeast_padded_transfer
      hn3 psi h ring
      (fun _ => x)
      (fun _ => false)
      T E M

  have htransfer :
      A * 2 ^ E <=
        n ^ T * B := by
    dsimp [A, B]
    unfold
      lemma5iMidLotteryAgentFailureCount
      lemma5iMidLotteryAgentBadB
    simpa [stoppedMarkedPaddedCount,
      E, M, T, decide_eq_true_eq]
      using htransfer0

  have hM :
      M0 + 1 = M := by
    dsimp [M0, M]
    omega

  have hhead : B <= B0 := by
    dsimp [B, B0]
    have hh0 :=
      (hoffset psi h E M0
        (by omega) hh).2.1
    rw [hM] at hh0
    exact hh0

  have hbinary :
      scale * B0 <= 2 ^ E := by
    dsimp [scale, B0, E, M0]
    exact
      lemma5iMidFreshLottery24Count
        hpsi

  have hscaled :
      (scale * A) * 2 ^ E <=
        n ^ T * 2 ^ E := by
    calc
      (scale * A) * 2 ^ E =
          scale * (A * 2 ^ E) := by
        ac_rfl
      _ <= scale * (n ^ T * B) :=
        Nat.mul_le_mul_left
          scale htransfer
      _ = n ^ T * (scale * B) := by
        ac_rfl
      _ <= n ^ T * (scale * B0) :=
        Nat.mul_le_mul_left
          (n ^ T)
          (Nat.mul_le_mul_left
            scale hhead)
      _ <= n ^ T * 2 ^ E :=
        Nat.mul_le_mul_left
          (n ^ T) hbinary

  have hfinal :
      scale * A <= n ^ T :=
    Nat.le_of_mul_le_mul_right
      hscaled
      (Nat.pow_pos (by omega : 0 < 2))

  simpa [scale, A, T] using hfinal

/-! ## Paper-window union from the wordwise physical projection -/

theorem lemma5iMidLatestResetPaperCount
    (hprojection :
      Lemma5iMidLatestResetWordProjection) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    WLGHeadOffsetBounds ->
    forall pre : DetSchedule n,
      pre ∈ allSchedules n
        (lemma5ArmHorizon n) ->
      lemma5iMidPaperFailureCount
          ring C pre *
          2 ^ psi <=
        n ^ lemma5PaperSweepHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C hcnz hoffset
  intro pre hpre

  let T : Nat :=
    lemma5PaperSweepHorizon n
  let words : List (DetSchedule n) :=
    allSchedules n T
  let D : Config n psi kappa :=
    runPPL ring C pre
  let bad : DetSchedule n -> Bool :=
    fun sweep =>
      lemma5iMidClockBadB
        ring C (pre ++ sweep)
  let agentPred :
      Fin n -> DetSchedule n -> Bool :=
    fun x =>
      lemma5iMidAgentBadB ring D x
  let agentCount : Fin n -> Nat :=
    fun x => words.countP (agentPred x)
  let preds :
      List (DetSchedule n -> Bool) :=
    List.ofFn agentPred
  let F : Nat :=
    lemma5iMidPaperFailureCount
      ring C pre

  by_cases hex :
      exists sweep : DetSchedule n,
        And (sweep ∈ words)
          (bad sweep = true)
  · obtain ⟨w0, hw0mem, hw0bad⟩ := hex

    have hw0mem' :
        w0 ∈ allSchedules n
          (lemma5PaperSweepHorizon n) := by
      simpa [words, T] using hw0mem

    have hp0 :=
      hprojection
        hn3 hpsi hkappa hnpow
        ring C hcnz
        PPL.Probability.stoppedClockSuffixBoundsCorrected
        pre w0 hpre hw0mem'
        (by simpa [bad] using hw0bad)

    have hpsi3 : 3 <= psi :=
      hp0.1
    have hpsin : psi <= n :=
      hp0.2.1

    have hbadToAny :
        forall sweep : DetSchedule n,
          sweep ∈ words ->
          bad sweep = true ->
          midAnyPred preds sweep = true := by
      intro sweep hsweep hbad
      have hsweep' :
          sweep ∈ allSchedules n
            (lemma5PaperSweepHorizon n) := by
        simpa [words, T] using hsweep
      obtain ⟨x, hx⟩ :=
        (hprojection
          hn3 hpsi hkappa hnpow
          ring C hcnz
          PPL.Probability.stoppedClockSuffixBoundsCorrected
          pre sweep hpre hsweep'
          (by simpa [bad] using hbad)).2.2
      apply
        midAnyPred_true_of_mem
          preds (agentPred x) sweep
      · dsimp [preds]
        rw [List.mem_ofFn]
        exact ⟨x, rfl⟩
      · simpa [agentPred, D] using hx

    have hunion :
        F <=
          (List.ofFn agentCount).sum := by
      calc
        F = words.countP bad := by
          rfl
        _ <=
            words.countP
              (midAnyPred preds) :=
          midCountP_mono_mem
            words bad (midAnyPred preds)
            (by
              intro sweep hsweep hbad
              exact
                hbadToAny
                  sweep hsweep hbad)
        _ <=
            (preds.map
              (fun p =>
                words.countP p)).sum :=
          midCountP_anyPred_le_sum
            words preds
        _ =
            (List.ofFn agentCount).sum := by
          dsimp [preds, agentCount, agentPred]
          rw [List.map_ofFn]
          rfl

    let common : Nat :=
      2 * n * 2 ^ psi

    have htwoN :
        2 <= 2 ^ n := by
      have hn1 : 1 <= n := by
        omega
      have h :=
        Nat.pow_le_pow_right
          (by omega : 0 < 2) hn1
      simpa using h

    have hnSelf :
        n <= 2 ^ n :=
      midNatLeTwoPowSelf n

    have hpsiPowN :
        2 ^ psi <= 2 ^ n :=
      Nat.pow_le_pow_right
        (by omega : 0 < 2) hpsin

    have hcommonEncounter :
        common <= 2 ^ (4 * n) := by
      have hm :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            htwoN hnSelf)
          hpsiPowN
      calc
        common <=
            (2 ^ n * 2 ^ n) *
              2 ^ n := by
          simpa [common,
            Nat.mul_assoc] using hm
        _ = 2 ^ (3 * n) := by
          rw [← Nat.pow_add,
            ← Nat.pow_add]
          congr 1
          omega
        _ <= 2 ^ (4 * n) :=
          Nat.pow_le_pow_right
            (by omega : 0 < 2)
            (by omega)

    have htwoPsi :
        2 <= 2 ^ psi := by
      have hp1 : 1 <= psi := by
        omega
      have h :=
        Nat.pow_le_pow_right
          (by omega : 0 < 2) hp1
      simpa using h

    have hcommonLottery :
        common <= 2 ^ (9 * psi) := by
      have hm :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            htwoPsi hnpow)
          (Nat.le_refl (2 ^ psi))
      calc
        common <=
            (2 ^ psi * 2 ^ psi) *
              2 ^ psi := by
          simpa [common,
            Nat.mul_assoc] using hm
        _ = 2 ^ (3 * psi) := by
          rw [← Nat.pow_add,
            ← Nat.pow_add]
          congr 1
          omega
        _ <= 2 ^ (9 * psi) :=
          Nat.pow_le_pow_right
            (by omega : 0 < 2)
            (by omega)

    have hagent :
        forall x : Fin n,
          common * agentCount x <=
            2 * n ^ T := by
      intro x
      let enc : Nat :=
        words.countP
          (lemma5iMidEncounterAgentBadB
            ring x)
      let lot : Nat :=
        words.countP
          (lemma5iMidLotteryAgentBadB
            ring D x)

      have hsplit :
          agentCount x <= enc + lot := by
        dsimp [agentCount, agentPred,
          enc, lot]
        exact
          midCountP_or_le_add
            words
            (lemma5iMidEncounterAgentBadB
              ring x)
            (lemma5iMidLotteryAgentBadB
              ring D x)

      have henc0 :=
        lemma5iMidEncounterAgentCount
          hn3 ring x
      have henc :
          common * enc <= n ^ T := by
        calc
          common * enc <=
              2 ^ (4 * n) * enc :=
            Nat.mul_le_mul_right
              enc hcommonEncounter
          _ =
              2 ^ (4 * n) *
                lemma5iMidEncounterAgentFailureCount
                  ring x := by
            dsimp [enc, words, T]
            rfl
          _ <=
              n ^ lemma5PaperSweepHorizon n :=
            henc0
          _ = n ^ T := by
            rfl

      have hlot0 :=
        lemma5iMidLotteryAgentCount
          hn3 hpsi ring D x hoffset
      have hlot :
          common * lot <= n ^ T := by
        calc
          common * lot <=
              2 ^ (9 * psi) * lot :=
            Nat.mul_le_mul_right
              lot hcommonLottery
          _ =
              2 ^ (9 * psi) *
                lemma5iMidLotteryAgentFailureCount
                  ring D x := by
            dsimp [lot, words, T]
            rfl
          _ <=
              n ^ lemma5PaperSweepHorizon n :=
            hlot0
          _ = n ^ T := by
            rfl

      calc
        common * agentCount x <=
            common * (enc + lot) :=
          Nat.mul_le_mul_left
            common hsplit
        _ =
            common * enc +
              common * lot := by
          rw [Nat.mul_add]
        _ <= n ^ T + n ^ T :=
          Nat.add_le_add henc hlot
        _ = 2 * n ^ T := by
          omega

    have hsum :
        (List.ofFn
          (fun x : Fin n =>
            common * agentCount x)).sum <=
        (List.ofFn
          (fun _ : Fin n =>
            2 * n ^ T)).sum :=
      FiniteUniformStoppingTree.ofFn_sum_le
        (fun x : Fin n =>
          common * agentCount x)
        (fun _ : Fin n =>
          2 * n ^ T)
        hagent

    have hsum' :
        common *
            (List.ofFn agentCount).sum <=
          n * (2 * n ^ T) := by
      calc
        common *
            (List.ofFn agentCount).sum =
          (List.ofFn
            (fun x : Fin n =>
              common * agentCount x)).sum :=
          (FiniteUniformStoppingTree.ofFn_sum_mul_left
            common agentCount).symm
        _ <=
          (List.ofFn
            (fun _ : Fin n =>
              2 * n ^ T)).sum :=
          hsum
        _ = n * (2 * n ^ T) :=
          FiniteUniformStoppingTree.ofFn_sum_const
            n (2 * n ^ T)

    have hscaledF :
        common * F <=
          n * (2 * n ^ T) :=
      Nat.le_trans
        (Nat.mul_le_mul_left
          common hunion)
        hsum'

    have hcancellable :
        (2 * n) * (2 ^ psi * F) <=
          (2 * n) * n ^ T := by
      calc
        (2 * n) * (2 ^ psi * F) =
            common * F := by
          dsimp [common]
          ac_rfl
        _ <= n * (2 * n ^ T) :=
          hscaledF
        _ = (2 * n) * n ^ T := by
          ac_rfl

    have hfinal :
        2 ^ psi * F <= n ^ T :=
      Nat.le_of_mul_le_mul_left
        hcancellable
        (by omega)

    simpa [F, T, Nat.mul_comm]
      using hfinal

  · have hzero :
        F = 0 := by
      dsimp [F]
      unfold lemma5iMidPaperFailureCount
      apply List.countP_eq_zero.mpr
      intro sweep hsweep hbad
      have hmem :
          sweep ∈ words := by
        simpa [words, T] using hsweep
      exact
        hex
          ⟨sweep,
            And.intro hmem
              (by simpa [bad] using hbad)⟩
    have hz : lemma5iMidPaperFailureCount ring C pre = 0 := hzero
    rw [hz]
    simp

/-! ## Restore the frozen 8n² suffix and discharge the target Prop -/

theorem lemma5iMidLatestResetSuffixBound_proved
    (hprojection :
      Lemma5iMidLatestResetWordProjection) :
    Lemma5iMidLatestResetSuffixBound := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro hcnz _hclock _hmarked
  intro _hpredict hoffset _hlottery
  intro pre hpre

  have hpaper :=
    lemma5iMidLatestResetPaperCount
      hprojection
      hn3 hpsi hkappa hnpow
      ring C hcnz hoffset
      pre hpre

  have hpad :=
    lemma5iMidSuffix_eq_paper_pad
      ring C pre hpre

  have hsum :
      2 * n * n +
          lemma5PaperSweepHorizon n =
        lemma5SweepHorizon n := by
    have h :=
      midSweepHorizon_split n
    omega

  calc
    lemma5iMidSuffixFailureCount
          ring C pre * 2 ^ psi =
        (lemma5iMidPaperFailureCount
            ring C pre *
          n ^ (2 * n * n)) *
          2 ^ psi := by
      rw [hpad]
    _ =
        n ^ (2 * n * n) *
          (lemma5iMidPaperFailureCount
            ring C pre * 2 ^ psi) := by
      ac_rfl
    _ <=
        n ^ (2 * n * n) *
          n ^ lemma5PaperSweepHorizon n :=
      Nat.mul_le_mul_left
        (n ^ (2 * n * n))
        hpaper
    _ =
        n ^
          (2 * n * n +
            lemma5PaperSweepHorizon n) := by
      rw [Nat.pow_add]
    _ = n ^ lemma5SweepHorizon n := by
      rw [hsum]

/--
splice with the latest-reset counting leaf reduced to its final
wordwise physical extraction.  No change to the frozen splice statement is
needed.
-/
theorem lemma5iSweepMidPhysicalCountSplice_latestReset
    (hTraversal :
      Lemma5iTraversalSuffixPhysicalProjection)
    (hprojection :
      Lemma5iMidLatestResetWordProjection) :
    Lemma5iSweepMidPhysicalCountSplice :=
  lemma5iSweepMidPhysicalCountSplice
    hTraversal
    (lemma5iMidLatestResetSuffixBound_proved
      hprojection)

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iMidResetClockZero
#print axioms PPL.Modes.Lemma5.lemma5iMidPaperFailureCount_zero_of_noArm
#print axioms PPL.Modes.Lemma5.lemma5iMidEncounterAgentCount
#print axioms PPL.Modes.Lemma5.lemma5iMidFreshLottery24Count
#print axioms PPL.Modes.Lemma5.lemma5iMidLotteryAgentCount
#print axioms PPL.Modes.Lemma5.lemma5iMidLatestResetPaperCount
#print axioms PPL.Modes.Lemma5.lemma5iMidLatestResetSuffixBound_proved
#print axioms PPL.Modes.Lemma5.lemma5iSweepMidPhysicalCountSplice_latestReset

