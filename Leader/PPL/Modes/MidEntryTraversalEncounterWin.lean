import Leader.PPL.Modes.MidEntryRetimedCurrentMax

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-!
# Lemma 5(i): retimed traversal with the paper A+B+C events

A is the ordered-word miss.
B is the stopped predictable-host >24*n encounter event.
C is the padded stopped-prefix >=48*psi WLG-win event.

The C numerator is deliberately padded.  ModeStoppedTreeTransfer.upper is an
exact-E/no-stop event and therefore does not cover TTL exhaustion when the
exhaustion itself stops the tracked lineage.
-/

/-! ## Public B/C numerators -/

def lemma5iTraversalEncounterFailureCountBC
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool) : Nat :=
  stoppedPredictableHostUpperTailCount
    ring host stop
    (lemma5PaperSweepHorizon n)
    (24 * n)

def lemma5iTraversalTTLFailureCountBC
    {n : Nat}
    (psi h : Nat)
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool) : Nat :=
  stoppedMarkedPaddedCount
    ring host stop
    (lemma5PaperSweepHorizon n)
    (lotteryL7Horizon psi 5)
    (fun bits =>
      decide
        (lotteryTarget psi 6 <=
          (lotteryRun psi
            (lotteryOffset h) bits).wins))

private def q19732TraversalWordMissBadB
    {n : Nat}
    (sweep : DetSchedule n) : Bool :=
  decide
    (Not
      ((lemma5ClockwiseSweepWord n).Sublist sweep))

private def q19732TraversalEncounterBadB
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (sweep : DetSchedule n) : Bool :=
  decide
    (24 * n <
      stoppedPredictableHostHits
        ring host stop sweep)

private def q19732TraversalTTLBadB
    {n : Nat}
    (psi h : Nat)
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (sweep : DetSchedule n) : Bool :=
  let bits :=
    stoppedEncounterBits ring host stop sweep
  decide
    (And
      (bits.length <= lotteryL7Horizon psi 5)
      ((fun u : List Bool =>
          decide
            (lotteryTarget psi 6 <=
              (lotteryRun psi
                (lotteryOffset h) u).wins))
        bits = true))

/-!
This is the sole new physical residual.

Starting from an actual current max-TTL reset, choose the prefix-predictable
owner/host, stopping rule, and current head offset.  If the 6*n^2 paper sweep
still has not reset every clock, then at least one of the paper events A, B,
or C failed.

The one-hop mechanics needed for the intended proof are public on main:
clockResetAt, determineModeSignalProjection, postDetermineModeSignalStable,
and step_signal_projection_of_stable.  What is not currently exported as one
theorem is the multi-step traversal invariant tying the current max owner to
the predictable host/stop process through arbitrary skipped scheduler letters.
-/
def Lemma5iRetimedTraversalABCSweepResidual : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    maxResetSignalB D = true ->
    Exists fun host : List (Fin n) -> Fin n =>
      Exists fun stop : List (Fin n) -> Bool =>
        Exists fun h : Nat =>
          And
            (h <= psi)
            (forall sweep : DetSchedule n,
              sweep ∈
                  allSchedules n
                    (lemma5PaperSweepHorizon n) ->
              !allClockResetsSeenB ring D sweep = true ->
              ((q19732TraversalWordMissBadB sweep ||
                  q19732TraversalEncounterBadB
                    ring host stop sweep) ||
                q19732TraversalTTLBadB
                  psi h ring host stop sweep) =
                true)

/-!
Correct current-max interface.  Unlike the old interface, its right side keeps
the B and C numerators visible.
-/
def Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    maxResetSignalB D = true ->
    Exists fun host : List (Fin n) -> Fin n =>
      Exists fun stop : List (Fin n) -> Bool =>
        Exists fun h : Nat =>
          And
            (h <= psi)
            ((allSchedules n
                (lemma5SweepHorizon n)).countP
              (fun suffix =>
                !allClockResetsSeenB ring D
                  (suffix.take
                    (lemma5PaperSweepHorizon n))) <=
              n ^ (2 * n * n) *
                (fixedWordMissCount
                    (lemma5ClockwiseSweepWord n)
                    (lemma5PaperSweepHorizon n) +
                  lemma5iTraversalEncounterFailureCountBC
                    ring host stop +
                  lemma5iTraversalTTLFailureCountBC
                    psi h ring host stop))

/-! ## Small finite-list counting bricks -/

private theorem q19732CountP_mono
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq :
      forall x,
        p x = true ->
        q x = true) :
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
          have hqx := hpq x hp
          simp [hp, hqx, ih]

private theorem q19732CountP_mono_on
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
      rw [List.countP_cons, List.countP_cons]
      have htail :
          xs.countP p <= xs.countP q :=
        ih (fun y hy hpy =>
          hpq y (by simp [hy]) hpy)
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx :
              q x = true :=
            hpq x (by simp) hp
          simp [hp, hqx]
          omega

private theorem q19732CountP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A -> Bool) :
    xs.countP (fun x => p x || q x) <=
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons,
        List.countP_cons,
        List.countP_cons]
      cases hp : p x <;>
        cases hq : q x <;>
        simp [hp, hq] at * <;>
        omega

private theorem q19732AllSchedules_add
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

private theorem q19732SumIfCount
    {A : Type}
    (xs : List A)
    (p : A -> Bool)
    (c : Nat) :
    (xs.map
      (fun x =>
        if p x then c else 0)).sum =
      xs.countP p * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons,
        List.sum_cons,
        List.countP_cons]
      cases hp : p x <;>
        simp [hp, ih, Nat.succ_mul, Nat.add_comm]

private theorem q19732CountP_take_pad
    {n H P : Nat}
    (p : DetSchedule n -> Bool) :
    (allSchedules n (H + P)).countP
        (fun word => p (word.take H)) =
      (allSchedules n H).countP p *
        n ^ P := by
  rw [q19732AllSchedules_add,
    List.countP_flatMap]
  simp only [Function.comp_def]
  have hmap :
      ((allSchedules n H).map
        (fun pre =>
          ((allSchedules n P).map
            (fun pad => pre ++ pad)).countP
              (fun word => p (word.take H)))) =
      (allSchedules n H).map
        (fun pre =>
          if p pre then n ^ P else 0) := by
    apply List.map_congr_left
    intro pre hpre
    rw [List.countP_map]
    simp only [Function.comp_def]
    have hlen :=
      allSchedules_schedule_length
        n H pre hpre
    have hfun :
        (fun pad : DetSchedule n =>
          p ((pre ++ pad).take H)) =
        (fun _ : DetSchedule n =>
          p pre) := by
      funext pad
      rw [← hlen, List.take_append_length]
    rw [hfun]
    cases hp : p pre <;>
      simp [hp, allSchedules_length]
  rw [hmap]
  exact q19732SumIfCount
    (allSchedules n H) p (n ^ P)

/-! ## Deterministic A+B+C projection to the three numerators -/

theorem
    lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC_of_deterministic
    (hABC : Lemma5iRetimedTraversalABCSweepResidual) :
    Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC := by
  intro n psi kappa
  intro hn3 hpsi hkappa
  intro ring D hlineage hmax

  obtain
      ⟨host, stop, h, hh, hcharge⟩ :=
    hABC hn3 hpsi hkappa
      ring D hlineage hmax

  refine ⟨host, stop, h, hh, ?_⟩

  let P : Nat :=
    lemma5PaperSweepHorizon n
  let Z : Nat :=
    2 * n * n
  let S : Nat :=
    lemma5SweepHorizon n

  let badP : DetSchedule n -> Bool :=
    fun sweep =>
      !allClockResetsSeenB ring D sweep
  let qA : DetSchedule n -> Bool :=
    q19732TraversalWordMissBadB
  let qB : DetSchedule n -> Bool :=
    q19732TraversalEncounterBadB
      ring host stop
  let qC : DetSchedule n -> Bool :=
    q19732TraversalTTLBadB
      psi h ring host stop
  let qAB : DetSchedule n -> Bool :=
    fun sweep => qA sweep || qB sweep

  have hmono :
      (allSchedules n P).countP badP <=
        (allSchedules n P).countP
          (fun sweep =>
            qAB sweep || qC sweep) := by
    apply
      q19732CountP_mono_on
        (allSchedules n P)
        badP
        (fun sweep =>
          qAB sweep || qC sweep)
    intro sweep hsweep hbad
    dsimp [badP, qAB, qA, qB, qC]
    exact
      hcharge sweep
        (by simpa [P] using hsweep)
        (by simpa [badP] using hbad)

  have hab :=
    q19732CountP_or_le_add
      (allSchedules n P) qA qB
  have habc :=
    q19732CountP_or_le_add
      (allSchedules n P) qAB qC

  have hAeq :
      (allSchedules n P).countP qA =
        fixedWordMissCount
          (lemma5ClockwiseSweepWord n) P := by
    rfl

  have hBeq :
      (allSchedules n P).countP qB =
        lemma5iTraversalEncounterFailureCountBC
          ring host stop := by
    rfl

  have hCeq :
      (allSchedules n P).countP qC =
        lemma5iTraversalTTLFailureCountBC
          psi h ring host stop := by
    rfl

  have hpaper :
      (allSchedules n P).countP badP <=
        fixedWordMissCount
            (lemma5ClockwiseSweepWord n) P +
          lemma5iTraversalEncounterFailureCountBC
            ring host stop +
          lemma5iTraversalTTLFailureCountBC
            psi h ring host stop := by
    calc
      (allSchedules n P).countP badP <=
          (allSchedules n P).countP
            (fun sweep =>
              qAB sweep || qC sweep) :=
        hmono
      _ <=
          (allSchedules n P).countP qAB +
            (allSchedules n P).countP qC :=
        habc
      _ <=
          ((allSchedules n P).countP qA +
            (allSchedules n P).countP qB) +
              (allSchedules n P).countP qC :=
        Nat.add_le_add_right hab _
      _ =
          fixedWordMissCount
              (lemma5ClockwiseSweepWord n) P +
            lemma5iTraversalEncounterFailureCountBC
              ring host stop +
            lemma5iTraversalTTLFailureCountBC
              psi h ring host stop := by
        rw [hAeq, hBeq, hCeq]

  have hpad0 :=
    q19732CountP_take_pad
      (n := n) (H := P) (P := Z) badP

  have hPS : P + Z = S := by
    dsimp [P, Z, S]
    exact lemma5iRetimedLastArmPadding n

  have hpad :
      (allSchedules n S).countP
          (fun suffix =>
            badP (suffix.take P)) =
        (allSchedules n P).countP badP *
          n ^ Z := by
    rw [← hPS]
    exact hpad0

  have hfinal :
      (allSchedules n S).countP
          (fun suffix =>
            badP (suffix.take P)) <=
        n ^ Z *
          (fixedWordMissCount
              (lemma5ClockwiseSweepWord n) P +
            lemma5iTraversalEncounterFailureCountBC
              ring host stop +
            lemma5iTraversalTTLFailureCountBC
              psi h ring host stop) := by
    rw [hpad]
    calc
      (allSchedules n P).countP badP *
          n ^ Z <=
        (fixedWordMissCount
              (lemma5ClockwiseSweepWord n) P +
            lemma5iTraversalEncounterFailureCountBC
              ring host stop +
            lemma5iTraversalTTLFailureCountBC
              psi h ring host stop) *
          n ^ Z :=
        Nat.mul_le_mul_right (n ^ Z) hpaper
      _ =
        n ^ Z *
          (fixedWordMissCount
              (lemma5ClockwiseSweepWord n) P +
            lemma5iTraversalEncounterFailureCountBC
              ring host stop +
            lemma5iTraversalTTLFailureCountBC
              psi h ring host stop) := by
        ac_rfl

  simpa [P, Z, S, badP] using hfinal

/-! ## Exact A+B+C paper-window budget -/

private theorem q19732Nat_le_twoPow_self
    (n : Nat) :
    n <= 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have hp :
          0 < 2 ^ n :=
        Nat.pow_pos (by omega)
      omega

private theorem q19732ThreeN_le_twoPow_twoN
    (n : Nat)
    (hn3 : 3 <= n) :
    3 * n <= 2 ^ (2 * n) := by
  have hsquare :=
    Nat.mul_le_mul
      (q19732Nat_le_twoPow_self n)
      (q19732Nat_le_twoPow_self n)
  calc
    3 * n <= n * n := by
      exact Nat.mul_le_mul_right n hn3
    _ <= 2 ^ n * 2 ^ n :=
      hsquare
    _ = 2 ^ (n + n) := by
      rw [Nat.pow_add]
    _ = 2 ^ (2 * n) := by
      congr 1
      omega

private theorem q19732ThreeN_le_twoPow_fivePsi
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hnpow : n <= 2 ^ psi) :
    3 * n <= 2 ^ (5 * psi) := by
  have hsquare :=
    Nat.mul_le_mul hnpow hnpow
  calc
    3 * n <= n * n := by
      exact Nat.mul_le_mul_right n hn3
    _ <= 2 ^ psi * 2 ^ psi :=
      hsquare
    _ = 2 ^ (psi + psi) := by
      rw [Nat.pow_add]
    _ = 2 ^ (2 * psi) := by
      congr 1
      omega
    _ <= 2 ^ (5 * psi) :=
      Nat.pow_le_pow_right
        (by omega : 0 < 2)
        (by omega)

private theorem
    q19732LotteryAtLeastWordCount_mono_threshold
    (k h T A B : Nat)
    (hAB : A <= B) :
    lotteryAtLeastWordCount k h T B <=
      lotteryAtLeastWordCount k h T A := by
  unfold lotteryAtLeastWordCount
    lotteryPredWordCount
  apply q19732CountP_mono
  intro word hw
  simp only [decide_eq_true_eq] at hw ⊢
  omega

/--
The three paper-window bad numerators jointly cost only one n-scaled unit:

  n * (A+B+C) <= n^P.

ModeStoppedTreeTransfer and PredictableHostTails are retained as arguments
because they are part of the outer Lemma-5 interface.  On current main the B
bound is already closed as stoppedPredictableHost24nBound, and C requires the
padded transfer rather than ModeStoppedTreeTransfer.upper.
-/
theorem lemma5iTraversalABC_paperBudgetBC
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (h : Nat)
    (hh : h <= psi)
    (_hmarked : ModeStoppedTreeTransfer)
    (_hpredict : PredictableHostTails)
    (hoffset : WLGHeadOffsetBounds)
    (hlottery : LotteryCountBounds) :
    n *
        (fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n) +
          lemma5iTraversalEncounterFailureCountBC
            ring host stop +
          lemma5iTraversalTTLFailureCountBC
            psi h ring host stop) <=
      n ^ lemma5PaperSweepHorizon n := by
  let P : Nat :=
    lemma5PaperSweepHorizon n

  let A : Nat :=
    fixedWordMissCount
      (lemma5ClockwiseSweepWord n) P
  let B : Nat :=
    lemma5iTraversalEncounterFailureCountBC
      ring host stop
  let C : Nat :=
    lemma5iTraversalTTLFailureCountBC
      psi h ring host stop

  have hAtail :
      A * 2 ^ (2 * n) <=
        n ^ P := by
    simpa [A, P] using
      lemma5ClockwiseSweepWord_miss_scaled n

  have hBtail :
      B * 2 ^ (4 * n) <=
        n ^ P := by
    simpa [B, P,
      lemma5iTraversalEncounterFailureCountBC, lemma5PaperSweepHorizon] using
      stoppedPredictableHost24nBound
        n (by omega) ring host stop

  let E : Nat :=
    lotteryL7Horizon psi 5
  let M5 : Nat :=
    lotteryTarget psi 5
  let M6 : Nat :=
    lotteryTarget psi 6
  let BW : Nat :=
    lotteryAtLeastWordCount
      psi h E M6
  let B0 : Nat :=
    lotteryAtLeastWordCount
      psi 0 E M5
  let scale : Nat :=
    2 ^ (5 * psi)

  have htransfer0 :=
    stoppedEncounterLotteryAtLeast_padded_transfer
      hn3 psi h ring host stop
      P E M6

  have htransfer :
      C * 2 ^ E <=
        n ^ P * BW := by
    simpa [C, BW,
      lemma5iTraversalTTLFailureCountBC]
      using htransfer0

  have hthreshold :
      M5 + 1 <= M6 := by
    dsimp [M5, M6]
    unfold lotteryTarget
    omega

  have hmono :
      lotteryAtLeastWordCount
          psi h E M6 <=
        lotteryAtLeastWordCount
          psi h E (M5 + 1) :=
    q19732LotteryAtLeastWordCount_mono_threshold
      psi h E (M5 + 1) M6
      hthreshold

  have hhead :
      lotteryAtLeastWordCount
          psi h E (M5 + 1) <=
        lotteryAtLeastWordCount
          psi 0 E M5 :=
    (hoffset
      psi h E M5
      (by omega) hh).2.1

  have hBW :
      BW <= B0 := by
    dsimp [BW, B0]
    exact Nat.le_trans hmono hhead

  have hL7 :
      scale * B0 <=
        2 ^ E := by
    dsimp [scale, B0, E, M5]
    exact
      (hlottery
        psi 5
        (by omega)
        (by omega)).1

  have hscaled :
      (scale * C) * 2 ^ E <=
        n ^ P * 2 ^ E := by
    calc
      (scale * C) * 2 ^ E =
          scale * (C * 2 ^ E) := by
        ac_rfl
      _ <=
          scale * (n ^ P * BW) :=
        Nat.mul_le_mul_left
          scale htransfer
      _ =
          n ^ P * (scale * BW) := by
        ac_rfl
      _ <=
          n ^ P * (scale * B0) :=
        Nat.mul_le_mul_left
          (n ^ P)
          (Nat.mul_le_mul_left
            scale hBW)
      _ <=
          n ^ P * 2 ^ E :=
        Nat.mul_le_mul_left
          (n ^ P) hL7

  have hCtail :
      scale * C <= n ^ P :=
    Nat.le_of_mul_le_mul_right
      hscaled
      (Nat.pow_pos
        (by omega : 0 < 2))

  have h3A :
      3 * n <=
        2 ^ (2 * n) :=
    q19732ThreeN_le_twoPow_twoN
      n hn3

  have h3B :
      3 * n <=
        2 ^ (4 * n) := by
    exact
      Nat.le_trans h3A
        (Nat.pow_le_pow_right
          (by omega : 0 < 2)
          (by omega))

  have h3C :
      3 * n <=
        scale := by
    dsimp [scale]
    exact
      q19732ThreeN_le_twoPow_fivePsi
        hn3 hnpow

  have hA3 :
      (3 * n) * A <= n ^ P := by
    calc
      (3 * n) * A <=
          2 ^ (2 * n) * A :=
        Nat.mul_le_mul_right A h3A
      _ = A * 2 ^ (2 * n) := by
        ac_rfl
      _ <= n ^ P :=
        hAtail

  have hB3 :
      (3 * n) * B <= n ^ P := by
    calc
      (3 * n) * B <=
          2 ^ (4 * n) * B :=
        Nat.mul_le_mul_right B h3B
      _ = B * 2 ^ (4 * n) := by
        ac_rfl
      _ <= n ^ P :=
        hBtail

  have hC3 :
      (3 * n) * C <= n ^ P := by
    calc
      (3 * n) * C <=
          scale * C :=
        Nat.mul_le_mul_right C h3C
      _ <= n ^ P :=
        hCtail

  have hsum3 :
      (3 * n) * (A + B + C) <=
        n ^ P + n ^ P + n ^ P := by
    rw [Nat.mul_add, Nat.mul_add]
    exact
      Nat.add_le_add
        (Nat.add_le_add hA3 hB3)
        hC3

  have hcancel :
      3 * (n * (A + B + C)) <=
        3 * n ^ P := by
    calc
      3 * (n * (A + B + C)) =
          (3 * n) * (A + B + C) := by
        ac_rfl
      _ <=
          n ^ P + n ^ P + n ^ P :=
        hsum3
      _ = 3 * n ^ P := by
        omega

  have hABC :
      n * (A + B + C) <=
        n ^ P :=
    Nat.le_of_mul_le_mul_left
      hcancel (by omega)

  simpa [A, B, C, P] using hABC

/-! ## Current-max suffix after applying the A+B+C budget -/

theorem lemma5iRetimedTraversalCurrentMaxSuffixBC_budget
    (hprojection :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    maxResetSignalB D = true ->
    n *
        (allSchedules n
          (lemma5SweepHorizon n)).countP
          (fun suffix =>
            !allClockResetsSeenB ring D
              (suffix.take
                (lemma5PaperSweepHorizon n))) <=
      n ^ lemma5SweepHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D hlineage
  intro hmarked hpredict hoffset hlottery
  intro hmax

  obtain
      ⟨host, stop, h, hh, hraw⟩ :=
    hprojection
      hn3 hpsi hkappa
      ring D hlineage hmax

  let P : Nat :=
    lemma5PaperSweepHorizon n
  let Z : Nat :=
    2 * n * n
  let S : Nat :=
    lemma5SweepHorizon n

  let A : Nat :=
    fixedWordMissCount
      (lemma5ClockwiseSweepWord n) P
  let B : Nat :=
    lemma5iTraversalEncounterFailureCountBC
      ring host stop
  let C : Nat :=
    lemma5iTraversalTTLFailureCountBC
      psi h ring host stop

  have hproj :
      (allSchedules n S).countP
          (fun suffix =>
            !allClockResetsSeenB ring D
              (suffix.take P)) <=
        n ^ Z * (A + B + C) := by
    simpa [P, Z, S, A, B, C]
      using hraw

  have hpaper :
      n * (A + B + C) <=
        n ^ P := by
    simpa [A, B, C, P] using
      lemma5iTraversalABC_paperBudgetBC
        hn3 hpsi hnpow
        ring host stop h hh
        hmarked hpredict
        hoffset hlottery

  have hPS :
      P + Z = S := by
    dsimp [P, Z, S]
    exact lemma5iRetimedLastArmPadding n

  have hfinal :
      n *
          (allSchedules n S).countP
            (fun suffix =>
              !allClockResetsSeenB ring D
                (suffix.take P)) <=
        n ^ S := by
    calc
      n *
          (allSchedules n S).countP
            (fun suffix =>
              !allClockResetsSeenB ring D
                (suffix.take P)) <=
        n * (n ^ Z * (A + B + C)) :=
        Nat.mul_le_mul_left n hproj
      _ =
        n ^ Z * (n * (A + B + C)) := by
          ac_rfl
      _ <=
        n ^ Z * n ^ P :=
          Nat.mul_le_mul_left
            (n ^ Z) hpaper
      _ =
        n ^ (Z + P) := by
          rw [Nat.pow_add]
      _ =
        n ^ S := by
          congr 1
          omega

  simpa [P, S] using hfinal

/-! ## First-terminal bind, re-exported without private upstream names -/

private def q19732RetimedTraversalBadAux
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa -> Nat -> DetSchedule n -> Bool
  | C, 0, word =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C
          (word.take
            (lemma5PaperSweepHorizon n))
      else
        false
  | C, fuel + 1, [] =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C []
      else
        false
  | C, fuel + 1, e :: rest =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C
          ((e :: rest).take
            (lemma5PaperSweepHorizon n))
      else
        q19732RetimedTraversalBadAux
          ring
          (pplStep ring C e)
          fuel rest

private theorem q19732TraversalBadB_fun_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma5iRetimedTraversalBadB ring C =
      q19732RetimedTraversalBadAux
        ring C (lemma5ArmHorizon n) := by
  funext word
  unfold lemma5iRetimedTraversalBadB
  generalize lemma5ArmHorizon n = fuel
  induction fuel generalizing C word with
  | zero =>
      unfoldRetimedTraversalAux
      unfold q19732RetimedTraversalBadAux
      rfl
  | succ fuel ih =>
      cases word with
      | nil =>
          unfoldRetimedTraversalAux
          unfold q19732RetimedTraversalBadAux
          rfl
      | cons e rest =>
          unfoldRetimedTraversalAux
          unfold q19732RetimedTraversalBadAux
          by_cases hm :
              maxResetSignalB C = true
          · simp only
              [hm, if_true, ite_true]
          · simp only
              [hm, if_false, ite_false,
                Bool.false_eq_true]
            exact ih _ _

private theorem q19732TraversalAux_eq_currentMax
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (fuel : Nat)
    (word : DetSchedule n)
    (hm : maxResetSignalB C = true) :
    q19732RetimedTraversalBadAux
        ring C fuel word =
      !allClockResetsSeenB ring C
        (word.take
          (lemma5PaperSweepHorizon n)) := by
  cases fuel with
  | zero =>
      simp [q19732RetimedTraversalBadAux, hm]
  | succ fuel =>
      cases word <;>
        simp [q19732RetimedTraversalBadAux, hm]

private theorem q19732SumMapLe
    {A : Type}
    (xs : List A)
    (f g : A -> Nat)
    (hfg :
      forall x,
        x ∈ xs ->
        f x <= g x) :
    (xs.map f).sum <=
      (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons]
      exact
        Nat.add_le_add
          (hfg x (by simp))
          (ih
            (fun y hy =>
              hfg y (by simp [hy])))

private theorem q19732SumMapConst
    {A : Type}
    (xs : List A)
    (c : Nat) :
    (xs.map (fun _ => c)).sum =
      xs.length * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.succ_mul, Nat.add_comm]

private theorem q19732SumMapMulLeft
    {A : Type}
    (xs : List A)
    (f : A -> Nat)
    (c : Nat) :
    c * (xs.map f).sum =
      (xs.map
        (fun x => c * f x)).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.mul_add]

private theorem q19732CountP_prefixInvariant
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
  rw [q19732AllSchedules_add,
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
  exact
    q19732SumIfCount
      (allSchedules n H)
      p (n ^ P)

private theorem q19732Paper_le_sweep
    (n : Nat) :
    lemma5PaperSweepHorizon n <=
      lemma5SweepHorizon n := by
  have h :=
    lemma5iRetimedLastArmPadding n
  omega

private theorem q19732TraversalCurrent_padding
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (sweep pad : DetSchedule n)
    (hlen :
      sweep.length =
        lemma5SweepHorizon n) :
    (!allClockResetsSeenB ring D
        ((sweep ++ pad).take
          (lemma5PaperSweepHorizon n))) =
      (!allClockResetsSeenB ring D
        (sweep.take
          (lemma5PaperSweepHorizon n))) := by
  have hle :
      lemma5PaperSweepHorizon n <=
        sweep.length := by
    rw [hlen]
    exact q19732Paper_le_sweep n
  rw [List.take_append_of_le_length hle]

private theorem q19732TraversalAuxCount
    (hprojection :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (hlineage :
        SignalLineageOwnership
          (psi := psi) (kappa := kappa) ring)
      (hmarked : ModeStoppedTreeTransfer)
      (hpredict : PredictableHostTails)
      (hoffset : WLGHeadOffsetBounds)
      (hlottery : LotteryCountBounds)
      (fuel : Nat)
      (C : Config n psi kappa),
    n *
        (allSchedules n
          (lemma5SweepHorizon n + fuel)).countP
          (q19732RetimedTraversalBadAux
            ring C fuel) <=
      n ^ fuel *
        n ^ lemma5SweepHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring hlineage
  intro hmarked hpredict hoffset hlottery
  intro fuel
  induction fuel with
  | zero =>
      intro C
      cases hm :
          maxResetSignalB C with
      | false =>
          simp [q19732RetimedTraversalBadAux, hm]
      | true =>
          have hfun :
              q19732RetimedTraversalBadAux
                  ring C 0 =
                (fun word =>
                  !allClockResetsSeenB ring C
                    (word.take
                      (lemma5PaperSweepHorizon n))) := by
            funext word
            exact
              q19732TraversalAux_eq_currentMax
                ring C 0 word hm
          rw [hfun, Nat.add_zero,
            Nat.pow_zero, Nat.one_mul]
          exact
            lemma5iRetimedTraversalCurrentMaxSuffixBC_budget
              hprojection
              hn3 hpsi hkappa hnpow
              ring C hlineage
              hmarked hpredict hoffset hlottery
              hm
  | succ fuel ih =>
      intro C
      cases hm :
          maxResetSignalB C with
      | true =>
          let p : DetSchedule n -> Bool :=
            fun word =>
              !allClockResetsSeenB ring C
                (word.take
                  (lemma5PaperSweepHorizon n))
          have hfun :
              q19732RetimedTraversalBadAux
                  ring C (fuel + 1) =
                p := by
            funext word
            dsimp [p]
            exact
              q19732TraversalAux_eq_currentMax
                ring C (fuel + 1)
                word hm
          rw [hfun]
          have hpad :=
            q19732CountP_prefixInvariant
              (n := n)
              (H := lemma5SweepHorizon n)
              (P := fuel + 1)
              p
              (by
                intro sweep hsweep pad
                dsimp [p]
                exact
                  q19732TraversalCurrent_padding
                    ring C sweep pad hsweep)
          rw [hpad]
          have hcur :=
            lemma5iRetimedTraversalCurrentMaxSuffixBC_budget
              hprojection
              hn3 hpsi hkappa hnpow
              ring C hlineage
              hmarked hpredict hoffset hlottery
              hm
          change
            n *
                ((allSchedules n
                    (lemma5SweepHorizon n)).countP p *
                  n ^ (fuel + 1)) <=
              n ^ (fuel + 1) *
                n ^ lemma5SweepHorizon n
          calc
            n *
                ((allSchedules n
                    (lemma5SweepHorizon n)).countP p *
                  n ^ (fuel + 1)) =
              n ^ (fuel + 1) *
                (n *
                  (allSchedules n
                    (lemma5SweepHorizon n)).countP p) := by
              ac_rfl
            _ <=
              n ^ (fuel + 1) *
                n ^ lemma5SweepHorizon n :=
              Nat.mul_le_mul_left
                (n ^ (fuel + 1))
                (by
                  simpa [p] using hcur)
      | false =>
          let B : Nat :=
            n ^ fuel *
              n ^ lemma5SweepHorizon n

          let childCount :
              DetSchedule n -> Nat :=
            fun pre =>
              ((allSchedules n
                  (lemma5SweepHorizon n + fuel)).map
                (fun suf => pre ++ suf)).countP
                (q19732RetimedTraversalBadAux
                  ring C (fuel + 1))

          have hpoint :
              forall pre : DetSchedule n,
                pre ∈ allSchedules n 1 ->
                n * childCount pre <=
                  B := by
            intro pre hpre
            have hlen :=
              allSchedules_schedule_length
                n 1 pre hpre
            cases pre with
            | nil =>
                simp at hlen
            | cons e rest =>
                cases rest with
                | nil =>
                    dsimp [childCount]
                    rw [List.countP_map]
                    simpa [Function.comp_def,
                      q19732RetimedTraversalBadAux,
                      hm, B]
                      using
                        ih (pplStep ring C e)
                | cons e2 rest2 =>
                    simp at hlen

          have hdecomp :
              (allSchedules n
                  (lemma5SweepHorizon n +
                    (fuel + 1))).countP
                  (q19732RetimedTraversalBadAux
                    ring C (fuel + 1)) =
                ((allSchedules n 1).map
                  childCount).sum := by
            rw [show
                lemma5SweepHorizon n +
                    (fuel + 1) =
                  1 +
                    (lemma5SweepHorizon n +
                      fuel) by omega,
              q19732AllSchedules_add,
              List.countP_flatMap]
            rfl

          calc
            n *
                (allSchedules n
                  (lemma5SweepHorizon n +
                    (fuel + 1))).countP
                  (q19732RetimedTraversalBadAux
                    ring C (fuel + 1)) =
              n *
                ((allSchedules n 1).map
                  childCount).sum := by
              rw [hdecomp]
            _ =
              ((allSchedules n 1).map
                (fun pre =>
                  n * childCount pre)).sum :=
              q19732SumMapMulLeft
                (allSchedules n 1)
                childCount n
            _ <=
              ((allSchedules n 1).map
                (fun _ => B)).sum :=
              q19732SumMapLe
                (allSchedules n 1)
                (fun pre =>
                  n * childCount pre)
                (fun _ => B)
                hpoint
            _ =
              (allSchedules n 1).length * B :=
              q19732SumMapConst
                (allSchedules n 1) B
            _ = n * B := by
              rw [allSchedules_length]
              simp
            _ =
              n ^ (fuel + 1) *
                n ^ lemma5SweepHorizon n := by
              dsimp [B]
              rw [Nat.pow_succ]
              ac_rfl

private theorem q19732Horizon_comm
    (n : Nat) :
    lemma5iHorizon n =
      lemma5SweepHorizon n +
        lemma5ArmHorizon n := by
  unfold lemma5iHorizon
  omega

/--
Strong traversal half: coefficient one rather than coefficient two.
-/
theorem lemma5iRetimedTraversalCount_of_currentMaxBC_strong
    (hprojection :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    n *
        lemma5iRetimedTraversalFailureCount
          ring C <=
      n ^ lemma5iHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C hlineage
  intro hmarked hpredict hoffset hlottery

  have haux :=
    q19732TraversalAuxCount
      hprojection
      hn3 hpsi hkappa hnpow
      ring hlineage
      hmarked hpredict hoffset hlottery
      (lemma5ArmHorizon n) C

  unfold lemma5iRetimedTraversalFailureCount
  rw [q19732Horizon_comm]
  rw [q19732TraversalBadB_fun_eq]

  calc
    n *
        (allSchedules n
          (lemma5SweepHorizon n +
            lemma5ArmHorizon n)).countP
          (q19732RetimedTraversalBadAux
            ring C (lemma5ArmHorizon n)) <=
      n ^ lemma5ArmHorizon n *
        n ^ lemma5SweepHorizon n :=
      haux
    _ =
      n ^
        (lemma5ArmHorizon n +
          lemma5SweepHorizon n) := by
      rw [Nat.pow_add]
    _ =
      n ^ (lemma5SweepHorizon n + lemma5ArmHorizon n) := by
      rw [Nat.add_comm]

/--
Exactly the traversal conjunct required by Lemma5iSweepMidCountRetimed.
-/
theorem lemma5iRetimedTraversalCount_of_currentMaxBC
    (hprojection :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    n *
        lemma5iRetimedTraversalFailureCount
          ring C <=
      2 * n ^ lemma5iHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C hlineage
  intro hmarked hpredict hoffset hlottery

  have hstrong :=
    lemma5iRetimedTraversalCount_of_currentMaxBC_strong
      hprojection
      hn3 hpsi hkappa hnpow
      ring C hlineage
      hmarked hpredict hoffset hlottery

  exact Nat.le_trans hstrong (by omega)

/--
Same theorem with the complete outer Lemma5iSweepMidCountRetimed premise list,
so it can be dropped into the first conjunct verbatim.
-/
theorem lemma5iSweepMidCountRetimed_traversal_of_currentMaxBC
    (hprojection :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC) :
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
    n *
        lemma5iRetimedTraversalFailureCount
          ring C <=
      2 * n ^ lemma5iHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro _hcnz hlineage _hclock
  intro hmarked hpredict hoffset hlottery

  exact
    lemma5iRetimedTraversalCount_of_currentMaxBC
      hprojection
      hn3 hpsi hkappa hnpow
      ring C hlineage
      hmarked hpredict hoffset hlottery

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC_of_deterministic
#print axioms PPL.Modes.Lemma5.lemma5iTraversalABC_paperBudgetBC
#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalCurrentMaxSuffixBC_budget
#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalCount_of_currentMaxBC_strong
#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalCount_of_currentMaxBC
#print axioms PPL.Modes.Lemma5.lemma5iSweepMidCountRetimed_traversal_of_currentMaxBC
