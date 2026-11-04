import Leader.PPL.Modes.ConstructionModeSplit
import Leader.PPL.Modes.SignalLineageClosed
import Leader.PPL.Modes.SignalAbsorptionLottery
import Leader.PPL.Probability.EncounterProjection
import Leader.PPL.Probability.MarkedWordTransfer

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


/-!
# Lemma 5(i): reset-lineage count

The stochastic/counting half is closed below.

The only residual is `Lemma5iResetLineageWordCharge`.  It is strictly
wordwise: after fixing the arm prefix, choose the first max-TTL lineage's
predictable host, stopping rule, and current Algorithm-4 head offset.  For one
sweep word, disappearance of that lineage must imply either

* more than `24*n` stopped lineage-host encounters, or
* at least `lotteryTarget psi 6 = 48*psi` wins on the stopped H/T stream.

There is no count inequality in the residual.
-/


private theorem countP_mono_reset
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


private theorem countP_mono_on_reset
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
      have hhead :
          p x = true -> q x = true := by
        intro hx
        exact hpq x (by simp) hx
      have htail :
          forall y,
            y ∈ xs ->
            p y = true ->
            q y = true := by
        intro y hy hp
        exact hpq y (by simp [hy]) hp
      have hi := ih htail
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] at * <;>
            omega
      | true =>
          have hqx : q x = true := hhead hp
          simp [hp, hqx] at *
          omega


private theorem countP_or_le_add_reset
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


private theorem allSchedules_add_reset
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
      simp only [
        allSchedules,
        List.flatMap_assoc,
        List.map_flatMap,
        List.flatMap_map
      ]
      congr
      funext pre
      congr
      funext suf
      rw [List.map_ofFn]
      congr 1
      funext e
      simp [List.append_assoc]


private theorem sum_if_countP_mul_reset
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
      rw [List.map_cons, List.sum_cons, List.countP_cons]
      cases hp : p x <;>
        simp [hp, ih, Nat.succ_mul, Nat.add_comm]


private theorem countP_prefix_reset
    {n a b : Nat}
    (p : DetSchedule n -> Bool) :
    (allSchedules n (a + b)).countP
        (fun word => p (word.take a)) =
      (allSchedules n a).countP p * n ^ b := by
  rw [allSchedules_add_reset, List.countP_flatMap]
  change
    ((allSchedules n a).map
      (fun pre =>
        ((allSchedules n b).map
          (fun suf => pre ++ suf)).countP
            (fun word => p (word.take a)))).sum =
      (allSchedules n a).countP p * n ^ b

  have hmap :
      (allSchedules n a).map
          (fun pre =>
            ((allSchedules n b).map
              (fun suf => pre ++ suf)).countP
                (fun word => p (word.take a))) =
        (allSchedules n a).map
          (fun pre =>
            if p pre then n ^ b else 0) := by
    apply List.map_congr_left
    intro pre hpre
    rw [List.countP_map]
    simp only [Function.comp_def]
    have hlen :
        pre.length = a :=
      allSchedules_schedule_length
        n a pre hpre
    have hfun :
        (fun suf : DetSchedule n =>
          p ((pre ++ suf).take a)) =
        (fun _ : DetSchedule n => p pre) := by
      funext suf
      have htake :
          (pre ++ suf).take a = pre := by
        rw [← hlen]
        simp
      rw [htake]
    rw [hfun]
    cases hp : p pre <;>
      simp [hp, allSchedules_length]

  rw [hmap]
  exact
    sum_if_countP_mul_reset
      (allSchedules n a) p (n ^ b)


private theorem sum_map_le_reset
    {A : Type}
    (xs : List A)
    (f g : A -> Nat)
    (hfg :
      forall x,
        x ∈ xs ->
        f x <= g x) :
    (xs.map f).sum <= (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [
        List.map_cons,
        List.sum_cons,
        List.map_cons,
        List.sum_cons
      ]
      exact
        Nat.add_le_add
          (hfg x (by simp))
          (ih
            (fun y hy =>
              hfg y (by simp [hy])))


private theorem sum_map_const_reset
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


private theorem sum_map_mul_right_reset
    {A : Type}
    (xs : List A)
    (f : A -> Nat)
    (c : Nat) :
    (xs.map f).sum * c =
      (xs.map (fun x => f x * c)).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.add_mul]


private theorem nat_le_two_pow_self_reset
    (n : Nat) :
    n <= 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have hpos := Nat.two_pow_pos n
      omega


private theorem n_le_two_pow_four_mul_reset
    (n : Nat) :
    n <= 2 ^ (4 * n) := by
  have hself :
      n <= 2 ^ n :=
    nat_le_two_pow_self_reset n
  have hmono :
      2 ^ n <= 2 ^ (4 * n) :=
    Nat.pow_le_pow_right
      (by omega : 0 < 2)
      (by omega)
  exact Nat.le_trans hself hmono


private theorem n_le_two_pow_five_psi_reset
    {n psi : Nat}
    (hnpow : n <= 2 ^ psi) :
    n <= 2 ^ (5 * psi) := by
  have hmono :
      2 ^ psi <= 2 ^ (5 * psi) :=
    Nat.pow_le_pow_right
      (by omega : 0 < 2)
      (by omega)
  exact Nat.le_trans hnpow hmono


private theorem lemma5ResetPaperPad_eq_sweep
    (n : Nat) :
    lemma5PaperSweepHorizon n + 2 * n * n =
      lemma5SweepHorizon n := by
  unfold lemma5PaperSweepHorizon
  unfold lemma5SweepHorizon
  calc
    6 * n * n + 2 * n * n =
        6 * (n * n) + 2 * (n * n) := by
      rw [
        Nat.mul_assoc 6 n n,
        Nat.mul_assoc 2 n n
      ]
    _ = 8 * (n * n) := by
      omega
    _ = 8 * n * n := by
      rw [Nat.mul_assoc]


private theorem resetEncounterEnvelope_le_l7_5
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi) :
    24 * n <= lotteryL7Horizon psi 5 := by
  have hcoef :
      24 <= 4 * 5 * psi := by
    omega
  calc
    24 * n <=
        24 * 2 ^ psi :=
      Nat.mul_le_mul_left 24 hnpow
    _ <=
        (4 * 5 * psi) * 2 ^ psi :=
      Nat.mul_le_mul_right
        (2 ^ psi) hcoef
    _ = lotteryL7Horizon psi 5 := by
      rfl


private theorem resetTarget5_succ_le_target6
    (psi : Nat)
    (hpsi : 2 <= psi) :
    lotteryTarget psi 5 + 1 <=
      lotteryTarget psi 6 := by
  unfold lotteryTarget
  omega


private theorem lotteryAtLeastWordCount_mono_threshold_reset
    (k h T A B : Nat)
    (hAB : A <= B) :
    lotteryAtLeastWordCount k h T B <=
      lotteryAtLeastWordCount k h T A := by
  unfold lotteryAtLeastWordCount
  unfold lotteryPredWordCount
  apply countP_mono_reset
  intro word hw
  simp only [decide_eq_true_eq] at hw ⊢
  omega


/-! ## The two stopped bad events -/


def lemma5iResetEncounterBadB
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (word : DetSchedule n) : Bool :=
  decide
    (24 * n <
      stoppedPredictableHostHits
        ring host stop word)


def lemma5iResetLotteryBadB
    {n : Nat}
    (psi h : Nat)
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (word : DetSchedule n) : Bool :=
  let bits :=
    stoppedEncounterBits
      ring host stop word
  decide
    (lotteryTarget psi 6 <=
      (lotteryRun psi
        (lotteryOffset h) bits).wins)


private def lemma5iResetLotteryPaddedBadB
    {n : Nat}
    (psi h : Nat)
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (word : DetSchedule n) : Bool :=
  let bits :=
    stoppedEncounterBits
      ring host stop word
  decide
    (And
      (bits.length <= lotteryL7Horizon psi 5)
      (lotteryTarget psi 6 <=
        (lotteryRun psi
          (lotteryOffset h) bits).wins))


/-!
The requested residual.

The arm prefix is fixed before `host`, `stop`, and `h` are chosen, so
all three objects are predictable with respect to the subsequent sweep.
Only the suffix word varies.

The intended deterministic proof starts at the first max-TTL witness in the
arm prefix and follows its ghost owner.  The clauses of
`SignalLineageOwnership` are exactly the ingredients needed to show that a
disappearing max-TTL lineage either sees >24*n stopped encounters or spends
at least 48*psi lottery wins.
-/


def Lemma5iResetLineageWordCharge : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    forall pre : DetSchedule n,
      pre ∈ allSchedules n (lemma5ArmHorizon n) ->
      exists
        host : List (Fin n) -> Fin n,
      exists
        stop : List (Fin n) -> Bool,
      exists h : Nat,
        And
          (h <= psi)
          (forall suf : DetSchedule n,
            suf ∈
              allSchedules n
                (lemma5SweepHorizon n) ->
            lemma5iResetLineageBadB
                ring C (pre ++ suf) = true ->
            (lemma5iResetEncounterBadB
                ring host stop
                (suf.take
                  (lemma5PaperSweepHorizon n)) ||
              lemma5iResetLotteryBadB
                psi h ring host stop
                (suf.take
                  (lemma5PaperSweepHorizon n))) =
              true)


/-! ## Stopped-stream bookkeeping -/


private theorem stoppedBits_length_eq_hitsAux_reset
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (pre word : DetSchedule n) :
    (stoppedEncounterBitsAux
      ring host stop pre word).length =
      stoppedPredictableHostHitsAux
        ring host stop pre word := by
  induction word generalizing pre with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hs : stop pre with
      | true =>
          simp [
            stoppedEncounterBitsAux,
            stoppedPredictableHostHitsAux,
            hs
          ]
      | false =>
          let x := host pre
          by_cases hH :
              e = ring.leftNeighbor x
          · have hi :
                incidentBit ring x e =
                  some true := by
              unfold incidentBit
              rw [if_pos hH]
            have hil :
                incidentLetter ring x e =
                  true := by
              simp [
                incidentLetter,
                twoEdgeLetter,
                hH
              ]
            simp [
              stoppedEncounterBitsAux,
              stoppedPredictableHostHitsAux,
              hs,
              x,
              hi,
              hil,
              ih (pre := pre ++ [e])
            ]
            <;> omega
          · by_cases hT : e = x
            · have hi :
                  incidentBit ring x e =
                    some false := by
                unfold incidentBit
                rw [if_neg hH, if_pos hT]
              have hil :
                  incidentLetter ring x e =
                    true := by
                simp [
                  incidentLetter,
                  twoEdgeLetter,
                  hT
                ]
              simp [
                stoppedEncounterBitsAux,
                stoppedPredictableHostHitsAux,
                hs,
                x,
                hi,
                hil,
                ih (pre := pre ++ [e])
              ]
              <;> omega
            · have hi :
                  incidentBit ring x e =
                    none := by
                simp [incidentBit, hH, hT]
              have hil :
                  incidentLetter ring x e =
                    false := by
                simp [
                  incidentLetter,
                  twoEdgeLetter,
                  hH,
                  hT
                ]
              simp [
                stoppedEncounterBitsAux,
                stoppedPredictableHostHitsAux,
                hs,
                x,
                hi,
                hil,
                ih (pre := pre ++ [e])
              ]


private theorem stoppedBits_length_eq_hits_reset
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (word : DetSchedule n) :
    (stoppedEncounterBits
      ring host stop word).length =
      stoppedPredictableHostHits
        ring host stop word := by
  exact
    stoppedBits_length_eq_hitsAux_reset
      ring host stop [] word


private theorem resetCharge_to_padded
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (h : Nat)
    (word : DetSchedule n)
    (hcharge :
      (lemma5iResetEncounterBadB
          ring host stop word ||
        lemma5iResetLotteryBadB
          psi h ring host stop word) =
        true) :
    (lemma5iResetEncounterBadB
        ring host stop word ||
      lemma5iResetLotteryPaddedBadB
        psi h ring host stop word) =
      true := by
  cases hq :
      lemma5iResetEncounterBadB
        ring host stop word with
  | true =>
      simp [hq]
  | false =>
      have hr :
          lemma5iResetLotteryBadB
              psi h ring host stop word =
            true := by
        simpa [hq] using hcharge

      have hhits :
          stoppedPredictableHostHits
              ring host stop word <=
            24 * n := by
        by_cases hgt :
            24 * n <
              stoppedPredictableHostHits
                ring host stop word
        · have hqt :
              lemma5iResetEncounterBadB
                  ring host stop word =
                true := by
            unfold lemma5iResetEncounterBadB
            exact decide_eq_true hgt
          rw [hqt] at hq
          cases hq
        · omega

      have hlen :
          (stoppedEncounterBits
              ring host stop word).length <=
            lotteryL7Horizon psi 5 := by
        calc
          (stoppedEncounterBits
              ring host stop word).length =
              stoppedPredictableHostHits
                ring host stop word :=
            stoppedBits_length_eq_hits_reset
              ring host stop word
          _ <= 24 * n := hhits
          _ <= lotteryL7Horizon psi 5 :=
            resetEncounterEnvelope_le_l7_5
              hpsi hnpow

      dsimp [lemma5iResetLotteryBadB] at hr
      have hwins :
          lotteryTarget psi 6 <=
            (lotteryRun psi
              (lotteryOffset h)
              (stoppedEncounterBits
                ring host stop word)).wins :=
        of_decide_eq_true hr

      have hrpad :
          lemma5iResetLotteryPaddedBadB
              psi h ring host stop word =
            true := by
        dsimp [lemma5iResetLotteryPaddedBadB]
        exact
          decide_eq_true
            (And.intro hlen hwins)

      simp [hq, hrpad]


/-! ## Per-arm suffix count -/


def lemma5iResetSuffixFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n) : Nat :=
  ((allSchedules n
      (lemma5SweepHorizon n)).map
    (fun suf => pre ++ suf)).countP
      (lemma5iResetLineageBadB ring C)


private theorem resetFailureCount_eq_suffixSum
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma5iResetLineageFailureCount ring C =
      ((allSchedules n
          (lemma5ArmHorizon n)).map
        (lemma5iResetSuffixFailureCount
          ring C)).sum := by
  unfold lemma5iResetLineageFailureCount
  unfold lemma5iResetSuffixFailureCount
  rw [
    show
      lemma5iHorizon n =
        lemma5ArmHorizon n +
          lemma5SweepHorizon n
      by rfl
  ]
  rw [allSchedules_add_reset, List.countP_flatMap]
  rfl


/-!
Counting theorem for one fixed arm prefix.

The physical charge uses the actual arbitrary-offset 48*psi event.  The
counting conversion first pads it under the complement of the >24*n encounter
event.  To preserve the exact 48*psi threshold despite the one-win offset
loss, it then compares against the fresh c=5 event:
40*psi + 1 <= 48*psi.

This is why no false fresh/offset equality is assumed.
-/


theorem lemma5iResetLineageSuffixCount
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (h : Nat)
    (hh : h <= psi)
    (hword :
      forall suf : DetSchedule n,
        suf ∈
          allSchedules n
            (lemma5SweepHorizon n) ->
        lemma5iResetLineageBadB
            ring C (pre ++ suf) = true ->
        (lemma5iResetEncounterBadB
            ring host stop
            (suf.take
              (lemma5PaperSweepHorizon n)) ||
          lemma5iResetLotteryBadB
            psi h ring host stop
            (suf.take
              (lemma5PaperSweepHorizon n))) =
          true)
    (hoffset : WLGHeadOffsetBounds)
    (hcount : LotteryCountBounds) :
    n * lemma5iResetSuffixFailureCount
          ring C pre <=
      2 * n ^ lemma5SweepHorizon n := by
  let P : Nat :=
    lemma5PaperSweepHorizon n
  let Z : Nat :=
    2 * n * n
  let S : Nat :=
    lemma5SweepHorizon n

  let q : DetSchedule n -> Bool :=
    lemma5iResetEncounterBadB
      ring host stop
  let r : DetSchedule n -> Bool :=
    lemma5iResetLotteryBadB
      psi h ring host stop
  let rp : DetSchedule n -> Bool :=
    lemma5iResetLotteryPaddedBadB
      psi h ring host stop

  let Q : Nat :=
    (allSchedules n P).countP q
  let R : Nat :=
    (allSchedules n P).countP rp

  have hpoint :
      forall suf : DetSchedule n,
        suf ∈ allSchedules n S ->
        lemma5iResetLineageBadB
            ring C (pre ++ suf) = true ->
        (q (suf.take P) ||
          rp (suf.take P)) =
          true := by
    intro suf hsuf hbad
    have hraw :
        (q (suf.take P) ||
          r (suf.take P)) =
          true := by
      dsimp [q, r, P, S]
      exact hword suf hsuf hbad
    dsimp [q, r, rp] at hraw ⊢
    exact
      resetCharge_to_padded
        hpsi hnpow ring host stop h
        (suf.take P) hraw

  have hqPrefix0 :=
    countP_prefix_reset
      (n := n)
      (a := lemma5PaperSweepHorizon n)
      (b := 2 * n * n)
      (lemma5iResetEncounterBadB
        ring host stop)
  rw [lemma5ResetPaperPad_eq_sweep n]
    at hqPrefix0
  have hqPrefix :
      (allSchedules n S).countP
          (fun suf =>
            q (suf.take P)) =
        Q * n ^ Z := by
    simpa [P, Z, S, q, Q]
      using hqPrefix0

  have hrPrefix0 :=
    countP_prefix_reset
      (n := n)
      (a := lemma5PaperSweepHorizon n)
      (b := 2 * n * n)
      (lemma5iResetLotteryPaddedBadB
        psi h ring host stop)
  rw [lemma5ResetPaperPad_eq_sweep n]
    at hrPrefix0
  have hrPrefix :
      (allSchedules n S).countP
          (fun suf =>
            rp (suf.take P)) =
        R * n ^ Z := by
    simpa [P, Z, S, rp, R]
      using hrPrefix0

  have hbadCount :
      lemma5iResetSuffixFailureCount
          ring C pre <=
        Q * n ^ Z + R * n ^ Z := by
    unfold lemma5iResetSuffixFailureCount
    rw [List.countP_map]
    simp only [Function.comp_def]
    calc
      (allSchedules n S).countP
          (fun suf =>
            lemma5iResetLineageBadB
              ring C (pre ++ suf)) <=
          (allSchedules n S).countP
            (fun suf =>
              q (suf.take P) ||
                rp (suf.take P)) :=
        countP_mono_on_reset
          (allSchedules n S)
          (fun suf =>
            lemma5iResetLineageBadB
              ring C (pre ++ suf))
          (fun suf =>
            q (suf.take P) ||
              rp (suf.take P))
          hpoint
      _ <=
          (allSchedules n S).countP
              (fun suf =>
                q (suf.take P)) +
            (allSchedules n S).countP
              (fun suf =>
                rp (suf.take P)) :=
        countP_or_le_add_reset
          (allSchedules n S)
          (fun suf => q (suf.take P))
          (fun suf => rp (suf.take P))
      _ = Q * n ^ Z + R * n ^ Z := by
        rw [hqPrefix, hrPrefix]

  have hqTail0 :=
    stoppedPredictableHost24nBound
      n (by omega) ring host stop
  have hqTail :
      Q * 2 ^ (4 * n) <=
        n ^ P := by
    exact hqTail0

  have hqScale :
      n * Q <= n ^ P := by
    have hn4 :
        n <= 2 ^ (4 * n) :=
      n_le_two_pow_four_mul_reset n
    calc
      n * Q <=
          2 ^ (4 * n) * Q :=
        Nat.mul_le_mul_right Q hn4
      _ = Q * 2 ^ (4 * n) := by
        ac_rfl
      _ <= n ^ P := hqTail

  let E : Nat :=
    lotteryL7Horizon psi 5
  let M5 : Nat :=
    lotteryTarget psi 5
  let M6 : Nat :=
    lotteryTarget psi 6
  let B : Nat :=
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
      R * 2 ^ E <=
        n ^ P * B := by
    have hf :
        rp =
          (fun word =>
            let bits := stoppedEncounterBits ring host stop word
            decide
              (And (bits.length <= E)
                ((fun bits : List Bool =>
                    decide
                      (M6 <=
                        (lotteryRun psi (lotteryOffset h) bits).wins))
                  bits = true))) := by
      funext word
      simp only [rp, lemma5iResetLotteryPaddedBadB, E, M6,
        decide_eq_true_eq]
    have hR : R = List.countP rp (allSchedules n P) := rfl
    rw [hR, hf]
    exact htransfer0

  have hthreshold :
      M5 + 1 <= M6 := by
    dsimp [M5, M6]
    exact
      resetTarget5_succ_le_target6
        psi hpsi

  have hmono :
      lotteryAtLeastWordCount
          psi h E M6 <=
        lotteryAtLeastWordCount
          psi h E (M5 + 1) :=
    lotteryAtLeastWordCount_mono_threshold_reset
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

  have hB :
      B <= B0 := by
    dsimp [B, B0]
    exact Nat.le_trans hmono hhead

  have hL7 :
      scale * B0 <= 2 ^ E := by
    dsimp [scale, B0, E, M5]
    exact
      (hcount
        psi 5
        (by omega)
        (by omega)).1

  have hscaled :
      (scale * R) * 2 ^ E <=
        n ^ P * 2 ^ E := by
    calc
      (scale * R) * 2 ^ E =
          scale * (R * 2 ^ E) := by
        ac_rfl
      _ <= scale * (n ^ P * B) :=
        Nat.mul_le_mul_left
          scale htransfer
      _ = n ^ P * (scale * B) := by
        ac_rfl
      _ <= n ^ P * (scale * B0) :=
        Nat.mul_le_mul_left
          (n ^ P)
          (Nat.mul_le_mul_left
            scale hB)
      _ <= n ^ P * 2 ^ E :=
        Nat.mul_le_mul_left
          (n ^ P) hL7

  have hrTail :
      scale * R <= n ^ P :=
    Nat.le_of_mul_le_mul_right
      hscaled
      (Nat.pow_pos (by omega : 0 < 2))

  have hnScale :
      n <= scale := by
    dsimp [scale]
    exact
      n_le_two_pow_five_psi_reset
        hnpow

  have hrScale :
      n * R <= n ^ P := by
    exact
      Nat.le_trans
        (Nat.mul_le_mul_right
          R hnScale)
        hrTail

  have hQR :
      n * Q + n * R <=
        n ^ P + n ^ P :=
    Nat.add_le_add hqScale hrScale

  calc
    n * lemma5iResetSuffixFailureCount
          ring C pre <=
        n * (Q * n ^ Z + R * n ^ Z) :=
      Nat.mul_le_mul_left n hbadCount
    _ =
        (n * Q + n * R) * n ^ Z := by
      rw [Nat.mul_add, Nat.add_mul, Nat.mul_assoc n Q, Nat.mul_assoc n R]
    _ <=
        (n ^ P + n ^ P) * n ^ Z :=
      Nat.mul_le_mul_right
        (n ^ Z) hQR
    _ =
        (2 * n ^ P) * n ^ Z := by
      congr 1
      omega
    _ =
        2 * (n ^ P * n ^ Z) := by
      ac_rfl
    _ =
        2 * n ^ (P + Z) := by
      rw [Nat.pow_add]
    _ =
        2 * n ^ S := by
      dsimp [P, Z, S]
      rw [lemma5ResetPaperPad_eq_sweep n]


/-!
Outer arm-prefix splice.

All free scheduler letters after the 6*n^2 paper sweep are accounted for
exactly by `countP_prefix_reset`; this is not an independence assumption.
The sum over arm prefixes then preserves the per-prefix factor 2.
-/


theorem lemma5iResetLineageCount
    (hcharge :
      Lemma5iResetLineageWordCharge) :
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
      ModeStoppedTreeTransfer ->
      PredictableHostTails ->
      WLGHeadOffsetBounds ->
      LotteryCountBounds ->
      n * lemma5iResetLineageFailureCount
            ring C <=
        2 * n ^ lemma5iHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro hcnz hlineage
  intro _hmarked _hpredict
  intro hoffset hcount

  let A : Nat :=
    lemma5ArmHorizon n
  let S : Nat :=
    lemma5SweepHorizon n
  let f : DetSchedule n -> Nat :=
    lemma5iResetSuffixFailureCount
      ring C

  have hper :
      forall pre : DetSchedule n,
        pre ∈ allSchedules n A ->
        n * f pre <=
          2 * n ^ S := by
    intro pre hpre
    obtain
      ⟨host, stop, h, hh, hword⟩ :=
      hcharge
        hn3 hpsi hkappa
        ring C
        hcnz hlineage
        pre
        (by simpa [A] using hpre)
    dsimp [f, S]
    exact
      lemma5iResetLineageSuffixCount
        hn3 hpsi hnpow
        ring C pre
        host stop h hh
        hword
        hoffset hcount

  have hsum :
      ((allSchedules n A).map
        (fun pre => f pre * n)).sum <=
        ((allSchedules n A).map
          (fun _ => 2 * n ^ S)).sum := by
    apply sum_map_le_reset
    intro pre hpre
    have hp := hper pre hpre
    simpa [Nat.mul_comm] using hp

  rw [resetFailureCount_eq_suffixSum]

  calc
    n *
        ((allSchedules n A).map f).sum =
        ((allSchedules n A).map f).sum * n := by
      ac_rfl
    _ =
        ((allSchedules n A).map
          (fun pre => f pre * n)).sum :=
      sum_map_mul_right_reset
        (allSchedules n A) f n
    _ <=
        ((allSchedules n A).map
          (fun _ => 2 * n ^ S)).sum :=
      hsum
    _ =
        (allSchedules n A).length *
          (2 * n ^ S) :=
      sum_map_const_reset
        (allSchedules n A)
        (2 * n ^ S)
    _ =
        n ^ A * (2 * n ^ S) := by
      rw [allSchedules_length]
    _ =
        2 * n ^ (A + S) := by
      rw [Nat.pow_add]
      ac_rfl
    _ =
        2 * n ^ lemma5iHorizon n := by
      dsimp [A, S]
      rfl


end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iResetLineageSuffixCount
#print axioms PPL.Modes.Lemma5.lemma5iResetLineageCount
