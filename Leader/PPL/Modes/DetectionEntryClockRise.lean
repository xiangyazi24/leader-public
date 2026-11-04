import Leader.PPL.Modes.DetectionEntrySplit
import Leader.Core.LeaderCountDyadicTail

namespace PPL.Modes.Lemma6

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.Lemma9
open LeaderCountDyadicTail

private def clockRiseAnyPred {A : Type} :
    List (A → Bool) → A → Bool
  | [], _ => false
  | p :: ps, x => p x || clockRiseAnyPred ps x

private theorem clockRiseAnyPred_true_of_mem
    {A : Type}
    (ps : List (A → Bool))
    (p : A → Bool)
    (x : A)
    (hmem : p ∈ ps)
    (hp : p x = true) :
    clockRiseAnyPred ps x = true := by
  induction ps with
  | nil =>
      simp at hmem
  | cons q qs ih =>
      rcases List.mem_cons.mp hmem with hq | hq
      · subst q
        simp [clockRiseAnyPred, hp]
      · have ht := ih hq
        simp [clockRiseAnyPred, ht]

private theorem clockRiseCountP_mono
    {A : Type}
    (xs : List A)
    (p q : A → Bool)
    (hpq : ∀ x, p x = true → q x = true) :
    xs.countP p ≤ xs.countP q := by
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

private theorem clockRiseCountP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A → Bool) :
    xs.countP (fun x => p x || q x) ≤
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

private theorem clockRiseCountP_anyPred_le_sum
    {A : Type}
    (xs : List A)
    (ps : List (A → Bool)) :
    xs.countP (clockRiseAnyPred ps) ≤
      (ps.map (fun p => xs.countP p)).sum := by
  induction ps with
  | nil =>
      simp [clockRiseAnyPred]
  | cons p ps ih =>
      calc
        xs.countP (clockRiseAnyPred (p :: ps)) =
            xs.countP
              (fun x => p x || clockRiseAnyPred ps x) := by
          rfl
        _ ≤ xs.countP p +
            xs.countP (clockRiseAnyPred ps) :=
          clockRiseCountP_or_le_add
            xs p (clockRiseAnyPred ps)
        _ ≤ xs.countP p +
            (ps.map (fun q => xs.countP q)).sum :=
          Nat.add_le_add_left ih _
        _ =
            ((p :: ps).map
              (fun q => xs.countP q)).sum := by
          simp

/-- Generic finite union bound used below:
a bad schedule belongs to one of two bad events for some x : Fin n. -/
private theorem clockRise_fin_union_two_le
    {A : Type} {n : Nat}
    (xs : List A)
    (bad : A → Bool)
    (p q : Fin n → A → Bool)
    (hcover :
      ∀ x, bad x = true →
        ∃ i : Fin n, p i x = true ∨ q i x = true) :
    xs.countP bad ≤
      (List.ofFn (fun i : Fin n =>
        xs.countP (p i))).sum +
      (List.ofFn (fun i : Fin n =>
        xs.countP (q i))).sum := by
  let ps : List (A → Bool) := List.ofFn p
  let qs : List (A → Bool) := List.ofFn q
  have hbad :
      ∀ x, bad x = true →
        clockRiseAnyPred (ps ++ qs) x = true := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    rcases hi with hp | hq
    · have hm0 : p i ∈ ps := by
        dsimp [ps]
        rw [List.mem_ofFn]
        exact ⟨i, rfl⟩
      have hm : p i ∈ ps ++ qs :=
        List.mem_append.mpr (Or.inl hm0)
      exact
        clockRiseAnyPred_true_of_mem
          (ps ++ qs) (p i) x hm hp
    · have hm0 : q i ∈ qs := by
        dsimp [qs]
        rw [List.mem_ofFn]
        exact ⟨i, rfl⟩
      have hm : q i ∈ ps ++ qs :=
        List.mem_append.mpr (Or.inr hm0)
      exact
        clockRiseAnyPred_true_of_mem
          (ps ++ qs) (q i) x hm hq
  calc
    xs.countP bad ≤
        xs.countP (clockRiseAnyPred (ps ++ qs)) :=
      clockRiseCountP_mono
        xs bad (clockRiseAnyPred (ps ++ qs)) hbad
    _ ≤
        ((ps ++ qs).map
          (fun r => xs.countP r)).sum :=
      clockRiseCountP_anyPred_le_sum xs (ps ++ qs)
    _ =
        (List.ofFn (fun i : Fin n =>
          xs.countP (p i))).sum +
        (List.ofFn (fun i : Fin n =>
          xs.countP (q i))).sum := by
      dsimp [ps, qs]
      rw [List.map_append, List.sum_append,
        List.map_ofFn, List.map_ofFn]
      simp only [Function.comp_def]

private theorem clockRise_sum_ofFn_le
    {n : Nat}
    (f g : Fin n → Nat)
    (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact
        Nat.add_le_add
          (hfg 0)
          (ih
            (fun i => f i.succ)
            (fun i => g i.succ)
            (fun i => hfg i.succ))

private theorem clockRise_sum_ofFn_mul_left
    {n : Nat}
    (a : Nat)
    (f : Fin n → Nat) :
    (List.ofFn (fun i => a * f i)).sum =
      a * (List.ofFn f).sum := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        ih, Nat.mul_add]

private theorem clockRise_sum_ofFn_const
    (n a : Nat) :
    (List.ofFn (fun _ : Fin n => a)).sum =
      n * a := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        ih, Nat.succ_mul]
      omega

theorem lemma6ClockRiseCount :
    Lemma6ClockRiseCount := by
  intro n psi kappa c
  intro hn3 hpsi hc hkappa hnpow
  intro ring C
  intro hsplit hleader hsignal
  intro hearly hoffset hcount

  have hn2 : 2 ≤ n := by
    omega

  let T : Nat := lemma9T n psi c
  let E : Nat := lemma9E psi c
  let M : Nat := lotteryTarget psi c
  let K : Nat := 2 * psi
  let d : Nat := n - 1
  let words := allSchedules n T
  let stop := firstLeaderStop ring C
  let host : Fin n → List (Fin n) → Fin n :=
    fun x _ => x

  let encBad : Fin n → DetSchedule n → Bool :=
    fun x word =>
      decide
        (stopReached stop word = false ∧
          stoppedPredictableHostHits
            ring (host x) stop word < E)

  let lotBad : Fin n → DetSchedule n → Bool :=
    fun x word =>
      let bits :=
        stoppedEncounterBits ring (host x) stop word
      decide
        (stopReached stop word = false ∧
          E ≤ bits.length ∧
          (lotteryRun psi
            (lotteryOffset (C x).hits.val)
            (bits.take E)).wins ≤ M)

  let bad : DetSchedule n → Bool :=
    fun word => !(reachesAux ring C word)

  let encCount : Fin n → Nat :=
    fun x => words.countP (encBad x)

  let lotCount : Fin n → Nat :=
    fun x => words.countP (lotBad x)

  have hrunAppend :
      ∀ (D : Config n psi kappa)
        (u v : DetSchedule n),
        runPPL ring D (u ++ v) =
          runPPL ring (runPPL ring D u) v := by
    intro D u v
    induction u generalizing D with
    | nil =>
        rfl
    | cons e rest ih =>
        simp only [List.cons_append,
          runPPL, runPopulationSchedule]
        exact ih (D := pplStep ring D e)

  have hgoodCurrent :
      ∀ (D : Config n psi kappa)
        (word : DetSchedule n),
        reachesAux ring D word = false →
          lemma6GoodB D = false := by
    intro D word h
    cases word with
    | nil =>
        simpa [reachesAux] using h
    | cons e rest =>
        cases hg : lemma6GoodB D with
        | false =>
            rfl
        | true =>
            simp [reachesAux, hg] at h

  have hstopAux :
      ∀ (pre word : DetSchedule n),
        reachesAux ring (runPPL ring C pre) word = false →
          stopReachedAux stop pre word = false := by
    intro pre word hfail
    induction word generalizing pre with
    | nil =>
        have hgood :
            lemma6GoodB (runPPL ring C pre) = false :=
          hgoodCurrent
            (runPPL ring C pre) [] hfail
        have hl :
            leaderPresent (runPPL ring C pre) = false := by
          unfold lemma6GoodB at hgood
          cases hv :
              leaderPresent (runPPL ring C pre) with
          | false =>
              rfl
          | true =>
              simp [hv] at hgood
        simpa [stopReachedAux, stop,
          firstLeaderStop] using hl
    | cons e rest ih =>
        let D := runPPL ring C pre
        have hgood :
            lemma6GoodB D = false :=
          hgoodCurrent D (e :: rest) hfail
        have hl : leaderPresent D = false := by
          unfold lemma6GoodB at hgood
          cases hv : leaderPresent D with
          | false =>
              rfl
          | true =>
              simp [hv] at hgood
        have htail :
            reachesAux ring
                (pplStep ring D e) rest = false := by
          have h2 :
              lemma6GoodB D = false ∧
                reachesAux ring (pplStep ring D e) rest = false := by
            simpa [reachesAux] using hfail
          exact h2.2
        have hcfg :
            runPPL ring C (pre ++ [e]) =
              pplStep ring D e := by
          dsimp [D]
          rw [hrunAppend C pre [e]]
          rfl
        have hih :
            stopReachedAux
                stop (pre ++ [e]) rest = false := by
          apply ih (pre := pre ++ [e])
          simpa [hcfg] using htail
        simpa [stopReachedAux, stop,
          firstLeaderStop, D, hl] using hih

  have hstopOfFail :
      ∀ word : DetSchedule n,
        reachesAux ring C word = false →
          stopReached stop word = false := by
    intro word hfail
    have h :=
      hstopAux [] word
        (by
          simpa [runPPL, runPopulationSchedule]
            using hfail)
    simpa [stopReached] using h

  have hcover :
      ∀ word, bad word = true →
        ∃ x : Fin n,
          encBad x word = true ∨
            lotBad x word = true := by
    intro word hbad
    have hfail :
        reachesAux ring C word = false := by
      cases h : reachesAux ring C word <;>
        simp [bad, h] at hbad ⊢
    have hstop := hstopOfFail word hfail
    obtain ⟨x, _hmode, hx⟩ :=
      hsplit hn3 hpsi hkappa
        ring C word hleader hsignal hfail
    change
      stoppedPredictableHostHits
          ring (host x) stop word < E ∨
        (E ≤
            (stoppedEncounterBits
              ring (host x) stop word).length ∧
          (lotteryRun psi
            (lotteryOffset (C x).hits.val)
            ((stoppedEncounterBits
              ring (host x) stop word).take E)).wins ≤ M)
      at hx
    refine ⟨x, ?_⟩
    rcases hx with hshort | hlot
    · left
      simp [encBad, hstop, hshort]
    · right
      rcases hlot with ⟨hlen, hwins⟩
      simp [lotBad, hstop, hlen, hwins]

  have hunionRaw :
      words.countP bad ≤
        (List.ofFn encCount).sum +
          (List.ofFn lotCount).sum := by
    exact
      clockRise_fin_union_two_le
        words bad encBad lotBad hcover

  have hunion :
      lemma6ClockPhaseFailureCount ring C c ≤
        (List.ofFn encCount).sum +
          (List.ofFn lotCount).sum := by
    change words.countP bad ≤
      (List.ofFn encCount).sum +
        (List.ofFn lotCount).sum
    exact hunionRaw

  have hdpos : 0 < d := by
    dsimp [d]
    omega

  have hdn : d + 1 = n := by
    dsimp [d]
    omega

  have hber :=
    LeaderCountDyadicTail.bernoulli_scaled d d

  have hscaledBlock :
      d * (2 * d ^ d) ≤
        d * n ^ d := by
    calc
      d * (2 * d ^ d) =
          (d + d) * d ^ d := by
        simp only [Nat.two_mul,
          Nat.add_mul, Nat.mul_add]
      _ ≤ d * (d + 1) ^ d := hber
      _ = d * n ^ d := by
        rw [hdn]

  have hblock :
      2 * d ^ d ≤ n ^ d :=
    Nat.le_of_mul_le_mul_left
      hscaledBlock hdpos

  have hfirst :
      2 ^ E * d ^ (d * E) ≤
        n ^ (d * E) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul] using
      (Nat.pow_le_pow_left hblock E)

  have hdlePow :
      d ≤ 2 ^ psi := by
    dsimp [d]
    omega

  have hcoef : 2 ≤ 64 * c := by
    omega

  have hdk :
      d * K ≤ E := by
    calc
      d * K ≤ (2 ^ psi) * K :=
        Nat.mul_le_mul_right K hdlePow
      _ = 2 * (psi * 2 ^ psi) := by
        dsimp [K]
        ac_rfl
      _ ≤ (64 * c) *
          (psi * 2 ^ psi) :=
        Nat.mul_le_mul_right
          (psi * 2 ^ psi) hcoef
      _ = E := by
        dsimp [E, lemma9E,
          lotteryL8Horizon]
        ac_rfl

  have hkcore :
      2 ^ K * d ^ (d * K) ≤
        n ^ (d * K) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul] using
      (Nat.pow_le_pow_left hblock K)

  let R : Nat := E - d * K

  have hER :
      E = d * K + R := by
    dsimp [R]
    omega

  have hdleN : d ≤ n := by
    dsimp [d]
    omega

  have hrem :
      d ^ R ≤ n ^ R :=
    Nat.pow_le_pow_left hdleN R

  have hsecond :
      2 ^ K * d ^ E ≤ n ^ E := by
    calc
      2 ^ K * d ^ E =
          (2 ^ K * d ^ (d * K)) *
            d ^ R := by
        rw [hER, Nat.pow_add]
        ac_rfl
      _ ≤ n ^ (d * K) * n ^ R :=
        Nat.mul_le_mul hkcore hrem
      _ = n ^ E := by
        rw [hER, Nat.pow_add]

  have hboth :=
    Nat.mul_le_mul hfirst hsecond

  have hTdef :
      T = n * E := by
    rfl

  have hTdecomp :
      T = d * E + E := by
    rw [hTdef, ← hdn,
      Nat.add_mul, Nat.one_mul]

  have hdecay :
      2 ^ (E + K) * d ^ T ≤ n ^ T := by
    calc
      2 ^ (E + K) * d ^ T =
          (2 ^ E * d ^ (d * E)) *
            (2 ^ K * d ^ E) := by
        rw [hTdecomp,
          Nat.pow_add, Nat.pow_add]
        ac_rfl
      _ ≤ n ^ (d * E) * n ^ E :=
        hboth
      _ = n ^ T := by
        rw [hTdecomp, Nat.pow_add]

  have hET : E ≤ T := by
    rw [hTdef]
    calc
      E = 1 * E := by simp
      _ ≤ n * E :=
        Nat.mul_le_mul_right E (by omega)

  have ha : E ≤ T + 1 := by
    omega

  have hscale :
      LowerTailScaleArithmetic n T E K := by
    unfold LowerTailScaleArithmetic
    have hbase :
        2 * n - 2 = 2 * d := by
      dsimp [d]
      omega
    rw [hbase, Nat.mul_pow]
    have hexp :
        T + K ≤
          (T + 1 - E) + (E + K) := by
      omega
    have hp :
        2 ^ (T + K) ≤
          2 ^ ((T + 1 - E) + (E + K)) :=
      Nat.pow_le_pow_right
        (by decide) hexp
    have hleft :
        (2 ^ T * d ^ T) * 2 ^ K ≤
          2 ^ (T + 1 - E) *
            (2 ^ (E + K) * d ^ T) := by
      calc
        (2 ^ T * d ^ T) * 2 ^ K =
            2 ^ (T + K) * d ^ T := by
          rw [Nat.pow_add]
          ac_rfl
        _ ≤
            2 ^ ((T + 1 - E) +
              (E + K)) * d ^ T :=
          Nat.mul_le_mul_right
            (d ^ T) hp
        _ =
            2 ^ (T + 1 - E) *
              (2 ^ (E + K) * d ^ T) := by
          rw [Nat.pow_add]
          ac_rfl
    have hm :=
      Nat.mul_le_mul_left
        (2 ^ (T + 1 - E)) hdecay
    calc
      (2 ^ T * d ^ T) * 2 ^ K ≤
          2 ^ (T + 1 - E) *
            (2 ^ (E + K) * d ^ T) :=
        hleft
      _ ≤
          2 ^ (T + 1 - E) * n ^ T :=
        hm
      _ =
          n ^ T * 2 ^ (T + 1 - E) := by
        ac_rfl

  have hraw :
      twoEdgeLowerTailCount n T E *
          2 ^ K ≤
        n ^ T :=
    twoEdgeLowerTail_scaled_of_arithmetic
      n T E K hn2 ha hscale

  have hnnK :
      n * n ≤ 2 ^ K := by
    have hsq :=
      Nat.mul_le_mul hnpow hnpow
    calc
      n * n ≤
          (2 ^ psi) * (2 ^ psi) :=
        hsq
      _ = 2 ^ (psi + psi) := by
        rw [Nat.pow_add]
      _ = 2 ^ K := by
        rw [show psi + psi = K by
          dsimp [K]
          omega]

  have hencRaw :
      n * n *
          twoEdgeLowerTailCount n T E ≤
        3 * n ^ T := by
    calc
      n * n *
          twoEdgeLowerTailCount n T E ≤
          2 ^ K *
            twoEdgeLowerTailCount n T E :=
        Nat.mul_le_mul_right
          (twoEdgeLowerTailCount n T E)
          hnnK
      _ =
          twoEdgeLowerTailCount n T E *
            2 ^ K := by
        ac_rfl
      _ ≤ n ^ T := hraw
      _ ≤ 3 * n ^ T := by
        omega

  have hL8 :
      2 ^ (c * psi) *
          lotteryAtMostWordCount
            psi 0 E M ≤
        2 ^ E := by
    simpa [E, M, lemma9E] using
      (hcount psi c (by omega) (by omega)).2

  have hnnC :
      n * n ≤ 2 ^ (c * psi) := by
    have ha0 :=
      Nat.mul_le_mul hnpow hnpow
    have hb0 :
        2 ^ psi * 2 ^ psi =
          2 ^ (2 * psi) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have he :
        2 * psi ≤ c * psi :=
      Nat.mul_le_mul_right psi (by omega)
    calc
      n * n ≤
          2 ^ psi * 2 ^ psi :=
        ha0
      _ = 2 ^ (2 * psi) := hb0
      _ ≤ 2 ^ (c * psi) :=
        Nat.pow_le_pow_right
          (by decide) he

  have hencBound :
      ∀ x : Fin n,
        n * n * encCount x ≤
          3 * n ^ T := by
    intro x
    have hh :
        (C x).hits.val ≤ psi := by
      have hlt := (C x).hits.isLt
      omega
    have he :=
      hearly n psi kappa T E M
        (C x).hits.val hn2 hpsi hh
        ring C (host x) hleader
    dsimp only at he
    change
      n * n *
          stoppedPredictableHostLowerFailureCount
            ring (host x) stop T E ≤
        3 * n ^ T
    exact
      Nat.le_trans
        (Nat.mul_le_mul_left
          (n * n) he.1)
        hencRaw

  have hlotBound :
      ∀ x : Fin n,
        n * n * lotCount x ≤
          n ^ T := by
    intro x
    let h : Nat := (C x).hits.val
    let B : Nat :=
      lotteryAtMostWordCount psi h E M
    let B0 : Nat :=
      lotteryAtMostWordCount psi 0 E M
    have hh : h ≤ psi := by
      dsimp [h]
      have hlt := (C x).hits.isLt
      omega
    have he :=
      hearly n psi kappa T E M h
        hn2 hpsi hh
        ring C (host x) hleader
    dsimp only at he
    have hbinary :
        lotCount x * 2 ^ E ≤
          n ^ T * B := by
      change
        stoppedLotteryLowerFailureCount
            psi h ring (host x) stop
            T E M * 2 ^ E ≤
          n ^ T * B
      exact he.2
    have hhead : B ≤ B0 := by
      dsimp [B, B0]
      exact
        (hoffset psi h E M
          (by omega) hh).1
    have hscaled :
        (2 ^ (c * psi) * lotCount x) *
            2 ^ E ≤
          n ^ T * 2 ^ E := by
      calc
        (2 ^ (c * psi) * lotCount x) *
              2 ^ E =
            2 ^ (c * psi) *
              (lotCount x * 2 ^ E) := by
          ac_rfl
        _ ≤
            2 ^ (c * psi) *
              (n ^ T * B) :=
          Nat.mul_le_mul_left _ hbinary
        _ =
            n ^ T *
              (2 ^ (c * psi) * B) := by
          ac_rfl
        _ ≤
            n ^ T *
              (2 ^ (c * psi) * B0) :=
          Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ hhead)
        _ ≤ n ^ T * 2 ^ E :=
          Nat.mul_le_mul_left _ hL8
    have htail :
        2 ^ (c * psi) * lotCount x ≤
          n ^ T :=
      Nat.le_of_mul_le_mul_right
        hscaled
        (Nat.pow_pos (by decide : 0 < 2))
    exact
      Nat.le_trans
        (Nat.mul_le_mul_right
          (lotCount x) hnnC)
        htail

  have hsumEnc :
      (List.ofFn
        (fun x : Fin n =>
          n * n * encCount x)).sum ≤
      (List.ofFn
        (fun _ : Fin n =>
          3 * n ^ T)).sum :=
    clockRise_sum_ofFn_le
      _ _ hencBound

  have hsumLot :
      (List.ofFn
        (fun x : Fin n =>
          n * n * lotCount x)).sum ≤
      (List.ofFn
        (fun _ : Fin n =>
          n ^ T)).sum :=
    clockRise_sum_ofFn_le
      _ _ hlotBound

  have hscaledFinal :
      n * n *
          lemma6ClockPhaseFailureCount
            ring C c ≤
        n * (4 * n ^ T) := by
    calc
      n * n *
          lemma6ClockPhaseFailureCount
            ring C c ≤
          n * n *
            ((List.ofFn encCount).sum +
              (List.ofFn lotCount).sum) :=
        Nat.mul_le_mul_left (n * n) hunion
      _ =
          (List.ofFn
            (fun x : Fin n =>
              n * n * encCount x)).sum +
          (List.ofFn
            (fun x : Fin n =>
              n * n * lotCount x)).sum := by
        rw [Nat.mul_add,
          ← clockRise_sum_ofFn_mul_left
            (n * n) encCount,
          ← clockRise_sum_ofFn_mul_left
            (n * n) lotCount]
      _ ≤
          (List.ofFn
            (fun _ : Fin n =>
              3 * n ^ T)).sum +
          (List.ofFn
            (fun _ : Fin n =>
              n ^ T)).sum :=
        Nat.add_le_add hsumEnc hsumLot
      _ =
          n * (3 * n ^ T) +
            n * n ^ T := by
        rw [clockRise_sum_ofFn_const,
          clockRise_sum_ofFn_const]
      _ = n * (4 * n ^ T) := by
        rw [← Nat.mul_add]
        congr 1
        omega

  have hcancel :
      n *
          (n *
            lemma6ClockPhaseFailureCount
              ring C c) ≤
        n * (4 * n ^ T) := by
    simpa [Nat.mul_assoc] using hscaledFinal

  have hout :
      n *
          lemma6ClockPhaseFailureCount
            ring C c ≤
        4 * n ^ T :=
    Nat.le_of_mul_le_mul_left
      hcancel (by omega)

  simpa [T] using hout

end PPL.Modes.Lemma6

#print axioms PPL.Modes.Lemma6.lemma6ClockRiseCount

