import Leader.PPL.MainTheorem.Statement
import Leader.PPL.MainTheorem.Whp
import Leader.PPL.ReachCPB.CappedNoUpper
import Leader.PPL.ReachCPB.BulletSweepClosed
import Leader.PPL.ReachCPB.ModeScrubStep
import Leader.PPL.ReachCPB.CdGeometryPairStep
import Leader.PPL.ReachCPB.LastPairRow
import Leader.PPL.ReachCPB.StepDetectPersistence
import Leader.PPL.ReachCPB.StepDist

/-!
# P_PL Theorem 1, general fixed-cut padding and the L16 padded bound

Fixed-cut scheduler counting (`theorem1_fixedCutPaddedBound`: a phase bound
`n * bad ≤ c * n ^ T` after every prefix of length `A` pads to the horizon)
and the L16 padded bound at one `(n, psi)` with no domain premise.

These were proved three times: privately in `Theorem1L16PaddedCanonical`
(log window), in `PsiBelowN/PaddedRows` (`psi < n`) and in
`PsiAtLeastN/SafePaddedRows` (`n ≤ psi`), with the domain premise threaded
and never used.  Those three files now take the lemmas below; their
statements are unchanged.

P_PL Theorem 1 cleanup, phase 2, step 6a.
-/

namespace PPL.Theorem1General

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Fixed-cut scheduler counting -/

theorem theorem1_sum_if_count
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

/--
Exact fixed-prefix padding identity. A predicate on the first T letters is
replicated over exactly n^P continuations.
-/
theorem theorem1_countP_take_pad
    {n T P : Nat}
    (p : DetSchedule n -> Bool) :
    (allSchedules n (T + P)).countP
        (fun word => p (word.take T)) =
      (allSchedules n T).countP p * n ^ P := by
  rw [theorem1_allSchedules_add,
    List.countP_flatMap]
  simp only [Function.comp_def]
  have hmap :
      ((allSchedules n T).map
        (fun pre =>
          ((allSchedules n P).map
            (fun pad => pre ++ pad)).countP
              (fun word => p (word.take T)))) =
      (allSchedules n T).map
        (fun pre =>
          if p pre then n ^ P else 0) := by
    apply List.map_congr_left
    intro pre hpre
    try simp only [Function.comp_apply]
    rw [List.countP_map]
    simp only [Function.comp_def]
    have hlen :=
      allSchedules_schedule_length
        n T pre hpre
    have hfun :
        (fun pad : DetSchedule n =>
          p ((pre ++ pad).take T)) =
        (fun _ : DetSchedule n =>
          p pre) := by
      funext pad
      rw [← hlen, List.take_append_length]
    rw [hfun]
    cases hp : p pre <;>
      simp [hp, allSchedules_length]
  rw [hmap]
  exact
    theorem1_sum_if_count
      (allSchedules n T) p (n ^ P)

theorem theorem1_mul_sum_le_length_mul
    {A : Type}
    (xs : List A)
    (f : A -> Nat)
    (d B : Nat)
    (hf :
      forall x : A,
        x ∈ xs ->
        d * f x <= B) :
    d * (xs.map f).sum <=
      xs.length * B := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx :
          d * f x <= B :=
        hf x (by simp)
      have htail :
          forall y : A,
            y ∈ xs ->
            d * f y <= B := by
        intro y hy
        exact hf y (by simp [hy])
      have hi := ih htail
      calc
        d * ((x :: xs).map f).sum =
            d * f x +
              d * (xs.map f).sum := by
          simp [Nat.mul_add]
        _ <= B + xs.length * B :=
          Nat.add_le_add hx hi
        _ = (x :: xs).length * B := by
          simp [Nat.succ_mul, Nat.add_comm]

/--
Static two-block padding.

The first block has fixed length A. For each exact A-prefix, the T-letter
phase has the supplied denominator-cleared count bound. The first summation
cost is exactly n^A, and theorem1_pad_phase_bound supplies the final padding
from A+T to H.
-/
theorem theorem1_fixedCutPaddedBound
    {n A T H c : Nat}
    (hATH : A + T <= H)
    (bad :
      DetSchedule n ->
      DetSchedule n ->
      Bool)
    (hphase :
      forall pre : DetSchedule n,
        pre ∈ allSchedules n A ->
        n *
            (allSchedules n T).countP
              (bad pre) <=
          c * n ^ T) :
    n *
        (allSchedules n H).countP
          (fun word =>
            bad
              (word.take A)
              ((word.drop A).take T)) <=
      c * n ^ H := by
  let shortBad : DetSchedule n -> Bool :=
    fun word =>
      bad (word.take A) (word.drop A)

  have hshortCount :
      (allSchedules n (A + T)).countP
          shortBad =
        ((allSchedules n A).map
          (fun pre =>
            (allSchedules n T).countP
              (bad pre))).sum := by
    rw [theorem1_allSchedules_add,
      List.countP_flatMap]
    apply congrArg List.sum
    apply List.map_congr_left
    intro pre hpre
    try simp only [Function.comp_apply]
    rw [List.countP_map]
    simp only [Function.comp_def]
    have hlen :=
      allSchedules_schedule_length
        n A pre hpre
    apply congrArg
      (fun p =>
        (allSchedules n T).countP p)
    funext suf
    have htake :
        (pre ++ suf).take A = pre := by
      rw [← hlen]
      exact List.take_append_length
    have hdrop :
        (pre ++ suf).drop A = suf := by
      rw [← hlen]
      exact List.drop_append_length
    dsimp [shortBad]
    rw [htake, hdrop]

  have hshort :
      n *
          (allSchedules n (A + T)).countP
            shortBad <=
        c * n ^ (A + T) := by
    rw [hshortCount]
    have hsum :=
      theorem1_mul_sum_le_length_mul
        (allSchedules n A)
        (fun pre =>
          (allSchedules n T).countP
            (bad pre))
        n (c * n ^ T) hphase
    calc
      n *
          ((allSchedules n A).map
            (fun pre =>
              (allSchedules n T).countP
                (bad pre))).sum <=
          (allSchedules n A).length *
            (c * n ^ T) :=
        hsum
      _ = n ^ A * (c * n ^ T) := by
        rw [allSchedules_length]
      _ = c * n ^ (A + T) := by
        rw [Nat.pow_add]
        ac_rfl

  have hpred :
      (fun word : DetSchedule n =>
        bad
          (word.take A)
          ((word.drop A).take T)) =
      (fun word : DetSchedule n =>
        shortBad (word.take (A + T))) := by
    funext word
    dsimp [shortBad]
    rw [List.take_take, List.drop_take]
    have hmin :
        min A (A + T) = A :=
      Nat.min_eq_left (by omega)
    have hsub :
        A + T - A = T := by
      omega
    rw [hmin, hsub]

  have hpadCount :=
    theorem1_countP_take_pad
      (n := n)
      (T := A + T)
      (P := H - (A + T))
      shortBad
  rw [Nat.add_sub_of_le hATH] at hpadCount

  have hfullCount :
      (allSchedules n H).countP
          (fun word =>
            bad
              (word.take A)
              ((word.drop A).take T)) =
        (allSchedules n (A + T)).countP
            shortBad *
          n ^ (H - (A + T)) := by
    rw [hpred]
    exact hpadCount

  rw [hfullCount]
  exact
    theorem1_pad_phase_bound
      hATH hshort

/-! ## L16 -/

/-- Theorem 1, L16 padded bound at one `(n, psi)`, from the capped mismatch
witness and the Lemma 4 deterministic core, with no domain premise: the
fixed-word bound `lemma16_wordBound_capped_noUpper` holds for every `n`.
The L16 padded bounds of the log window (`PPL`), of `psi < n`
(`PPL.PsiBelowN`) and of `n ≤ psi` (`PPL.PsiAtLeastN`) are special cases. -/
theorem theorem1L16PaddedBound_of_mismatchWitness_core
    (hMismatchCanon :
      PPL.Convergence.ReachCPB.Lemma16MismatchWitnessCappedSpec)
    (hcore : PPL.lemma4_deterministic_core)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    n *
        (allSchedules n
          (theorem1Horizon n psi)).countP
            (theorem1Bad16B ring C0) <=
      12 * n ^ theorem1Horizon n psi := by

  have hword :
      PPL.Convergence.ReachCPB.Lemma16WordBound ring C0 :=
    PPL.Convergence.ReachCPB.lemma16_wordBound_capped_noUpper
      PPL.Convergence.ReachCPB.lemma16BulletSweepNatBound_closed
      (PPL.Convergence.ReachCPB.lemma16DetectPersistenceCapped
        PPL.Convergence.ReachCPB.lemma16DetectPersistenceCappedStepSpec_proved)
      (PPL.Convergence.ReachCPB.lemma16ModeCappedReachCount
        PPL.Convergence.ReachCPB.modeScrubOneStepSpec_proved)
      (PPL.Convergence.ReachCPB.lemma16DistForcingCapped
        PPL.Convergence.ReachCPB.lemma16DistForcingCappedStep)
      (PPL.Convergence.ReachCPB.lemma16LastForcingCapped
        PPL.Convergence.ReachCPB.lemma16LastForcingCappedStepSpec_proved)
      hMismatchCanon
      (PPL.Convergence.ReachCPB.lemma16CdTraceUntilSuccess_proved
        PPL.Convergence.ReachCPB.lemma16CdGeometryPairStepSpec_proved)
      hcore
      hn3 hpsi
      theorem1ModeC_ge_six
      (theorem1Kappa_eq_lemma16_form psi)
      hnpow ring C0

  have hTH :
      0 + theorem1H16 n psi <=
        theorem1Horizon n psi := by
    rw [theorem1Horizon_eq_phase_sum]
    omega

  have hphase :
      forall pre : DetSchedule n,
        pre ∈ allSchedules n 0 ->
        n *
            (allSchedules n
              (theorem1H16 n psi)).countP
              (fun phase =>
                !(PPL.Convergence.ReachCPB.reachesCPB ring C0 phase)) <=
          12 * n ^ theorem1H16 n psi := by
    intro _pre _hpre
    simpa
      [PPL.Convergence.ReachCPB.Lemma16WordBound,
        PPL.Convergence.ReachCPB.lemma16FailureCount,
        theorem1H16]
      using hword

  have hpad :=
    theorem1_fixedCutPaddedBound
      (n := n)
      (A := 0)
      (T := theorem1H16 n psi)
      (H := theorem1Horizon n psi)
      (c := 12)
      hTH
      (fun _ phase =>
        !(PPL.Convergence.ReachCPB.reachesCPB ring C0 phase))
      hphase

  have hfun :
      theorem1Bad16B ring C0 =
        fun word => theorem1Bad16B ring C0 word := rfl
  rw [hfun]
  simpa
    [theorem1Bad16B,
      theorem1Block16]
    using hpad

end PPL.Theorem1General

#print axioms PPL.Theorem1General.theorem1_fixedCutPaddedBound
#print axioms PPL.Theorem1General.theorem1L16PaddedBound_of_mismatchWitness_core
