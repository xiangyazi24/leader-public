import Leader.PPL.Modes.ConstructionModeSplit


/-!
# P_PL Lemma 5 deterministic failure splits


Truth audit.


* Lemma5iFailureSplit is TRUE as stated.  In fact it is stronger than its
  interface: neither neverLeaderless nor SignalLineageOwnership is needed for
  the split.  Full-horizon failure implies failure on every shorter prefix.
  If the arm event fails, phase A fires.  If the arm event succeeds, either
  not every clock is reset in the paper sweep (phase C) or every clock is
  reset and C_mid is still absent on the paper prefix (phase D).  The
  reset-lineage phase B is therefore redundant for coverage and remains only
  as a nonnegative summand for the later counting budget.


* Lemma5iiFailureSplit is TRUE as stated.  It is exactly the Boolean
  partition of a failed constructAlong word according to whether
  lemma5iiEncounterBadB holds.


No counterexample exists for either leaf, so no corrected statement is
needed.
-/


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


private theorem countP_mono_local
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
          have hqx : q x = true :=
            hpq x hp
          simp [hp, hqx]
          omega


private theorem countP_or_le_add_local
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
        simp [hp, hq] <;>
        omega


private theorem take_append_take_drop_local
    {A : Type}
    (xs : List A) (a b : Nat) :
    xs.take a ++ (xs.drop a).take b =
      xs.take (a + b) := by
  induction a generalizing xs with
  | zero =>
      simp
  | succ a ih =>
      cases xs with
      | nil =>
          simp
      | cons x xs =>
          simp [Nat.succ_add, ih]


private theorem reachesAux_false_take_local
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n) :
    reachesAux ring good C word = false →
      ∀ k,
        reachesAux ring good C (word.take k) = false := by
  induction word generalizing C with
  | nil =>
      intro hfalse k
      simpa [reachesAux] using hfalse
  | cons e rest ih =>
      intro hfalse k
      have hgood : good C = false := by
        cases hg : good C with
        | false =>
            rfl
        | true =>
            simp [reachesAux, hg] at hfalse
      have htail :
          reachesAux ring good
              (pplStep ring C e) rest = false := by
        simpa [reachesAux, hgood] using hfalse
      cases k with
      | zero =>
          simpa [reachesAux, hgood]
      | succ k =>
          have htaken :=
            ih (C := pplStep ring C e) htail k
          simpa [reachesAux, hgood] using htaken


theorem lemma5iFailureSplit :
    Lemma5iFailureSplit := by
  intro n psi kappa
  intro _hn3 _hpsi _hkappa _hnpow
  intro ring C
  intro _hcnz _hlineage


  have hcover :
      ∀ word : DetSchedule n,
        (!(reachesAux ring midPhysicalB C word)) = true →
          (lemma5iLeaderArmBadB ring C word ||
            (lemma5iTraversalBadB ring C word ||
              lemma5iMidClockBadB ring C word)) = true := by
    intro word hbad
    have hfull :
        reachesAux ring midPhysicalB C word = false := by
      cases h :
          reachesAux ring midPhysicalB C word with
      | false =>
          rfl
      | true =>
          simp [h] at hbad


    have hpaperTake :
        reachesAux ring midPhysicalB C
            (word.take
              (lemma5ArmHorizon n +
                lemma5PaperSweepHorizon n)) = false :=
      reachesAux_false_take_local
        ring midPhysicalB C word hfull
          (lemma5ArmHorizon n +
            lemma5PaperSweepHorizon n)


    have hpaperEq :
        lemma5iPaperPrefix word =
          word.take
            (lemma5ArmHorizon n +
              lemma5PaperSweepHorizon n) := by
      unfold lemma5iPaperPrefix
        lemma5iArmPrefix
        lemma5iPaperSweepSuffix
      exact
        take_append_take_drop_local
          word
          (lemma5ArmHorizon n)
          (lemma5PaperSweepHorizon n)


    have hpaper :
        reachesAux ring midPhysicalB C
            (lemma5iPaperPrefix word) = false := by
      rw [hpaperEq]
      exact hpaperTake


    cases harm :
        reachesAux ring maxResetSignalB C
          (lemma5iArmPrefix word) with
    | false =>
        simp [lemma5iLeaderArmBadB, harm]
    | true =>
        cases hreset :
            allClockResetsSeenB ring
              (runPPL ring C
                (lemma5iArmPrefix word))
              (lemma5iPaperSweepSuffix word) with
        | false =>
            simp [lemma5iLeaderArmBadB,
              lemma5iTraversalBadB,
              harm, hreset]
        | true =>
            simp [lemma5iLeaderArmBadB,
              lemma5iTraversalBadB,
              lemma5iMidClockBadB,
              harm, hreset, hpaper]


  have hmono :
      (allSchedules n (lemma5iHorizon n)).countP
          (fun word =>
            !(reachesAux ring midPhysicalB C word)) ≤
        (allSchedules n (lemma5iHorizon n)).countP
          (fun word =>
            lemma5iLeaderArmBadB ring C word ||
              (lemma5iTraversalBadB ring C word ||
                lemma5iMidClockBadB ring C word)) :=
    countP_mono_local
      (allSchedules n (lemma5iHorizon n))
      (fun word =>
        !(reachesAux ring midPhysicalB C word))
      (fun word =>
        lemma5iLeaderArmBadB ring C word ||
          (lemma5iTraversalBadB ring C word ||
            lemma5iMidClockBadB ring C word))
      hcover


  have horOuter :
      (allSchedules n (lemma5iHorizon n)).countP
          (fun word =>
            lemma5iLeaderArmBadB ring C word ||
              (lemma5iTraversalBadB ring C word ||
                lemma5iMidClockBadB ring C word)) ≤
        (allSchedules n (lemma5iHorizon n)).countP
            (lemma5iLeaderArmBadB ring C) +
          (allSchedules n (lemma5iHorizon n)).countP
            (fun word =>
              lemma5iTraversalBadB ring C word ||
                lemma5iMidClockBadB ring C word) :=
    countP_or_le_add_local
      (allSchedules n (lemma5iHorizon n))
      (lemma5iLeaderArmBadB ring C)
      (fun word =>
        lemma5iTraversalBadB ring C word ||
          lemma5iMidClockBadB ring C word)


  have horInner :
      (allSchedules n (lemma5iHorizon n)).countP
          (fun word =>
            lemma5iTraversalBadB ring C word ||
              lemma5iMidClockBadB ring C word) ≤
        (allSchedules n (lemma5iHorizon n)).countP
            (lemma5iTraversalBadB ring C) +
          (allSchedules n (lemma5iHorizon n)).countP
            (lemma5iMidClockBadB ring C) :=
    countP_or_le_add_local
      (allSchedules n (lemma5iHorizon n))
      (lemma5iTraversalBadB ring C)
      (lemma5iMidClockBadB ring C)


  have hthree :
      (allSchedules n (lemma5iHorizon n)).countP
          (fun word =>
            !(reachesAux ring midPhysicalB C word)) ≤
        (allSchedules n (lemma5iHorizon n)).countP
            (lemma5iLeaderArmBadB ring C) +
          ((allSchedules n (lemma5iHorizon n)).countP
              (lemma5iTraversalBadB ring C) +
            (allSchedules n (lemma5iHorizon n)).countP
              (lemma5iMidClockBadB ring C)) := by
    calc
      (allSchedules n (lemma5iHorizon n)).countP
          (fun word =>
            !(reachesAux ring midPhysicalB C word))
          ≤
        (allSchedules n (lemma5iHorizon n)).countP
          (fun word =>
            lemma5iLeaderArmBadB ring C word ||
              (lemma5iTraversalBadB ring C word ||
                lemma5iMidClockBadB ring C word)) :=
        hmono
      _ ≤
        (allSchedules n (lemma5iHorizon n)).countP
            (lemma5iLeaderArmBadB ring C) +
          (allSchedules n (lemma5iHorizon n)).countP
            (fun word =>
              lemma5iTraversalBadB ring C word ||
                lemma5iMidClockBadB ring C word) :=
        horOuter
      _ ≤
        (allSchedules n (lemma5iHorizon n)).countP
            (lemma5iLeaderArmBadB ring C) +
          ((allSchedules n (lemma5iHorizon n)).countP
              (lemma5iTraversalBadB ring C) +
            (allSchedules n (lemma5iHorizon n)).countP
              (lemma5iMidClockBadB ring C)) :=
        Nat.add_le_add_left horInner _


  unfold lemma5iFailureCount
    lemma5iLeaderArmFailureCount
    lemma5iResetLineageFailureCount
    lemma5iTraversalFailureCount
    lemma5iMidClockFailureCount
  omega


theorem lemma5iiFailureSplit :
    Lemma5iiFailureSplit := by
  intro n psi kappa c
  intro _hn3 _hpsi _hc _hkappa _hnpow
  intro ring C
  intro _hmid


  have hcover :
      ∀ word : DetSchedule n,
        (!(constructAlong ring C word)) = true →
          (lemma5iiEncounterBadB psi c ring word ||
            lemma5iiPostResetClockBadB
              ring C c word) = true := by
    intro word hbad
    cases henc :
        lemma5iiEncounterBadB psi c ring word with
    | true =>
        simp [henc]
    | false =>
        have hconstruct :
            constructAlong ring C word = false := by
          cases hcstr :
              constructAlong ring C word with
          | false =>
              rfl
          | true =>
              simp [hcstr] at hbad
        simp [lemma5iiPostResetClockBadB,
          henc, hconstruct]


  have hmono :
      (allSchedules n
          (lemma5iiHorizon n psi kappa)).countP
        (fun word =>
          !(constructAlong ring C word)) ≤
      (allSchedules n
          (lemma5iiHorizon n psi kappa)).countP
        (fun word =>
          lemma5iiEncounterBadB psi c ring word ||
            lemma5iiPostResetClockBadB
              ring C c word) :=
    countP_mono_local
      (allSchedules n
        (lemma5iiHorizon n psi kappa))
      (fun word =>
        !(constructAlong ring C word))
      (fun word =>
        lemma5iiEncounterBadB psi c ring word ||
          lemma5iiPostResetClockBadB
            ring C c word)
      hcover


  have hor :
      (allSchedules n
          (lemma5iiHorizon n psi kappa)).countP
        (fun word =>
          lemma5iiEncounterBadB psi c ring word ||
            lemma5iiPostResetClockBadB
              ring C c word) ≤
      (allSchedules n
          (lemma5iiHorizon n psi kappa)).countP
          (lemma5iiEncounterBadB psi c ring) +
        (allSchedules n
          (lemma5iiHorizon n psi kappa)).countP
          (lemma5iiPostResetClockBadB ring C c) :=
    countP_or_le_add_local
      (allSchedules n
        (lemma5iiHorizon n psi kappa))
      (lemma5iiEncounterBadB psi c ring)
      (lemma5iiPostResetClockBadB ring C c)


  simpa [lemma5iiFailureCount,
    lemma5iiEncounterFailureCount,
    lemma5iiPostResetClockFailureCount] using
    Nat.le_trans hmono hor


end PPL.Modes.Lemma5


#print axioms PPL.Modes.Lemma5.lemma5iFailureSplit
#print axioms PPL.Modes.Lemma5.lemma5iiFailureSplit


