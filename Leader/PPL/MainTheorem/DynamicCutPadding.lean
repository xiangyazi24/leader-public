import Leader.PPL.MainTheorem.PaddingInterface
import Leader.PPL.MainTheorem.GeneralFixedCut

/-!
P_PL Theorem 1 cleanup, step 6f: the counting helpers `sum_if_count`,
`countP_take_pad` and `mul_sum_le_length_mul` are the
`PPL.Theorem1General` versions (`Leader/PPL/MainTheorem/GeneralFixedCut.lean`);
the private copies are gone.
-/

namespace PPL


private theorem theorem1Dynamic_countP_mono
    {A : Type}
    (xs : List A)
    (p q : A → Bool)
    (h :
      ∀ x : A,
        x ∈ xs →
        p x = true →
        q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have htail :
          ∀ y : A,
            y ∈ xs →
            p y = true →
            q y = true := by
        intro y hy hpy
        exact h y (by simp [hy]) hpy
      have hi := ih htail
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [List.countP_cons, hp, hq] at hi ⊢ <;>
            omega
      | true =>
          have hxq :
              q x = true :=
            h x (by simp) hp
          simpa [List.countP_cons, hp, hxq]
            using Nat.succ_le_succ hi


private theorem theorem1Dynamic_factor_length
    {n H T : Nat}
    {word p phase pad : DetSchedule n}
    (hword :
      word ∈ allSchedules n H)
    (hphase :
      phase ∈ allSchedules n T)
    (hfactor :
      word = p ++ phase ++ pad) :
    p.length + T ≤ H := by
  have hwordLen :=
    allSchedules_schedule_length
      n H word hword
  have hphaseLen :=
    allSchedules_schedule_length
      n T phase hphase
  have hlen :=
    congrArg List.length hfactor
  simp only [List.length_append] at hlen
  rw [hwordLen, hphaseLen] at hlen
  omega


private theorem theorem1Dynamic_rootStopped
    {n H T c : Nat}
    (stop : DetSchedule n → Bool)
    (phaseBad :
      DetSchedule n →
      DetSchedule n →
      Bool)
    (globalBad : DetSchedule n → Bool)
    (hfree :
      ∀ p q : DetSchedule n,
        stop p = true →
        stop q = true →
        List.IsPrefix p q →
        p = q)
    (hphase :
      ∀ p : DetSchedule n,
        stop p = true →
        p.length + T ≤ H →
        n *
            (allSchedules n T).countP
              (phaseBad p) ≤
          c * n ^ T)
    (hcover :
      ∀ word : DetSchedule n,
        word ∈ allSchedules n H →
        globalBad word = true →
        ∃ p : DetSchedule n,
          ∃ phase : DetSchedule n,
            ∃ pad : DetSchedule n,
              stop p = true ∧
                phase ∈ allSchedules n T ∧
                  word = p ++ phase ++ pad ∧
                    phaseBad p phase = true)
    (hstop :
      stop [] = true) :
    n *
        (allSchedules n H).countP
          globalBad ≤
      c * n ^ H := by
  by_cases hTH : T ≤ H
  · have hcount :
        (allSchedules n H).countP
            globalBad ≤
          (allSchedules n H).countP
            (fun word =>
              phaseBad [] (word.take T)) := by
      apply theorem1Dynamic_countP_mono
      intro word hword hbad
      obtain
          ⟨p, phase, pad,
            hp, hphaseMem,
            hfactor, hphaseBad⟩ :=
        hcover word hword hbad
      have hpref :
          List.IsPrefix
            ([] : DetSchedule n) p := by
        exact ⟨p, by simp⟩
      have hpEq :
          ([] : DetSchedule n) = p :=
        hfree [] p hstop hp hpref
      subst p
      have hphaseLen :=
        allSchedules_schedule_length
          n T phase hphaseMem
      have htake :
          word.take T = phase := by
        rw [hfactor]
        simp only [List.nil_append]
        rw [← hphaseLen,
          List.take_append_length]
      rw [htake]
      exact hphaseBad


    have hphase0 :
        n *
            (allSchedules n T).countP
              (phaseBad []) ≤
          c * n ^ T :=
      hphase [] hstop
        (by simpa using hTH)


    have hpadCount :=
      Theorem1General.theorem1_countP_take_pad
        (n := n)
        (T := T)
        (P := H - T)
        (phaseBad [])
    rw [Nat.add_sub_of_le hTH] at hpadCount


    calc
      n *
          (allSchedules n H).countP
            globalBad ≤
        n *
          (allSchedules n H).countP
            (fun word =>
              phaseBad [] (word.take T)) :=
        Nat.mul_le_mul_left n hcount
      _ =
        n *
          ((allSchedules n T).countP
              (phaseBad []) *
            n ^ (H - T)) := by
        rw [hpadCount]
      _ ≤ c * n ^ H :=
        theorem1_pad_phase_bound
          hTH hphase0
  · have hcount :
        (allSchedules n H).countP
            globalBad ≤
          (allSchedules n H).countP
            (fun _ => false) := by
      apply theorem1Dynamic_countP_mono
      intro word hword hbad
      obtain
          ⟨p, phase, pad,
            hp, hphaseMem,
            hfactor, hphaseBad⟩ :=
        hcover word hword hbad
      have hlen :=
        theorem1Dynamic_factor_length
          hword hphaseMem hfactor
      exact False.elim (hTH (by omega))
    have hle :
        (allSchedules n H).countP
            globalBad ≤ 0 := by
      simpa using hcount
    have hz :
        (allSchedules n H).countP
            globalBad = 0 := by
      omega
    rw [hz]
    simp


/--
Finite prefix-free cylinder/Kraft induction.


If the empty prefix stops, prefix-freeness says it is the only stopping
prefix and the fixed-prefix padding bound applies. Otherwise, for positive
horizon, split on the first scheduler letter and recurse independently below
each child. Summing the child bounds multiplies by exactly n, which is the
finite Kraft identity at the next depth.
-/
private theorem theorem1DynamicCutPadding_aux :
    Theorem1DynamicCutPadding := by
  unfold Theorem1DynamicCutPadding
  intro n H T c
  induction H with
  | zero =>
      intro stop phaseBad globalBad
      intro hfree hphase hcover
      cases hs0 : stop [] with
      | true =>
          exact
            theorem1Dynamic_rootStopped
              stop phaseBad globalBad
              hfree hphase hcover hs0
      | false =>
          have hcount :
              (allSchedules n 0).countP
                  globalBad ≤
                (allSchedules n 0).countP
                  (fun _ => false) := by
            apply theorem1Dynamic_countP_mono
            intro word hword hbad
            obtain
                ⟨p, phase, pad,
                  hp, hphaseMem,
                  hfactor, hphaseBad⟩ :=
              hcover word hword hbad
            have hlen :=
              theorem1Dynamic_factor_length
                hword hphaseMem hfactor
            have hpLen :
                p.length = 0 := by
              omega
            have hpNil :
                p = [] :=
              List.eq_nil_of_length_eq_zero
                hpLen
            subst p
            rw [hs0] at hp
            simp at hp
          have hle :
              (allSchedules n 0).countP
                  globalBad ≤ 0 := by
            simpa using hcount
          have hz :
              (allSchedules n 0).countP
                  globalBad = 0 := by
            omega
          rw [hz]
          simp
  | succ H ih =>
      intro stop phaseBad globalBad
      intro hfree hphase hcover
      cases hs0 : stop [] with
      | true =>
          exact
            theorem1Dynamic_rootStopped
              stop phaseBad globalBad
              hfree hphase hcover hs0
      | false =>
          have hpoint :
              ∀ pre : DetSchedule n,
                pre ∈ allSchedules n 1 →
                n *
                    ((allSchedules n H).map
                      (fun suf =>
                        pre ++ suf)).countP
                      globalBad ≤
                  c * n ^ H := by
            intro pre hpre
            have hlen :=
              allSchedules_schedule_length
                n 1 pre hpre
            cases pre with
            | nil =>
                simp at hlen
            | cons e rest =>
                cases rest with
                | cons e2 rest2 =>
                    simp only
                      [List.length_cons,
                        List.length_nil] at hlen
                    omega
                | nil =>
                    have hfree' :
                        ∀ p q : DetSchedule n,
                          stop (e :: p) = true →
                          stop (e :: q) = true →
                          List.IsPrefix p q →
                          p = q := by
                      intro p q hp hq hpref
                      have hcons :
                          List.IsPrefix
                            (e :: p) (e :: q) := by
                        rcases hpref with
                          ⟨tail, htail⟩
                        refine ⟨tail, ?_⟩
                        simpa using
                          congrArg
                            (fun s => e :: s)
                            htail
                      have heq :=
                        hfree
                          (e :: p) (e :: q)
                          hp hq hcons
                      simpa using heq


                    have hphase' :
                        ∀ p : DetSchedule n,
                          stop (e :: p) = true →
                          p.length + T ≤ H →
                          n *
                              (allSchedules n T).countP
                                (phaseBad
                                  (e :: p)) ≤
                            c * n ^ T := by
                      intro p hp hPT
                      apply hphase (e :: p) hp
                      simp only [List.length_cons]
                      omega


                    have hih :=
                      ih
                        (fun p =>
                          stop (e :: p))
                        (fun p phase =>
                          phaseBad
                            (e :: p) phase)
                        (fun word =>
                          globalBad
                            (e :: word))
                        hfree'
                        hphase'
                        (by
                          intro word hword hbad
                          have hwordLen :=
                            allSchedules_schedule_length
                              n H word hword
                          have hfullMem :
                              e :: word ∈
                                allSchedules n
                                  (H + 1) :=
                            mem_allSchedules_of_length
                              n (H + 1)
                              (e :: word)
                              (by
                                simp [hwordLen])
                          obtain
                              ⟨p0, phase, pad,
                                hp0, hphaseMem,
                                hfactor,
                                hphaseBad⟩ :=
                            hcover
                              (e :: word)
                              hfullMem hbad
                          cases p0 with
                          | nil =>
                              rw [hs0] at hp0
                              simp at hp0
                          | cons a p =>
                              have hparts :
                                  e = a ∧
                                    word =
                                      p ++ phase ++ pad := by
                                simpa [List.append_assoc]
                                  using hfactor
                              rcases hparts with
                                ⟨hea, htail⟩
                              subst a
                              exact
                                ⟨p, phase, pad,
                                  hp0, hphaseMem,
                                  htail, hphaseBad⟩)


                    rw [List.countP_map]
                    simpa [Function.comp_def]
                      using hih


          have hsum :=
            Theorem1General.theorem1_mul_sum_le_length_mul
              (allSchedules n 1)
              (fun pre =>
                ((allSchedules n H).map
                  (fun suf =>
                    pre ++ suf)).countP
                    globalBad)
              n (c * n ^ H)
              hpoint


          calc
            n *
                (allSchedules n (H + 1)).countP
                  globalBad =
              n *
                (((allSchedules n 1).map
                  (fun pre =>
                    ((allSchedules n H).map
                      (fun suf =>
                        pre ++ suf)).countP
                        globalBad)).sum) := by
              rw [show H + 1 = 1 + H by omega,
                theorem1_allSchedules_add,
                List.countP_flatMap]
              rfl
            _ ≤
              (allSchedules n 1).length *
                (c * n ^ H) :=
              hsum
            _ = n * (c * n ^ H) := by
              rw [allSchedules_length]
              simp
            _ = c * n ^ (H + 1) := by
              rw [Nat.pow_succ]
              ac_rfl


theorem theorem1DynamicCutPadding_proved :
    Theorem1DynamicCutPadding :=
  theorem1DynamicCutPadding_aux


end PPL


#print axioms PPL.theorem1DynamicCutPadding_proved
