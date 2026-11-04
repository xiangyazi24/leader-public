import Leader.PPL.Probability.MarkedWordTransfer

namespace PPL.Probability

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

private theorem leftNeighbor_ne_self_early
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 ≤ n)
    (x : Fin n) :
    ring.leftNeighbor x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  change (x.val + n - 1) % n = x.val at hv
  rcases Nat.eq_zero_or_pos x.val with h0 | hpos
  · have h1 :
        (x.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h0] at hv
    omega
  · have h1 :
        (x.val + n - 1) % n = x.val - 1 := by
      rw [show x.val + n - 1 =
          (x.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1] at hv
    omega

private theorem take_append_singleton_of_le_early
    {A : Type}
    (E : Nat)
    (xs : List A)
    (a : A)
    (hE : E ≤ xs.length) :
    (xs ++ [a]).take E = xs.take E := by
  rw [List.take_append]
  have hz : E - xs.length = 0 :=
    Nat.sub_eq_zero_of_le hE
  rw [hz]
  simp

private theorem completionPotential_append_of_full_early
    (E : Nat)
    (P : List Bool → Bool)
    (bits : List Bool)
    (b : Bool)
    (hE : E ≤ bits.length) :
    completionPotential E P (bits ++ [b]) =
      completionPotential E P bits := by
  unfold completionPotential
  rw [take_append_singleton_of_le_early
    E bits b hE]

private theorem completionPotential_split_early
    (E : Nat)
    (P : List Bool → Bool)
    (bits : List Bool)
    (hshort : bits.length < E) :
    completionPotential E P (bits ++ [true]) +
        completionPotential E P (bits ++ [false]) =
      2 * completionPotential E P bits := by
  have htake :
      bits.take E = bits :=
    List.take_of_length_le (Nat.le_of_lt hshort)
  have htakeH :
      (bits ++ [true]).take E =
        bits ++ [true] :=
    List.take_of_length_le (by simp; omega)
  have htakeT :
      (bits ++ [false]).take E =
        bits ++ [false] :=
    List.take_of_length_le (by simp; omega)
  have hr :
      E - bits.length =
        (E - (bits.length + 1)) + 1 := by
    omega
  have hrec :
      binaryCompletionCount P bits
          (E - bits.length) =
        binaryCompletionCount P
            (bits ++ [false])
            (E - (bits.length + 1)) +
          binaryCompletionCount P
            (bits ++ [true])
            (E - (bits.length + 1)) := by
    rw [hr]
    exact
      binaryCompletionCount_succ
        P bits (E - (bits.length + 1))
  unfold completionPotential
  rw [htake, htakeH, htakeT]
  simp only
    [List.length_append, List.length_singleton]
  rw [show
      E - (bits.length + 1) =
        E - (bits.length + 1) by rfl]
  rw [hrec, Nat.pow_succ]
  simp [Nat.add_mul, Nat.mul_add,
    Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm]
  ac_rfl

private theorem completionPotential_eq_twoPow_of_full_early
    (E : Nat)
    (P : List Bool → Bool)
    (bits : List Bool)
    (hE : E ≤ bits.length)
    (hp : P (bits.take E) = true) :
    completionPotential E P bits = 2 ^ E := by
  have hlen :
      (bits.take E).length = E := by
    rw [List.length_take]
    omega
  dsimp only [completionPotential]
  rw [hlen]
  simp [binaryCompletionCount,
    allHTWords, hp]

private theorem stoppedMarkedPotential_child_sum_ge2
    {n : Nat}
    (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (E : Nat)
    (P : List Bool → Bool)
    (s : MarkedWordState n) :
    (List.ofFn (fun e : Fin n =>
      markedStatePotential E P
        (stoppedMarkedStep ring host stop s e))).sum =
      n * markedStatePotential E P s := by
  by_cases hs : s.stopped
  · calc
      (List.ofFn (fun e : Fin n =>
        markedStatePotential E P
          (stoppedMarkedStep
            ring host stop s e))).sum =
          (List.ofFn (fun _ : Fin n =>
            markedStatePotential E P s)).sum := by
        apply ofFn_sum_eq
        intro e
        simp [stoppedMarkedStep, hs,
          markedStatePotential]
      _ = n * markedStatePotential E P s :=
        ofFn_sum_const n _
  · by_cases hp : stop s.pre
    · calc
        (List.ofFn (fun e : Fin n =>
          markedStatePotential E P
            (stoppedMarkedStep
              ring host stop s e))).sum =
            (List.ofFn (fun _ : Fin n =>
              markedStatePotential E P s)).sum := by
          apply ofFn_sum_eq
          intro e
          simp [stoppedMarkedStep, hs, hp,
            markedStatePotential]
        _ = n * markedStatePotential E P s :=
          ofFn_sum_const n _
    · by_cases hfull : E ≤ s.bits.length
      · have hpoint :
            ∀ e : Fin n,
              markedStatePotential E P
                  (stoppedMarkedStep
                    ring host stop s e) =
                markedStatePotential E P s := by
          intro e
          cases hm :
              incidentBit ring
                (host s.pre) e with
          | none =>
              simp [stoppedMarkedStep, hs, hp,
                hm, markedStatePotential]
          | some b =>
              simp [stoppedMarkedStep, hs, hp,
                hm, markedStatePotential,
                completionPotential_append_of_full_early
                  E P s.bits b hfull]
        calc
          (List.ofFn (fun e : Fin n =>
            markedStatePotential E P
              (stoppedMarkedStep
                ring host stop s e))).sum =
              (List.ofFn (fun _ : Fin n =>
                markedStatePotential E P s)).sum := by
            apply ofFn_sum_eq
            exact hpoint
          _ = n * markedStatePotential E P s :=
            ofFn_sum_const n _
      · have hshort :
            s.bits.length < E := by
          omega
        let a :=
          ring.leftNeighbor (host s.pre)
        let b := host s.pre
        let f : Fin n → Nat :=
          fun e =>
            markedStatePotential E P
              (stoppedMarkedStep
                ring host stop s e)
        let c : Nat :=
          markedStatePotential E P s
        have hab : a ≠ b := by
          dsimp [a, b]
          exact
            leftNeighbor_ne_self_early
              ring hn2 (host s.pre)
        have hba : b ≠ a := Ne.symm hab
        have ha :
            f a =
              completionPotential E P
                (s.bits ++ [true]) := by
          have hm :
              incidentBit ring
                  (host s.pre) a =
                some true := by
            simp [a, incidentBit]
          simp [f, stoppedMarkedStep, hs,
            hp, hm, markedStatePotential]
        have hb :
            f b =
              completionPotential E P
                (s.bits ++ [false]) := by
          have hm :
              incidentBit ring
                  (host s.pre) b =
                some false := by
            simp [a, b, incidentBit, hba]
          simp [f, stoppedMarkedStep, hs,
            hp, hm, markedStatePotential]
        have hother :
            ∀ e, e ≠ a → e ≠ b →
              f e = c := by
          intro e hea heb
          have hm :
              incidentBit ring
                  (host s.pre) e = none := by
            simp [a, b, incidentBit,
              hea, heb]
          simp [f, c, stoppedMarkedStep,
            hs, hp, hm, markedStatePotential]
        have hpair :
            f a + f b = 2 * c := by
          rw [ha, hb]
          exact
            completionPotential_split_early
              E P s.bits hshort
        have hsum :=
          PredictableTwoTargetFiniteTree.ofFn_sum_two_values_else_const
              a b f c hab hother
        calc
          (List.ofFn (fun e : Fin n =>
            markedStatePotential E P
              (stoppedMarkedStep
                ring host stop s e))).sum =
              f a + f b + (n - 2) * c := by
            simpa [f] using hsum
          _ = 2 * c + (n - 2) * c := by
            rw [hpair]
          _ = n * c := by
            rw [← Nat.add_mul]
            congr 1
            omega
          _ = n * markedStatePotential E P s :=
            rfl

private theorem sum_map_flatMap_early
    {A B : Type}
    (xs : List A)
    (ys : A → List B)
    (f : B → Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map
        (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih]

private theorem sum_map_mul_left_early
    {A : Type}
    (xs : List A)
    (c : Nat)
    (f : A → Nat) :
    (xs.map (fun x => c * f x)).sum =
      c * (xs.map f).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.mul_add]

private theorem stoppedMarkedPotential_exact_ge2
    {n : Nat}
    (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (E T : Nat)
    (P : List Bool → Bool) :
    stoppedMarkedPotentialSum
        ring host stop E T P =
      n ^ T * (allHTWords E).countP P := by
  induction T with
  | zero =>
      simp [stoppedMarkedPotentialSum,
        allSchedules, stoppedMarkedRun,
        stoppedMarkedStart,
        markedStatePotential,
        completionPotential,
        binaryCompletionCount]
  | succ T ih =>
      unfold stoppedMarkedPotentialSum at ih ⊢
      rw [allSchedules,
        sum_map_flatMap_early]
      have hinner :
          ∀ pre : DetSchedule n,
            ((List.ofFn
              (fun e : Fin n =>
                pre ++ [e])).map
              (fun word =>
                markedStatePotential E P
                  (stoppedMarkedRun
                    ring host stop
                    (stoppedMarkedStart n)
                    word))).sum =
              n * markedStatePotential E P
                (stoppedMarkedRun
                  ring host stop
                  (stoppedMarkedStart n)
                  pre) := by
        intro pre
        rw [List.map_ofFn]
        calc
          (List.ofFn
            (fun e : Fin n =>
              markedStatePotential E P
                (stoppedMarkedRun
                  ring host stop
                  (stoppedMarkedStart n)
                  (pre ++ [e])))).sum =
              (List.ofFn
                (fun e : Fin n =>
                  markedStatePotential E P
                    (stoppedMarkedStep
                      ring host stop
                      (stoppedMarkedRun
                        ring host stop
                        (stoppedMarkedStart n)
                        pre)
                      e))).sum := by
            apply ofFn_sum_eq
            intro e
            rw [stoppedMarkedRun_append]
            rfl
          _ =
              n * markedStatePotential E P
                (stoppedMarkedRun
                  ring host stop
                  (stoppedMarkedStart n)
                  pre) :=
            stoppedMarkedPotential_child_sum_ge2
              hn2 ring host stop E P _
      calc
        ((allSchedules n T).map
          (fun pre =>
            ((List.ofFn
              (fun e : Fin n =>
                pre ++ [e])).map
              (fun word =>
                markedStatePotential E P
                  (stoppedMarkedRun
                    ring host stop
                    (stoppedMarkedStart n)
                    word))).sum)).sum =
            ((allSchedules n T).map
              (fun pre =>
                n * markedStatePotential E P
                  (stoppedMarkedRun
                    ring host stop
                    (stoppedMarkedStart n)
                    pre))).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro pre _
          exact hinner pre
        _ =
            n * ((allSchedules n T).map
              (fun pre =>
                markedStatePotential E P
                  (stoppedMarkedRun
                    ring host stop
                    (stoppedMarkedStart n)
                    pre))).sum :=
          sum_map_mul_left_early _ n _
        _ =
            n *
              (n ^ T *
                (allHTWords E).countP P) := by
          rw [ih]
        _ =
            n ^ (T + 1) *
              (allHTWords E).countP P := by
          rw [Nat.pow_succ]
          ac_rfl

private theorem countP_mul_le_sum_early
    {A : Type}
    (xs : List A)
    (p : A → Bool)
    (c : Nat)
    (f : A → Nat)
    (h :
      ∀ x, x ∈ xs →
        p x = true → c ≤ f x) :
    xs.countP p * c ≤ (xs.map f).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have ht :=
        ih
          (fun y hy hpy =>
            h y (by simp [hy]) hpy)
      rw [List.countP_cons,
        List.map_cons, List.sum_cons]
      cases hp : p x with
      | false =>
          simp [hp] at *
          omega
      | true =>
          have hx :=
            h x (by simp) hp
          simp [hp, Nat.succ_mul] at *
          omega

private theorem stoppedMarkedWordTransfer_ge2
    {n : Nat}
    (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (T E : Nat)
    (P : List Bool → Bool) :
    stoppedMarkedExactCount
          ring host stop T E P *
        2 ^ E ≤
      n ^ T * (allHTWords E).countP P := by
  have hdom :
      stoppedMarkedExactCount
            ring host stop T E P *
          2 ^ E ≤
        stoppedMarkedPotentialSum
          ring host stop E T P := by
    unfold stoppedMarkedExactCount
      stoppedMarkedPotentialSum
    apply countP_mul_le_sum_early
    intro word _ hgood
    dsimp only at hgood
    have hg :
        (stopReached stop word = false) ∧
          E ≤
            (stoppedEncounterBits
              ring host stop word).length ∧
          P ((stoppedEncounterBits
            ring host stop word).take E) =
            true :=
      of_decide_eq_true hgood
    have hbits :=
      stoppedMarkedRun_start_bits
        ring host stop word
    have hp :=
      completionPotential_eq_twoPow_of_full_early
        E P
        (stoppedEncounterBits
          ring host stop word)
        hg.2.1 hg.2.2
    change
      2 ^ E ≤
        markedStatePotential E P
          (stoppedMarkedRun
            ring host stop
            (stoppedMarkedStart n)
            word)
    unfold markedStatePotential
    rw [hbits, hp]
    exact Nat.le_refl _
  exact
    Nat.le_trans hdom
      (Nat.le_of_eq
        (stoppedMarkedPotential_exact_ge2
          hn2 ring host stop E T P))

theorem stoppedEncounterLotteryAtMost_transfer_ge2
    {n : Nat}
    (hn2 : 2 ≤ n)
    (k h : Nat)
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (T E M : Nat) :
    stoppedLotteryLowerFailureCount
          k h ring host stop T E M *
        2 ^ E ≤
      n ^ T *
        lotteryAtMostWordCount
          k h E M := by
  have ht :=
    stoppedMarkedWordTransfer_ge2
      hn2 ring host stop T E
      (fun bits =>
        decide
          ((lotteryRun k
            (lotteryOffset h) bits).wins ≤ M))
  simpa [stoppedMarkedExactCount,
    stoppedLotteryLowerFailureCount,
    lotteryAtMostWordCount,
    lotteryPredWordCount,
    decide_eq_true_eq] using ht

theorem earlyLeaderStopBounds :
    EarlyLeaderStopBounds := by
  intro n psi kappa T E M h
  intro hn2 hpsi hh
  intro ring C0 host hleader
  let stop := firstLeaderStop ring C0
  have htails :=
    predictableHostTails
      n T E hn2 ring host
  have henc :
      stoppedPredictableHostLowerFailureCount
          ring host stop T E ≤
        twoEdgeLowerTailCount n T E :=
    (htails.2.2 stop).2
  have hlot :
      stoppedLotteryLowerFailureCount
            psi h ring host stop T E M *
          2 ^ E ≤
        n ^ T *
          lotteryAtMostWordCount
            psi h E M :=
    stoppedEncounterLotteryAtMost_transfer_ge2
      hn2 psi h ring host stop T E M
  exact ⟨henc, hlot⟩

#print axioms PPL.Probability.stoppedEncounterLotteryAtMost_transfer_ge2
#print axioms PPL.Probability.earlyLeaderStopBounds

end PPL.Probability
