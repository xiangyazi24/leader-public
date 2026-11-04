import Leader.PPL.MainTheorem.DynamicCutPadding
import Leader.Wu.Elimination.SafeEliminationWordCost
import Init.Omega

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/Superseded/Theorem1LogWindow/Theorem1L17Dynamic.lean`, namespace `PPL.Superseded.LogWindow`: `theorem1L17FirstHitStop_cover`, `theorem1L17FirstHitCutAdapter_proved`, `theorem1L17DynamicPaddedBound_proved`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-! ## Small public schedule/list bridges -/

theorem theorem1L17RunPPL_append
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (a b : DetSchedule n) :
    PPL.Probability.runPPL ring C (a ++ b) =
      PPL.Probability.runPPL ring
        (PPL.Probability.runPPL ring C a) b := by
  unfold PPL.Probability.runPPL
  induction a generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append,
        PPL.Probability.runPopulationSchedule]
      exact
        ih
          (C :=
            PopulationProtocol.step
              (PPL.protocol psi kappa) ring C e)

theorem theorem1L17Take_append_take_drop
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

theorem theorem1L17Drop_append_of_le_length
    {A : Type}
    (p r : List A) (k : Nat)
    (hk : k ≤ p.length) :
    (p ++ r).drop k = p.drop k ++ r := by
  induction k generalizing p with
  | zero =>
      rfl
  | succ k ih =>
      cases p with
      | nil =>
          simp at hk
      | cons a p =>
          simp only [List.length_cons,
            Nat.succ_le_succ_iff] at hk
          simpa using ih (p := p) hk

/-! ## Public first-hit facts -/

theorem theorem1FirstHitCut_le_length
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    {t : Nat}
    (h :
      theorem1FirstHitCut ring good C word =
        some t) :
    t ≤ word.length := by
  induction word generalizing C t with
  | nil =>
      cases hg : good C with
      | false =>
          simp [theorem1FirstHitCut, hg] at h
      | true =>
          have h' :
              (some 0 : Option Nat) = some t := by
            simpa [theorem1FirstHitCut, hg] using h
          have ht : 0 = t :=
            Option.some.inj h'
          omega
  | cons e rest ih =>
      cases hg : good C with
      | true =>
          have h' :
              (some 0 : Option Nat) = some t := by
            simpa [theorem1FirstHitCut, hg] using h
          have ht : 0 = t :=
            Option.some.inj h'
          omega
      | false =>
          rw [theorem1FirstHitCut, hg] at h
          cases hr :
              theorem1FirstHitCut
                ring good
                (PPL.Probability.pplStep ring C e)
                rest with
          | none =>
              simp [hr] at h
          | some u =>
              rw [hr] at h
              have hut : u + 1 = t :=
                Option.some.inj h
              have hu :=
                ih
                  (C :=
                    PPL.Probability.pplStep
                      ring C e)
                  (t := u)
                  hr
              simp only [List.length_cons]
              omega

theorem theorem1FirstHitCut_some_endpoint
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    {t : Nat}
    (h :
      theorem1FirstHitCut ring good C word =
        some t) :
    good
        (PPL.Probability.runPPL
          ring C (word.take t)) =
      true := by
  induction word generalizing C t with
  | nil =>
      cases hg : good C with
      | false =>
          simp [theorem1FirstHitCut, hg] at h
      | true =>
          have h' :
              (some 0 : Option Nat) = some t := by
            simpa [theorem1FirstHitCut, hg] using h
          have ht : 0 = t :=
            Option.some.inj h'
          subst t
          simpa [PPL.Probability.runPPL,
            PPL.Probability.runPopulationSchedule]
            using hg
  | cons e rest ih =>
      cases hg : good C with
      | true =>
          have h' :
              (some 0 : Option Nat) = some t := by
            simpa [theorem1FirstHitCut, hg] using h
          have ht : 0 = t :=
            Option.some.inj h'
          subst t
          simpa [PPL.Probability.runPPL,
            PPL.Probability.runPopulationSchedule]
            using hg
      | false =>
          rw [theorem1FirstHitCut, hg] at h
          cases hr :
              theorem1FirstHitCut
                ring good
                (PPL.Probability.pplStep ring C e)
                rest with
          | none =>
              simp [hr] at h
          | some u =>
              rw [hr] at h
              have hut : u + 1 = t :=
                Option.some.inj h
              subst t
              have hu :=
                ih
                  (C :=
                    PPL.Probability.pplStep
                      ring C e)
                  (t := u)
                  hr
              simpa [PPL.Probability.runPPL,
                PPL.Probability.runPopulationSchedule,
                PPL.Probability.pplStep]
                using hu

theorem theorem1FirstHitCut_before_false
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    {t : Nat}
    (h :
      theorem1FirstHitCut ring good C word =
        some t) :
    ∀ s, s < t →
      good
          (PPL.Probability.runPPL
            ring C (word.take s)) =
        false := by
  induction word generalizing C t with
  | nil =>
      intro s hs
      have ht :=
        theorem1FirstHitCut_le_length
          ring good C [] h
      simp at ht
      omega
  | cons e rest ih =>
      cases hg : good C with
      | true =>
          have h' :
              (some 0 : Option Nat) = some t := by
            simpa [theorem1FirstHitCut, hg] using h
          have ht : 0 = t :=
            Option.some.inj h'
          intro s hs
          omega
      | false =>
          rw [theorem1FirstHitCut, hg] at h
          cases hr :
              theorem1FirstHitCut
                ring good
                (PPL.Probability.pplStep ring C e)
                rest with
          | none =>
              simp [hr] at h
          | some u =>
              rw [hr] at h
              have hut : u + 1 = t :=
                Option.some.inj h
              intro s hs
              cases s with
              | zero =>
                  simpa [PPL.Probability.runPPL,
                    PPL.Probability.runPopulationSchedule]
                    using hg
              | succ s =>
                  have hs' : s < u := by
                    omega
                  have hu :=
                    ih
                      (C :=
                        PPL.Probability.pplStep
                          ring C e)
                      (t := u)
                      hr s hs'
                  simpa [PPL.Probability.runPPL,
                    PPL.Probability.runPopulationSchedule,
                    PPL.Probability.pplStep]
                    using hu

theorem theorem1FirstHitCut_take
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    {t : Nat}
    (h :
      theorem1FirstHitCut ring good C word =
        some t) :
    theorem1FirstHitCut
        ring good C (word.take t) =
      some t := by
  induction word generalizing C t with
  | nil =>
      have ht :=
        theorem1FirstHitCut_le_length
          ring good C [] h
      have hzero : t = 0 := by
        simp at ht
        omega
      subst t
      simpa using h
  | cons e rest ih =>
      cases hg : good C with
      | true =>
          have h' :
              (some 0 : Option Nat) = some t := by
            simpa [theorem1FirstHitCut, hg] using h
          have ht : 0 = t :=
            Option.some.inj h'
          subst t
          simp [theorem1FirstHitCut, hg]
      | false =>
          rw [theorem1FirstHitCut, hg] at h
          cases hr :
              theorem1FirstHitCut
                ring good
                (PPL.Probability.pplStep ring C e)
                rest with
          | none =>
              simp [hr] at h
          | some u =>
              rw [hr] at h
              have hut : u + 1 = t :=
                Option.some.inj h
              subst t
              have hu :=
                ih
                  (C :=
                    PPL.Probability.pplStep
                      ring C e)
                  (t := u)
                  hr
              simpa [theorem1FirstHitCut, hg, hu]

theorem theorem1FirstHitCut_terminal_prefixFree
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (p q : DetSchedule n)
    (hp :
      theorem1FirstHitCut ring good C p =
        some p.length)
    (hq :
      theorem1FirstHitCut ring good C q =
        some q.length)
    (hpq : List.IsPrefix p q) :
    p = q := by
  rcases hpq with ⟨r, rfl⟩
  by_cases hr : r = []
  · simp [hr]
  · have hrlen : 0 < r.length := by
      have hne : r.length ≠ 0 := by
        intro hz
        apply hr
        exact List.eq_nil_of_length_eq_zero hz
      omega
    have hlt :
        p.length < (p ++ r).length := by
      simp only [List.length_append]
      omega
    have hgood :=
      theorem1FirstHitCut_some_endpoint
        ring good C p hp
    have hbad :=
      theorem1FirstHitCut_before_false
        ring good C (p ++ r) hq
        p.length hlt
    rw [List.take_append_of_le_length
      (Nat.le_refl p.length)] at hbad
    rw [hgood] at hbad
    cases hbad

/-! ## countP is exactly the L17 raw failure numerator -/

theorem theorem1L17Nodup_ofFn_of_injective
    {q : Nat} {A : Type}
    (f : Fin q → A)
    (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

theorem theorem1L17Nodup_flatMap_of_nodup
    {A B : Type}
    (xs : List A)
    (f : A → List B)
    (hxs : xs.Nodup)
    (hfn :
      ∀ x, x ∈ xs → (f x).Nodup)
    (hdisjoint :
      ∀ x, x ∈ xs →
      ∀ y, y ∈ xs →
        x ≠ y →
        ∀ a, a ∈ f x →
        ∀ b, b ∈ f y →
          a ≠ b) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      refine ⟨hfn x (by simp), ?_, ?_⟩
      · apply ih hxs.2
        · intro y hy
          exact hfn y (by simp [hy])
        · intro y hy z hz hyz
          exact
            hdisjoint
              y (by simp [hy])
              z (by simp [hz])
              hyz
      · intro a ha b hb
        rw [List.mem_flatMap] at hb
        obtain ⟨y, hy, hby⟩ := hb
        apply
          hdisjoint
            x (by simp)
            y (by simp [hy])
        · intro hxy
          exact hxs.1 (hxy ▸ hy)
        · exact ha
        · exact hby

theorem theorem1L17AllSchedules_nodup
    (n T : Nat) :
    (allSchedules n T).Nodup := by
  induction T with
  | zero =>
      simp [allSchedules]
  | succ T ih =>
      rw [allSchedules]
      apply
        theorem1L17Nodup_flatMap_of_nodup
          _ _ ih
      · intro pre hpre
        apply theorem1L17Nodup_ofFn_of_injective
        intro e f hef
        exact
          List.singleton_inj.mp
            (List.append_cancel_left hef)
      · intro pre hpre other hother hne
        intro a ha b hb hab
        rw [List.mem_ofFn] at ha hb
        obtain ⟨e, rfl⟩ := ha
        obtain ⟨f, rfl⟩ := hb
        apply hne
        apply List.append_inj_left hab
        rw [allSchedules_schedule_length
              n T pre hpre,
            allSchedules_schedule_length
              n T other hother]

theorem theorem1L17Nodup_map_of_injective
    {A B : Type}
    (f : A → B)
    (xs : List A)
    (hf : Function.Injective f)
    (hxs : xs.Nodup) :
    (xs.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne,
    List.pairwise_map]
  apply
    (List.nodup_iff_pairwise_ne.mp hxs).imp
  intro a b hab hEq
  exact hab (hf hEq)

theorem theorem1L17AllSchedules_reverse_perm
    (n T : Nat) :
    ((allSchedules n T).map
      (fun word : DetSchedule n =>
        word.reverse)).Perm
      (allSchedules n T) := by
  classical
  have hbase :=
    theorem1L17AllSchedules_nodup n T
  have hrevInj :
      Function.Injective
        (fun word : DetSchedule n =>
          word.reverse) := by
    intro a b hab
    have h :=
      congrArg
        (fun word : DetSchedule n =>
          word.reverse)
        hab
    simpa using h
  have hrevNodup :=
    theorem1L17Nodup_map_of_injective
      (fun word : DetSchedule n =>
        word.reverse)
      (allSchedules n T)
      hrevInj hbase
  apply
    (List.perm_ext_iff_of_nodup
      hrevNodup hbase).2
  intro word
  constructor
  · intro h
    rw [List.mem_map] at h
    obtain ⟨u, hu, rfl⟩ := h
    apply
      mem_allSchedules_of_length
        n T u.reverse
    simpa using
      allSchedules_schedule_length
        n T u hu
  · intro h
    have hr :
        word.reverse ∈ allSchedules n T := by
      apply
        mem_allSchedules_of_length
          n T word.reverse
      rw [List.length_reverse]
      exact
        allSchedules_schedule_length
          n T word h
    rw [List.mem_map]
    exact
      ⟨word.reverse, hr, by simp⟩

theorem theorem1L17ListSum_eq_of_perm
    {xs ys : List Nat}
    (hperm : xs.Perm ys) :
    xs.sum = ys.sum := by
  induction hperm with
  | nil =>
      rfl
  | cons _ _ ih =>
      simp [ih]
  | swap =>
      simpa [List.sum_cons]
        using Nat.add_left_comm ..
  | trans _ _ ih1 ih2 =>
      exact ih1.trans ih2

theorem theorem1L17CountP_eq_sum_indicator
    {A : Type}
    (xs : List A)
    (p : A → Bool) :
    xs.countP p =
      (xs.map
        (fun x =>
          if p x then 1 else 0)).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons,
        List.sum_cons,
        List.countP_cons]
      cases hp : p x <;>
        simp [hp, ih] <;>
        omega

theorem theorem1L17CountP_eq_fixedWordSum
    {n T : Nat}
    (p : DetSchedule n → Bool) :
    (allSchedules n T).countP p =
      FixedSpanRenewalPayload.wordSum
        n T
        (fun word =>
          if p word then 1 else 0) := by
  rw [theorem1L17CountP_eq_sum_indicator]
  unfold FixedSpanRenewalPayload.wordSum
  have hperm :=
    (theorem1L17AllSchedules_reverse_perm
      n T).map
      (fun word : DetSchedule n =>
        if p word then 1 else 0)
  have hsum :=
    theorem1L17ListSum_eq_of_perm hperm
  simpa only [List.map_map,
    Function.comp_def]
    using hsum.symm

theorem theorem1L17LiteralRun_eq_protocolERun
    {n : Nat}
    (ring : DirectedRing n)
    (C : PPL.LiteralElimConfig n)
    (word : DetSchedule n) :
    LDSinkBoundedKernel.run
        (PPL.literalElim ring) C word =
      PPL.Probability.runPopulationSchedule
        PPL.Elim.protocolE ring C word := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [LDSinkBoundedKernel.run,
        PPL.Probability.runPopulationSchedule]
      simpa [PPL.literalElim,
        PPL.Convergence.LDLocal.stepE]
        using
          ih
            (C :=
              PopulationProtocol.step
                PPL.Elim.protocolE ring C e)

theorem theorem1L17CountP_eq_failureWordSum
    {n T : Nat}
    (ring : DirectedRing n)
    (C : PPL.LiteralElimConfig n) :
    (allSchedules n T).countP
        (fun phase =>
          !(@decide
            (PPL.LiteralL1
              (PPL.Probability.runPopulationSchedule
                PPL.Elim.protocolE ring
                C phase))
            (theorem1LiteralL1Decidable _))) =
      LeaderCountDyadicTail.wordSum
        (PPL.literalElim ring)
        (K2ArbitraryElimination.FiniteAccounting.miss
          PPL.LiteralL1)
        C T := by
  classical
  rw [theorem1L17CountP_eq_fixedWordSum]
  rw [←
    K2FiniteSafeEliminationExpected.wordSum_run]
  apply
    congrArg
      (fun f : DetSchedule n → Nat =>
        FixedSpanRenewalPayload.wordSum
          n T f)
  funext phase
  rw [theorem1L17LiteralRun_eq_protocolERun]
  unfold
    K2ArbitraryElimination.FiniteAccounting.miss
  by_cases h :
      PPL.LiteralL1
        (PPL.Probability.runPopulationSchedule
          PPL.Elim.protocolE ring
          C phase)
  · simp [h]
  · simp [h]

theorem theorem1L17PhaseBad_count_eq_failureCount
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p : DetSchedule n) :
    (allSchedules n
        (theorem1H17 n)).countP
        (theorem1L17PhaseBad
          ring C0 p) =
      PPL.Convergence.L17.l17FailureCount
        theorem1C17 ring
        (PPL.Elim.viewConfig
          (PPL.Probability.runPPL
            ring C0 p)) := by
  have hfun :
      theorem1L17PhaseBad ring C0 p =
        fun phase => theorem1L17PhaseBad ring C0 p phase := rfl
  rw [hfun]
  simpa [theorem1L17PhaseBad,
    theorem1H17,
    PPL.Convergence.L17.l17FailureCount]
    using
      theorem1L17CountP_eq_failureWordSum
        (T := theorem1H17 n)
        ring
        (PPL.Elim.viewConfig
          (PPL.Probability.runPPL
            ring C0 p))

/-! ## First-hit stopping family for dynamic L17 -/

def theorem1L17FirstHitStop
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p : DetSchedule n) : Bool :=
  decide
    (theorem1H16 n psi ≤ p.length ∧
      PPL.CPB ring
        (PPL.Probability.runPPL
          ring C0
          (p.take
            (theorem1H16 n psi))) ∧
      theorem1FirstHitCut
          ring
          PPL.Modes.Lemma5.midPhysicalB
          (PPL.Probability.runPPL
            ring C0
            (p.take
              (theorem1H16 n psi)))
          (p.drop
            (theorem1H16 n psi)) =
        some
          (p.drop
            (theorem1H16 n psi)).length)

theorem theorem1L17FirstHitStop_prefixFree
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    ∀ p q : DetSchedule n,
      theorem1L17FirstHitStop
          ring C0 p = true →
      theorem1L17FirstHitStop
          ring C0 q = true →
      List.IsPrefix p q →
      p = q := by
  intro p q hp hq hpq
  unfold theorem1L17FirstHitStop at hp hq
  have hp' :=
    of_decide_eq_true hp
  have hq' :=
    of_decide_eq_true hq
  rcases hp' with
    ⟨hpLen, hpCPB, hpHit⟩
  rcases hq' with
    ⟨hqLen, hqCPB, hqHit⟩
  rcases hpq with ⟨r, rfl⟩
  have htake :
      (p ++ r).take
          (theorem1H16 n psi) =
        p.take
          (theorem1H16 n psi) := by
    rw [List.take_append_of_le_length hpLen]
  have hdrop :
      (p ++ r).drop
          (theorem1H16 n psi) =
        p.drop
            (theorem1H16 n psi) ++
          r :=
    theorem1L17Drop_append_of_le_length
      p r (theorem1H16 n psi) hpLen
  rw [htake, hdrop] at hqHit
  have hsEq :=
    theorem1FirstHitCut_terminal_prefixFree
      ring
      PPL.Modes.Lemma5.midPhysicalB
      (PPL.Probability.runPPL
        ring C0
        (p.take
          (theorem1H16 n psi)))
      (p.drop
        (theorem1H16 n psi))
      (p.drop
          (theorem1H16 n psi) ++
        r)
      hpHit hqHit
      (by
        exact ⟨r, rfl⟩)
  have hlen :=
    congrArg List.length hsEq
  simp only [List.length_append] at hlen
  have hrzero : r.length = 0 := by
    omega
  have hrnil : r = [] :=
    List.eq_nil_of_length_eq_zero hrzero
  simp [hrnil]

theorem theorem1L17FirstHitStop_local
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p : DetSchedule n)
    (hp :
      theorem1L17FirstHitStop
        ring C0 p = true) :
    PPL.Elim.PB ring
        (PPL.Elim.viewConfig
          (PPL.Probability.runPPL
            ring C0 p)) ∧
      (allSchedules n
          (theorem1H17 n)).countP
          (theorem1L17PhaseBad
            ring C0 p) ≤
        PPL.Convergence.L17.l17FailureCount
          theorem1C17 ring
          (PPL.Elim.viewConfig
            (PPL.Probability.runPPL
              ring C0 p)) := by
  unfold theorem1L17FirstHitStop at hp
  have hp' :=
    of_decide_eq_true hp
  rcases hp' with
    ⟨hpLen, hpCPB, hpHit⟩
  have hclosed :=
    PPL.Convergence.ReachCPB.cpb_run_closed
      hn3 hpsi ring
      (PPL.Probability.runPPL
        ring C0
        (p.take
          (theorem1H16 n psi)))
      (p.drop
        (theorem1H16 n psi))
      hpCPB
  have hrun :
      PPL.Probability.runPPL ring C0 p =
        PPL.Probability.runPPL
          ring
          (PPL.Probability.runPPL
            ring C0
            (p.take
              (theorem1H16 n psi)))
          (p.drop
            (theorem1H16 n psi)) := by
    have happ :=
      theorem1L17RunPPL_append
        ring C0
        (p.take
          (theorem1H16 n psi))
        (p.drop
          (theorem1H16 n psi))
    rw [List.take_append_drop] at happ
    exact happ
  have hCPBend :
      PPL.CPB ring
        (PPL.Probability.runPPL
          ring C0 p) := by
    rw [hrun]
    exact hclosed
  have hPB :
      PPL.Elim.PB ring
        (PPL.Elim.viewConfig
          (PPL.Probability.runPPL
            ring C0 p)) :=
    (PPL.Convergence.LiteralEliminationBridges.cpbViewBridge
        ring
        (PPL.Probability.runPPL
          ring C0 p)).1
      hCPBend
  refine ⟨hPB, ?_⟩
  exact
    Nat.le_of_eq
      (theorem1L17PhaseBad_count_eq_failureCount
        ring C0 p)

end PPL
