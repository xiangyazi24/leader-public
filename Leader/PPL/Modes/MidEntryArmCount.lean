import Leader.PPL.Modes.ConstructionModeSplit
import Leader.PPL.Modes.SignalLineageLocal
import Leader.Wu.Scheduler.RepeatedBlocks
import Leader.Core.LeaderCountDyadicTail

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage

/-!
# Lemma 5(i): leader-arm failure count

A currently present leader has one predictable forcing scheduler letter: its
initiator edge.  On that letter DetermineMode line 35 installs the maximum
right-signal TTL, and the already-proved post-DetermineMode signal projection
shows that the full P_PL pair interaction preserves that responder signal.

Thus a word counted by the leader-arm bad event must avoid one predictable
letter at every arm-prefix node.  The exact finite scheduler tree has one hot
child and n-1 cold children at each such node, so there are exactly
(n-1)^A bad arm prefixes, where A = lemma5ArmHorizon n.  The later sweep suffix
is unrestricted and contributes n^S extensions.

The final arithmetic uses the public integer half-life
  2 * (n-1)^n <= n^n
and n <= 2^(K n), with K n = log2 n + 1.  The arm horizon contains at least
n*K n interactions, so the one-edge avoidance decay absorbs the leading
factor n.
-/

/-! ## Small Boolean-fold helpers -/

private theorem foldl_or_true_local
    (xs : List Bool) :
    xs.foldl (fun acc b => acc || b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      simp only [List.foldl_cons, Bool.true_or]
      exact ih

private theorem foldl_or_true_of_mem_local
    (xs : List Bool)
    (hmem : true ∈ xs) :
    xs.foldl (fun acc b => acc || b) false = true := by
  induction xs with
  | nil =>
      simp at hmem
  | cons b xs ih =>
      rcases List.mem_cons.mp hmem with hb | ht
      · subst b
        simp only [List.foldl_cons, Bool.false_or]
        exact foldl_or_true_local xs
      · cases b
        · simp only [List.foldl_cons, Bool.false_or]
          exact ih ht
        · simp only [List.foldl_cons, Bool.false_or]
          exact foldl_or_true_local xs

private theorem true_mem_of_foldl_or_true_local
    (xs : List Bool)
    (h :
      xs.foldl (fun acc b => acc || b) false = true) :
    true ∈ xs := by
  induction xs with
  | nil =>
      simp at h
  | cons b xs ih =>
      cases b with
      | false =>
          have ht :
              xs.foldl (fun acc b => acc || b) false =
                true := by
            simpa only [List.foldl_cons, Bool.false_or] using h
          exact List.mem_cons.mpr (Or.inr (ih ht))
      | true =>
          exact List.mem_cons.mpr (Or.inl rfl)

private theorem leaderPresent_exists_local
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : leaderPresent C = true) :
    Exists (fun i : Fin n => (C i).leader = true) := by
  unfold leaderPresent at h
  have hm :=
    true_mem_of_foldl_or_true_local
      (List.ofFn (fun i : Fin n => (C i).leader)) h
  rw [List.mem_ofFn] at hm
  obtain ⟨i, hi⟩ := hm
  exact ⟨i, hi⟩

/-! ## Literal line-35 forcing edge -/

private theorem rightNeighbor_ne_self_arm
    {n : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

/--
A leader used as the initiator forces a max-TTL reset signal in the literal
one-step successor.  This is the physical one-interaction fact needed by the
counting argument.
-/
theorem lemma5iLeaderArmSingleStep
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hleader : (C e).leader = true) :
    maxResetSignalB
      (pplStep ring C e) = true := by
  have hself :
      ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_arm hn3 ring e

  have hd :=
    determineModeSignalProjection
      (psi := psi) (kappa := kappa)
      hpsi
      (C e)
      (C (ring.rightNeighbor e))

  have hs :=
    step_signal_projection_of_stable
      postDetermineModeSignalStable
      hpsi ring C e hself

  dsimp only at hd hs

  have harmed :
      armedSignalVal (C e) = kappa := by
    simp [armedSignalVal, hleader]

  have hcases := hd.2.2
  unfold DetermineModeResponderCases at hcases
  dsimp only at hcases

  have hdetMax :
      (PPL.determineMode
        (C e)
        (C (ring.rightNeighbor e))).2.signalR.val =
          kappa := by
    rcases hcases with hzero | hrest
    · have hk0 : kappa = 0 := by
        calc
          kappa = armedSignalVal (C e) := harmed.symm
          _ = 0 := hzero.1
      calc
        (PPL.determineMode
          (C e)
          (C (ring.rightNeighbor e))).2.signalR.val =
            0 := hzero.2.2.1
        _ = kappa := hk0.symm
    · rcases hrest with hleft | hright
      · calc
          (PPL.determineMode
            (C e)
            (C (ring.rightNeighbor e))).2.signalR.val =
              armedSignalVal (C e) := hleft.2.2.1
          _ = kappa := harmed
      · have hlt :
            kappa <
              (C (ring.rightNeighbor e)).signalR.val := by
          calc
            kappa = armedSignalVal (C e) := harmed.symm
            _ <
                (C (ring.rightNeighbor e)).signalR.val :=
              hright.1
        have hrlt :=
          (C (ring.rightNeighbor e)).signalR.isLt
        omega

  have hfullMax :
      (pplStep ring C e
        (ring.rightNeighbor e)).signalR.val =
          kappa := by
    calc
      (pplStep ring C e
        (ring.rightNeighbor e)).signalR.val =
          (PPL.determineMode
            (C e)
            (C (ring.rightNeighbor e))).2.signalR.val := by
        simpa [PPL.Probability.pplStep,
          PPL.Modes.SignalLineage.step] using
          congrArg Fin.val hs.2.2.1
      _ = kappa := hdetMax

  unfold maxResetSignalB
  apply foldl_or_true_of_mem_local
  rw [List.mem_ofFn]
  refine ⟨ring.rightNeighbor e, ?_⟩
  simp [hfullMax]

/-! ## Predictable leader selector and one-hot projection -/

private theorem runPPL_reachable_local
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) :
    PopulationProtocol.Reachable
      (PPL.protocol psi kappa) ring C
      (runPPL ring C word) := by
  induction word generalizing C with
  | nil =>
      exact PopulationProtocol.Reachable.refl _
  | cons e rest ih =>
      have hone :
          PopulationProtocol.OneStep
            (PPL.protocol psi kappa) ring C
            (pplStep ring C e) := by
        exact ⟨e, rfl⟩
      have hfirst :=
        PopulationProtocol.OneStep.to_reachable hone
      have htail :=
        ih (C := pplStep ring C e)
      change
        PopulationProtocol.Reachable
          (PPL.protocol psi kappa) ring C
          (runPPL ring (pplStep ring C e) rest)
      exact PopulationProtocol.Reachable.trans hfirst htail

noncomputable def lemma5iLeaderArmHost
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n) : Fin n :=
  dite
    (Exists
      (fun i : Fin n =>
        ((runPPL ring C pre) i).leader = true))
    (fun h => Classical.choose h)
    (fun _ => ⟨0, ring.hn⟩)

private theorem lemma5iLeaderArmHost_is_leader
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hnever : neverLeaderless ring C)
    (pre : DetSchedule n) :
    ((runPPL ring C pre)
      (lemma5iLeaderArmHost ring C pre)).leader =
        true := by
  have hreach :=
    runPPL_reachable_local ring C pre
  have hpresent :=
    hnever (runPPL ring C pre) hreach
  have hex :=
    leaderPresent_exists_local
      (runPPL ring C pre) hpresent
  unfold lemma5iLeaderArmHost
  rw [dif_pos hex]
  exact Classical.choose_spec hex

def lemma5iForcingEdgeHitsAux
    {n : Nat}
    (host : List (Fin n) -> Fin n) :
    List (Fin n) -> List (Fin n) -> Nat
  | _, [] => 0
  | pre, e :: rest =>
      (if e = host pre then 1 else 0) +
        lemma5iForcingEdgeHitsAux host
          (pre ++ [e]) rest

def lemma5iForcingEdgeHits
    {n : Nat}
    (host : List (Fin n) -> Fin n)
    (word : DetSchedule n) : Nat :=
  lemma5iForcingEdgeHitsAux host [] word

def lemma5iForcingEdgeZeroCount
    {n : Nat}
    (host : List (Fin n) -> Fin n)
    (T : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word =>
      decide (lemma5iForcingEdgeHits host word = 0))

noncomputable def lemma5iArmForcingMissB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Bool :=
  decide
    (lemma5iForcingEdgeHits
      (lemma5iLeaderArmHost ring C)
      (lemma5iArmPrefix word) = 0)

/-! ## Prefix semantics: ARM bad implies no forcing letter -/

private theorem runPPL_append_local
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    runPPL ring C (u ++ v) =
      runPPL ring
        (runPPL ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append,
        runPPL, runPopulationSchedule]
      exact
        ih
          (C := pplStep ring C e)

private theorem runPPL_append_singleton_local
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n) :
    runPPL ring C (pre ++ [e]) =
      pplStep ring
        (runPPL ring C pre) e := by
  rw [runPPL_append_local]
  rfl

private theorem reachesAux_current_false_local
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hfail :
      reachesAux ring good C word = false) :
    good C = false := by
  cases word with
  | nil =>
      simpa [reachesAux] using hfail
  | cons e rest =>
      cases hg : good C with
      | false =>
          rfl
      | true =>
          simp [reachesAux, hg] at hfail

private theorem reachesAux_tail_false_local
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (e : Fin n)
    (rest : DetSchedule n)
    (hfail :
      reachesAux ring good C (e :: rest) = false) :
    reachesAux ring good
      (pplStep ring C e) rest = false := by
  have hgood :=
    reachesAux_current_false_local
      ring good C (e :: rest) hfail
  simpa [reachesAux, hgood] using hfail

private theorem forcingHitsAux_zero_of_arm_failure
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hnever : neverLeaderless ring C) :
    forall (pre rest : DetSchedule n),
      reachesAux ring maxResetSignalB
          (runPPL ring C pre) rest = false ->
        lemma5iForcingEdgeHitsAux
          (lemma5iLeaderArmHost ring C)
          pre rest = 0 := by
  intro pre rest
  induction rest generalizing pre with
  | nil =>
      intro _hfail
      rfl
  | cons e rest ih =>
      intro hfail
      have htail :=
        reachesAux_tail_false_local
          ring maxResetSignalB
          (runPPL ring C pre)
          e rest hfail

      have hne :
          e ≠ lemma5iLeaderArmHost ring C pre := by
        intro he
        subst e
        have hleader :=
          lemma5iLeaderArmHost_is_leader
            ring C hnever pre
        have harm :=
          lemma5iLeaderArmSingleStep
            hn3 hpsi ring
            (runPPL ring C pre)
            (lemma5iLeaderArmHost ring C pre)
            hleader
        have hnextFalse :=
          reachesAux_current_false_local
            ring maxResetSignalB
            (pplStep ring
              (runPPL ring C pre)
              (lemma5iLeaderArmHost ring C pre))
            rest htail
        rw [harm] at hnextFalse
        simp at hnextFalse

      have htail' :
          reachesAux ring maxResetSignalB
              (runPPL ring C (pre ++ [e])) rest =
            false := by
        rw [runPPL_append_singleton_local]
        exact htail

      have hih :=
        ih (pre := pre ++ [e]) htail'

      simp [lemma5iForcingEdgeHitsAux, hne, hih]

/--
Wordwise physical reduction requested by the ARM split: if the leader-arm bad
event holds, then throughout the arm prefix the predictable current leader's
initiator edge is never selected.
-/
theorem lemma5iLeaderArmBad_implies_forcingMiss
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hnever : neverLeaderless ring C)
    (word : DetSchedule n) :
    lemma5iLeaderArmBadB ring C word = true ->
      lemma5iArmForcingMissB ring C word = true := by
  intro hbad

  have hfail :
      reachesAux ring maxResetSignalB C
        (lemma5iArmPrefix word) = false := by
    unfold lemma5iLeaderArmBadB at hbad
    cases h :
        reachesAux ring maxResetSignalB C
          (lemma5iArmPrefix word) with
    | false =>
        rfl
    | true =>
        simp [h] at hbad

  have hz :
      lemma5iForcingEdgeHits
          (lemma5iLeaderArmHost ring C)
          (lemma5iArmPrefix word) =
        0 := by
    have haux :=
      forcingHitsAux_zero_of_arm_failure
        hn3 hpsi ring C hnever
        [] (lemma5iArmPrefix word)
        (by
          simpa [runPPL, runPopulationSchedule]
            using hfail)
    simpa [lemma5iForcingEdgeHits] using haux

  unfold lemma5iArmForcingMissB
  simp [hz]

/-! ## Exact one-hot predictable tree count -/

private theorem countP_eq_sum_indicator_local
    {A : Type}
    (xs : List A)
    (p : A -> Bool) :
    xs.countP p =
      (xs.map
        (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.countP_cons,
        List.map_cons, List.sum_cons, ih]
      cases h : p x <;>
        simp [h, Nat.add_comm]

private theorem ofFn_sum_eq_local
    {n : Nat}
    (f g : Fin n -> Nat)
    (hfg : forall i, f i = g i) :
    (List.ofFn f).sum =
      (List.ofFn g).sum := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        hfg 0]
      exact
        congrArg (g 0 + ·)
          (ih
            (fun i => f i.succ)
            (fun i => g i.succ)
            (fun i => hfg i.succ))

private theorem ofFn_sum_const_local
    (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum =
      n * c := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        ih, Nat.succ_mul]
      exact Nat.add_comm _ _

private theorem sum_spike_local
    (n : Nat) :
    forall (a : Fin n) (v : Nat),
      (List.ofFn
        (fun e : Fin n =>
          if e = a then v else 0)).sum =
        v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn
              (fun i : Fin n =>
                if i.succ = (0 : Fin (n + 1))
                then v else 0)).sum = 0 := by
          have hh :=
            ofFn_sum_eq_local
              (fun i : Fin n =>
                if i.succ = (0 : Fin (n + 1))
                then v else 0)
              (fun _ : Fin n => 0)
              (by
                intro i
                have hn :
                    i.succ ≠
                      (0 : Fin (n + 1)) := by
                  intro he
                  have hv := congrArg Fin.val he
                  change i.val + 1 = 0 at hv
                  omega
                rw [if_neg hn])
          simpa only
            [ofFn_sum_const_local, Nat.mul_zero]
            using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn :
            (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh :=
          ofFn_sum_eq_local
            (fun i : Fin n =>
              if i.succ = a.succ
              then v else 0)
            (fun i : Fin n =>
              if i = a then v else 0)
            (by
              intro i
              simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

private theorem countP_not_add_countP_local
    {A : Type}
    (p : A -> Bool)
    (xs : List A) :
    xs.countP (fun x => !p x) +
        xs.countP p =
      xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.countP_cons,
        List.countP_cons,
        List.length_cons]
      cases hp : p x <;>
        simp [hp, Nat.add_assoc,
          Nat.add_comm] at * <;>
        omega

private theorem oneEdgeLetter_count_local
    {n : Nat}
    (a : Fin n) :
    (List.ofFn
      (fun e : Fin n => e)).countP
        (fun e => decide (e = a)) =
      1 := by
  rw [countP_eq_sum_indicator_local,
    List.map_ofFn]
  calc
    (List.ofFn
      (fun e : Fin n =>
        if decide (e = a)
        then 1 else 0)).sum =
        (List.ofFn
          (fun e : Fin n =>
            if e = a
            then 1 else 0)).sum := by
      apply ofFn_sum_eq_local
      intro e
      by_cases h : e = a <;>
        simp [h]
    _ = 1 :=
      sum_spike_local n a 1

private theorem oneEdgeCold_count_local
    {n : Nat}
    (a : Fin n) :
    (List.ofFn
      (fun e : Fin n => e)).countP
        (fun e => !decide (e = a)) =
      n - 1 := by
  have hpart :=
    countP_not_add_countP_local
      (fun e : Fin n => decide (e = a))
      (List.ofFn (fun e : Fin n => e))
  rw [oneEdgeLetter_count_local a] at hpart
  simp only [List.length_ofFn] at hpart
  omega

private theorem forcingHitsAux_append_singleton
    {n : Nat}
    (host : List (Fin n) -> Fin n)
    (pre word : List (Fin n))
    (e : Fin n) :
    lemma5iForcingEdgeHitsAux host pre
        (word ++ [e]) =
      lemma5iForcingEdgeHitsAux host pre word +
        (if e = host (pre ++ word)
          then 1 else 0) := by
  induction word generalizing pre with
  | nil =>
      simp [lemma5iForcingEdgeHitsAux]
  | cons x xs ih =>
      simp only [List.cons_append,
        lemma5iForcingEdgeHitsAux]
      rw [ih (pre := pre ++ [x])]
      have hp :
          (pre ++ [x]) ++ xs =
            pre ++ (x :: xs) := by
        simp [List.append_assoc]
      rw [hp]
      omega

private theorem forcingHits_append_singleton
    {n : Nat}
    (host : List (Fin n) -> Fin n)
    (word : DetSchedule n)
    (e : Fin n) :
    lemma5iForcingEdgeHits host (word ++ [e]) =
      lemma5iForcingEdgeHits host word +
        (if e = host word then 1 else 0) := by
  simpa [lemma5iForcingEdgeHits] using
    forcingHitsAux_append_singleton
      host [] word e

private theorem forcing_extension_zero_count_local
    {n : Nat}
    (host : List (Fin n) -> Fin n)
    (word : DetSchedule n) :
    (List.ofFn
      (fun e : Fin n =>
        word ++ [e])).countP
        (fun u =>
          decide
            (lemma5iForcingEdgeHits
              host u = 0)) =
      (if decide
          (lemma5iForcingEdgeHits
            host word = 0)
       then n - 1 else 0) := by
  have hmap :
      List.ofFn
          (fun e : Fin n =>
            word ++ [e]) =
        (List.ofFn
          (fun e : Fin n => e)).map
            (fun e => word ++ [e]) := by
    rw [List.map_ofFn]
    rfl

  rw [hmap, List.countP_map]
  simp only [Function.comp_def]

  by_cases hz :
      lemma5iForcingEdgeHits
        host word = 0
  · have hp :
        (fun e : Fin n =>
          decide
            (lemma5iForcingEdgeHits
              host (word ++ [e]) = 0)) =
        (fun e : Fin n =>
          !decide (e = host word)) := by
      funext e
      rw [forcingHits_append_singleton]
      by_cases he : e = host word <;>
        simp [he, hz]
    rw [hp, oneEdgeCold_count_local]
    simp [hz]
  · have hp :
        (fun e : Fin n =>
          decide
            (lemma5iForcingEdgeHits
              host (word ++ [e]) = 0)) =
        (fun _ : Fin n => false) := by
      funext e
      rw [forcingHits_append_singleton]
      by_cases he : e = host word <;>
        simp [he, hz]
    rw [hp]
    simp [hz]

private theorem sum_if_count_local
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
        List.countP_cons, ih]
      cases p x <;>
        simp [Nat.add_mul, Nat.add_comm]

private theorem forcingZeroCount_succ_local
    {n T : Nat}
    (host : List (Fin n) -> Fin n) :
    lemma5iForcingEdgeZeroCount
        host (T + 1) =
      (n - 1) *
        lemma5iForcingEdgeZeroCount
          host T := by
  unfold lemma5iForcingEdgeZeroCount
  rw [allSchedules, List.countP_flatMap]

  have hmap :
      (List.map
        (List.countP
          (fun u =>
            decide
              (lemma5iForcingEdgeHits
                host u = 0)) ∘
          (fun word =>
            List.ofFn
              (fun e : Fin n =>
                word ++ [e])))
        (allSchedules n T)) =
      (List.map
        (fun word =>
          if decide
              (lemma5iForcingEdgeHits
                host word = 0)
          then n - 1 else 0)
        (allSchedules n T)) := by
    apply List.map_congr_left
    intro word _hword
    change
      (List.ofFn
        (fun e : Fin n =>
          word ++ [e])).countP
          (fun u =>
            decide
              (lemma5iForcingEdgeHits
                host u = 0)) =
        _
    exact
      forcing_extension_zero_count_local
        host word

  rw [hmap, sum_if_count_local]
  ac_rfl

private theorem lemma5iForcingEdgeZeroCount_eq_closed_local
    {n T : Nat}
    (host : List (Fin n) -> Fin n) :
    lemma5iForcingEdgeZeroCount host T =
      (n - 1) ^ T := by
  induction T with
  | zero =>
      simp [lemma5iForcingEdgeZeroCount,
        allSchedules,
        lemma5iForcingEdgeHits,
        lemma5iForcingEdgeHitsAux]
  | succ T ih =>
      rw [forcingZeroCount_succ_local,
        ih, Nat.pow_succ]
      ac_rfl

/-! ## Lifting the arm-prefix count through the free sweep suffix -/

private theorem countP_take_eq_mul_pow_local
    {n A B : Nat}
    (p : DetSchedule n -> Bool) :
    (allSchedules n (A + B)).countP
        (fun word => p (word.take A)) =
      (allSchedules n A).countP p *
        n ^ B := by
  rw [PPLLSchedulerBlocks.allSchedules_add,
    List.countP_flatMap]

  have hmap :
      (List.map
        (List.countP
          (fun word =>
            p (word.take A)) ∘
          (fun pre =>
            (allSchedules n B).map
              (fun suf => pre ++ suf)))
        (allSchedules n A)) =
      (List.map
        (fun pre =>
          if p pre then n ^ B else 0)
        (allSchedules n A)) := by
    apply List.map_congr_left
    intro pre hpre
    change
      ((allSchedules n B).map
        (fun suf =>
          pre ++ suf)).countP
          (fun word =>
            p (word.take A)) =
        (if p pre then n ^ B else 0)

    rw [List.countP_map]
    simp only [Function.comp_def]

    have hlen :=
      allSchedules_schedule_length
        n A pre hpre

    have hfun :
        (fun suf : DetSchedule n =>
          p ((pre ++ suf).take A)) =
        (fun _ : DetSchedule n =>
          p pre) := by
      funext suf
      have ht :
          (pre ++ suf).take A = pre := by
        rw [← hlen]
        simp
      rw [ht]

    rw [hfun]
    cases hp : p pre <;>
      simp [hp, allSchedules_length]

  rw [hmap, sum_if_count_local]

private theorem countP_mono_local
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
      rw [List.countP_cons,
        List.countP_cons]
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx :
              q x = true :=
            hpq x hp
          simp [hp, hqx]
          omega

/-! ## ARM numerator bound -/

/--
The ARM conjunct of Lemma5iArmResetCount.

The extra paper assumptions on kappa and psi-vs-n are retained in the theorem
interface, although the one-edge arm estimate itself needs only n >= 3 and
psi >= 2.
-/
theorem lemma5iLeaderArmCount
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (_hkappa : 48 * psi <= kappa)
    (_hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hnever : neverLeaderless ring C) :
    n * lemma5iLeaderArmFailureCount
          ring C <=
      2 * n ^ lemma5iHorizon n := by

  have hmono :
      lemma5iLeaderArmFailureCount
          ring C <=
        (allSchedules n
          (lemma5iHorizon n)).countP
            (lemma5iArmForcingMissB
              ring C) := by
    unfold lemma5iLeaderArmFailureCount
    apply countP_mono_local
    intro word hbad
    exact
      lemma5iLeaderArmBad_implies_forcingMiss
        hn3 hpsi ring C hnever
        word hbad

  have hforcingCount :
      (allSchedules n
        (lemma5iHorizon n)).countP
          (lemma5iArmForcingMissB
            ring C) =
        (n - 1) ^ lemma5ArmHorizon n *
          n ^ lemma5SweepHorizon n := by
    unfold lemma5iArmForcingMissB
    unfold lemma5iArmPrefix
    unfold lemma5iHorizon
    rw [countP_take_eq_mul_pow_local
      (A := lemma5ArmHorizon n) (B := lemma5SweepHorizon n)
      (fun w => decide
        (lemma5iForcingEdgeHits
          (lemma5iLeaderArmHost ring C) w = 0))]
    change
      lemma5iForcingEdgeZeroCount
          (lemma5iLeaderArmHost ring C)
          (lemma5ArmHorizon n) *
          n ^ lemma5SweepHorizon n =
        (n - 1) ^ lemma5ArmHorizon n *
          n ^ lemma5SweepHorizon n
    rw [lemma5iForcingEdgeZeroCount_eq_closed_local]

  let A : Nat := lemma5ArmHorizon n
  let S : Nat := lemma5SweepHorizon n
  let K0 : Nat := K n

  have hmono' :
      lemma5iLeaderArmFailureCount
          ring C <=
        (n - 1) ^ A * n ^ S := by
    calc
      lemma5iLeaderArmFailureCount
          ring C <=
          (allSchedules n
            (lemma5iHorizon n)).countP
              (lemma5iArmForcingMissB
                ring C) := hmono
      _ =
          (n - 1) ^ lemma5ArmHorizon n *
            n ^ lemma5SweepHorizon n :=
        hforcingCount
      _ =
          (n - 1) ^ A * n ^ S := by
        rfl

  have hn2 : 2 <= n := by
    omega

  have hhalf :
      2 * (n - 1) ^ n <= n ^ n :=
    LeaderCountDyadicTail.integer_half_life
      n (by omega)

  have hkcore :
      2 ^ K0 *
          (n - 1) ^ (n * K0) <=
        n ^ (n * K0) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul] using
      (Nat.pow_le_pow_left hhalf K0)

  have hKle :
      K0 <= 2 * (1 + 4 * K0) := by
    omega

  have hAK :
      n * K0 <= A := by
    calc
      n * K0 <=
          n * (2 * (1 + 4 * K0)) :=
        Nat.mul_le_mul_left n hKle
      _ = A := by
        dsimp [A, K0, lemma5ArmHorizon]
        ac_rfl

  let R : Nat := A - n * K0

  have hAR :
      A = n * K0 + R := by
    calc
      A =
          (A - n * K0) + n * K0 :=
        (Nat.sub_add_cancel hAK).symm
      _ =
          n * K0 + (A - n * K0) :=
        Nat.add_comm _ _
      _ = n * K0 + R := by
        rfl

  have hbase :
      n - 1 <= n := by
    omega

  have hrem :
      (n - 1) ^ R <= n ^ R :=
    Nat.pow_le_pow_left hbase R

  have hdecay :
      2 ^ K0 * (n - 1) ^ A <=
        n ^ A := by
    calc
      2 ^ K0 * (n - 1) ^ A =
          (2 ^ K0 *
            (n - 1) ^ (n * K0)) *
              (n - 1) ^ R := by
        rw [hAR, Nat.pow_add]
        ac_rfl
      _ <=
          n ^ (n * K0) * n ^ R :=
        Nat.mul_le_mul hkcore hrem
      _ = n ^ A := by
        rw [hAR, Nat.pow_add]

  have hnK :
      n <= 2 ^ K0 := by
    have hp :=
      (LeaderCountDyadicTail.log_parameters
        n hn2).2.2.2
    simpa [K0, K] using hp

  have harmDecay :
      n * (n - 1) ^ A <=
        n ^ A := by
    calc
      n * (n - 1) ^ A <=
          2 ^ K0 * (n - 1) ^ A :=
        Nat.mul_le_mul_right
          ((n - 1) ^ A) hnK
      _ <= n ^ A := hdecay

  have hfailure :
      n * lemma5iLeaderArmFailureCount
            ring C <=
        n ^ A * n ^ S := by
    calc
      n * lemma5iLeaderArmFailureCount
            ring C <=
          n *
            ((n - 1) ^ A * n ^ S) :=
        Nat.mul_le_mul_left n hmono'
      _ =
          (n * (n - 1) ^ A) *
            n ^ S := by
        ac_rfl
      _ <=
          n ^ A * n ^ S :=
        Nat.mul_le_mul_right
          (n ^ S) harmDecay

  calc
    n * lemma5iLeaderArmFailureCount
          ring C <=
        n ^ A * n ^ S := hfailure
    _ = n ^ (A + S) :=
      (Nat.pow_add n A S).symm
    _ = n ^ lemma5iHorizon n := by
      rfl
    _ <=
        2 * n ^ lemma5iHorizon n := by
      omega

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iLeaderArmSingleStep
#print axioms PPL.Modes.Lemma5.lemma5iLeaderArmBad_implies_forcingMiss
#print axioms PPL.Modes.Lemma5.lemma5iLeaderArmCount
