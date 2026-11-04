import Leader.PPL.MainTheorem.GeneralQuietWindowFit
import Leader.PPL.MainTheorem.GeneralTargets
import Leader.PPL.MainTheorem.GeneralFixedCut
import Leader.PPL.MainTheorem.WindowSPLEntryDynamicPadding

/-!
# P_PL Theorem 1, general L18 first-hit bound: the failure count as a parameter

The L18 padded bound goes through the dynamic first-`C_mid` cut: a word with
a bad L18 event factors as a stopped prefix, a bad `H5(ii)` phase and a pad
(`theorem1L18FirstHitStop_cover_at`); the bad phases after one stopped
prefix are at most `n^{H5ii}/n` (`theorem1L18FirstHitPhaseBound_at`); and
`theorem1DynamicCutPadding_proved` sums over the stopped prefixes
(`theorem1L18DynamicPaddedBound_at`).

The `psi < n` chain (`PPL.PsiBelowN.FirstHit`, rooted `S_PL`) and the
`n ≤ psi` chain (`PPL.PsiAtLeastN.SafeFirstHit`, rooted safe predicate)
proved this twice, and `PPL.theorem1L18FirstHitStop_cover` and
`PPL.PsiAtLeastN.theorem1L18SafeFirstHitStop_cover` proved the cover twice.
The two proofs differ only in the rooted predicate and in the per-root
Lemma-18 failure count: `n_mul_l18FailureCount_le_pow_scoped` (needs
`psi < n` and the scoped forcing bridge) or
`n_mul_l18SafeFailureCount_le_pow` (every `psi`).  Here both are
parameters (`loc` and `hfail`).

`PPL.theorem1L18FirstHitStop_cover` is relocated here from
`Theorem1L5iiL18Dynamic.lean` as the `S_PL` special case, with its name and
statement unchanged.

P_PL Theorem 1 cleanup, phase 2, step 6c (the arguments are
those of `Theorem1L18FirstHitFromForcing.lean`).
-/

namespace PPL.Theorem1General

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Literal helpers -/

/-- Literal PB is closed along every literal Algorithm-5 run. -/
theorem theorem1PB_run
    {n : Nat}
    (ring : DirectedRing n)
    (w : DetSchedule n) :
    ∀ D : PPL.LiteralElimConfig n,
      PPL.Elim.PB ring D →
      PPL.Elim.PB ring
        (PPL.Probability.runPopulationSchedule
          PPL.Elim.protocolE ring D w) := by
  induction w with
  | nil =>
      intro D hD
      exact hD
  | cons e rest ih =>
      intro D hD
      exact
        ih _
          (PPL.Convergence.LDLocal.pbStepClosure ring D e hD)

/-- A full configuration whose literal view has exactly one leader has a
unique leader root. -/
theorem theorem1Unique_of_leaderCount
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : PPL.Elim.leaderCount (PPL.Elim.viewConfig C) = 1) :
    ∃ root : Fin n,
      PPL.Convergence.L18.L18UniqueLeaderAt C root := by
  have h1 :
      (List.ofFn
        (fun i : Fin n =>
          if (C i).leader = true then 1 else 0)).sum = 1 := h
  have hofFn :
      (List.ofFn
        (fun i : Fin n =>
          if (C i).leader = true then 1 else 0)) =
        (List.finRange n).map
          (fun i : Fin n =>
            if (C i).leader = true then 1 else 0) := by
    unfold List.finRange
    rw [List.map_ofFn]
    rfl
  rw [hofFn,
    theorem1_sum_if_count (List.finRange n) (fun i => (C i).leader) 1,
    Nat.mul_one, List.countP_eq_length_filter] at h1
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp h1
  refine ⟨r, ?_⟩
  intro i
  have hmem :
      i ∈ (List.finRange n).filter (fun i => (C i).leader) ↔
        i = r := by
    rw [hr]
    simp
  rw [List.mem_filter] at hmem
  constructor
  · intro hl
    exact hmem.mp ⟨List.mem_finRange i, hl⟩
  · intro hi
    exact (hmem.mpr hi).2

/-! ## The cover by stopped prefixes -/

/-- Every word whose L18 event (for the rooted predicate `loc`) is bad
factors as a first-`C_mid` stopped prefix, an `H5(ii)` phase whose phase
event is bad, and a pad. -/
theorem theorem1L18FirstHitStop_cover_at
    {n psi : Nat}
    (loc : Fin n → Config n psi (theorem1Kappa psi) → Bool)
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (hword :
      word ∈
        allSchedules n
          (theorem1Horizon n psi))
    (hbad :
      theorem1Bad18Gen ring loc C0 word = true) :
    ∃ p : DetSchedule n,
      ∃ phase : DetSchedule n,
        ∃ pad : DetSchedule n,
          theorem1L17FirstHitStop ring C0 p = true ∧
            phase ∈
              allSchedules n
                (theorem1H5ii n psi) ∧
            word = p ++ phase ++ pad ∧
            theorem1L18FirstHitPhaseBadGen
              ring loc C0 p phase = true := by
  cases hcut :
      theorem1MidCut ring C0 word with
  | none =>
      simp [theorem1Bad18Gen,
        theorem1MidState, hcut] at hbad
  | some t =>
      have hbadCore := hbad
      unfold theorem1Bad18Gen at hbadCore
      rw [hcut] at hbadCore
      simp only [theorem1MidState, hcut] at hbadCore
      try dsimp only at hbadCore

      have houter :=
        Bool.and_eq_true_iff.mp hbadCore
      have hleft :=
        Bool.and_eq_true_iff.mp houter.1
      have hleft0 :=
        Bool.and_eq_true_iff.mp hleft.1
      have hreach := hleft0.1
      have hconstruct := hleft0.2
      have hlit := hleft.2
      have hroots := houter.2

      obtain
          ⟨p, phase, pad,
            hstop, hphaseMem, hfactor,
            hpEq, hphaseEq⟩ :=
        theorem1DynamicFirstHitFactor
          hn3 hpsi
          (T := theorem1H5ii n psi)
          (Nat.le_refl _)
          ring C0 word hword t hcut hreach

      have hpState :=
        theorem1DynamicFirstHitPrefixState
          ring C0 word t hcut

      subst p
      subst phase

      have hconstruct' :
          PPL.Modes.Lemma5.constructAlong
              ring
              (PPL.Probability.runPPL
                ring C0
                (word.take
                  (theorem1H16 n psi + t)))
              ((word.drop
                (theorem1H16 n psi + t)).take
                  (theorem1H5ii n psi)) =
            true := by
        rw [hpState]
        simpa [theorem1QuietWord]
          using hconstruct

      have hlit' :
          @decide
              (PPL.LiteralL1
                (PPL.Probability.runPopulationSchedule
                  PPL.Elim.protocolE ring
                  (PPL.Elim.viewConfig
                    (PPL.Probability.runPPL
                      ring C0
                      (word.take
                        (theorem1H16 n psi + t))))
                  (((word.drop
                    (theorem1H16 n psi + t)).take
                      (theorem1H5ii n psi)).take
                        (theorem1H17 n))))
              (theorem1LiteralL1Decidable _) =
            true := by
        rw [hpState]
        simpa
          [theorem1Literal17End,
            theorem1L17Word,
            theorem1QuietWord]
          using (@of_decide_eq_true _ _ hlit)

      have hroots' :
          theorem1AllLeaderRootsMissGen
              ring loc
              (PPL.Convergence.ConstructCoupling.runPrime
                ring
                (PPL.Probability.runPPL
                  ring C0
                  (word.take
                    (theorem1H16 n psi + t)))
                (((word.drop
                  (theorem1H16 n psi + t)).take
                    (theorem1H5ii n psi)).take
                      (theorem1H17 n)))
              ((((word.drop
                (theorem1H16 n psi + t)).take
                  (theorem1H5ii n psi)).drop
                    (theorem1H17 n)).take
                      (theorem1H18 n psi)) =
            true := by
        rw [hpState]
        simpa
          [theorem1Prime17End,
            theorem1L17Word,
            theorem1L18Word,
            theorem1QuietWord]
          using hroots

      have hphaseBad :
          theorem1L18FirstHitPhaseBadGen
              ring loc C0
              (word.take
                (theorem1H16 n psi + t))
              ((word.drop
                (theorem1H16 n psi + t)).take
                  (theorem1H5ii n psi)) =
            true := by
        unfold theorem1L18FirstHitPhaseBadGen
        dsimp only
        exact
          Bool.and_eq_true_iff.mpr
            ⟨Bool.and_eq_true_iff.mpr
                ⟨hconstruct', hlit'⟩,
              hroots'⟩

      exact
        ⟨word.take
            (theorem1H16 n psi + t),
          (word.drop
            (theorem1H16 n psi + t)).take
              (theorem1H5ii n psi),
          pad,
          hstop,
          hphaseMem,
          hfactor,
          hphaseBad⟩

/-! ## The phase bound -/

/-- The L18 phase bound at one `(n, psi)` after one stopped prefix `p`, for
a rooted predicate `loc` whose per-root failure count is at most
`n^{H18}/n` (`hfail`).

A bad phase is bad already on its first `H17 + H18` letters (the rest is a
pad, `theorem1_countP_take_pad`).  For each `H17` prefix whose literal
endpoint has one leader, that leader root misses `loc` on every `H18` suffix
counted, so `hfail` bounds the suffixes; summing over the `n^{H17}`
prefixes gives `n^{H17+H18}/n`. -/
theorem theorem1L18FirstHitPhaseBound_at
    {n psi : Nat}
    (ring : DirectedRing n)
    (loc : Fin n → Config n psi (theorem1Kappa psi) → Bool)
    (hfail :
      ∀ (root : Fin n) (C : Config n psi (theorem1Kappa psi)),
        CPB ring C →
        PPL.Convergence.L18.L18UniqueLeaderAt C root →
        n * (allSchedules n (theorem1H18 n psi)).countP
            (fun suf => !(theorem1L18HitsB ring (loc root) C suf)) ≤
          n ^ theorem1H18 n psi)
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (C0 : Config n psi (theorem1Kappa psi))
    (p : DetSchedule n)
    (hstop : theorem1L17FirstHitStop ring C0 p = true) :
    n *
        (allSchedules n (theorem1H5ii n psi)).countP
          (theorem1L18FirstHitPhaseBadGen ring loc C0 p) ≤
      n ^ theorem1H5ii n psi := by
  let Cmid : Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C0 p
  let T : Nat := theorem1H17 n
  let U : Nat := theorem1H18 n psi
  let R : Nat := theorem1H5ii n psi - (T + U)
  have hcover : T + U ≤ theorem1H5ii n psi :=
    theorem1H17_add_H18_le_H5ii hn3 hpsi hnpow
  have hH : (T + U) + R = theorem1H5ii n psi := by
    dsimp only [R]
    omega
  have hPBmid :
      PPL.Elim.PB ring (PPL.Elim.viewConfig Cmid) :=
    (theorem1L17FirstHitStop_local hn3 hpsi ring C0 p hstop).1

  -- The literal-one indicator of an H17 prefix, and the reduced event.
  let l1 : DetSchedule n → Bool := fun w17 =>
    @decide
      (PPL.LiteralL1
        (PPL.Probability.runPopulationSchedule
          PPL.Elim.protocolE ring
          (PPL.Elim.viewConfig Cmid)
          w17))
      (theorem1LiteralL1Decidable _)
  let g : DetSchedule n → Bool := fun u =>
    l1 (u.take T) &&
      theorem1AllLeaderRootsMissGen ring loc
        (PPL.Convergence.ConstructCoupling.runPrime
          ring Cmid (u.take T))
        (u.drop T)

  -- Step 1: a bad phase gives the reduced event on its first T+U letters.
  have hreduce :
      ∀ phase : DetSchedule n,
        theorem1L18FirstHitPhaseBadGen ring loc C0 p phase = true →
          g (phase.take (T + U)) = true := by
    intro phase hbad
    unfold theorem1L18FirstHitPhaseBadGen at hbad
    simp only [Bool.and_eq_true] at hbad
    obtain ⟨⟨_hcons, hl1⟩, hmiss⟩ := hbad
    have htake :
        (phase.take (T + U)).take T = phase.take T := by
      rw [List.take_take]
      have hm : min T (T + U) = T := by omega
      rw [hm]
    have hdrop :
        (phase.take (T + U)).drop T =
          (phase.drop T).take U := by
      rw [List.drop_take]
      have hm : T + U - T = U := by omega
      rw [hm]
    dsimp only [g]
    rw [htake, hdrop, Bool.and_eq_true]
    exact ⟨hl1, hmiss⟩

  have hmono :
      (allSchedules n (theorem1H5ii n psi)).countP
          (theorem1L18FirstHitPhaseBadGen ring loc C0 p) ≤
        (allSchedules n (theorem1H5ii n psi)).countP
          (fun w => g (w.take (T + U))) :=
    List.countP_mono_left
      (fun phase _ hbad => hreduce phase hbad)

  have hpad :
      (allSchedules n (theorem1H5ii n psi)).countP
          (fun w => g (w.take (T + U))) =
        (allSchedules n (T + U)).countP g * n ^ R := by
    rw [← hH]
    exact theorem1_countP_take_pad g

  -- Step 2: per H17 prefix, the H18 count.
  have hper :
      ∀ pre ∈ allSchedules n T,
        n * ((allSchedules n U).map (fun suf => pre ++ suf)).countP g ≤
          n ^ U := by
    intro pre hpre
    have hlen : pre.length = T :=
      allSchedules_schedule_length n T pre hpre
    rw [List.countP_map]
    have hfun :
        (g ∘ fun suf => pre ++ suf) =
          (fun suf =>
            l1 pre &&
              theorem1AllLeaderRootsMissGen ring loc
                (PPL.Convergence.ConstructCoupling.runPrime
                  ring Cmid pre)
                suf) := by
      funext suf
      simp only [Function.comp_apply, g]
      rw [← hlen, List.take_append_length, List.drop_append_length]
    rw [hfun]
    cases hl : l1 pre with
    | false =>
        simp
    | true =>
        let C17 : Config n psi (theorem1Kappa psi) :=
          PPL.Convergence.ConstructCoupling.runPrime ring Cmid pre
        have hproj :
            PPL.Elim.viewConfig C17 =
              PPL.Probability.runPopulationSchedule
                PPL.Elim.protocolE ring
                (PPL.Elim.viewConfig Cmid) pre :=
          PPL.Convergence.LiteralEliminationBridges.runPrime_projects
            hpsi ring Cmid pre
        have hL1 :
            PPL.LiteralL1
              (PPL.Probability.runPopulationSchedule
                PPL.Elim.protocolE ring
                (PPL.Elim.viewConfig Cmid) pre) :=
          @of_decide_eq_true _ (theorem1LiteralL1Decidable _) hl
        have hcount :
            PPL.Elim.leaderCount (PPL.Elim.viewConfig C17) = 1 := by
          rw [hproj]
          exact hL1
        obtain ⟨root, hUnique⟩ :=
          theorem1Unique_of_leaderCount C17 hcount
        have hPB17 :
            PPL.Elim.PB ring (PPL.Elim.viewConfig C17) := by
          rw [hproj]
          exact theorem1PB_run ring pre _ hPBmid
        have hCPB17 : CPB ring C17 :=
          (PPL.Convergence.LiteralEliminationBridges.cpbViewBridge
            ring C17).mpr hPB17
        have hbound := hfail root C17 hCPB17 hUnique
        have hle :
            (allSchedules n U).countP
                (fun suf =>
                  true &&
                    theorem1AllLeaderRootsMissGen ring loc C17 suf) ≤
              (allSchedules n U).countP
                (fun suf => !(theorem1L18HitsB ring (loc root) C17 suf)) := by
          apply List.countP_mono_left
          intro suf _ hmiss
          rw [Bool.true_and] at hmiss
          have hroot : (C17 root).leader = true :=
            (hUnique root).mpr rfl
          have hmissRoot :=
            theorem1AllLeaderRootsMissGen_root
              ring loc C17 suf root hroot hmiss
          rw [hmissRoot]
          rfl
        exact
          Nat.le_trans (Nat.mul_le_mul_left n hle) hbound

  have hprefix :
      n * (allSchedules n (T + U)).countP g ≤ n ^ (T + U) := by
    rw [theorem1_allSchedules_add, List.countP_flatMap]
    simp only [Function.comp_def]
    have hsum :=
      theorem1_mul_sum_le_length_mul
        (allSchedules n T)
        (fun pre =>
          ((allSchedules n U).map (fun suf => pre ++ suf)).countP g)
        n (n ^ U) hper
    rw [allSchedules_length, ← Nat.pow_add] at hsum
    exact hsum

  calc
    n * (allSchedules n (theorem1H5ii n psi)).countP
          (theorem1L18FirstHitPhaseBadGen ring loc C0 p) ≤
        n * ((allSchedules n (T + U)).countP g * n ^ R) := by
      rw [← hpad]
      exact Nat.mul_le_mul_left n hmono
    _ = (n * (allSchedules n (T + U)).countP g) * n ^ R := by
      rw [Nat.mul_assoc]
    _ ≤ n ^ (T + U) * n ^ R :=
      Nat.mul_le_mul_right (n ^ R) hprefix
    _ = n ^ theorem1H5ii n psi := by
      rw [← Nat.pow_add, hH]

/-! ## The padded L18 bound -/

/-- The padded L18 bound at one `(n, psi)` for a rooted predicate `loc`,
from the phase bound after every stopped prefix: dynamic cut padding over
the first-`C_mid` stopping family, with the cover. -/
theorem theorem1L18DynamicPaddedBound_at
    {n psi : Nat}
    (ring : DirectedRing n)
    (loc : Fin n → Config n psi (theorem1Kappa psi) → Bool)
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (C0 : Config n psi (theorem1Kappa psi))
    (hphase :
      ∀ p : DetSchedule n,
        theorem1L17FirstHitStop ring C0 p = true →
        p.length + theorem1H5ii n psi ≤ theorem1Horizon n psi →
        n *
            (allSchedules n (theorem1H5ii n psi)).countP
              (theorem1L18FirstHitPhaseBadGen ring loc C0 p) ≤
          n ^ theorem1H5ii n psi) :
    n *
        (allSchedules n (theorem1Horizon n psi)).countP
          (theorem1Bad18Gen ring loc C0) ≤
      n ^ theorem1Horizon n psi := by
  rw [← Nat.one_mul (n ^ theorem1Horizon n psi)]
  exact
    theorem1DynamicCutPadding_proved
      (n := n)
      (H := theorem1Horizon n psi)
      (T := theorem1H5ii n psi)
      (c := 1)
      (theorem1L17FirstHitStop ring C0)
      (theorem1L18FirstHitPhaseBadGen ring loc C0)
      (theorem1Bad18Gen ring loc C0)
      (theorem1L17FirstHitStop_prefixFree ring C0)
      (by
        intro p hp hlen
        simpa using hphase p hp hlen)
      (by
        intro word hword hbad
        exact
          theorem1L18FirstHitStop_cover_at
            loc hn3 hpsi ring C0 word hword hbad)

/-! ## The `S_PL` instance -/

/-- `theorem1L18FirstHitPhaseBad` is the L18 phase event for rooted
`S_PL`. -/
theorem theorem1L18FirstHitPhaseBad_eq
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p phase : DetSchedule n) :
    theorem1L18FirstHitPhaseBad ring C0 p phase =
      theorem1L18FirstHitPhaseBadGen ring
        (fun root C => decide (SPLAt ring root C)) C0 p phase := by
  unfold theorem1L18FirstHitPhaseBad theorem1L18FirstHitPhaseBadGen
  dsimp only
  exact congrArg (and _) (theorem1AllLeaderRootsMissB_eq ring _ _)

end PPL.Theorem1General

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- Every word with the L18 bad event factors as a first-`C_mid` stopped
prefix, an `H5(ii)` phase that is L18 bad, and a pad
(`PPL.Theorem1General.theorem1L18FirstHitStop_cover_at` for rooted `S_PL`;
relocated from `Theorem1L5iiL18Dynamic.lean` in step 6c, statement
unchanged). -/
theorem theorem1L18FirstHitStop_cover
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (hword :
      word ∈
        allSchedules n
          (theorem1Horizon n psi))
    (hbad :
      theorem1Bad18B ring C0 word = true) :
    ∃ p : DetSchedule n,
      ∃ phase : DetSchedule n,
        ∃ pad : DetSchedule n,
          theorem1L17FirstHitStop ring C0 p = true ∧
            phase ∈
              allSchedules n
                (theorem1H5ii n psi) ∧
            word = p ++ phase ++ pad ∧
            theorem1L18FirstHitPhaseBad
              ring C0 p phase = true := by
  rw [PPL.Theorem1General.theorem1Bad18B_eq] at hbad
  obtain ⟨p, phase, pad, hstop, hmem, hfactor, hphase⟩ :=
    PPL.Theorem1General.theorem1L18FirstHitStop_cover_at
      (fun root C => decide (SPLAt ring root C))
      hn3 hpsi ring C0 word hword hbad
  refine ⟨p, phase, pad, hstop, hmem, hfactor, ?_⟩
  rw [PPL.Theorem1General.theorem1L18FirstHitPhaseBad_eq]
  exact hphase

end PPL
