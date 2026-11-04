import Leader.PPL.Modes.MidEntryLeaderWave
import Leader.PPL.Modes.MidEntryTraversalRotation

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-!
The Wave residual is decomposed only on the active portion of a prefix:
the stopped wave is still live and the rotated word has not yet completed.

This avoids the three earlier over-strong all-prefix invariants.  Once the
wave dies, C is the intended terminal branch; once the rotated word completes,
the reset frontier is consumed immediately.  If B has already fired, the
residual is already discharged and no later physical invariant is needed.

Witness audit:
* The old long trace is outside the paper window; the active rows do
  not demand a post-horizon invariant.
* The global-max rerooting bug is absent because the Wave host does
  not reroot to the remote competitor.
* The Wave host stays on the merged carrier; B fires after 769
  encounters, so no invariant is needed after that discharge.
* ERRATA S3.11: a dead wave is not revived by a later leader arm.  The stopped
  stream has already frozen, and these one-step rows have a live-wave premise.
-/

/-! -------------------------------------------------------------------------
    D1.  Active prefix and the two semantic one-step debts
------------------------------------------------------------------------- -/

def Lemma5iLeaderWaveActivePrefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n) : Prop :=
  lemma5iLeaderWaveStopB ring D pre = false ∧
    ¬ (PPL.seqR ring
        (lemma5iLeaderWaveStart ring D) n).Sublist pre

/-- One H charge: the old host is the responder of the scheduled edge. -/
def lemma5iLeaderWaveHitCharge
    {n : Nat}
    (ring : DirectedRing n)
    (x e : Fin n) : Nat :=
  if ring.rightNeighbor e = x then 1 else 0

/-- Pure prefix bookkeeping for the location tracker. -/
def Lemma5iLeaderWaveLocationOneStep : Prop :=
  ∀ {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n),
    Lemma5iLeaderWaveActivePrefix ring D pre →
    lemma5iLeaderWaveHost ring D (pre ++ [e]) =
      if e = lemma5iLeaderWaveHost ring D pre then
        ring.rightNeighbor
          (lemma5iLeaderWaveHost ring D pre)
      else
        lemma5iLeaderWaveHost ring D pre

/--
Physical TTL monotonicity for the merged carrier.

A T step moves the host and loses no TTL.  An H step can lose at most one
TTL unit.  A nonincident step frames the old host exactly.
-/
def Lemma5iLeaderWaveTTLMergeOneStep : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n),
    Lemma5iLeaderWaveActivePrefix ring D pre →
    ((runPPL ring D pre)
        (lemma5iLeaderWaveHost ring D pre)).signalR.val ≤
      ((runPPL ring D (pre ++ [e]))
        (lemma5iLeaderWaveHost ring D
          (pre ++ [e]))).signalR.val +
        lemma5iLeaderWaveHitCharge
          ring
          (lemma5iLeaderWaveHost ring D pre)
          e

/--
A reset witness for the j-th selected rotated edge.
-/
def Lemma5iLeaderWaveResetWitness
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (start : Fin n)
    (pre : DetSchedule n)
    (j : Nat) : Prop :=
  ∃ before after : DetSchedule n,
    pre =
        before ++
          (PPL.shiftRight ring start j :: after) ∧
      (PPL.seqR ring start j).Sublist before ∧
      clockResetAt
          ring
          (runPPL ring D before)
          (PPL.shiftRight ring start j)
          (PPL.shiftRight ring start j) =
        true

/--
The live Wave frontier.  q is the number of selected clockwise edges already
consumed.  The next selected edge is exactly the current Wave host.
-/
def Lemma5iLeaderWaveResetFrontierAt
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n) : Prop :=
  let start := lemma5iLeaderWaveStart ring D
  let host := lemma5iLeaderWaveHost ring D pre
  ∃ q : Nat,
    q < n ∧
      host = PPL.shiftRight ring start q ∧
      (PPL.seqR ring start q).Sublist pre ∧
      ¬ (PPL.seqR ring start (q + 1)).Sublist pre ∧
      ∀ j : Nat,
        j < q →
          Lemma5iLeaderWaveResetWitness
            ring D start pre j

/--
The only reset-frontier one-step debt.

It is invoked only while the Wave is live and A has not completed.  On the
next letter either the Wave dies (the TTL potential is then consumed), the
last selected edge completes and all clocks have reset, or the live frontier
continues.
-/
def Lemma5iLeaderWaveResetFrontierOneStep : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n),
    Lemma5iLeaderWaveActivePrefix ring D pre →
    Lemma5iLeaderWaveResetFrontierAt ring D pre →
    let post := pre ++ [e]
    lemma5iLeaderWaveStopB ring D post = true ∨
      ((PPL.seqR ring
          (lemma5iLeaderWaveStart ring D) n).Sublist post ∧
        allClockResetsSeenB ring D post = true) ∨
      Lemma5iLeaderWaveResetFrontierAt ring D post

def Lemma5iLeaderWaveTTLPotentialAt
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (h : Nat)
    (pre : DetSchedule n) : Prop :=
  let host := lemma5iLeaderWaveHost ring D
  let stop := lemma5iLeaderWaveStopB ring D
  let Cpre := runPPL ring D pre
  let x := host pre
  let bits :=
    stoppedEncounterBits ring host stop pre
  let W :=
    lotteryRun psi
      (lotteryOffset h) bits
  kappa ≤ W.wins + (Cpre x).signalR.val

/--
The only TTL-accounting one-step debt.

It is invoked only while the stopped Wave is still live and A is incomplete.
If the next step kills the Wave, the frozen lottery wins already cover kappa;
otherwise the potential continues.
-/
def Lemma5iLeaderWaveTTLPotentialOneStep : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (h : Nat)
    (pre : DetSchedule n)
    (e : Fin n),
    Lemma5iLeaderWaveActivePrefix ring D pre →
    Lemma5iLeaderWaveTTLPotentialAt
      ring D h pre →
    let post := pre ++ [e]
    let host := lemma5iLeaderWaveHost ring D
    let stop := lemma5iLeaderWaveStopB ring D
    let bits :=
      stoppedEncounterBits ring host stop post
    let W :=
      lotteryRun psi
        (lotteryOffset h) bits
    (stop post = true →
      kappa ≤ W.wins) ∧
      (stop post = false →
        Lemma5iLeaderWaveTTLPotentialAt
          ring D h post)

/-! -------------------------------------------------------------------------
    D2.  Mechanical location and TTL-merge facts
------------------------------------------------------------------------- -/

private theorem q20084RightNeighbor_ne_self
    {n : Nat}
    (hn3 : 3 ≤ n)
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

private theorem q20084Signal_le_armed
    {psi kappa : Nat}
    (q : PPL.State psi kappa) :
    q.signalR.val ≤ armedSignalVal q := by
  unfold armedSignalVal
  by_cases hlead : q.leader = true
  · rw [if_pos hlead]
    have hlt := q.signalR.isLt
    omega
  · rw [if_neg hlead]
    exact Nat.le_refl _

private theorem q20084RunPPL_append_local
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

private theorem q20084RunPPL_append_singleton
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n) :
    runPPL ring C (pre ++ [e]) =
      pplStep ring
        (runPPL ring C pre) e := by
  rw [q20084RunPPL_append_local]
  rfl

theorem lemma5iLeaderWaveHost_append_singleton
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n) :
    lemma5iLeaderWaveHost ring D (pre ++ [e]) =
      if e = lemma5iLeaderWaveHost ring D pre then
        ring.rightNeighbor
          (lemma5iLeaderWaveHost ring D pre)
      else
        lemma5iLeaderWaveHost ring D pre := by
  simp only
    [lemma5iLeaderWaveHost,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil]
  try rfl

theorem lemma5iLeaderWaveLocationOneStep_proved :
    Lemma5iLeaderWaveLocationOneStep := by
  unfold Lemma5iLeaderWaveLocationOneStep
  intro n psi kappa ring D pre e _hactive
  exact
    lemma5iLeaderWaveHost_append_singleton
      ring D pre e

/--
Pair-local source fact for the Wave TTL inequality.
-/
theorem lemma5iLeaderWaveTTLMerge_local
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (x e : Fin n) :
    (C x).signalR.val ≤
      (pplStep ring C e
        (if e = x then
          ring.rightNeighbor x
        else x)).signalR.val +
        lemma5iLeaderWaveHitCharge ring x e := by
  unfold lemma5iLeaderWaveHitCharge

  by_cases hex : e = x
  · subst e
    have hself :=
      q20084RightNeighbor_ne_self
        hn3 ring x
    have hd :=
      determineModeSignalProjection
        (psi := psi) (kappa := kappa)
        hpsi
        (C x)
        (C (ring.rightNeighbor x))
    have hs :=
      step_signal_projection_of_stable
        postDetermineModeSignalStable
        hpsi ring C x hself
    dsimp only at hd hs

    have hpost :
        (pplStep ring C x
          (ring.rightNeighbor x)).signalR.val =
        (PPL.determineMode
          (C x)
          (C (ring.rightNeighbor x))).2.signalR.val := by
      simpa
        [PPL.Probability.pplStep,
          PPL.Modes.SignalLineage.step]
        using
          congrArg Fin.val hs.2.2.1

    simp only
      [if_pos rfl,
        if_neg hself,
        Nat.add_zero]
    try simp only [if_true, ite_true, ↓reduceIte]
    rw [hpost]

    have hbase :=
      q20084Signal_le_armed (C x)
    rcases hd.2.2 with hz | hl | hr
    · omega
    · rw [hl.2.2.1]
      omega
    · rw [hr.2.1]
      split <;> omega

  · by_cases hrx :
        ring.rightNeighbor e = x
    · have hself :=
        q20084RightNeighbor_ne_self
          hn3 ring e
      have hex' : e ≠ x := hex
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

      have hpost :
          (pplStep ring C e x).signalR.val =
            (PPL.determineMode
              (C e)
              (C (ring.rightNeighbor e))).2.signalR.val := by
        rw [← hrx]
        simpa
          [PPL.Probability.pplStep,
            PPL.Modes.SignalLineage.step]
          using
            congrArg Fin.val hs.2.2.1

      simp only
        [if_neg hex',
          if_pos hrx]
      rw [hpost, ← hrx]

      rcases hd.2.2 with hz | hl | hr
      · omega
      · rw [hl.2.2.1]
        omega
      · rw [hr.2.1]
        split <;> omega

    · have haway :=
        step_signal_hits_away
          ring C e x
          (Ne.symm hex)
          (Ne.symm hrx)
      have hpost :
          (pplStep ring C e x).signalR.val =
            (C x).signalR.val := by
        simpa
          [PPL.Probability.pplStep,
            PPL.Modes.SignalLineage.step]
          using
            congrArg Fin.val haway.1
      simp only
        [if_neg hex,
          if_neg hrx,
          Nat.add_zero,
          hpost,
          Nat.le_refl]

theorem lemma5iLeaderWaveTTLMergeOneStep_proved :
    Lemma5iLeaderWaveTTLMergeOneStep := by
  unfold Lemma5iLeaderWaveTTLMergeOneStep
  intro n psi kappa
  intro hn3 hpsi ring D pre e _hactive

  rw [q20084RunPPL_append_singleton]
  rw [lemma5iLeaderWaveHost_append_singleton]

  exact
    lemma5iLeaderWaveTTLMerge_local
      hn3 hpsi ring
      (runPPL ring D pre)
      (lemma5iLeaderWaveHost ring D pre)
      e

/-! -------------------------------------------------------------------------
    D3.  Wave residual -> existing corrected BC projection
------------------------------------------------------------------------- -/

private theorem q20084WaveTTLBad_eq_q19765TTLBad
    {n : Nat}
    (psi h : Nat)
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (sweep : DetSchedule n) :
    lemma5iLeaderWaveTTLBad
        psi h ring host stop sweep =
      q19765TTLBad
        psi h ring host stop sweep := by
  apply Bool.eq_iff_iff.mpr
  simp
    [lemma5iLeaderWaveTTLBad,
      q19765TTLBad]

private theorem q20084CountP_mono_on
    {A : Type}
    (xs : List A)
    (p q : A → Bool)
    (hpq :
      ∀ x,
        x ∈ xs →
        p x = true →
        q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons,
        List.countP_cons]
      have htail :
          xs.countP p ≤ xs.countP q :=
        ih
          (fun y hy hpy =>
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

private theorem q20084CountP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A → Bool) :
    xs.countP
        (fun x => p x || q x) ≤
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

private theorem q20084AllSchedules_add
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
      simp only
        [allSchedules,
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

private theorem q20084SumIfCount
    {A : Type}
    (xs : List A)
    (p : A → Bool)
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
        simp [hp, ih, Nat.succ_mul,
          Nat.add_comm]

private theorem q20084CountP_take_pad
    {n H P : Nat}
    (p : DetSchedule n → Bool) :
    (allSchedules n (H + P)).countP
        (fun word => p (word.take H)) =
      (allSchedules n H).countP p *
        n ^ P := by
  rw [q20084AllSchedules_add,
    List.countP_flatMap]
  simp only [Function.comp_def]
  have hmap :
      ((allSchedules n H).map
        (fun pre =>
          ((allSchedules n P).map
            (fun pad => pre ++ pad)).countP
              (fun word =>
                p (word.take H)))) =
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
  exact
    q20084SumIfCount
      (allSchedules n H)
      p (n ^ P)

/--
The Wave residual feeds the exact corrected projection Prop already consumed
by ABCWire.  Despite its historical name, that Prop existentially quantifies
an arbitrary prefix-predictable host/stop pair.
-/
theorem lemma5iTraversalProjection_of_residualWave
    (hWave :
      Lemma5iRetimedTraversalABCSweepResidualWave) :
    Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBCCorrected := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D hlineage hmax

  let start :=
    lemma5iLeaderWaveStart ring D
  let host :=
    lemma5iLeaderWaveHost ring D
  let stop :=
    lemma5iLeaderWaveStopB ring D
  let h :=
    (D start).hits.val

  have hraw :=
    hWave
      hn3 hpsi hkappa hnpow
      ring D hlineage hmax

  change
    (D start).signalR.val = kappa ∧
      h ≤ psi ∧
      ∀ sweep : DetSchedule n,
        sweep ∈
            allSchedules n
              (lemma5PaperSweepHorizon n) →
        !allClockResetsSeenB
            ring D sweep = true →
        ((lemma5iLeaderWaveRotatedMiss
              ring start sweep ||
            lemma5iLeaderWaveEncounterBad
              ring host stop sweep) ||
          lemma5iLeaderWaveTTLBad
            psi h ring host stop sweep) =
          true
    at hraw

  refine
    ⟨host, stop, h, hraw.2.1, ?_⟩

  let P : Nat :=
    lemma5PaperSweepHorizon n
  let Z : Nat :=
    2 * n * n
  let S : Nat :=
    lemma5SweepHorizon n

  let badP : DetSchedule n → Bool :=
    fun sweep =>
      !allClockResetsSeenB ring D sweep
  let qA : DetSchedule n → Bool :=
    q19765RotatedMiss ring start
  let qB : DetSchedule n → Bool :=
    q19765EncounterBad ring host stop
  let qC : DetSchedule n → Bool :=
    q19765TTLBad psi h ring host stop
  let qAB : DetSchedule n → Bool :=
    fun sweep =>
      qA sweep || qB sweep

  have hmono :
      (allSchedules n P).countP badP ≤
        (allSchedules n P).countP
          (fun sweep =>
            qAB sweep || qC sweep) := by
    apply
      q20084CountP_mono_on
        (allSchedules n P)
        badP
        (fun sweep =>
          qAB sweep || qC sweep)
    intro sweep hsweep hbad

    have hw :=
      hraw.2.2 sweep
        (by simpa [P] using hsweep)
        (by simpa [badP] using hbad)

    rw [q20084WaveTTLBad_eq_q19765TTLBad
      psi h ring host stop sweep] at hw

    dsimp [qAB, qA, qB, qC]
    simpa
      [lemma5iLeaderWaveRotatedMiss,
        q19765RotatedMiss,
        lemma5iLeaderWaveEncounterBad,
        q19765EncounterBad]
      using hw

  have hab :=
    q20084CountP_or_le_add
      (allSchedules n P) qA qB
  have habc :=
    q20084CountP_or_le_add
      (allSchedules n P) qAB qC

  have hAeq :
      (allSchedules n P).countP qA =
        fixedWordMissCount
          (lemma5ClockwiseSweepWord n) P := by
    simpa [qA] using
      lemma5iRotatedSweepMissCount_eq_fixedWordMissCount
        ring start P

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
      (allSchedules n P).countP badP ≤
        fixedWordMissCount
            (lemma5ClockwiseSweepWord n) P +
          lemma5iTraversalEncounterFailureCountBC
            ring host stop +
          lemma5iTraversalTTLFailureCountBC
            psi h ring host stop := by
    calc
      (allSchedules n P).countP badP ≤
          (allSchedules n P).countP
            (fun sweep =>
              qAB sweep || qC sweep) :=
        hmono
      _ ≤
          (allSchedules n P).countP qAB +
            (allSchedules n P).countP qC :=
        habc
      _ ≤
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
    q20084CountP_take_pad
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
            badP (suffix.take P)) ≤
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
          n ^ Z ≤
        (fixedWordMissCount
              (lemma5ClockwiseSweepWord n) P +
            lemma5iTraversalEncounterFailureCountBC
              ring host stop +
            lemma5iTraversalTTLFailureCountBC
              psi h ring host stop) *
          n ^ Z :=
        Nat.mul_le_mul_right
          (n ^ Z) hpaper
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

/--
Exact ABCWire consumer target.

The existing corrected budget theorem invokes
lemma5iTraversalABC_paperBudgetBC for the arbitrary Wave host/stop pair.
-/
theorem lemma5iTraversalBudget_of_residualWave
    (hWave :
      Lemma5iRetimedTraversalABCSweepResidualWave) :
    ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hkappa : 48 * psi ≤ kappa)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring →
    ModeStoppedTreeTransfer →
    PredictableHostTails →
    WLGHeadOffsetBounds →
    LotteryCountBounds →
    maxResetSignalB D = true →
    n *
        (allSchedules n
          (lemma5SweepHorizon n)).countP
          (fun suffix =>
            !allClockResetsSeenB ring D
              (suffix.take
                (lemma5PaperSweepHorizon n))) ≤
      n ^ lemma5SweepHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D hlineage
  intro hmarked hpredict hoffset hlottery
  intro hmax

  exact
    lemma5iRetimedTraversalCurrentMaxSuffixBC_budget_corrected
      (lemma5iTraversalProjection_of_residualWave
        hWave)
      hn3 hpsi hkappa hnpow
      ring D hlineage
      hmarked hpredict
      hoffset hlottery
      hmax

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iLeaderWaveHost_append_singleton
#print axioms PPL.Modes.Lemma5.lemma5iLeaderWaveLocationOneStep_proved
#print axioms PPL.Modes.Lemma5.lemma5iLeaderWaveTTLMerge_local
#print axioms PPL.Modes.Lemma5.lemma5iLeaderWaveTTLMergeOneStep_proved
#print axioms PPL.Modes.Lemma5.lemma5iTraversalProjection_of_residualWave
#print axioms PPL.Modes.Lemma5.lemma5iTraversalBudget_of_residualWave
