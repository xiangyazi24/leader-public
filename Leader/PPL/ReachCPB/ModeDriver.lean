import Leader.PPL.ReachCPB.Forcing
import Leader.PPL.Modes.ClockSuffixBridge
import Leader.PPL.Modes.SignalLineageLocal
import Leader.PPL.Convergence.QuietWindow


/-!
# Deterministic H6 driver: possible convergence of the Lemma-16 mode phase

The probabilistic Lemma-16 mode block (`lemma16ModeCappedReachCount`) counts
failing scheduler words.  This module proves the corresponding *possible
convergence* statement with an explicit scheduler word: from every
configuration whose live bullets are all peaceful, a fixed word of length at
most `lemma16H6 n psi kappa` drives the literal P_PL run either to `C_PB` or
to `DetectReadyCapped` (leaderless, signal-free, every stored mode Detect,
every clock at the cap `kappa`).

## The driver

Let `z = 0` and let `seqR ring z n = [0, 1, ..., n-1]` be the clockwise sweep
of directed edges `(i, i+1)`.  With `R = 8 * kappa * 2^psi` the driver is two
copies of

  `modeRepeatEach R (seqR ring z n)`,

i.e. every edge of the sweep scheduled `R` times in a row.  Its length is
`2 * n * R = lemma16H6 n psi kappa` exactly.  Only `R ≥ psi * kappa + 1` is
used by the argument.

## Why it works (checked against `PPL.determineMode`, Algorithm 4)

Only DetermineMode writes `signalR`, `hits`, `clock` and `mode`; the rest of
the interaction (CreateLeader line 5 onwards, MoveToken, EliminateLeaders)
leaves those four fields alone (`postDetermineModeSignalStable`,
`clockSuffixPairProjection`, `postDetermineModeModeStable`).  A leader can be
born during the run (line 6 or a MoveToken birth), but as soon as one exists
the configuration is `C_PB`, because `AllLivePeaceful` is preserved by every
step (`allLivePeaceful_step_closed`, `cpb_of_allLivePeaceful_hasLeader`) and
`C_PB` is closed (`cpb_run_closed`).  So while the run is not yet `C_PB` every
pre-state is leaderless, and line 35 never re-arms a signal.

* Sweep 1 (drain).  Every interaction writes the initiator's `signalR` to 0.
  With a leaderless initiator of signal 0 and a responder of signal `s > 0`,
  the responder's hit counter is bumped, and every time it reaches `psi` the
  signal drops by one; the potential
  `s * psi - min hits (psi - 1)` drops by exactly one per interaction.  Hence
  one interaction plus `psi * kappa` further ones clear both endpoints.  In a
  leaderless run signals only move from initiator to responder and never grow,
  so blocks never re-pollute a cleared site; after the sweep every site (being
  the responder of some edge) has signal 0.
* Sweep 2 (clock rise).  In a leaderless signal-free configuration the
  no-signal branch (lines 46--50) leaves the initiator clock unchanged, bumps
  the responder hits and, at `psi` hits, raises the responder clock capped at
  `kappa`; `finishModes` writes `mode := (clock == kappa)` at both endpoints.
  Clocks never decrease, signals stay 0, and the potential
  `(kappa - clock) * psi - min hits (psi - 1)` drops by one per interaction
  until the clock is capped.  Every site is the responder of one block, so at
  the end every clock is `kappa`; a capped site that later acts as initiator
  keeps its clock and is rewritten Detect.

The claims about signal direction, non-re-pollution,
leader births and monotonicity of capped clocks were all checked against the
literal transition; none of them is false on this carrier.
-/


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


/-! ## The driver word -/


/-- Schedule every edge of `L` exactly `R` times in a row, in list order. -/
def modeRepeatEach {n : Nat} (R : Nat) : List (Fin n) → DetSchedule n
  | [] => []
  | e :: es => List.replicate R e ++ modeRepeatEach R es


theorem modeRepeatEach_length {n : Nat} (R : Nat) (L : List (Fin n)) :
    (modeRepeatEach R L).length = L.length * R := by
  induction L with
  | nil => simp [modeRepeatEach]
  | cons e es ih =>
      rw [modeRepeatEach, List.length_append, List.length_replicate, ih,
        List.length_cons, Nat.succ_mul]
      omega


/-- Block length of the H6 driver: `R = 8 * kappa * 2^psi`. -/
def modeDriverReps (psi kappa : Nat) : Nat :=
  8 * kappa * 2 ^ psi


/-- One clockwise sweep over `seqR ring 0 n`, each edge repeated `R` times. -/
def modeDriverSweep {n : Nat} (ring : DirectedRing n) (R : Nat) :
    DetSchedule n :=
  modeRepeatEach R (PPL.seqR ring ⟨0, ring.hn⟩ n)


/-- The deterministic H6 driver: two repeated-edge clockwise sweeps.  The
first drains every reset signal, the second raises every clock to `kappa`. -/
def lemma16ModeDriver {n : Nat} (ring : DirectedRing n)
    (psi kappa : Nat) : DetSchedule n :=
  modeDriverSweep ring (modeDriverReps psi kappa) ++
    modeDriverSweep ring (modeDriverReps psi kappa)


theorem lemma16ModeDriver_length {n : Nat} (ring : DirectedRing n)
    (psi kappa : Nat) :
    (lemma16ModeDriver ring psi kappa).length = lemma16H6 n psi kappa := by
  have hseq : (PPL.seqR ring ⟨0, ring.hn⟩ n).length = n := by
    simp [PPL.seqR]
  unfold lemma16ModeDriver modeDriverSweep
  rw [List.length_append, modeRepeatEach_length, hseq]
  unfold modeDriverReps lemma16H6
  have h1 : 8 * kappa * 2 ^ psi = 8 * (kappa * 2 ^ psi) :=
    Nat.mul_assoc 8 kappa (2 ^ psi)
  have h2 : 16 * n * kappa * 2 ^ psi = 16 * (n * (kappa * 2 ^ psi)) := by
    rw [Nat.mul_assoc 16 n kappa, Nat.mul_assoc 16 (n * kappa),
      Nat.mul_assoc n kappa]
  have h3 : n * (8 * (kappa * 2 ^ psi)) = 8 * (n * (kappa * 2 ^ psi)) :=
    Nat.mul_left_comm n 8 (kappa * 2 ^ psi)
  rw [h1, h2, h3]
  omega


/-! ## Generic run bookkeeping -/


private theorem md_runPPL_append
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    runPPL ring C (u ++ v) =
      runPPL ring (runPPL ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append, runPPL, runPopulationSchedule]
      exact ih (C := PopulationProtocol.step (PPL.protocol psi kappa) ring C e)


private theorem md_runPPL_cons
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) (w : DetSchedule n) :
    runPPL ring C (e :: w) =
      runPPL ring
        (PopulationProtocol.step (PPL.protocol psi kappa) ring C e) w :=
  rfl


private theorem md_runPPL_nil
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    runPPL ring C [] = C :=
  rfl


private theorem md_rightNeighbor_ne_self
    {n : Nat} (ring : DirectedRing n)
    (hn2 : 2 ≤ n) (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega


/-- Every configuration has no leader. -/
def ModeLeaderless {n psi kappa : Nat} (C : Config n psi kappa) : Prop :=
  ∀ i : Fin n, (C i).leader = false


/-- Every reset signal is zero. -/
def ModeSignalFree {n psi kappa : Nat} (C : Config n psi kappa) : Prop :=
  ∀ i : Fin n, (C i).signalR.val = 0


/-- One literal step from an `AllLivePeaceful` configuration either reaches
`C_PB` or is leaderless: any leader present after the step certifies `C_PB`
because peacefulness of live bullets is preserved. -/
private theorem md_step_cpb_or_leaderless
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (X : Config n psi kappa) (e : Fin n)
    (hpeace : AllLivePeaceful ring X) :
    PPL.CPB ring
        (PopulationProtocol.step (PPL.protocol psi kappa) ring X e) ∨
      ModeLeaderless
        (PopulationProtocol.step (PPL.protocol psi kappa) ring X e) := by
  let Y : Config n psi kappa :=
    PopulationProtocol.step (PPL.protocol psi kappa) ring X e
  by_cases h : ∃ i : Fin n, (Y i).leader = true
  · left
    exact cpb_of_allLivePeaceful_hasLeader ring Y
      (allLivePeaceful_step_closed hn3 hpsi ring X e hpeace) h
  · right
    intro i
    cases hi : (Y i).leader with
    | false => rfl
    | true => exact absurd ⟨i, hi⟩ h


/-- The four DetermineMode-owned fields of the two scheduled endpoints after
one literal step are exactly those written by `determineMode`; every other
site is unchanged. -/
private theorem md_step_fields
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (X : Config n psi kappa) (e : Fin n) :
    let j := ring.rightNeighbor e
    let d := PPL.determineMode (X e) (X j)
    let Y := PopulationProtocol.step (PPL.protocol psi kappa) ring X e
    ((Y e).signalR = d.1.signalR ∧ (Y e).hits = d.1.hits ∧
        (Y e).clock = d.1.clock ∧ (Y e).mode = d.1.mode) ∧
      ((Y j).signalR = d.2.signalR ∧ (Y j).hits = d.2.hits ∧
        (Y j).clock = d.2.clock ∧ (Y j).mode = d.2.mode) ∧
      (∀ k : Fin n, k ≠ e → k ≠ j → Y k = X k) := by
  dsimp only
  have hs := PPL.Modes.SignalLineage.postDetermineModeSignalStable hpsi
    (X e) (X (ring.rightNeighbor e))
  have hc := PPL.Probability.clockSuffixPairProjection hpsi
    (X e) (X (ring.rightNeighbor e))
  have hm := PPL.Convergence.ConstructCoupling.postDetermineModeModeStable hpsi
    (X e) (X (ring.rightNeighbor e))
  dsimp only at hs hc hm
  have hne : ring.rightNeighbor e ≠ e :=
    md_rightNeighbor_ne_self ring (by omega) e
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa [PopulationProtocol.step, PPL.protocol, PPL.transition, hpsi]
      using hs.1
  · simpa [PopulationProtocol.step, PPL.protocol, PPL.transition, hpsi]
      using hs.2.1
  · simpa [PopulationProtocol.step, PPL.protocol, PPL.transition, hpsi]
      using hc.1
  · simpa [PopulationProtocol.step, PPL.protocol, PPL.transition, hpsi]
      using hm.1
  · simpa [PopulationProtocol.step, PPL.protocol, PPL.transition, hpsi, hne]
      using hs.2.2.1
  · simpa [PopulationProtocol.step, PPL.protocol, PPL.transition, hpsi, hne]
      using hs.2.2.2
  · simpa [PopulationProtocol.step, PPL.protocol, PPL.transition, hpsi, hne]
      using hc.2.2.1
  · simpa [PopulationProtocol.step, PPL.protocol, PPL.transition, hpsi, hne]
      using hm.2
  · intro k hke hkj
    simp [PopulationProtocol.step, PPL.protocol, hke, hkj]
    try rfl


/-! ## Local DetermineMode facts -/


/-- Drain potential of a responder in sweep 1: zero iff the reset signal is
zero; otherwise `signalR * psi - min hits (psi - 1)`, which counts the
interactions a leaderless signal-free initiator still needs. -/
def modeSignalPot {psi kappa : Nat} (q : PPL.State psi kappa) : Nat :=
  if q.signalR.val = 0 then 0
  else q.signalR.val * psi - min q.hits.val (psi - 1)


/-- Clock-rise potential of a responder in sweep 2: zero iff the clock is at
the cap; otherwise `(kappa - clock) * psi - min hits (psi - 1)`. -/
def modeClockPot {psi kappa : Nat} (q : PPL.State psi kappa) : Nat :=
  if q.clock.val = kappa then 0
  else (kappa - q.clock.val) * psi - min q.hits.val (psi - 1)


private theorem md_min_eq (a b : Nat) : Nat.min a b = min a b := rfl


private theorem md_succ_mul_split (s psi : Nat) (hs : 0 < s) :
    s * psi = (s - 1) * psi + psi := by
  rw [← Nat.succ_mul]
  congr 1
  omega


theorem modeSignalPot_le {psi kappa : Nat} (q : PPL.State psi kappa) :
    modeSignalPot q ≤ kappa * psi := by
  unfold modeSignalPot
  have hs : q.signalR.val ≤ kappa := Nat.lt_succ_iff.mp q.signalR.isLt
  have hm : q.signalR.val * psi ≤ kappa * psi := Nat.mul_le_mul_right psi hs
  split <;> omega


theorem modeClockPot_le {psi kappa : Nat} (q : PPL.State psi kappa) :
    modeClockPot q ≤ kappa * psi := by
  unfold modeClockPot
  have hm : (kappa - q.clock.val) * psi ≤ kappa * psi :=
    Nat.mul_le_mul_right psi (Nat.sub_le _ _)
  split <;> omega


theorem signal_zero_of_modeSignalPot_zero {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (q : PPL.State psi kappa)
    (h : modeSignalPot q = 0) : q.signalR.val = 0 := by
  unfold modeSignalPot at h
  by_cases hs : q.signalR.val = 0
  · exact hs
  · rw [if_neg hs] at h
    have hsplit := md_succ_mul_split q.signalR.val psi (by omega)
    have hmin : min q.hits.val (psi - 1) ≤ psi - 1 := Nat.min_le_right _ _
    omega


theorem clock_cap_of_modeClockPot_zero {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (q : PPL.State psi kappa)
    (h : modeClockPot q = 0) : q.clock.val = kappa := by
  unfold modeClockPot at h
  by_cases hc : q.clock.val = kappa
  · exact hc
  · rw [if_neg hc] at h
    have hle : q.clock.val ≤ kappa := Nat.lt_succ_iff.mp q.clock.isLt
    have hsplit := md_succ_mul_split (kappa - q.clock.val) psi (by omega)
    have hmin : min q.hits.val (psi - 1) ≤ psi - 1 := Nat.min_le_right _ _
    omega


/-- DetermineMode always writes the initiator's reset signal to zero. -/
private theorem md_dm_left_signal_zero {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : PPL.State psi kappa) :
    (PPL.determineMode l r).1.signalR.val = 0 := by
  have h := PPL.Modes.SignalLineage.determineModeSignalProjection hpsi l r
  dsimp only at h
  exact h.1


/-- Sweep-1 step: with a leaderless initiator of signal zero, the responder's
drain potential drops by one (or stays zero). -/
private theorem md_dm_signalPot_drop {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : PPL.State psi kappa)
    (hlead : l.leader = false) (hls : l.signalR.val = 0) :
    modeSignalPot (PPL.determineMode l r).2 ≤ modeSignalPot r - 1 := by
  have h := PPL.Modes.SignalLineage.determineModeSignalProjection hpsi l r
  dsimp only at h
  have hc := h.2.2
  unfold PPL.Modes.SignalLineage.DetermineModeResponderCases at hc
  have harm : PPL.Modes.SignalLineage.armedSignalVal l = 0 := by
    simp [PPL.Modes.SignalLineage.armedSignalVal, hlead, hls]
  unfold PPL.Modes.SignalLineage.bumpedHitsVal at hc
  dsimp only at hc
  rw [harm] at hc
  rw [md_min_eq] at hc
  have hhle : r.hits.val ≤ psi := Nat.lt_succ_iff.mp r.hits.isLt
  rcases hc with ⟨_, hr0, hq0, _⟩ | ⟨hpos, _⟩ | ⟨hrpos, hqs, hqh⟩
  · simp [modeSignalPot, hr0, hq0]
  · omega
  · have hsplit := md_succ_mul_split r.signalR.val psi hrpos
    unfold modeSignalPot
    rw [if_neg (by omega : ¬ r.signalR.val = 0)]
    by_cases hb : min (r.hits.val + 1) psi = psi
    · rw [if_pos hb] at hqs hqh
      rw [hqs, hqh]
      split
      · omega
      · have hmin : min r.hits.val (psi - 1) ≤ psi - 1 := Nat.min_le_right _ _
        have h0 : min 0 (psi - 1) = 0 := Nat.zero_min _
        rw [h0]
        omega
    · rw [if_neg hb] at hqs hqh
      rw [hqs, hqh]
      rw [if_neg (by omega : ¬ r.signalR.val = 0)]
      omega


/-- Sweep-2 step (no-signal branch, lines 46--50) from a leaderless
signal-free pair. -/
private theorem md_dm_noSignal {psi kappa : Nat}
    (_hpsi : 2 ≤ psi) (l r : PPL.State psi kappa)
    (hlead : l.leader = false)
    (hls : l.signalR.val = 0) (hrs : r.signalR.val = 0) :
    let d := PPL.determineMode l r
    d.1.clock = l.clock ∧
      d.1.mode = (l.clock.val == kappa) ∧
      d.2.signalR.val = 0 ∧
      d.2.mode = (d.2.clock.val == kappa) ∧
      (min (r.hits.val + 1) psi = psi →
        d.2.clock.val = min (r.clock.val + 1) kappa ∧ d.2.hits.val = 0) ∧
      (min (r.hits.val + 1) psi ≠ psi →
        d.2.clock = r.clock ∧ d.2.hits.val = min (r.hits.val + 1) psi) := by
  have hls0 : l.signalR = (0 : Fin (kappa + 1)) := by
    apply Fin.ext
    simpa using hls
  have hrs0 : r.signalR = (0 : Fin (kappa + 1)) := by
    apply Fin.ext
    simpa using hrs
  by_cases hhit : Nat.min (r.hits.val + 1) psi = psi
  · simp only [PPL.determineMode, hlead]
    unfoldFinishModes
    simp [hls0, hrs0, hhit] <;> omega
  · simp only [PPL.determineMode, hlead]
    unfoldFinishModes
    simp [hls0, hrs0, hhit] <;> omega


/-- Sweep-2 responder: the clock potential drops by one (or stays zero). -/
private theorem md_dm_clockPot_drop {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : PPL.State psi kappa)
    (hlead : l.leader = false)
    (hls : l.signalR.val = 0) (hrs : r.signalR.val = 0) :
    modeClockPot (PPL.determineMode l r).2 ≤ modeClockPot r - 1 := by
  have h := md_dm_noSignal hpsi l r hlead hls hrs
  dsimp only at h
  obtain ⟨_, _, _, _, hhit, hno⟩ := h
  have hcle : r.clock.val ≤ kappa := Nat.lt_succ_iff.mp r.clock.isLt
  have hhle : r.hits.val ≤ psi := Nat.lt_succ_iff.mp r.hits.isLt
  unfold modeClockPot
  by_cases hb : min (r.hits.val + 1) psi = psi
  · obtain ⟨hc', hh'⟩ := hhit hb
    rw [hc', hh']
    by_cases hck : r.clock.val = kappa
    · rw [if_pos (by omega : min (r.clock.val + 1) kappa = kappa)]
      omega
    · rw [if_neg hck]
      have hsplit := md_succ_mul_split (kappa - r.clock.val) psi (by omega)
      have hmin : min r.hits.val (psi - 1) = psi - 1 := by omega
      have h0 : min 0 (psi - 1) = 0 := Nat.zero_min _
      have hk : kappa - min (r.clock.val + 1) kappa = kappa - r.clock.val - 1 := by
        omega
      split
      · omega
      · rw [h0, hk]
        omega
  · obtain ⟨hc', hh'⟩ := hno hb
    rw [hc', hh']
    split
    · omega
    · have hmin1 : min (min (r.hits.val + 1) psi) (psi - 1) =
          min r.hits.val (psi - 1) + 1 := by
        omega
      rw [hmin1]
      omega


/-! ## Sweep 1: one repeated edge drains both endpoints -/


/-- Repeated drain of one edge whose initiator already carries no signal. -/
private theorem md_drain_tail
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (e : Fin n) :
    ∀ (m : Nat) (X : Config n psi kappa) (K : Nat),
      AllLivePeaceful ring X →
      ModeLeaderless X →
      (X e).signalR.val = 0 →
      modeSignalPot (X (ring.rightNeighbor e)) ≤ K →
      let Y := runPPL ring X (List.replicate m e)
      PPL.CPB ring Y ∨
        (ModeLeaderless Y ∧ (Y e).signalR.val = 0 ∧
          modeSignalPot (Y (ring.rightNeighbor e)) ≤ K - m ∧
          ∀ k : Fin n, k ≠ e → k ≠ ring.rightNeighbor e → Y k = X k) := by
  intro m
  induction m with
  | zero =>
      intro X K _ hlead he hK
      right
      exact ⟨hlead, he,
        (show modeSignalPot (X (ring.rightNeighbor e)) ≤ K - 0 by omega),
        fun _ _ _ => rfl⟩
  | succ m ih =>
      intro X K hpeace hlead he hK
      dsimp only
      rw [List.replicate_succ, md_runPPL_cons]
      let X1 : Config n psi kappa :=
        PopulationProtocol.step (PPL.protocol psi kappa) ring X e
      have hpeace1 : AllLivePeaceful ring X1 :=
        allLivePeaceful_step_closed hn3 hpsi ring X e hpeace
      rcases md_step_cpb_or_leaderless hn3 hpsi ring X e hpeace with hcpb | hlead1
      · left
        exact cpb_run_closed hn3 hpsi ring X1 _ hcpb
      · have hf := md_step_fields hn3 hpsi ring X e
        dsimp only at hf
        obtain ⟨⟨hs1, _, _, _⟩, ⟨hs2, hh2, _, _⟩, hoth⟩ := hf
        have he1 : (X1 e).signalR.val = 0 := by
          show (PopulationProtocol.step (PPL.protocol psi kappa) ring X e e).signalR.val = 0
          rw [hs1]
          exact md_dm_left_signal_zero hpsi _ _
        have hK1 : modeSignalPot (X1 (ring.rightNeighbor e)) ≤ K - 1 := by
          have hdrop := md_dm_signalPot_drop hpsi (X e) (X (ring.rightNeighbor e))
            (hlead e) he
          have heq : modeSignalPot (X1 (ring.rightNeighbor e)) =
              modeSignalPot (PPL.determineMode (X e) (X (ring.rightNeighbor e))).2 := by
            show modeSignalPot (PopulationProtocol.step (PPL.protocol psi kappa)
              ring X e (ring.rightNeighbor e)) = _
            unfold modeSignalPot
            rw [hs2, hh2]
          omega
        have hrec := ih X1 (K - 1) hpeace1 hlead1 he1 hK1
        dsimp only at hrec
        rcases hrec with hcpb | ⟨hl, hy, hpot, hk⟩
        · left
          exact hcpb
        · right
          refine ⟨hl, hy, Nat.le_trans hpot (by omega), ?_⟩
          intro k hke hkj
          rw [hk k hke hkj]
          exact hoth k hke hkj


/-- One full sweep-1 block: `R ≥ psi * kappa + 1` repetitions of edge `e`
clear the reset signal at both endpoints (unless `C_PB` is reached). -/
private theorem md_drain_block
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (e : Fin n) (R : Nat)
    (hR : kappa * psi + 1 ≤ R)
    (X : Config n psi kappa)
    (hpeace : AllLivePeaceful ring X) :
    let Y := runPPL ring X (List.replicate R e)
    PPL.CPB ring Y ∨
      (ModeLeaderless Y ∧ (Y e).signalR.val = 0 ∧
        (Y (ring.rightNeighbor e)).signalR.val = 0 ∧
        ∀ k : Fin n, k ≠ e → k ≠ ring.rightNeighbor e → Y k = X k) := by
  dsimp only
  obtain ⟨m, rfl⟩ : ∃ m, R = m + 1 := ⟨R - 1, by omega⟩
  rw [List.replicate_succ, md_runPPL_cons]
  let X1 : Config n psi kappa :=
    PopulationProtocol.step (PPL.protocol psi kappa) ring X e
  have hpeace1 : AllLivePeaceful ring X1 :=
    allLivePeaceful_step_closed hn3 hpsi ring X e hpeace
  rcases md_step_cpb_or_leaderless hn3 hpsi ring X e hpeace with hcpb | hlead1
  · left
    exact cpb_run_closed hn3 hpsi ring X1 _ hcpb
  · have hf := md_step_fields hn3 hpsi ring X e
    dsimp only at hf
    obtain ⟨⟨hs1, _, _, _⟩, _, hoth⟩ := hf
    have he1 : (X1 e).signalR.val = 0 := by
      show (PopulationProtocol.step (PPL.protocol psi kappa) ring X e e).signalR.val = 0
      rw [hs1]
      exact md_dm_left_signal_zero hpsi _ _
    have hrec := md_drain_tail hn3 hpsi ring e m X1 (kappa * psi)
      hpeace1 hlead1 he1 (modeSignalPot_le _)
    dsimp only at hrec
    rcases hrec with hcpb | ⟨hl, hy, hpot, hk⟩
    · left
      exact hcpb
    · right
      refine ⟨hl, hy, ?_, ?_⟩
      · apply signal_zero_of_modeSignalPot_zero hpsi
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hpot (by omega))
      · intro k hke hkj
        rw [hk k hke hkj]
        exact hoth k hke hkj


/-- Sweep 1 over an arbitrary edge list: every site that is the responder of
some processed edge, or was already signal-free, ends signal-free. -/
private theorem md_drain_sweep
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (R : Nat)
    (hR : kappa * psi + 1 ≤ R) :
    ∀ (L : List (Fin n)) (X : Config n psi kappa),
      AllLivePeaceful ring X →
      ModeLeaderless X →
      let Y := runPPL ring X (modeRepeatEach R L)
      PPL.CPB ring Y ∨
        (ModeLeaderless Y ∧
          ∀ x : Fin n,
            ((∃ e, e ∈ L ∧ ring.rightNeighbor e = x) ∨
                (X x).signalR.val = 0) →
              (Y x).signalR.val = 0) := by
  intro L
  induction L with
  | nil =>
      intro X _ hlead
      right
      refine ⟨hlead, ?_⟩
      intro x hx
      rcases hx with ⟨e, he, _⟩ | hx
      · cases he
      · exact hx
  | cons e es ih =>
      intro X hpeace hlead
      dsimp only
      rw [modeRepeatEach, md_runPPL_append]
      have hb := md_drain_block hn3 hpsi ring e R hR X hpeace
      dsimp only at hb
      let X1 : Config n psi kappa := runPPL ring X (List.replicate R e)
      rcases hb with hcpb | ⟨hl1, hz1, hz2, hoth⟩
      · left
        exact cpb_run_closed hn3 hpsi ring X1 _ hcpb
      · have hpeace1 : AllLivePeaceful ring X1 :=
          allLivePeaceful_run_closed hn3 hpsi ring X _ hpeace
        have hrec := ih X1 hpeace1 hl1
        dsimp only at hrec
        rcases hrec with hcpb | ⟨hl, hall⟩
        · left
          exact hcpb
        · right
          refine ⟨hl, ?_⟩
          intro x hx
          apply hall x
          rcases hx with ⟨e', he', hex⟩ | hx
          · rcases List.mem_cons.mp he' with rfl | hes
            · right
              rw [← hex]
              exact hz2
            · left
              exact ⟨e', hes, hex⟩
          · right
            by_cases hxe : x = e
            · subst x
              exact hz1
            · by_cases hxj : x = ring.rightNeighbor e
              · subst x
                exact hz2
              · show (runPPL ring X (List.replicate R e) x).signalR.val = 0
                rw [hoth x hxe hxj]
                exact hx


/-! ## Sweep 2: one repeated edge caps the responder clock -/


/-- A site is finished for sweep 2: its clock is capped and it stores Detect. -/
def ModeCappedDetect {psi kappa : Nat} (q : PPL.State psi kappa) : Prop :=
  q.clock.val = kappa ∧ q.mode = true


/-- Responder bookkeeping carried through a sweep-2 block: either the site is
already finished or its clock potential is positive.  Any sweep-2 interaction
establishes this for its responder. -/
def ModeRiseOK {psi kappa : Nat} (q : PPL.State psi kappa) : Prop :=
  ModeCappedDetect q ∨ 0 < modeClockPot q


private theorem md_rise_step
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (e : Fin n)
    (X : Config n psi kappa)
    (hlead : ModeLeaderless X) (hsf : ModeSignalFree X) :
    let Y := PopulationProtocol.step (PPL.protocol psi kappa) ring X e
    let j := ring.rightNeighbor e
    ModeSignalFree Y ∧
      modeClockPot (Y j) ≤ modeClockPot (X j) - 1 ∧
      ModeRiseOK (Y j) ∧
      (ModeCappedDetect (X e) → ModeCappedDetect (Y e)) ∧
      (∀ k : Fin n, k ≠ e → k ≠ j → Y k = X k) := by
  dsimp only
  have hf := md_step_fields hn3 hpsi ring X e
  dsimp only at hf
  obtain ⟨⟨hs1, _, hc1, hm1⟩, ⟨hs2, hh2, hc2, hm2⟩, hoth⟩ := hf
  have hd := md_dm_noSignal hpsi (X e) (X (ring.rightNeighbor e))
    (hlead e) (hsf e) (hsf _)
  dsimp only at hd
  obtain ⟨hdc1, hdm1, hds2, hdm2, _, _⟩ := hd
  have hne : ring.rightNeighbor e ≠ e :=
    md_rightNeighbor_ne_self ring (by omega) e
  have hdrop := md_dm_clockPot_drop hpsi (X e) (X (ring.rightNeighbor e))
    (hlead e) (hsf e) (hsf _)
  have hpotY : modeClockPot (PopulationProtocol.step (PPL.protocol psi kappa)
      ring X e (ring.rightNeighbor e)) =
      modeClockPot (PPL.determineMode (X e) (X (ring.rightNeighbor e))).2 := by
    unfold modeClockPot
    rw [hc2, hh2]
  refine ⟨?_, ?_, ?_, ?_, hoth⟩
  · intro k
    by_cases hke : k = e
    · subst k
      rw [hs1]
      exact md_dm_left_signal_zero hpsi _ _
    · by_cases hkj : k = ring.rightNeighbor e
      · subst k
        rw [hs2]
        exact hds2
      · rw [hoth k hke hkj]
        exact hsf k
  · rw [hpotY]
    exact hdrop
  · by_cases hz : modeClockPot (PopulationProtocol.step (PPL.protocol psi kappa)
        ring X e (ring.rightNeighbor e)) = 0
    · left
      have hcap := clock_cap_of_modeClockPot_zero hpsi _ hz
      refine ⟨hcap, ?_⟩
      rw [hm2, hdm2, ← hc2, hcap]
      simp
    · right
      omega
  · intro hgood
    obtain ⟨hcl, _⟩ := hgood
    refine ⟨?_, ?_⟩
    · rw [hc1, hdc1]
      exact hcl
    · rw [hm1, hdm1, hcl]
      simp


/-- Repeated sweep-2 steps on one edge. -/
private theorem md_rise_tail
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (e : Fin n) :
    ∀ (m : Nat) (X : Config n psi kappa) (K : Nat),
      AllLivePeaceful ring X →
      ModeLeaderless X →
      ModeSignalFree X →
      modeClockPot (X (ring.rightNeighbor e)) ≤ K →
      let Y := runPPL ring X (List.replicate m e)
      PPL.CPB ring Y ∨
        (ModeLeaderless Y ∧ ModeSignalFree Y ∧
          modeClockPot (Y (ring.rightNeighbor e)) ≤ K - m ∧
          ((0 < m ∨ ModeRiseOK (X (ring.rightNeighbor e))) →
            ModeRiseOK (Y (ring.rightNeighbor e))) ∧
          (ModeCappedDetect (X e) → ModeCappedDetect (Y e)) ∧
          ∀ k : Fin n, k ≠ e → k ≠ ring.rightNeighbor e → Y k = X k) := by
  intro m
  induction m with
  | zero =>
      intro X K _ hlead hsf hK
      right
      refine ⟨hlead, hsf,
        (show modeClockPot (X (ring.rightNeighbor e)) ≤ K - 0 by omega),
        ?_, fun h => h, fun _ _ _ => rfl⟩
      intro h
      rcases h with h | h
      · omega
      · exact h
  | succ m ih =>
      intro X K hpeace hlead hsf hK
      dsimp only
      rw [List.replicate_succ, md_runPPL_cons]
      let X1 : Config n psi kappa :=
        PopulationProtocol.step (PPL.protocol psi kappa) ring X e
      have hpeace1 : AllLivePeaceful ring X1 :=
        allLivePeaceful_step_closed hn3 hpsi ring X e hpeace
      rcases md_step_cpb_or_leaderless hn3 hpsi ring X e hpeace with hcpb | hlead1
      · left
        exact cpb_run_closed hn3 hpsi ring X1 _ hcpb
      · have hs := md_rise_step hn3 hpsi ring e X hlead hsf
        dsimp only at hs
        obtain ⟨hsf1, hdrop, hok1, hgood1, hoth⟩ := hs
        have hrec := ih X1 (K - 1) hpeace1 hlead1 hsf1
          (Nat.le_trans hdrop (by omega))
        dsimp only at hrec
        rcases hrec with hcpb | ⟨hl, hsfY, hpot, hok, hgood, hk⟩
        · left
          exact hcpb
        · right
          refine ⟨hl, hsfY, Nat.le_trans hpot (by omega), ?_, ?_, ?_⟩
          · intro _
            exact hok (Or.inr hok1)
          · intro h
            exact hgood (hgood1 h)
          · intro k hke hkj
            rw [hk k hke hkj]
            exact hoth k hke hkj


/-- One full sweep-2 block: `R ≥ psi * kappa + 1` repetitions cap and Detect
the responder, keep a finished initiator finished, and keep the run
leaderless and signal-free (unless `C_PB` is reached). -/
private theorem md_rise_block
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (e : Fin n) (R : Nat)
    (hR : kappa * psi + 1 ≤ R)
    (X : Config n psi kappa)
    (hpeace : AllLivePeaceful ring X)
    (hlead : ModeLeaderless X)
    (hsf : ModeSignalFree X) :
    let Y := runPPL ring X (List.replicate R e)
    PPL.CPB ring Y ∨
      (ModeLeaderless Y ∧ ModeSignalFree Y ∧
        ModeCappedDetect (Y (ring.rightNeighbor e)) ∧
        (ModeCappedDetect (X e) → ModeCappedDetect (Y e)) ∧
        ∀ k : Fin n, k ≠ e → k ≠ ring.rightNeighbor e → Y k = X k) := by
  dsimp only
  have hrec := md_rise_tail hn3 hpsi ring e R X (kappa * psi)
    hpeace hlead hsf (modeClockPot_le _)
  dsimp only at hrec
  rcases hrec with hcpb | ⟨hl, hsfY, hpot, hok, hgood, hk⟩
  · left
    exact hcpb
  · right
    refine ⟨hl, hsfY, ?_, hgood, hk⟩
    rcases hok (Or.inl (by omega)) with h | h
    · exact h
    · omega


/-- Sweep 2 over an arbitrary edge list. -/
private theorem md_rise_sweep
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (R : Nat)
    (hR : kappa * psi + 1 ≤ R) :
    ∀ (L : List (Fin n)) (X : Config n psi kappa),
      AllLivePeaceful ring X →
      ModeLeaderless X →
      ModeSignalFree X →
      let Y := runPPL ring X (modeRepeatEach R L)
      PPL.CPB ring Y ∨
        (ModeLeaderless Y ∧ ModeSignalFree Y ∧
          ∀ x : Fin n,
            ((∃ e, e ∈ L ∧ ring.rightNeighbor e = x) ∨
                ModeCappedDetect (X x)) →
              ModeCappedDetect (Y x)) := by
  intro L
  induction L with
  | nil =>
      intro X _ hlead hsf
      right
      refine ⟨hlead, hsf, ?_⟩
      intro x hx
      rcases hx with ⟨e, he, _⟩ | hx
      · cases he
      · exact hx
  | cons e es ih =>
      intro X hpeace hlead hsf
      dsimp only
      rw [modeRepeatEach, md_runPPL_append]
      have hb := md_rise_block hn3 hpsi ring e R hR X hpeace hlead hsf
      dsimp only at hb
      let X1 : Config n psi kappa := runPPL ring X (List.replicate R e)
      rcases hb with hcpb | ⟨hl1, hsf1, hg2, hg1, hoth⟩
      · left
        exact cpb_run_closed hn3 hpsi ring X1 _ hcpb
      · have hpeace1 : AllLivePeaceful ring X1 :=
          allLivePeaceful_run_closed hn3 hpsi ring X _ hpeace
        have hrec := ih X1 hpeace1 hl1 hsf1
        dsimp only at hrec
        rcases hrec with hcpb | ⟨hl, hsfY, hall⟩
        · left
          exact hcpb
        · right
          refine ⟨hl, hsfY, ?_⟩
          intro x hx
          apply hall x
          rcases hx with ⟨e', he', hex⟩ | hx
          · rcases List.mem_cons.mp he' with rfl | hes
            · right
              rw [← hex]
              exact hg2
            · left
              exact ⟨e', hes, hex⟩
          · right
            by_cases hxe : x = e
            · subst x
              exact hg1 hx
            · by_cases hxj : x = ring.rightNeighbor e
              · subst x
                exact hg2
              · show ModeCappedDetect (runPPL ring X (List.replicate R e) x)
                rw [hoth x hxe hxj]
                exact hx


/-! ## Coverage of the clockwise sweep and the endpoint predicates -/


/-- Every site is the responder of some edge of `seqR ring 0 n`. -/
theorem seqR_zero_covers_responders {n : Nat} (ring : DirectedRing n)
    (x : Fin n) :
    ∃ e, e ∈ PPL.seqR ring ⟨0, ring.hn⟩ n ∧ ring.rightNeighbor e = x := by
  have hn := ring.hn
  by_cases hx : x.val = 0
  · let k : Fin n := ⟨n - 1, by omega⟩
    refine ⟨PPL.shiftRight ring ⟨0, ring.hn⟩ k.val,
      List.mem_ofFn.mpr ⟨k, rfl⟩, ?_⟩
    apply Fin.ext
    show ((0 + (n - 1)) % n + 1) % n = x.val
    rw [Nat.zero_add, Nat.mod_eq_of_lt (show n - 1 < n by omega),
      Nat.sub_add_cancel (show 1 ≤ n by omega), Nat.mod_self]
    omega
  · let k : Fin n := ⟨x.val - 1, by omega⟩
    refine ⟨PPL.shiftRight ring ⟨0, ring.hn⟩ k.val,
      List.mem_ofFn.mpr ⟨k, rfl⟩, ?_⟩
    apply Fin.ext
    show ((0 + (x.val - 1)) % n + 1) % n = x.val
    rw [Nat.zero_add, Nat.mod_eq_of_lt (show x.val - 1 < n by omega),
      Nat.sub_add_cancel (show 1 ≤ x.val by omega), Nat.mod_eq_of_lt x.isLt]


private theorem md_foldl_and_true_of_all
    (xs : List Bool)
    (hall : ∀ b, b ∈ xs → b = true) :
    xs.foldl (fun acc b => acc && b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      have hb : b = true :=
        hall b (by simp)
      rw [List.foldl_cons, hb, Bool.true_and]
      exact
        ih
          (fun y hy =>
            hall y (by simp [hy]))


private theorem md_signalFreeB_true
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (hzero : ∀ i : Fin n, (C i).signalR.val = 0) :
    PPL.Modes.Lemma6.signalFreeB C = true := by
  unfold PPL.Modes.Lemma6.signalFreeB PPL.Modes.Lemma6.allAgentsB
  apply md_foldl_and_true_of_all
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, rfl⟩ := hb
  simp [hzero i]


private theorem md_allDetectB_true
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (hdet : ∀ i : Fin n, (C i).mode = true) :
    PPL.Modes.Lemma6.allDetectB C = true := by
  unfold PPL.Modes.Lemma6.allDetectB PPL.Modes.Lemma6.allAgentsB
  apply md_foldl_and_true_of_all
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, rfl⟩ := hb
  simp [hdet i]


/-! ## Headline -/


/-- The explicit driver works: for every `AllLivePeaceful` configuration, the
run of `lemma16ModeDriver ring psi kappa` ends in `C_PB` or in
`DetectReadyCapped`.

Proof: sweep 1 (`md_drain_sweep`) either reaches `C_PB` (closed thereafter)
or ends leaderless and signal-free, since every site is the responder of an
edge of `seqR ring 0 n`; sweep 2 (`md_rise_sweep`) then either reaches `C_PB`
or ends leaderless, signal-free, with every site capped and Detect.
`AllLivePeaceful` is carried by `allLivePeaceful_run_closed`.
-/
theorem lemma16ModeDriver_spec
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 0 < kappa)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hpeace : AllLivePeaceful ring C) :
    PPL.CPB ring
        (runPPL ring C (lemma16ModeDriver ring psi kappa)) ∨
      DetectReadyCapped ring
        (runPPL ring C (lemma16ModeDriver ring psi kappa)) := by
  have hR : kappa * psi + 1 ≤ modeDriverReps psi kappa := by
    unfold modeDriverReps
    have h1 : psi + 1 ≤ 2 ^ psi := Nat.lt_two_pow_self
    have h2 : kappa * (psi + 1) ≤ kappa * 2 ^ psi := Nat.mul_le_mul_left kappa h1
    have h3 : kappa * (psi + 1) = kappa * psi + kappa := Nat.mul_succ kappa psi
    have h4 : 8 * kappa * 2 ^ psi = 8 * (kappa * 2 ^ psi) :=
      Nat.mul_assoc 8 kappa (2 ^ psi)
    omega
  let R := modeDriverReps psi kappa
  let L := PPL.seqR ring ⟨0, ring.hn⟩ n
  unfold lemma16ModeDriver modeDriverSweep
  by_cases hlead0 : ∃ i : Fin n, (C i).leader = true
  · left
    exact cpb_run_closed hn3 hpsi ring C _
      (cpb_of_allLivePeaceful_hasLeader ring C hpeace hlead0)
  rw [md_runPPL_append]
  have hlead0' : ModeLeaderless C := by
    intro i
    cases hi : (C i).leader with
    | false => rfl
    | true => exact absurd ⟨i, hi⟩ hlead0
  have h1 := md_drain_sweep hn3 hpsi ring R hR L C hpeace hlead0'
  dsimp only at h1
  let D : Config n psi kappa := runPPL ring C (modeRepeatEach R L)
  rcases h1 with hcpb | ⟨hlD, hzD⟩
  · left
    exact cpb_run_closed hn3 hpsi ring D _ hcpb
  have hsfD : ModeSignalFree D := by
    intro x
    exact hzD x (Or.inl (seqR_zero_covers_responders ring x))
  have hpeaceD : AllLivePeaceful ring D :=
    allLivePeaceful_run_closed hn3 hpsi ring C _ hpeace
  have h2 := md_rise_sweep hn3 hpsi ring R hR L D hpeaceD hlD hsfD
  dsimp only at h2
  rcases h2 with hcpb | ⟨hlE, hsfE, hgE⟩
  · left
    exact hcpb
  · right
    let E : Config n psi kappa := runPPL ring D (modeRepeatEach R L)
    have hg : ∀ x : Fin n, ModeCappedDetect (E x) := fun x =>
      hgE x (Or.inl (seqR_zero_covers_responders ring x))
    refine ⟨⟨allLivePeaceful_run_closed hn3 hpsi ring D _ hpeaceD,
      hlE, md_signalFreeB_true E hsfE,
      md_allDetectB_true E (fun x => (hg x).2)⟩, fun x => (hg x).1⟩


/-- **Deterministic H6 (Lemma-16 mode phase, possible convergence).**
For `3 ≤ n`, `2 ≤ psi`, `0 < kappa`, every configuration whose live bullets
are all peaceful has a scheduler word of length at most
`lemma16H6 n psi kappa` whose literal P_PL endpoint is `C_PB` or
`DetectReadyCapped`.  The witness is `lemma16ModeDriver ring psi kappa`
(two clockwise sweeps, every edge repeated `8 * kappa * 2^psi` times), whose
length is exactly `lemma16H6 n psi kappa`.
-/
theorem lemma16ModeForcingCapped_exists
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 0 < kappa)
    (ring : DirectedRing n) :
    ∀ C : Config n psi kappa,
      AllLivePeaceful ring C →
      ∃ word : DetSchedule n,
        word.length ≤ lemma16H6 n psi kappa ∧
          (PPL.CPB ring (runPPL ring C word) ∨
            DetectReadyCapped ring (runPPL ring C word)) := by
  intro C hpeace
  refine ⟨lemma16ModeDriver ring psi kappa, ?_, ?_⟩
  · rw [lemma16ModeDriver_length]
    exact Nat.le_refl _
  · exact lemma16ModeDriver_spec hn3 hpsi hkappa ring C hpeace


/-- The same statement under the paper parameter block used by the existing
H6 call sites (`kappa = 8 * modeC * psi`, `6 ≤ modeC`); the premise
`n ≤ 2^psi` is not needed and only kept for interface compatibility.
-/
theorem lemma16ModeForcingCapped_exists_paper
    {n psi kappa modeC : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hc : 6 ≤ modeC)
    (hkappa : kappa = 8 * modeC * psi)
    (_hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n) :
    ∀ C : Config n psi kappa,
      AllLivePeaceful ring C →
      ∃ word : DetSchedule n,
        word.length ≤ lemma16H6 n psi kappa ∧
          (PPL.CPB ring (runPPL ring C word) ∨
            DetectReadyCapped ring (runPPL ring C word)) := by
  have hpos : 0 < kappa := by
    rw [hkappa]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  exact lemma16ModeForcingCapped_exists hn3 hpsi hpos ring


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16ModeForcingCapped_exists
#print axioms PPL.Convergence.ReachCPB.lemma16ModeForcingCapped_exists_paper
#print axioms PPL.Convergence.ReachCPB.lemma16ModeDriver_spec
