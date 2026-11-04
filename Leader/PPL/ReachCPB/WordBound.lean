import Leader.PPL.Safety.PeacefulScan
import Leader.PPL.Modes.DetectionEntryCoverage
import Leader.PPL.Modes.DetectionEntryCounting
import Leader.PPL.Modes.DetectionEntryClockSplit
import Leader.PPL.Modes.EarlyLeaderStop
import Leader.PPL.Modes.SignalAbsorptionClosed
import Leader.PPL.Perfect
import Leader.PPL.TokenCorrectness.Ghost


/-!
# P_PL Lemma 16: reach C_PB


Truth audit.


The Theorem-1 consumer should target PPL.CPB ring C itself.  "A leader
appears" is only an internal success stop after the Lemma-15 cleanup has made
every live bullet peaceful.  Before that cleanup, a leader can coexist with
old non-peaceful live bullets, so leaderPresent alone is not the final target.


At the frozen horizons, the five charged blocks have coefficients


  1 + 8 + 1 + 1 + 1 = 12,


so the exact finite-word statement below gives failure at most 12/n.


There is one parameter-interface correction to the R10 headline.  The frozen
H6 is written for arbitrary kappa = c1*psi, but the currently proved Lemma-6
interface is specialized to kappa = 8*modeC*psi with 6 <= modeC.  Therefore
this file proves Lemma 16 under that exact current specialization.  For the
headline theorem one may either require c1 to be a multiple of 8 (choosing a
multiple of 16 is harmless and the canonical lower bound 32*C17+352 is itself
divisible by 16), or generalize Lemma 6 to arbitrary kappa.  No divisibility
assumption is hidden here.
-/


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


/-! ## Frozen horizons -/


def lemma16K (n : Nat) : Nat :=
  Nat.log2 n + 1


def lemma16L4 (psi : Nat) : Nat :=
  8 * psi * psi - 4 * psi


def lemma16H15 (n : Nat) : Nat :=
  2 * n * (2 * n + 4 * lemma16K n)


def lemma16H6 (n psi kappa : Nat) : Nat :=
  16 * n * kappa * 2 ^ psi


def lemma16HDist (n : Nat) : Nat :=
  2 * n * (1 + 4 * lemma16K n)


def lemma16HLast (n : Nat) : Nat :=
  2 * n * (n + 4 * lemma16K n)


def lemma16HToken (n psi : Nat) : Nat :=
  2 * n * (lemma16L4 psi + 4 * lemma16K n)


def lemma16Horizon (n psi kappa : Nat) : Nat :=
  lemma16H15 n +
    lemma16H6 n psi kappa +
    lemma16HDist n +
    lemma16HLast n +
    lemma16HToken n psi


/-! ## Endpoint predicates used by the forcing chain -/


def AllLivePeaceful
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  ∀ i : Fin n,
    (C i).bullet = (2 : Fin 3) →
      PPL.Peaceful ring C i


instance instDecidableAllLivePeaceful
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Decidable (AllLivePeaceful ring C) := by
  unfold AllLivePeaceful
  infer_instance


def allLivePeacefulB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (AllLivePeaceful ring C)


instance instDecidableCPBRun
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) :
    Decidable (PPL.CPB ring (PPL.Probability.runPPL ring C word)) :=
  PPL.instDecidableCPB ring
    (PPL.Probability.runPPL ring C word : Config n psi kappa)


def cpbB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (PPL.CPB ring C)


def DetectReady
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  AllLivePeaceful ring C ∧
    (∀ i : Fin n, (C i).leader = false) ∧
    PPL.Modes.Lemma6.signalFreeB C = true ∧
    PPL.Modes.Lemma6.allDetectB C = true


instance instDecidableDetectReady
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Decidable (DetectReady ring C) := by
  unfold DetectReady
  infer_instance


def DistReady
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  DetectReady ring C ∧
    ∀ i : Fin n,
      (C (ring.rightNeighbor i)).dist.val =
        ((C i).dist.val + 1) % (2 * psi)


instance instDecidableDistReady
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Decidable (DistReady ring C) := by
  unfold DistReady
  infer_instance


def LastReady
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  DistReady ring C ∧
    ∀ i : Fin n, (C i).last = false


instance instDecidableLastReady
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Decidable (LastReady ring C) := by
  unfold LastReady
  infer_instance


def detectOrCPBB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (PPL.CPB ring C ∨ DetectReady ring C)


def distOrCPBB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (PPL.CPB ring C ∨ DistReady ring C)


def lastOrCPBB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (PPL.CPB ring C ∨ LastReady ring C)


/-! ## Reaching C_PB and the finite-word numerator -/


def reachesCPB
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa → DetSchedule n → Bool
  | C, [] =>
      decide (PPL.CPB ring C)
  | C, e :: rest =>
      decide (PPL.CPB ring C) ||
        reachesCPB ring
          (PopulationProtocol.step
            (PPL.protocol psi kappa) ring C e)
          rest


def endpointFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (T : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word =>
      !good (PPL.Probability.runPPL ring C word))


def lemma16FailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma16Horizon n psi kappa)).countP
    (fun word => !(reachesCPB ring C word))


def Lemma16WordBound
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  n * lemma16FailureCount ring C ≤
    12 * n ^ lemma16Horizon n psi kappa


/-! ## Lemma-15 input, independent of the sibling file's declaration names -/


/-- Exact Nat interface needed from the sibling Lemma-15 development. -/
def Lemma16BulletSweepNatBound : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    n *
        endpointFailureCount ring
          (allLivePeacefulB ring) C
          (lemma16H15 n) ≤
      n ^ lemma16H15 n


/-! ## Precisely isolated deterministic remainders -/


/-- Paper C_det persistence: once leaderless, signal-free, all-Detect, and
all live bullets are peaceful, every later endpoint is either already C_PB
or is still in that same Detect-ready condition. -/
def Lemma16DetectPersistence : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (word : DetSchedule n),
    DetectReady ring C →
      PPL.CPB ring (PPL.Probability.runPPL ring C word) ∨
        DetectReady ring (PPL.Probability.runPPL ring C word)


/-- If Detect-ready is not already dist-consistent, one current directed edge
witnesses the inconsistency.  Arbitrary interleavings before that edge cannot
repair it in Detect mode; hitting the edge either creates a leader (hence C_PB
after cleanup) or leaves a dist-consistent endpoint. -/
def Lemma16DistForcingSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    DetectReady ring C →
      ∃ word : DetSchedule n,
        word.length = 1 ∧
          ∀ schedule : DetSchedule n,
            word.Sublist schedule →
              PPL.CPB ring
                  (PPL.Probability.runPPL ring C schedule) ∨
                DistReady ring
                  (PPL.Probability.runPPL ring C schedule)


/-- The paper seqL(0,n) sweep, stated rotation-free as an existential fixed
word of exact length n.  Under DistReady it clears all last bits unless a
leader is created first. -/
def Lemma16LastForcingSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    DistReady ring C →
      ∃ word : DetSchedule n,
        word.length = n ∧
          ∀ schedule : DetSchedule n,
            word.Sublist schedule →
              PPL.CPB ring
                  (PPL.Probability.runPPL ring C schedule) ∨
                LastReady ring
                  (PPL.Probability.runPPL ring C schedule)


/-- Extract from the Lemma-3 mismatch a concrete Lemma-4 source/color.  The
second conjunct is the missing semantic endpoint: completion of the selected
fresh lineage detects that fixed mismatch and creates a leader, which together
with the already-clean bullet invariant gives C_PB. -/
def Lemma16MismatchWitnessSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    LastReady ring C →
    ¬PPL.Perfect ring C →
      ∃ k : Fin n, ∃ kind : PPL.TokenKind,
        PPL.Cd ring k kind C ∧
          ∀ schedule : DetSchedule n,
            PPL.HasFreshCompletion kind k
                (PPL.ghostRun hpsi ring 0
                  (PPL.initialGhost C) schedule) →
              PPL.CPB ring
                (PPL.Probability.runPPL ring C schedule)


/-- Trace-wide C_d preservation required by the corrected Lemma-4 statement.
The alternative branch is leader creation, which is already C_PB because the
bullet-clean invariant has been maintained. -/
def Lemma16CdTraceUntilSuccessSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (k : Fin n)
      (kind : PPL.TokenKind),
    LastReady ring C →
    PPL.Cd ring k kind C →
      ∀ schedule : DetSchedule n,
        PPL.CPB ring
            (PPL.Probability.runPPL ring C schedule) ∨
          PPL.CdTrace hpsi ring k kind C schedule


/-! ## Already-provable deterministic closure facts -/


theorem allLivePeaceful_step_closed
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : AllLivePeaceful ring C) :
    AllLivePeaceful ring
      (PopulationProtocol.step
        (PPL.protocol psi kappa) ring C e) := by
  let C' : Config n psi kappa :=
    PopulationProtocol.step (PPL.protocol psi kappa) ring C e
  have hnew : PPL.NewFirePeacefulProp :=
    PPL.Safety.PeacefulProps.newFirePeaceful
      PPL.Safety.PeacefulProps.peacefulScanLocality
  have hkeep : PPL.PeacefulKeepPhysicalProp :=
    PPL.Safety.PeacefulProps.peacefulKeepPhysical
      PPL.Safety.PeacefulProps.peacefulScanLocality
  intro i hi
  by_cases hold : (C i).bullet = (2 : Fin 3)
  · exact
      (hkeep hn3 hpsi ring C e i hold (hC i hold)).1 hi
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      by_cases hleft : (C e).bullet = (2 : Fin 3)
      · exact
          (hkeep hn3 hpsi ring C e e hleft (hC e hleft)).2
            rfl hi hold
      · exact
          hnew hn3 hpsi ring C e (ring.rightNeighbor e)
            hi hold (Or.inr hleft)
    · exact
        hnew hn3 hpsi ring C e i
          hi hold (Or.inl hir)


theorem allLivePeaceful_run_closed
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hC : AllLivePeaceful ring C) :
    AllLivePeaceful ring
      (PPL.Probability.runPPL ring C word) := by
  induction word generalizing C with
  | nil =>
      simpa [PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule] using hC
  | cons e rest ih =>
      have hstep :=
        allLivePeaceful_step_closed
          hn3 hpsi ring C e hC
      simp only [PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule]
      exact
        ih
          (C :=
            PopulationProtocol.step
              (PPL.protocol psi kappa) ring C e)
          hstep


theorem cpb_of_allLivePeaceful_hasLeader
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hpeace : AllLivePeaceful ring C)
    (hleader : ∃ i : Fin n, (C i).leader = true) :
    PPL.CPB ring C := by
  unfold PPL.CPB PPL.CPBCore
  refine ⟨hleader, ?_⟩
  intro i hi
  change PPL.Peaceful ring C i
  exact hpeace i hi


theorem cpb_run_closed
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hC : PPL.CPB ring C) :
    PPL.CPB ring
      (PPL.Probability.runPPL ring C word) := by
  induction word generalizing C with
  | nil =>
      simpa [PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule] using hC
  | cons e rest ih =>
      have hstep :=
        PPL.Safety.PeacefulProps.cpb_step_closed_proved
          hn3 hpsi ring C e hC
      simp only [PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule]
      exact
        ih
          (C :=
            PopulationProtocol.step
              (PPL.protocol psi kappa) ring C e)
          hstep


theorem reachesCPB_eq_endpoint
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) :
    reachesCPB ring C word =
      decide
        (PPL.CPB ring
          (PPL.Probability.runPPL ring C word)) := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      by_cases hC : PPL.CPB ring C
      · have hend :=
          cpb_run_closed
            hn3 hpsi ring C (e :: rest) hC
        simp [reachesCPB, hC, hend]
      · have hstep :
          reachesCPB ring
              (PopulationProtocol.step
                (PPL.protocol psi kappa) ring C e)
              rest =
            decide
              (PPL.CPB ring
                (PPL.Probability.runPPL ring
                  (PopulationProtocol.step
                    (PPL.protocol psi kappa) ring C e)
                  rest)) :=
          ih
            (C :=
              PopulationProtocol.step
                (PPL.protocol psi kappa) ring C e)
        simp [reachesCPB, hC, hstep,
          PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule]
        all_goals exact decide_eq_decide.mpr Iff.rfl


theorem lemma16FailureCount_eq_endpoint
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma16FailureCount ring C =
      endpointFailureCount ring (cpbB ring) C
        (lemma16Horizon n psi kappa) := by
  unfold lemma16FailureCount endpointFailureCount cpbB
  apply congrArg
    (fun p =>
      (allSchedules n
        (lemma16Horizon n psi kappa)).countP p)
  funext word
  rw [reachesCPB_eq_endpoint
    hn3 hpsi ring C word]


theorem lemma16LastReady_not_perfect
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hC : LastReady ring C) :
    ¬PPL.Perfect ring C := by
  have hzero :
      ∀ i : Fin n, (C i).leader = false :=
    hC.1.1.2.1
  exact
    PPL.leaderless_not_perfect
      hn3 hnpow ring C hzero


/-! ## Lemma-6 closure at the exact frozen H6 -/


theorem lemma16H6_eq_lemma6Horizon
    {n psi kappa modeC : Nat}
    (hkappa : kappa = 8 * modeC * psi) :
    lemma16H6 n psi kappa =
      PPL.Modes.Lemma6.lemma6Horizon
        n psi modeC := by
  unfold lemma16H6
    PPL.Modes.Lemma6.lemma6Horizon
    PPL.Modes.Lemma9.lemma9T
    PPL.Modes.Lemma9.lemma9E
    PPL.Probability.lotteryL8Horizon
  rw [hkappa]
  calc
    16 * n * (8 * modeC * psi) * 2 ^ psi =
        (16 * 8) *
          (n * modeC * psi * 2 ^ psi) := by
      ac_rfl
    _ =
        (2 * 64) *
          (n * modeC * psi * 2 ^ psi) := by
      rfl
    _ =
        2 *
          (n *
            (64 * modeC * psi * 2 ^ psi)) := by
      ac_rfl


theorem lemma16Lemma6WordBound
    (hclock :
      PPL.Modes.Lemma6.Lemma6ClockRiseCount)
    {n psi kappa modeC : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hc : 6 ≤ modeC)
    (hkappa : kappa = 8 * modeC * psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    PPL.Modes.Lemma6.Lemma6WordBound
      ring C modeC := by
  have hbridge :
      PPL.Modes.Lemma6.Lemma6DeterministicBridge :=
    PPL.Modes.Lemma6.lemma6Bridge_of_split
      PPL.Modes.Lemma6.lemma6LeaderlessSignalCoverage
      PPL.Modes.Lemma6.lemma6SignalClearanceCount
      PPL.Modes.Lemma6.lemma6ClockFailureSplit
      hclock
      PPL.Modes.Lemma6.lemma6TwoBlockBind
  exact
    PPL.Modes.Lemma6.lemma6_wordBound
      PPL.Probability.earlyLeaderStopBounds
      hbridge
      hn3 hpsi hc hkappa hnpow
      ring C
      (PPL.Modes.SignalLineage.signalLineageOwnership ring)
      (fun i hi =>
        PPL.Modes.Lemma9.lemma9_wordBound_closed
          hn3 hpsi hc hkappa hnpow
          ring C i hi)


/-! ## The Lemma-6 good-state endpoint bridge from one precise missing fact -/


private theorem foldlOr_true
    (xs : List Bool) :
    xs.foldl (fun a b => a || b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      simpa [List.foldl_cons] using ih


private theorem foldlOr_false_allFalse
    (xs : List Bool)
    (h :
      xs.foldl (fun a b => a || b) false = false) :
    ∀ b, b ∈ xs → b = false := by
  induction xs with
  | nil =>
      intro b hb
      simp at hb
  | cons a xs ih =>
      cases ha : a with
      | false =>
          have ht :
              xs.foldl (fun u v => u || v) false =
                false := by
            simpa [List.foldl_cons, ha] using h
          intro b hb
          rcases List.mem_cons.mp hb with hb | hb
          · subst b
            rfl
          · exact ih ht b hb
      | true =>
          have ht :
              xs.foldl (fun u v => u || v) true =
                true :=
            foldlOr_true xs
          have hf : False := by
            rw [List.foldl_cons, ha, Bool.false_or] at h
            rw [ht] at h
            contradiction
          exact hf.elim


private theorem foldlOr_true_existsTrue
    (xs : List Bool)
    (h :
      xs.foldl (fun a b => a || b) false = true) :
    ∃ b, b ∈ xs ∧ b = true := by
  induction xs with
  | nil =>
      simp at h
  | cons a xs ih =>
      cases ha : a with
      | true =>
          exact ⟨true, by simp, rfl⟩
      | false =>
          have ht :
              xs.foldl (fun u v => u || v) false =
                true := by
            simpa [List.foldl_cons, ha] using h
          obtain ⟨b, hb, hbt⟩ := ih ht
          exact ⟨b, by simp [hb], hbt⟩


private theorem leaderPresent_false_all
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h :
      PPL.Probability.leaderPresent C = false) :
    ∀ i : Fin n, (C i).leader = false := by
  unfold PPL.Probability.leaderPresent at h
  have hall :=
    foldlOr_false_allFalse
      (List.ofFn
        (fun i : Fin n => (C i).leader))
      h
  intro i
  apply hall (C i).leader
  rw [List.mem_ofFn]
  exact ⟨i, rfl⟩


private theorem leaderPresent_true_exists
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h :
      PPL.Probability.leaderPresent C = true) :
    ∃ i : Fin n, (C i).leader = true := by
  unfold PPL.Probability.leaderPresent at h
  obtain ⟨b, hb, hbt⟩ :=
    foldlOr_true_existsTrue
      (List.ofFn
        (fun i : Fin n => (C i).leader))
      h
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  exact ⟨i, hi.trans hbt⟩


private theorem lemma6Good_of_clean
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hclean : AllLivePeaceful ring C)
    (hgood :
      PPL.Modes.Lemma6.lemma6GoodB C = true) :
    PPL.CPB ring C ∨ DetectReady ring C := by
  unfold PPL.Modes.Lemma6.lemma6GoodB at hgood
  cases hl :
      PPL.Probability.leaderPresent C with
  | true =>
      have hex :=
        leaderPresent_true_exists C hl
      exact
        Or.inl
          (cpb_of_allLivePeaceful_hasLeader
            ring C hclean hex)
  | false =>
      cases hs :
          PPL.Modes.Lemma6.signalFreeB C with
      | false =>
          simp [hl, hs] at hgood
      | true =>
          cases hd :
              PPL.Modes.Lemma6.allDetectB C with
          | false =>
              simp [hl, hs, hd] at hgood
          | true =>
              exact
                Or.inr
                  ⟨hclean,
                    leaderPresent_false_all C hl,
                    hs, hd⟩


def Lemma16ModeEndpointSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (word : DetSchedule n),
    AllLivePeaceful ring C →
    PPL.Modes.Lemma6.reachesAux
        ring C word = true →
      PPL.CPB ring
          (PPL.Probability.runPPL ring C word) ∨
        DetectReady ring
          (PPL.Probability.runPPL ring C word)


theorem lemma16ModeEndpointSpec_of_persistence
    (hpersist : Lemma16DetectPersistence) :
    Lemma16ModeEndpointSpec := by
  intro n psi kappa
  intro hn3 hpsi
  intro ring C word
  intro hclean hreach
  induction word generalizing C with
  | nil =>
      have hgood :
          PPL.Modes.Lemma6.lemma6GoodB C =
            true := by
        simpa [PPL.Modes.Lemma6.reachesAux] using
          hreach
      have hnow :=
        lemma6Good_of_clean ring C hclean hgood
      simpa [PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule] using
        hnow
  | cons e rest ih =>
      cases hgood :
          PPL.Modes.Lemma6.lemma6GoodB C with
      | true =>
          have hnow :=
            lemma6Good_of_clean
              ring C hclean hgood
          rcases hnow with hcpb | hdet
          · exact
              Or.inl
                (cpb_run_closed
                  hn3 hpsi ring C
                  (e :: rest) hcpb)
          · exact
              hpersist
                hn3 hpsi ring C
                (e :: rest) hdet
      | false =>
          have htail :
              PPL.Modes.Lemma6.reachesAux
                  ring
                  (PPL.Probability.pplStep ring C e)
                  rest = true := by
            simpa [PPL.Modes.Lemma6.reachesAux,
              hgood] using hreach
          have hclean' :
              AllLivePeaceful ring
                (PPL.Probability.pplStep ring C e) := by
            simpa [PPL.Probability.pplStep] using
              allLivePeaceful_step_closed
                hn3 hpsi ring C e hclean
          exact
            ih
              (C :=
                PPL.Probability.pplStep ring C e)
              hclean' htail


/-! ## Finite-word counting kernel -/


private theorem allSchedules_add_local
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
      simp only [allSchedules,
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


private theorem runPPL_append_local
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    PPL.Probability.runPPL ring C (u ++ v) =
      PPL.Probability.runPPL ring
        (PPL.Probability.runPPL ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append,
        PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule]
      exact
        ih
          (C :=
            PPL.Probability.pplStep ring C e)


private theorem countP_mono_local
    {A : Type}
    (xs : List A)
    (p q : A → Bool)
    (hpq :
      ∀ x, p x = true → q x = true) :
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


private theorem scaled_sum_le_countP_mul_add_length_mul
    {A : Type}
    (xs : List A)
    (p : A → Bool)
    (f : A → Nat)
    (scale u v : Nat)
    (hpoint :
      ∀ x, x ∈ xs →
        scale * f x ≤
          (if p x then u else 0) + v) :
    scale * (xs.map f).sum ≤
      xs.countP p * u + xs.length * v := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx := hpoint x (by simp)
      have ht :=
        ih
          (fun y hy =>
            hpoint y (by simp [hy]))
      rw [List.map_cons, List.sum_cons,
        List.countP_cons, List.length_cons,
        Nat.mul_add, Nat.succ_mul]
      cases hp : p x <;>
        simp [hp, Nat.add_mul] at hx ⊢ <;>
        omega


private def childEndpointFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (U : Nat)
    (pre : DetSchedule n) : Nat :=
  ((allSchedules n U).map
    (fun suf => pre ++ suf)).countP
      (fun word =>
        !good
          (PPL.Probability.runPPL
            ring C word))


private theorem childEndpointFailureCount_le_full
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (U : Nat)
    (pre : DetSchedule n) :
    childEndpointFailureCount
        ring good C U pre ≤
      n ^ U := by
  unfold childEndpointFailureCount
  calc
    ((allSchedules n U).map
      (fun suf => pre ++ suf)).countP
        (fun word =>
          !good
            (PPL.Probability.runPPL
              ring C word))
        ≤
      ((allSchedules n U).map
        (fun suf => pre ++ suf)).length :=
      List.countP_le_length
    _ = (allSchedules n U).length := by
      rw [List.length_map]
    _ = n ^ U :=
      allSchedules_length n U


private theorem childEndpointFailureCount_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (U : Nat)
    (pre : DetSchedule n) :
    childEndpointFailureCount
        ring good C U pre =
      endpointFailureCount
        ring good
        (PPL.Probability.runPPL
          ring C pre) U := by
  unfold childEndpointFailureCount
    endpointFailureCount
  rw [List.countP_map]
  simp only [Function.comp_def]
  apply congrArg
    (fun p =>
      (allSchedules n U).countP p)
  funext suf
  rw [runPPL_append_local]


private theorem endpointFailureCount_eq_child_sum
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (T U : Nat) :
    endpointFailureCount ring good C (T + U) =
      ((allSchedules n T).map
        (childEndpointFailureCount
          ring good C U)).sum := by
  unfold endpointFailureCount
    childEndpointFailureCount
  rw [allSchedules_add_local,
    List.countP_flatMap]
  rfl


private theorem phaseBind
    {n psi kappa T U A B : Nat}
    (ring : DirectedRing n)
    (mid final : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (hmid :
      n * endpointFailureCount
            ring mid C T ≤
        A * n ^ T)
    (hnext :
      ∀ D : Config n psi kappa,
        mid D = true →
          n * endpointFailureCount
                ring final D U ≤
            B * n ^ U) :
    n * endpointFailureCount
          ring final C (T + U) ≤
      (A + B) * n ^ (T + U) := by
  let badPre : DetSchedule n → Bool :=
    fun pre =>
      !mid
        (PPL.Probability.runPPL
          ring C pre)
  let child : DetSchedule n → Nat :=
    childEndpointFailureCount
      ring final C U


  have hpoint :
      ∀ pre, pre ∈ allSchedules n T →
        n * child pre ≤
          (if badPre pre
            then n * n ^ U else 0) +
            B * n ^ U := by
    intro pre hpre
    let D :=
      PPL.Probability.runPPL
        ring C pre
    by_cases hm : mid D = true
    · have hbad : badPre pre = false := by
        show (!mid D) = false
        rw [hm]
        rfl
      rw [hbad]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      have heq :
          child pre =
            endpointFailureCount
              ring final D U := by
        dsimp [child, D]
        exact
          childEndpointFailureCount_eq
            ring final C U pre
      rw [heq]
      exact hnext D hm
    · have hmfalse : mid D = false := by
        cases h : mid D with
        | false =>
            rfl
        | true =>
            exact False.elim (hm h)
      have hbad : badPre pre = true := by
        show (!mid D) = true
        rw [hmfalse]
        rfl
      rw [hbad]
      simp only [if_true]
      have hfull :
          child pre ≤ n ^ U := by
        dsimp [child]
        exact
          childEndpointFailureCount_le_full
            ring final C U pre
      have hmul :=
        Nat.mul_le_mul_left n hfull
      omega


  have hsum :=
    scaled_sum_le_countP_mul_add_length_mul
      (allSchedules n T)
      badPre child
      n (n * n ^ U) (B * n ^ U)
      hpoint


  have hbadCount :
      (allSchedules n T).countP badPre =
        endpointFailureCount
          ring mid C T := by
    rfl
  have hlen :
      (allSchedules n T).length =
        n ^ T :=
    allSchedules_length n T
  rw [hbadCount, hlen] at hsum


  have hfirst :
      endpointFailureCount ring mid C T *
          (n * n ^ U) ≤
        (A * n ^ T) * n ^ U := by
    calc
      endpointFailureCount ring mid C T *
            (n * n ^ U) =
          (n *
            endpointFailureCount ring mid C T) *
              n ^ U := by
        ac_rfl
      _ ≤
          (A * n ^ T) * n ^ U :=
        Nat.mul_le_mul_right
          (n ^ U) hmid


  have hdecomp :=
    endpointFailureCount_eq_child_sum
      ring final C T U
  rw [hdecomp]
  calc
    n *
        ((allSchedules n T).map child).sum
        ≤
      endpointFailureCount ring mid C T *
          (n * n ^ U) +
        n ^ T * (B * n ^ U) :=
      hsum
    _ ≤
      (A * n ^ T) * n ^ U +
        n ^ T * (B * n ^ U) :=
      Nat.add_le_add
        hfirst (Nat.le_refl _)
    _ =
      (A + B) * n ^ (T + U) := by
      rw [Nat.pow_add, Nat.add_mul]
      simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]


private theorem endpointFailureCount_zero_of_all_good
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (T : Nat)
    (hall :
      ∀ word : DetSchedule n,
        good
          (PPL.Probability.runPPL
            ring C word) = true) :
    endpointFailureCount
      ring good C T = 0 := by
  unfold endpointFailureCount
  apply List.countP_eq_zero.mpr
  intro word hword hbad
  have hg := hall word
  simp [hg] at hbad


private theorem fixedWordPhaseBound
    {n psi kappa : Nat}
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ lemma16K n)
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (L : Nat)
    (hlen : word.length = L)
    (hforce :
      ∀ schedule : DetSchedule n,
        word.Sublist schedule →
          good
            (PPL.Probability.runPPL
              ring C schedule) = true) :
    n *
        endpointFailureCount ring good C
          (2 * n *
            (L + 4 * lemma16K n)) ≤
      n ^ (2 * n *
        (L + 4 * lemma16K n)) := by
  let H :=
    2 * n *
      (L + 4 * lemma16K n)
  have hmono :
      endpointFailureCount ring good C H ≤
        PPL.Probability.fixedWordMissCount
          word H := by
    unfold endpointFailureCount
    change
      (allSchedules n H).countP
          (fun schedule =>
            !good
              (PPL.Probability.runPPL
                ring C schedule)) ≤
        (allSchedules n H).countP
          (fun schedule =>
            decide (¬word.Sublist schedule))
    apply countP_mono_local
    intro schedule hbad
    by_cases hsub : word.Sublist schedule
    · have hg :=
        hforce schedule hsub
      simp [hg] at hbad
    · simp [hsub]


  have hpsiPow :
      2 ^ psi ≤
        2 ^ lemma16K n :=
    Nat.pow_le_pow_right
      (by decide) hpsiK
  have hK4 :
      lemma16K n ≤
        4 * lemma16K n := by
    omega
  have h4Pow :
      2 ^ lemma16K n ≤
        2 ^ (4 * lemma16K n) :=
    Nat.pow_le_pow_right
      (by decide) hK4
  have hnscale :
      n ≤ 2 ^ (4 * lemma16K n) :=
    Nat.le_trans hnpow
      (Nat.le_trans hpsiPow h4Pow)


  have hfixed :=
    PPL.Probability.fixedWordMissCount_mul_twoPow_le_of_length
      word L (4 * lemma16K n) hlen
  change
    PPL.Probability.fixedWordMissCount
          word H *
        2 ^ (4 * lemma16K n) ≤
      n ^ H at hfixed


  have hscaled :
      n *
          PPL.Probability.fixedWordMissCount
            word H ≤
        n ^ H := by
    calc
      n *
          PPL.Probability.fixedWordMissCount
            word H =
        PPL.Probability.fixedWordMissCount
            word H * n := by
          ac_rfl
      _ ≤
        PPL.Probability.fixedWordMissCount
            word H *
          2 ^ (4 * lemma16K n) :=
        Nat.mul_le_mul_left _ hnscale
      _ ≤ n ^ H :=
        hfixed


  exact
    Nat.le_trans
      (Nat.mul_le_mul_left n hmono)
      hscaled


/-! ## Per-block bounds -/


private theorem modePhaseBound
    (hclock :
      PPL.Modes.Lemma6.Lemma6ClockRiseCount)
    (hmode : Lemma16ModeEndpointSpec)
    {n psi kappa modeC : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hc : 6 ≤ modeC)
    (hkappa : kappa = 8 * modeC * psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hclean :
      allLivePeacefulB ring C = true) :
    n *
        endpointFailureCount
          ring (detectOrCPBB ring) C
          (lemma16H6 n psi kappa) ≤
      8 * n ^ lemma16H6 n psi kappa := by
  have hcleanP :
      AllLivePeaceful ring C :=
    of_decide_eq_true hclean
  have hH :=
    lemma16H6_eq_lemma6Horizon
      (n := n) (psi := psi)
      (kappa := kappa)
      (modeC := modeC) hkappa
  have hmono :
      endpointFailureCount
          ring (detectOrCPBB ring) C
          (PPL.Modes.Lemma6.lemma6Horizon
            n psi modeC) ≤
        PPL.Modes.Lemma6.lemma6FailureCount
          ring C modeC := by
    unfold endpointFailureCount
      PPL.Modes.Lemma6.lemma6FailureCount
    apply countP_mono_local
    intro word hbad
    cases hr :
        PPL.Modes.Lemma6.reachesAux
          ring C word with
    | false =>
        simp [hr]
    | true =>
        have hor :=
          hmode hn3 hpsi ring C word
            hcleanP hr
        have hgood :
            detectOrCPBB ring
              (PPL.Probability.runPPL
                ring C word) = true := by
          simp [detectOrCPBB, hor]
        simp [hgood] at hbad
  have hmonoScaled :=
    Nat.mul_le_mul_left n hmono
  have h6 :=
    lemma16Lemma6WordBound
      hclock
      hn3 hpsi hc hkappa hnpow
      ring C
  unfold PPL.Modes.Lemma6.Lemma6WordBound at h6
  rw [hH]
  exact
    Nat.le_trans hmonoScaled h6


private theorem distPhaseBound
    (hdist : Lemma16DistForcingSpec)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ lemma16K n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hstart :
      detectOrCPBB ring C = true) :
    n *
        endpointFailureCount
          ring (distOrCPBB ring) C
          (lemma16HDist n) ≤
      n ^ lemma16HDist n := by
  have hstartP :
      PPL.CPB ring C ∨ DetectReady ring C :=
    of_decide_eq_true hstart
  rcases hstartP with hcpb | hdet
  · have hz :=
      endpointFailureCount_zero_of_all_good
        ring (distOrCPBB ring) C
        (lemma16HDist n)
        (fun word => by
          have hend :=
            cpb_run_closed
              hn3 hpsi ring C word hcpb
          simp [distOrCPBB, hend])
    rw [hz]
    simp
  · obtain ⟨word, hlen, hforce⟩ :=
      hdist hn3 hpsi ring C hdet
    have hb :=
      fixedWordPhaseBound
        hnpow hpsiK
        ring (distOrCPBB ring) C
        word 1 hlen
        (fun schedule hsub => by
          have hor :=
            hforce schedule hsub
          simp [distOrCPBB, hor])
    simpa [lemma16HDist] using hb


private theorem lastPhaseBound
    (hlast : Lemma16LastForcingSpec)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ lemma16K n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hstart :
      distOrCPBB ring C = true) :
    n *
        endpointFailureCount
          ring (lastOrCPBB ring) C
          (lemma16HLast n) ≤
      n ^ lemma16HLast n := by
  have hstartP :
      PPL.CPB ring C ∨ DistReady ring C :=
    of_decide_eq_true hstart
  rcases hstartP with hcpb | hdistReady
  · have hz :=
      endpointFailureCount_zero_of_all_good
        ring (lastOrCPBB ring) C
        (lemma16HLast n)
        (fun word => by
          have hend :=
            cpb_run_closed
              hn3 hpsi ring C word hcpb
          simp [lastOrCPBB, hend])
    rw [hz]
    simp
  · obtain ⟨word, hlen, hforce⟩ :=
      hlast hn3 hpsi ring C hdistReady
    have hb :=
      fixedWordPhaseBound
        hnpow hpsiK
        ring (lastOrCPBB ring) C
        word n hlen
        (fun schedule hsub => by
          have hor :=
            hforce schedule hsub
          simp [lastOrCPBB, hor])
    simpa [lemma16HLast] using hb


private theorem tokenPhaseBound
    (hmismatch : Lemma16MismatchWitnessSpec)
    (htrace : Lemma16CdTraceUntilSuccessSpec)
    (hcore : PPL.lemma4_deterministic_core)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ lemma16K n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hstart :
      lastOrCPBB ring C = true) :
    n *
        endpointFailureCount
          ring (cpbB ring) C
          (lemma16HToken n psi) ≤
      n ^ lemma16HToken n psi := by
  have hstartP :
      PPL.CPB ring C ∨ LastReady ring C :=
    of_decide_eq_true hstart
  rcases hstartP with hcpb | hlastReady
  · have hz :=
      endpointFailureCount_zero_of_all_good
        ring (cpbB ring) C
        (lemma16HToken n psi)
        (fun word => by
          have hend :=
            cpb_run_closed
              hn3 hpsi ring C word hcpb
          simp [cpbB, hend])
    rw [hz]
    simp
  · have hnotPerfect :=
      lemma16LastReady_not_perfect
        hn3 hnpow ring C hlastReady
    obtain
        ⟨k, kind, hCd, hcompletion⟩ :=
      hmismatch
        hn3 hpsi hnpow
        ring C hlastReady hnotPerfect
    have hforce :
        ∀ schedule : DetSchedule n,
          (PPL.lemma4Word ring k psi).Sublist
              schedule →
            cpbB ring
              (PPL.Probability.runPPL
                ring C schedule) = true := by
      intro schedule hsub
      by_cases hcpbEnd :
          PPL.CPB ring
            (PPL.Probability.runPPL
              ring C schedule)
      · simp [cpbB, hcpbEnd]
      · have htraceOr :=
          htrace
            hn3 hpsi ring C k kind
            hlastReady hCd schedule
        rcases htraceOr with hcpb | hCdTrace
        · exact False.elim (hcpbEnd hcpb)
        · have hcompleted :=
            hcore
              hpsi ring k kind
              C schedule hCdTrace hsub
          have hcpb :=
            hcompletion schedule hcompleted
          exact False.elim (hcpbEnd hcpb)
    have hlen0 :=
      PPL.lemma4Word_length
        hpsi ring k
    have hlen :
        (PPL.lemma4Word ring k psi).length =
          lemma16L4 psi := by
      simpa [lemma16L4] using hlen0
    have hb :=
      fixedWordPhaseBound
        hnpow hpsiK
        ring (cpbB ring) C
        (PPL.lemma4Word ring k psi)
        (lemma16L4 psi) hlen hforce
    simpa [lemma16HToken] using hb


/-! ## Lemma 16 -/


theorem lemma16_wordBound
    (h15 : Lemma16BulletSweepNatBound)
    (hclock :
      PPL.Modes.Lemma6.Lemma6ClockRiseCount)
    (hpersist : Lemma16DetectPersistence)
    (hdist : Lemma16DistForcingSpec)
    (hlast : Lemma16LastForcingSpec)
    (hmismatch : Lemma16MismatchWitnessSpec)
    (htrace : Lemma16CdTraceUntilSuccessSpec)
    (hcore : PPL.lemma4_deterministic_core)
    {n psi kappa modeC : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hc : 6 ≤ modeC)
    (hkappa : kappa = 8 * modeC * psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ lemma16K n)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Lemma16WordBound ring C := by
  have hmode :
      Lemma16ModeEndpointSpec :=
    lemma16ModeEndpointSpec_of_persistence
      hpersist


  have h0 :
      n *
          endpointFailureCount
            ring (allLivePeacefulB ring) C
            (lemma16H15 n) ≤
        1 * n ^ lemma16H15 n := by
    simpa using
      h15 hn3 hpsi ring C


  have h01 :=
    phaseBind
      ring
      (allLivePeacefulB ring)
      (detectOrCPBB ring)
      C h0
      (fun D hD =>
        modePhaseBound
          hclock hmode
          hn3 hpsi hc hkappa hnpow
          ring D hD)


  have h012 :=
    phaseBind (B := 1)
      ring
      (detectOrCPBB ring)
      (distOrCPBB ring)
      C h01
      (fun D hD =>
        Nat.le_trans
          (distPhaseBound
          hdist
          hn3 hpsi hnpow hpsiK
          ring D hD)
          (Nat.le_of_eq (Nat.one_mul _).symm))


  have h0123 :=
    phaseBind (B := 1)
      ring
      (distOrCPBB ring)
      (lastOrCPBB ring)
      C h012
      (fun D hD =>
        Nat.le_trans
          (lastPhaseBound
          hlast
          hn3 hpsi hnpow hpsiK
          ring D hD)
          (Nat.le_of_eq (Nat.one_mul _).symm))


  have hfinal :=
    phaseBind (B := 1)
      ring
      (lastOrCPBB ring)
      (cpbB ring)
      C h0123
      (fun D hD =>
        Nat.le_trans
          (tokenPhaseBound
          hmismatch htrace hcore
          hn3 hpsi hnpow hpsiK
          ring D hD)
          (Nat.le_of_eq (Nat.one_mul _).symm))


  have hfailEq :=
    lemma16FailureCount_eq_endpoint
      hn3 hpsi ring C
  unfold Lemma16WordBound
  rw [hfailEq]
  simpa [lemma16Horizon] using hfinal


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.allLivePeaceful_step_closed
#print axioms PPL.Convergence.ReachCPB.allLivePeaceful_run_closed
#print axioms PPL.Convergence.ReachCPB.cpb_of_allLivePeaceful_hasLeader
#print axioms PPL.Convergence.ReachCPB.cpb_run_closed
#print axioms PPL.Convergence.ReachCPB.reachesCPB_eq_endpoint
#print axioms PPL.Convergence.ReachCPB.lemma16FailureCount_eq_endpoint
#print axioms PPL.Convergence.ReachCPB.lemma16LastReady_not_perfect
#print axioms PPL.Convergence.ReachCPB.lemma16H6_eq_lemma6Horizon
#print axioms PPL.Convergence.ReachCPB.lemma16Lemma6WordBound
#print axioms PPL.Convergence.ReachCPB.lemma16ModeEndpointSpec_of_persistence
#print axioms PPL.Convergence.ReachCPB.lemma16_wordBound


