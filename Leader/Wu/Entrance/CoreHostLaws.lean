import Leader.Wu.Entrance.EnvelopeInterface
import Leader.Wu.Comparison.ExpiringK2Projection
import Leader.Wu.Elimination.BirthDispatcherLeaderNormalize
import Leader.Wu.Entrance.RelativeRulerContract

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceV2K2

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthShortDoneTerminalFirstHit BirthCheckChainR1Ring
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FiniteUniformStoppingTree FixedSpanRenewalPayload
open B6LocalReverseFill
open B6EntranceV2

variable {n psi kappa tau : Nat} {P : Type}
variable {ring : DirectedRing n}

/-- Positive `signal_B` residue is allowed, but a
leaderless continuation carries no live K2 bullet. -/
def K2DrainedCell (q : Phys psi kappa tau) : Prop :=
  let u := B6Sanitation.rawCell q
  u.leader = false ∧ u.bullet = 0

/-- Corrected K2 endpoint.  This is the drained-cell condition with the old
`ExpiryAt` premise retained. -/
def K2DrainedAt (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P)
    (X : Workspace ring psi) (C : PConfig n P) : Prop :=
  ExpiryAt view WP X C ∧ CoreAll view X K2DrainedCell C

/-- Corrected replacement for `HostK2ClearableOrLeader`.
This is `HostK2DrainOrLeader`. -/
def HostK2ClearableOrLeaderV2
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (L : Nat) : Prop :=
  HostStageWord host view ring WP
    (ExpiryAt view WP) (K2DrainedAt view WP) L

/-- The downstream prepared state must start from the corrected K2 endpoint;
otherwise the old false `signal_B = 0` condition is silently reintroduced. -/
def CorePreparedV2 (hpsi : 0 < psi) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P)
    (X : Workspace ring psi) (C : PConfig n P) : Prop :=
  K2DrainedAt view WP X C ∧
  B6Sanitation.RulerNF ring X.core.J (physConfig view C) ∧
  B6EntranceCompose.CanonicalArc hpsi ring X.core.J (physConfig view C) ∧
  B6EntranceCompose.LocalCover ring X.core.J (physConfig view C)

/-- The prepared state with NO absolute phase: the ruler conjunct asks only for
the successor arc.  Successor to `CorePreparedV2`, which required the core to be
anchored at label zero -- a requirement the law-six refutation killed. -/
def CorePreparedRel (hpsi : 0 < psi) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P)
    (X : Workspace ring psi) (C : PConfig n P) : Prop :=
  K2DrainedAt view WP X C ∧
  B6PreparedRelativeContract.RulerNFRel hpsi ring X.core.J
    (physConfig view C) ∧
  B6EntranceCompose.CanonicalArc hpsi ring X.core.J (physConfig view C) ∧
  B6EntranceCompose.LocalCover ring X.core.J (physConfig view C)

/-- Ruler stage with the corrected source and destination predicates. -/
def HostRulerWordV2 (hpsi : 0 < psi) (host : B9Host.HostRow P)
    (view : P → Phys psi kappa tau) (ring : DirectedRing n)
    (WP : WriterProtected ring psi P) (L : Nat) : Prop :=
  HostCoreStageWord host view ring WP (K2DrainedAt view WP)
    (CorePreparedV2 hpsi view WP) L

/-- Route stage paired with `CorePreparedV2`. -/
def HostRouteWordV2 (hpsi : 0 < psi) (host : B9Host.HostRow P)
    (view : P → Phys psi kappa tau) (ring : DirectedRing n)
    (WP : WriterProtected ring psi P) (L : Nat) : Prop :=
  HostCoreStageWord host view ring WP (CorePreparedV2 hpsi view WP)
    (fun _ _ => False) L

/-- V2 law bundle.  Only the K2/ruler/route boundary changes; writer,
traffic, expiry, locality and static-expiry contracts are reused verbatim. -/
structure EntranceHostLawsV2 (hpsi : 0 < psi) (host : B9Host.HostRow P)
    (view : P → Phys psi kappa tau) (ring : DirectedRing n)
    (WP : WriterProtected ring psi P) (b : EntranceBudgets) : Prop where
  writerLocal : HostWriterProtectedLocal WP
  bitSilence : HostCoreBitSilence host view ring WP
  staticExpiry : HostStaticExpiryTick host view
  writerAdmission : HostWriterAdmission host view ring WP b.writer.L
  trafficWord : HostDirectionalTrafficExit host view ring WP b.traffic.L
  expiryWord : HostComparisonExpiryWord host view ring WP b.expiry.L
  k2Word : HostK2ClearableOrLeaderV2 host view ring WP b.k2.L
  rulerWord : HostRulerWordV2 hpsi host view ring WP b.ruler.L
  routeWord : HostRouteWordV2 hpsi host view ring WP b.route.L

private theorem internalWord_appendV2K2 (I : Interval ring)
    (u v : List (Fin n)) (hu : InternalWord I u) (hv : InternalWord I v) :
    InternalWord I (u ++ v) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hu e he
  · exact hv e he

private theorem runHost_appendV2K2 (host : B9Host.HostRow P)
    (ring : DirectedRing n) (u v : List (Fin n)) (C : PConfig n P) :
    runHost host ring (u ++ v) C =
      runHost host ring v (runHost host ring u C) := by
  simp only [runHost, List.foldl_append]

private theorem continue_requestV2K2 (host : B9Host.HostRow P)
    (view : P → Phys psi kappa tau) (ring : DirectedRing n)
    (I : Interval ring) (A B : PConfig n P → Prop)
    (C : PConfig n P) (u : List (Fin n)) (Lu Lv : Nat)
    (huI : InternalWord I u) (huL : u.length ≤ Lu)
    (huE : HostExit host view ring I A (runHost host ring u C))
    (hnext : ∀ D : PConfig n P, HostLeaderless view D → A D →
      ∃ v : List (Fin n), InternalWord I v ∧ v.length ≤ Lv ∧
        HostExit host view ring I B (runHost host ring v D)) :
    ∃ w : List (Fin n), InternalWord I w ∧ w.length ≤ Lu + Lv ∧
      HostExit host view ring I B (runHost host ring w C) := by
  rcases huE with hA | hHit | hBirth
  · let D := runHost host ring u C
    by_cases hD : HostLeaderless view D
    · obtain ⟨v, hvI, hvL, hvE⟩ := hnext D hD hA
      refine ⟨u ++ v, internalWord_appendV2K2 I u v huI hvI, ?_, ?_⟩
      · simp only [List.length_append]
        omega
      · rw [runHost_appendV2K2]
        exact hvE
    · have hlen : u.length ≤ Lu + Lv := by omega
      exact ⟨u, huI, hlen, Or.inr (Or.inr hD)⟩
  · have hlen : u.length ≤ Lu + Lv := by omega
    exact ⟨u, huI, hlen, Or.inr (Or.inl hHit)⟩
  · have hlen : u.length ≤ Lu + Lv := by omega
    exact ⟨u, huI, hlen, Or.inr (Or.inr hBirth)⟩

theorem postWriterRequestV2 (hpsi : 0 < psi) (host : B9Host.HostRow P)
    (view : P → Phys psi kappa tau) (ring : DirectedRing n)
    (WP : WriterProtected ring psi P) (b : EntranceBudgets)
    (hTraffic : HostDirectionalTrafficExit host view ring WP b.traffic.L)
    (hExpiry : HostComparisonExpiryWord host view ring WP b.expiry.L)
    (hK2 : HostK2ClearableOrLeaderV2 host view ring WP b.k2.L)
    (hRuler : HostRulerWordV2 hpsi host view ring WP b.ruler.L)
    (hRoute : HostRouteWordV2 hpsi host view ring WP b.route.L)
    (X : Workspace ring psi) (C : PConfig n P)
    (hC : HostLeaderless view C) (hW : WriterAt WP X C) :
    ∃ w : List (Fin n), InternalWord X.env.I w ∧
      w.length ≤ postWriterL b ∧
      HostExit host view ring X.env.I (fun _ => False)
        (runHost host ring w C) := by
  obtain ⟨u, huI, huL, huE⟩ := hTraffic X C hC hW
  obtain ⟨u1, hu1I, hu1L, hu1E⟩ :=
    continue_requestV2K2 host view ring X.env.I
      (TrafficAt view WP X) (ExpiryAt view WP X)
      C u b.traffic.L b.expiry.L huI huL huE
      (fun D hD hT => hExpiry X D hD hT)
  obtain ⟨u2, hu2I, hu2L, hu2E⟩ :=
    continue_requestV2K2 host view ring X.env.I
      (ExpiryAt view WP X) (K2DrainedAt view WP X)
      C u1 (b.traffic.L + b.expiry.L) b.k2.L hu1I hu1L hu1E
      (fun D hD hE => hK2 X D hD hE)
  have hRuler' := B6EntranceV2.coreStageWord_stage host view ring WP
    (K2DrainedAt view WP) (CorePreparedV2 hpsi view WP)
    b.ruler.L hRuler
  obtain ⟨u3, hu3I, hu3L, hu3E⟩ :=
    continue_requestV2K2 host view ring X.env.I
      (K2DrainedAt view WP X) (CorePreparedV2 hpsi view WP X)
      C u2 ((b.traffic.L + b.expiry.L) + b.k2.L) b.ruler.L
      hu2I hu2L hu2E (fun D hD hS => hRuler' X D hD hS)
  have hRoute' := B6EntranceV2.coreStageWord_stage host view ring WP
    (CorePreparedV2 hpsi view WP) (fun _ _ => False)
    b.route.L hRoute
  obtain ⟨u4, hu4I, hu4L, hu4E⟩ :=
    continue_requestV2K2 host view ring X.env.I
      (CorePreparedV2 hpsi view WP X) (fun _ => False)
      C u3 (((b.traffic.L + b.expiry.L) + b.k2.L) + b.ruler.L)
      b.route.L hu3I hu3L hu3E
      (fun D hD hP => hRoute' X D hD hP)
  exact ⟨u4, hu4I, hu4L, hu4E⟩


/-- Same matcher mass proof as V2, but consuming the corrected deterministic
request above. -/
theorem postWriter_massV2 (hpsi : 0 < psi) (host : B9Host.HostRow P)
    (view : P → Phys psi kappa tau) (ring : DirectedRing n)
    (WP : WriterProtected ring psi P) (b : EntranceBudgets)
    (hpostQ : 1 ≤ postWriterQ b)
    (hpostMatch : (4 * envelopeTouchBound psi) ^ postWriterL b ≤ postWriterQ b)
    (hTraffic : HostDirectionalTrafficExit host view ring WP b.traffic.L)
    (hExpiry : HostComparisonExpiryWord host view ring WP b.expiry.L)
    (hK2 : HostK2ClearableOrLeaderV2 host view ring WP b.k2.L)
    (hRuler : HostRulerWordV2 hpsi host view ring WP b.ruler.L)
    (hRoute : HostRouteWordV2 hpsi host view ring WP b.route.L) :
    ∀ (X : Workspace ring psi) (C : PConfig n P),
      HostAlive view ring C → WriterAt WP X C →
      postWriterQ b * aliveCount (B9Host.hostStep host ring)
          (HostAlive view ring) C (postWriterB n b) ≤
        (postWriterQ b - 1) * n ^ (postWriterB n b) := by
  intro X C hC hW
  obtain ⟨w, hI, hL, hExit⟩ := postWriterRequestV2 hpsi host view ring WP b
    hTraffic hExpiry hK2 hRuler hRoute X C hC.1 hW
  have hM : 1 ≤ envelopeTouchBound psi := by
    unfold envelopeTouchBound envelopeWidth coreWidth collarWidth
    omega
  have hbudget : B6EntranceCompose.EscapeBudget n
      (postWriterL b) (envelopeTouchBound psi)
      (postWriterB n b) (postWriterQ b) :=
    ⟨hM, hpostQ, rfl, hpostMatch⟩
  have hm := B6EntranceV2.hostRequest_mass_of_budget host view ring X.env.I
    (fun _ => False) w C (postWriterL b) (envelopeTouchBound psi)
    (postWriterB n b) (postWriterQ b) hbudget hL
    (B6EntranceV2.envelope_touch_le X) hC.1
    (by intro A D _; simp) ⟨hI, hExit⟩
  rw [B6EntranceV2.avoidCount_eq_hostPending host view ring
    (fun _ => False) C (postWriterB n b)] at hm
  have hPendingFalse :
      (HostPending view ring (fun _ : PConfig n P => False)) =
        HostAlive view ring := by
    funext D
    simp only [HostPending, not_false_eq_true, and_true]
  rw [hPendingFalse] at hm
  exact hm

-- END PART 1

/-- V2 composition theorem.  The stochastic/matcher layer
is unchanged; only the post-writer deterministic stage predicates differ. -/
theorem uniformReadyWindowEscape_of_obligationsV2
    (hpsi : 0 < psi) (host : B9Host.HostRow P)
    (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (b : EntranceBudgets) (hbud : b.Valid n psi)
    (hlaws : EntranceHostLawsV2 hpsi host view ring WP b) :
    UniformHostReadyWindowEscape host view ring
      (entranceB n b) (entranceQ b) := by
  rcases hbud with
    ⟨hBw, hTouch, _, _, _, _, _, hPostQ, hPostMatch⟩
  have hQw : 1 ≤ b.writer.Q := hBw.2.1
  have hWriter := B6EntranceV2.writerAdmission_mass
    host view ring WP b hBw hTouch
    hlaws.writerLocal hlaws.writerAdmission
  have hTail : ∀ C : PConfig n P, HostAlive view ring C → WriterStage WP C →
      postWriterQ b * aliveCount (B9Host.hostStep host ring)
          (HostAlive view ring) C (postWriterB n b) ≤
        (postWriterQ b - 1) * n ^ (postWriterB n b) := by
    intro C hC hStage
    rcases hStage with ⟨X, hX⟩
    exact postWriter_massV2 hpsi host view ring WP b hPostQ hPostMatch
      hlaws.trafficWord hlaws.expiryWord hlaws.k2Word
      hlaws.rulerWord hlaws.routeWord X C hC hX
  have htwo : UniformEscapeMass (B9Host.hostStep host ring)
      (HostAlive view ring) (entranceB n b) (entranceQ b) := by
    change UniformEscapeMass (B9Host.hostStep host ring)
      (HostAlive view ring)
      (b.writer.B + postWriterB n b)
      (b.writer.Q * postWriterQ b)
    exact BirthTwoStageEscape.two_stage_escape
      (B9Host.hostStep host ring) (HostAlive view ring) (WriterStage WP)
      b.writer.B (postWriterB n b) b.writer.Q (postWriterQ b)
      hQw hPostQ hWriter hTail
  intro C hC
  rw [B6LocalReverseFill.avoidCount_eq_alive_complement]
  change entranceQ b * aliveCount (B9Host.hostStep host ring)
      (HostAlive view ring) C (entranceB n b) ≤
    (entranceQ b - 1) * n ^ (entranceB n b)
  by_cases hReady : HostReadyWindow view ring C
  · have hnot : ¬ HostAlive view ring C := fun h => h.2 hReady
    rw [BirthTwoStageEscape.aliveCount_not_good
      (B9Host.hostStep host ring) (HostAlive view ring)
      C hnot (entranceB n b), Nat.mul_zero]
    exact Nat.zero_le _
  · exact htwo C ⟨hC, hReady⟩

/-! ## Explicit reverse-envelope K2 word -/

def k2DrainWord (ring : DirectedRing n) (X : Workspace ring psi) :
    List (Fin n) :=
  (List.range (X.env.I.size - 1)).reverse.map
    (fun k => cell ring X.env.I.first k)

def k2DrainLength (psi : Nat) : Nat := envelopeWidth psi - 1

theorem k2DrainWord_internal (ring : DirectedRing n)
    (X : Workspace ring psi) :
    InternalWord X.env.I (k2DrainWord ring X) := by
  intro e he
  rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
  have hk' : k ∈ List.range (X.env.I.size - 1) := by
    simpa using hk
  have hlt : k < X.env.I.size - 1 := List.mem_range.mp hk'
  apply (B6LocalReverseFill.internal_iff X.env.I _).2
  constructor
  · exact B6LocalReverseFill.support_cell X.env.I (by omega)
  · rw [BirthCheckChainR1Ring.right_cell]
    exact B6LocalReverseFill.support_cell X.env.I (by omega)

theorem k2DrainWord_length (ring : DirectedRing n)
    (X : Workspace ring psi) :
    (k2DrainWord ring X).length = k2DrainLength psi := by
  simp only [k2DrainWord, List.length_map, List.length_reverse,
    List.length_range, k2DrainLength]
  rw [X.env.size_eq]

/-! ## Closed psi=3 obstruction to the old law -/

namespace Regression

private theorem h3 : 0 < 3 := by decide
private def ring45 : DirectedRing 45 := ⟨by decide⟩

/-- Leaderless, no bullet, positive absence signal.
Stall is deliberately zero so the same configuration is not a ReadyWindow. -/
private def obstructionCell : Phys 3 3 48 :=
  let b : BoundedAgentState 3 3 := {
    leader := false
    probe := false
    phase := false
    bit := false
    wait := true
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := 0
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 1
    bullet := 0
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false
  }
  ⟨⟨b, false⟩, 0⟩

private def obstructionConfig : PConfig 45 (Phys 3 3 48) :=
  fun _ => obstructionCell

private def envI : Interval ring45 where
  first := 0
  size := 44
  nonempty := by decide
  fits := by decide

private def env : Envelope ring45 3 where
  I := envI
  size_eq := by decide
  proper := by decide

private def coreI : Interval ring45 where
  first := cell ring45 envI.first 4
  size := 36
  nonempty := by decide
  fits := by decide

private def core : Core ring45 3 env where
  J := coreI
  first_eq := rfl
  size_eq := by decide
  subset := by decide

private def X : Workspace ring45 3 := ⟨env, core⟩

private def WP : WriterProtected ring45 3 (Phys 3 3 48) :=
  fun _ _ => True

private def k2Host : B9Host.HostRow (Phys 3 3 48) :=
  ⟨ExpiringK2Projection.row h3⟩

/-- Closed field-level computation: FIRE and MOVE are disabled; aligned
follower SIGNAL computes max(1,1,0)=1; the dummy sink sees no bullet. -/
private theorem obstructionPairFixed :
    k2Host.row obstructionCell obstructionCell =
      (obstructionCell, obstructionCell) := by
  decide

private theorem obstructionStepFixed (e : Fin 45) :
    B9Host.hostStep k2Host ring45 obstructionConfig e =
      obstructionConfig := by
  funext i
  simp [B9Host.hostStep, obstructionConfig, obstructionPairFixed]

private theorem obstructionRunFixed (w : List (Fin 45)) :
    runHost k2Host ring45 w obstructionConfig = obstructionConfig := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      change runHost k2Host ring45 w
        (B9Host.hostStep k2Host ring45 obstructionConfig e) =
          obstructionConfig
      rw [obstructionStepFixed]
      exact ih

private theorem obstructionLeaderless :
    HostLeaderless (fun q : Phys 3 3 48 => q) obstructionConfig := by
  change BirthShortDoneTerminalFirstHit.Leaderless obstructionConfig
  intro i
  rfl

private theorem obstructionExpiry :
    ExpiryAt (fun q : Phys 3 3 48 => q) WP X obstructionConfig := by
  constructor
  · constructor
    · exact True.intro
    · intro i hi
      change ResetEchoClearCell obstructionCell
      unfold ResetEchoClearCell
      exact ⟨rfl, rfl⟩
  · intro i hi
    change ComparisonCleanCell obstructionCell
    unfold ComparisonCleanCell
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


private theorem obstructionNotReady :
    ¬ HostReadyWindow (fun q : Phys 3 3 48 => q) ring45
      obstructionConfig := by
  change ¬ BirthCheckChainR1PerBlock.ReadyWindow ring45 obstructionConfig
  intro h
  rcases h with ⟨s, hs⟩
  have h0 := hs 0 (by decide : 0 < 3)
  exact h0.stall rfl

private theorem obstructionNotHit :
    ¬ HostHitInside (fun q : Phys 3 3 48 => q) ring45 X.env.I
      obstructionConfig := by
  change ¬ B6LocalReverseFill.HitInside ring45 X.env.I obstructionConfig
  intro hhit
  apply (B6LocalReverseFill.hitInside_not_unfinished
    ring45 X.env.I obstructionConfig hhit)
  exact ⟨obstructionLeaderless, obstructionNotReady⟩

private theorem obstructionNotSanitized :
    ¬ SanitizedAt (fun q : Phys 3 3 48 => q) WP X obstructionConfig := by
  intro h
  have hk := h.2 (4 : Fin 45) (by decide)
  change K2QuietCell obstructionCell at hk
  unfold K2QuietCell at hk
  have hs := hk.2.1
  change (1 : Fin 2) = 0 at hs
  exact (by decide : (1 : Fin 2) ≠ 0) hs


/-- The old source predicate is genuinely satisfied. -/
theorem obstruction_old_source :
    HostLeaderless (fun q : Phys 3 3 48 => q) obstructionConfig ∧
      ExpiryAt (fun q : Phys 3 3 48 => q) WP X obstructionConfig :=
  ⟨obstructionLeaderless, obstructionExpiry⟩

/-- Stronger than the requested regression: every word fails the complete
old `HostExit`, hence so does every internal word of the stated length. -/
theorem obstruction_old_exit_fails_every_word (w : List (Fin 45)) :
    ¬ HostExit k2Host (fun q : Phys 3 3 48 => q) ring45 X.env.I
      (SanitizedAt (fun q : Phys 3 3 48 => q) WP X)
      (runHost k2Host ring45 w obstructionConfig) := by
  rw [obstructionRunFixed]
  intro h
  rcases h with hS | hHit | hBirth
  · exact obstructionNotSanitized hS
  · exact obstructionNotHit hHit
  · exact hBirth obstructionLeaderless

/-- Regression in the internal-word form. -/
theorem obstruction_old_exit_fails_every_internal_word
    (w : List (Fin 45))
    (_hw : InternalWord X.env.I w)
    (_hlen : w.length ≤ k2DrainLength 3) :
    ¬ HostExit k2Host (fun q : Phys 3 3 48 => q) ring45 X.env.I
      (SanitizedAt (fun q : Phys 3 3 48 => q) WP X)
      (runHost k2Host ring45 w obstructionConfig) :=
  obstruction_old_exit_fails_every_word w

/-- The old generic law is false on the closed pure-K2 host.  The obstruction
uses no wrap edge; in fact it survives arbitrary scheduler words. -/
theorem obstruction_refutes_old_law :
    ¬ HostK2ClearableOrLeader k2Host
      (fun q : Phys 3 3 48 => q) ring45 WP (k2DrainLength 3) := by
  intro h
  obtain ⟨w, hw, hlen, hexit⟩ :=
    h X obstructionConfig obstructionLeaderless obstructionExpiry
  exact (obstruction_old_exit_fails_every_internal_word w hw hlen) hexit

end Regression

-- END PART 2

/-! ## R1 instance statement and proof seams

The corrected law is stated, not assumed proved.  Two full-R1 seams are required
before the reverse-sweep K2 induction can be closed.  The intended proof uses the following already-compiled K2 facts:

* `LDSinkKernelC.absorbProtectedMove`
* `LDSinkKernelC.kernelC_labels`
* `LDSinkKernelC.stallC_pair`, `LDSinkKernelC.stallC_step_signal`
* `LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation`
* `ExpiringK2Projection.observe_row`, `observe_step`, `observe_run`
* `ExpiringK2Projection.row_frame`, `row_nonK2`, `row_controls`
* `ExpiringK2Projection.run_frame`, `run_nonK2`
* `K2BirthDispatcher.initializeNewborn_exact`
* `K2BirthDispatcher.collisionRow_frame`, `collisionRow_of_not_both`
* `K2BirthDispatcher.finalPhysical_nonK2`, `finalPhysical_of_no_birth`
* `K2BirthLeaderNormalize.normalizeLeader_observation`
* `K2BirthLeaderNormalize.normalizedMetadata_signal_of_no_birth`
* `K2BirthLeaderNormalize.observe_row_of_no_birth`
* `K2BirthLeaderNormalize.row_metadata_nonK2`, `row_leader_labels_zero`
* `B6LocalReverseFill.internal_iff` and the interval support lemmas.

`K2GlobalShortPairMass` is intentionally not part of this local leaderless
obligation.
-/

/-- The full R1 prefix must preserve the source invariant
on each internal service while the execution remains leaderless. -/
def R1K2DrainFrame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi))) : Prop :=
  ∀ (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi))) (e : Fin n),
    HostLeaderless (fun q => q) C →
    ExpiryAt (fun q => q) WP X C →
    internal X.env.I e →
    let D := B9Host.hostStep
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring C e
    HostLeaderless (fun q => q) D →
      ExpiryAt (fun q => q) WP X D

/-- On a service whose inputs and outputs are followers,
R1's final K2 observation agrees with the existing dispatcher shadow row. -/
def R1LeaderlessK2Agreement
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) : Prop :=
  ∀ (l r : Phys psi psi (16 * psi)),
    (B6Sanitation.rawCell l).leader = false →
    (B6Sanitation.rawCell r).leader = false →
    let q := (B9Host.r1Host (kappa := psi) (tau := 16 * psi)
      hpsi h2).row l r
    (B6Sanitation.rawCell q.1).leader = false →
    (B6Sanitation.rawCell q.2).leader = false →
      (ExpiringK2Projection.observeCell q.1,
       ExpiringK2Projection.observeCell q.2) =
        K2BirthDispatcher.shadowRow
          (ExpiringK2Projection.observeCell l)
          (ExpiringK2Projection.observeCell r)

/-- The two non-combinatorial seams that the future R1 proof must discharge. -/
def R1K2ProofSeams
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi))) : Prop :=
  R1K2DrainFrame hpsi h2 ring WP ∧ R1LeaderlessK2Agreement hpsi h2

/-- Named R1 instance statement of the corrected law.  Its deterministic word
is exactly the reverse-envelope word of length `envelopeWidth psi - 1`. -/
def R1HostK2ClearableOrLeaderV2
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi))) : Prop :=
  HostK2ClearableOrLeaderV2
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q)
    ring WP (k2DrainLength psi)

/-- Definitional check exposing the exact R1 target without proving the two
open seams. -/
theorem R1HostK2ClearableOrLeaderV2_spec
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi))) :
    R1HostK2ClearableOrLeaderV2 hpsi h2 ring WP ↔
      HostK2ClearableOrLeaderV2
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        (fun q : Phys psi psi (16 * psi) => q)
        ring WP (k2DrainLength psi) := by
  rfl

end B6EntranceV2K2

-- END PART 3

#print axioms B6EntranceV2K2.uniformReadyWindowEscape_of_obligationsV2
#print axioms B6EntranceV2K2.k2DrainWord_internal
#print axioms B6EntranceV2K2.k2DrainWord_length
#print axioms B6EntranceV2K2.Regression.obstruction_old_source
#print axioms B6EntranceV2K2.Regression.obstruction_old_exit_fails_every_internal_word
#print axioms B6EntranceV2K2.Regression.obstruction_refutes_old_law
#print axioms B6EntranceV2K2.R1HostK2ClearableOrLeaderV2_spec
