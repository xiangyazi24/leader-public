import Leader.Wu.Splice.HostRow
import Leader.Wu.Entrance.StageComposition
import Leader.Wu.Entrance.LocalRulerWord
import Leader.Wu.Entrance.WriterSilence
import Leader.Wu.Comparison.PathStallRepair
import Leader.Wu.Splice.TripleHitWords
import Leader.Wu.Birth.CheckChainPerBlock


/-!
# B6 entrance V2


Host-parametric fixed-envelope/core interface.  The executable host is a
`B9Host.HostRow P`; `view` exposes the R1 physical record carried by `P`.
This permits both the current R1 carrier and a future R2 carrier with extra
writer-producer state.


The host-generic matcher section is the `B6StageWordMass` proof pattern with
four substitutions: `Config` becomes `PConfig`, `step1` becomes
`B9Host.hostStep host ring`, `runR` becomes `runHost`, and pair locality is
supplied by `B9Host.hostStep_pairLocal`.
-/


set_option autoImplicit false
set_option Elab.async false


namespace B6EntranceV2


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair PPLLPathStallComparisonRepair
open BirthShortDoneTerminalFirstHit BirthCheckChainR1Ring
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FiniteUniformStoppingTree FixedSpanRenewalPayload
open B6WindowLocality B9OrderedWindowMatcher
open B6LocalReverseFill
open B9Host


variable {n ψ κ τ : Nat} {P : Type}
variable {ring : DirectedRing n}


abbrev Phys (ψ κ τ : Nat) := B9Host.Phys ψ κ τ
abbrev PConfig (n : Nat) (P : Type) := Fin n → P


def physConfig (view : P → Phys ψ κ τ) (C : PConfig n P) :
    B6LocalReverseFill.Config n ψ κ τ :=
  fun i => view (C i)


def entranceKappa (ψ : Nat) : Nat := ψ
def entranceTau (ψ : Nat) : Nat := 16 * ψ


def collarWidth (ψ : Nat) : Nat := ψ + 1
def coreWidth (ψ : Nat) : Nat := 4 * ψ * ψ
def envelopeWidth (ψ : Nat) : Nat :=
  coreWidth ψ + 2 * collarWidth ψ


def envelopeTouchBound (ψ : Nat) : Nat := envelopeWidth ψ + 1


structure Envelope (ring : DirectedRing n) (ψ : Nat) where
  I : Interval ring
  size_eq : I.size = envelopeWidth ψ
  proper : I.size < n


structure Core (ring : DirectedRing n) (ψ : Nat)
    (E : Envelope ring ψ) where
  J : Interval ring
  first_eq : J.first = cell ring E.I.first (collarWidth ψ)
  size_eq : J.size = coreWidth ψ
  subset : ∀ i, support J i = true → support E.I i = true


structure Workspace (ring : DirectedRing n) (ψ : Nat) where
  env : Envelope ring ψ
  core : Core ring ψ env


abbrev WriterProtected (ring : DirectedRing n) (ψ : Nat)
    (P : Type) := Workspace ring ψ → PConfig n P → Prop


def CoreAll (view : P → Phys ψ κ τ) (X : Workspace ring ψ)
    (Pred : Phys ψ κ τ → Prop) (C : PConfig n P) : Prop :=
  ∀ i, support X.core.J i = true → Pred (view (C i))


def CoreBitsAgree (view : P → Phys ψ κ τ) (X : Workspace ring ψ)
    (C D : PConfig n P) : Prop :=
  ∀ i, support X.core.J i = true →
    (B6Sanitation.rawCell (view (C i))).bit =
      (B6Sanitation.rawCell (view (D i))).bit


def ComparisonCleanCell (q : Phys ψ κ τ) : Prop :=
  let u := B6Sanitation.rawCell q
  u.state = .none ∧ u.path = .bot ∧ u.path2 = none ∧
  u.path4 = none ∧ u.path5 = none ∧
  u.p = false ∧ u.p_carry = false ∧
  q.core.erase.path0Crossed = false


def ResetEchoClearCell (q : Phys ψ κ τ) : Prop :=
  let u := B6Sanitation.rawCell q
  u.reset_cmd = false ∧ u.echo = false


def K2QuietCell (q : Phys ψ κ τ) : Prop :=
  let u := B6Sanitation.rawCell q
  u.leader = false ∧ u.signal_B = 0 ∧ u.bullet = 0


def WriterAt (WP : WriterProtected ring ψ P)
    (X : Workspace ring ψ) (C : PConfig n P) : Prop :=
  WP X C


def TrafficAt (view : P → Phys ψ κ τ)
    (WP : WriterProtected ring ψ P)
    (X : Workspace ring ψ) (C : PConfig n P) : Prop :=
  WriterAt WP X C ∧ CoreAll view X ResetEchoClearCell C


def ExpiryAt (view : P → Phys ψ κ τ)
    (WP : WriterProtected ring ψ P)
    (X : Workspace ring ψ) (C : PConfig n P) : Prop :=
  TrafficAt view WP X C ∧ CoreAll view X ComparisonCleanCell C


def SanitizedAt (view : P → Phys ψ κ τ)
    (WP : WriterProtected ring ψ P)
    (X : Workspace ring ψ) (C : PConfig n P) : Prop :=
  ExpiryAt view WP X C ∧ CoreAll view X K2QuietCell C


def CorePrepared (hψ : 0 < ψ) (view : P → Phys ψ κ τ)
    (WP : WriterProtected ring ψ P)
    (X : Workspace ring ψ) (C : PConfig n P) : Prop :=
  SanitizedAt view WP X C ∧
  B6Sanitation.RulerNF ring X.core.J (physConfig view C) ∧
  B6EntranceCompose.CanonicalArc hψ ring X.core.J (physConfig view C) ∧
  B6EntranceCompose.LocalCover ring X.core.J (physConfig view C)


def HostLeaderless (view : P → Phys ψ κ τ) (C : PConfig n P) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless (physConfig view C)


def HostReadyWindow (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (C : PConfig n P) : Prop :=
  BirthCheckChainR1PerBlock.ReadyWindow ring (physConfig view C)


/-- Directly expose the complement alive class used by the final avoidance
rewrite; this is definitionally the physical `B6LocalReverseFill.Unfinished`. -/
def HostAlive (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (C : PConfig n P) : Prop :=
  HostLeaderless view C ∧ ¬ HostReadyWindow view ring C


def HostHitInside (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (I : Interval ring) (C : PConfig n P) : Prop :=
  B6LocalReverseFill.HitInside ring I (physConfig view C)


def runHost (host : HostRow P) (ring : DirectedRing n)
    (w : List (Fin n)) (C : PConfig n P) : PConfig n P :=
  w.foldl (B9Host.hostStep host ring) C


def HostExit (_host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (I : Interval ring)
    (Target : PConfig n P → Prop) (C : PConfig n P) : Prop :=
  Target C ∨ HostHitInside view ring I C ∨ ¬ HostLeaderless view C


def HostRequest (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (I : Interval ring)
    (Target : PConfig n P → Prop) (w : List (Fin n))
    (C : PConfig n P) : Prop :=
  InternalWord I w ∧ HostExit host view ring I Target (runHost host ring w C)


def AgreeOn (I : Interval ring) (C D : PConfig n P) : Prop :=
  ∀ i, support I i = true → C i = D i


def HostIntervalLocal (I : Interval ring)
    (Target : PConfig n P → Prop) : Prop :=
  ∀ C D, AgreeOn I C D → (Target C ↔ Target D)


def HostWriterProtectedLocal (WP : WriterProtected ring ψ P) : Prop :=
  ∀ X : Workspace ring ψ, HostIntervalLocal X.env.I (WriterAt WP X)


def HostCoreBitSilence (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (WP : WriterProtected ring ψ P) : Prop :=
  ∀ (X : Workspace ring ψ) (C : PConfig n P) (e : Fin n),
    WriterAt WP X C → HostLeaderless view C → internal X.env.I e →
    let D := B9Host.hostStep host ring C e
    HostLeaderless view D → WriterAt WP X D ∧ CoreBitsAgree view X C D


def StaticExpiryEndpoint (old out : Phys ψ κ τ) : Prop :=
  deletionActive out.core.erase = false →
  PathProgressView.ofState out.core = PathProgressView.ofState old.core →
  ((old.stall.val = 0 → ComparisonCleanCell out) ∧
   (0 < old.stall.val → out.stall.val < old.stall.val))


def HostStaticExpiryTick (host : HostRow P)
    (view : P → Phys ψ κ τ) : Prop :=
  ∀ l r : P,
    let q := host.row l r
    StaticExpiryEndpoint (view l) (view q.1) ∧
      StaticExpiryEndpoint (view r) (view q.2)


def HostStageWord (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (_WP : WriterProtected ring ψ P)
    (From To : Workspace ring ψ → PConfig n P → Prop) (L : Nat) : Prop :=
  ∀ (X : Workspace ring ψ) (C : PConfig n P),
    HostLeaderless view C → From X C →
    ∃ w : List (Fin n), InternalWord X.env.I w ∧ w.length ≤ L ∧
      HostExit host view ring X.env.I (To X) (runHost host ring w C)


def HostCoreStageWord (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (_WP : WriterProtected ring ψ P)
    (From To : Workspace ring ψ → PConfig n P → Prop) (L : Nat) : Prop :=
  ∀ (X : Workspace ring ψ) (C : PConfig n P),
    HostLeaderless view C → From X C →
    ∃ w : List (Fin n), InternalWord X.env.I w ∧
      InternalWord X.core.J w ∧ w.length ≤ L ∧
      HostExit host view ring X.env.I (To X) (runHost host ring w C)


def HostWriterAdmission (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (WP : WriterProtected ring ψ P) (L : Nat) : Prop :=
  ∀ C : PConfig n P, HostLeaderless view C →
    ∃ X : Workspace ring ψ, ∃ w : List (Fin n),
      InternalWord X.env.I w ∧ w.length ≤ L ∧
      HostExit host view ring X.env.I (WriterAt WP X) (runHost host ring w C)


def HostDirectionalTrafficExit (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (WP : WriterProtected ring ψ P) (L : Nat) : Prop :=
  HostStageWord host view ring WP (WriterAt WP) (TrafficAt view WP) L


def HostComparisonExpiryWord (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (WP : WriterProtected ring ψ P) (L : Nat) : Prop :=
  HostStageWord host view ring WP (TrafficAt view WP) (ExpiryAt view WP) L


def HostK2ClearableOrLeader (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (WP : WriterProtected ring ψ P) (L : Nat) : Prop :=
  HostStageWord host view ring WP (ExpiryAt view WP) (SanitizedAt view WP) L


def HostRulerWord (hψ : 0 < ψ) (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (WP : WriterProtected ring ψ P) (L : Nat) : Prop :=
  HostCoreStageWord host view ring WP (SanitizedAt view WP)
    (CorePrepared hψ view WP) L


def HostRouteWord (hψ : 0 < ψ) (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (WP : WriterProtected ring ψ P) (L : Nat) : Prop :=
  HostCoreStageWord host view ring WP (CorePrepared hψ view WP)
    (fun _ _ => False) L


structure StageBudget where
  L : Nat
  M : Nat
  B : Nat
  Q : Nat


structure EntranceBudgets where
  writer : StageBudget
  traffic : StageBudget
  expiry : StageBudget
  k2 : StageBudget
  ruler : StageBudget
  route : StageBudget


def postWriterL (b : EntranceBudgets) : Nat :=
  (((b.traffic.L + b.expiry.L) + b.k2.L) + b.ruler.L) + b.route.L


def postWriterQ (b : EntranceBudgets) : Nat :=
  (((b.traffic.Q * b.expiry.Q) * b.k2.Q) * b.ruler.Q) * b.route.Q


def postWriterB (n : Nat) (b : EntranceBudgets) : Nat :=
  2 * n * postWriterL b


def entranceB (n : Nat) (b : EntranceBudgets) : Nat :=
  b.writer.B + postWriterB n b


def entranceQ (b : EntranceBudgets) : Nat :=
  b.writer.Q * postWriterQ b


def StageBudget.Valid (n : Nat) (b : StageBudget) : Prop :=
  B6EntranceCompose.EscapeBudget n b.L b.M b.B b.Q


/-- The writer matcher uses its own `M`; therefore it must dominate the fixed
workspace touch bound.  The post-writer tail pays one matcher for the whole
fixed envelope and carries its own explicit product inequality. -/
def EntranceBudgets.Valid (n ψ : Nat) (b : EntranceBudgets) : Prop :=
  b.writer.Valid n ∧
  envelopeTouchBound ψ ≤ b.writer.M ∧
  b.traffic.Valid n ∧ b.expiry.Valid n ∧
  b.k2.Valid n ∧ b.ruler.Valid n ∧ b.route.Valid n ∧
  1 ≤ postWriterQ b ∧
  (4 * envelopeTouchBound ψ) ^ postWriterL b ≤ postWriterQ b


structure EntranceHostLaws (hψ : 0 < ψ) (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (WP : WriterProtected ring ψ P) (b : EntranceBudgets) : Prop where
  writerLocal : HostWriterProtectedLocal WP
  bitSilence : HostCoreBitSilence host view ring WP
  staticExpiry : HostStaticExpiryTick host view
  writerAdmission : HostWriterAdmission host view ring WP b.writer.L
  trafficWord : HostDirectionalTrafficExit host view ring WP b.traffic.L
  expiryWord : HostComparisonExpiryWord host view ring WP b.expiry.L
  k2Word : HostK2ClearableOrLeader host view ring WP b.k2.L
  rulerWord : HostRulerWord hψ host view ring WP b.ruler.L
  routeWord : HostRouteWord hψ host view ring WP b.route.L


/-! ## Host-generic ordered-matcher mass -/

private theorem internalWord_append (I : Interval ring)
    (u v : List (Fin n)) (hu : InternalWord I u) (hv : InternalWord I v) :
    InternalWord I (u ++ v) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hu e he
  · exact hv e he

private theorem runHost_append (host : HostRow P) (ring : DirectedRing n)
    (u v : List (Fin n)) (C : PConfig n P) :
    runHost host ring (u ++ v) C =
      runHost host ring v (runHost host ring u C) := by
  simp only [runHost, List.foldl_append]

theorem runHost_outside (host : HostRow P) (ring : DirectedRing n)
    (I : Interval ring) (i : Fin n) (hi : support I i = false) :
    ∀ (w : List (Fin n)) (C : PConfig n P),
      InternalWord I w → runHost host ring w C i = C i := by
  intro w
  induction w with
  | nil =>
      intro C _
      rfl
  | cons e w ih =>
      intro C hw
      have he := (internal_iff I e).mp (hw e List.mem_cons_self)
      have ht : InternalWord I w :=
        fun f hf => hw f (List.mem_cons_of_mem e hf)
      change runHost host ring w (B9Host.hostStep host ring C e) i = C i
      rw [ih (B9Host.hostStep host ring C e) ht]
      apply (B9Host.hostStep_pairLocal host ring).other
      · intro hie
        have hit : support I i = true := by
          rw [hie]
          exact he.1
        rw [hit] at hi
        cases hi
      · intro hie
        have hit : support I i = true := by
          rw [hie]
          exact he.2
        rw [hit] at hi
        cases hi

theorem hostHitInside_of_agree (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (I : Interval ring) (C D : PConfig n P)
    (hCD : AgreeOn I C D) (h : HostHitInside view ring I C) :
    HostHitInside view ring I D := by
  apply B6LocalReverseFill.hitInside_of_agree ring I
    (physConfig view C) (physConfig view D) ?_ h
  intro i hi
  exact congrArg view (hCD i hi)

def HostPending (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (Target : PConfig n P → Prop) (C : PConfig n P) : Prop :=
  HostAlive view ring C ∧ ¬ Target C

theorem hostExit_not_pending (_host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (I : Interval ring)
    (Target : PConfig n P → Prop) (C : PConfig n P)
    (h : HostExit _host view ring I Target C) :
    ¬ HostPending view ring Target C := by
  intro hp
  rcases h with hT | hHit | hBirth
  · exact hp.2 hT
  · have hU : B6LocalReverseFill.Unfinished ring (physConfig view C) := hp.1
    exact B6LocalReverseFill.hitInside_not_unfinished ring I
      (physConfig view C) hHit hU
  · exact hBirth hp.1.1

theorem avoidCount_eq_hostPending (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (Target : PConfig n P → Prop) (C : PConfig n P) (T : Nat) :
    avoidCount (B9Host.hostStep host ring) (HostAlive view ring) Target C T =
      aliveCount (B9Host.hostStep host ring)
        (HostPending view ring Target) C T := by
  change avoidCount (B9Host.hostStep host ring)
      (HostAlive view ring) Target C T =
    aliveCount (B9Host.hostStep host ring)
      (fun D => HostAlive view ring D ∧ ¬ Target D) C T
  exact B6LocalReverseFill.avoidCount_eq_alive_complement
    (B9Host.hostStep host ring) (HostAlive view ring) Target C T

theorem request_exit_of_agree (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (I : Interval ring) (Target : PConfig n P → Prop)
    (req : List (Fin n)) (C : PConfig n P)
    (hC : HostLeaderless view C) (hint : InternalWord I req)
    (hlocal : HostIntervalLocal I Target)
    (hexit : HostExit host view ring I Target (runHost host ring req C))
    (D : PConfig n P)
    (hCD : AgreeOn I (runHost host ring req C) D) :
    HostExit host view ring I Target D := by
  rcases hexit with hT | hHit | hBirth
  · exact Or.inl ((hlocal _ _ hCD).mp hT)
  · exact Or.inr (Or.inl
      (hostHitInside_of_agree view ring I _ _ hCD hHit))
  · right
    right
    intro hD
    apply hBirth
    intro i
    by_cases hi : support I i = true
    · have heq : view ((runHost host ring req C) i) = view (D i) :=
        congrArg view (hCD i hi)
      change (view ((runHost host ring req C) i)).core.core.leader = false
      rw [heq]
      exact hD i
    · have hf : support I i = false := by
        cases hb : support I i with
        | false => rfl
        | true => exact (hi hb).elim
      have hout := runHost_outside host ring I i hf req C hint
      change (view ((runHost host ring req C) i)).core.core.leader = false
      rw [hout]
      exact hC i


theorem matcher_success_not_pending (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (I : Interval ring) (Target : PConfig n P → Prop)
    (req : List (Fin n)) (C : PConfig n P)
    (hC : HostLeaderless view C) (hne : req ≠ [])
    (hint : InternalWord I req) (hlocal : HostIntervalLocal I Target)
    (hexit : HostExit host view ring I Target (runHost host ring req C))
    (u : List (Fin n))
    (hs : B9SpliceTripleHitWords.runNode
      (ordStep (touchOf ring (support I))) (.active req) u = StopNode.success) :
    aliveBit (B9Host.hostStep host ring)
      (HostPending view ring Target) C u = 0 := by
  classical
  rcases B6WindowLocality.success_prefix_agrees
      (B9Host.hostStep_pairLocal host ring)
      (support I) req hne (fun e he => hint e he) u hs C with
    ⟨p, hp, hagree⟩
  have hexit' := request_exit_of_agree host view ring I Target req C
    hC hint hlocal hexit (runHost host ring p C)
    (fun i hi => (hagree i hi).symm)
  unfold aliveBit
  apply if_neg
  intro halive
  rcases hp with ⟨v, rfl⟩
  have hsplit := (aliveAlong_append (B9Host.hostStep host ring)
    (HostPending view ring Target) C p v).mp halive
  have hpending : HostPending view ring Target
      (p.foldl (B9Host.hostStep host ring) C) :=
    aliveAlong_good hsplit.2
  exact hostExit_not_pending host view ring I Target
    (runHost host ring p C) hexit' hpending

private theorem power_mono_exp (b r s : Nat) (hb : 1 ≤ b) (hrs : r ≤ s) :
    b ^ r ≤ b ^ s := by
  have he : r + (s - r) = s := by omega
  have hd : 1 ≤ b ^ (s - r) := Nat.pow_pos (by omega)
  calc
    b ^ r ≤ b ^ r * b ^ (s - r) := Nat.le_mul_of_pos_right _ hd
    _ = b ^ s := by rw [← Nat.pow_add, he]

private theorem disjoint_escape (A B N Q : Nat)
    (hpair : A + B ≤ N) (hmass : N ≤ Q * B) :
    Q * A ≤ (Q - 1) * N := by
  have hs : Q * A + Q * B ≤ Q * N := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left Q hpair
  rw [Nat.sub_one_mul]
  omega

private theorem alive_mass_pad {S : Type}
    (step : S → Fin n → S) (Good : S → Prop) (C : S)
    (T U Q : Nat) (hTU : T ≤ U)
    (hbase : Q * aliveCount step Good C T ≤ (Q - 1) * n ^ T) :
    Q * aliveCount step Good C U ≤ (Q - 1) * n ^ U := by
  have hsum : T + (U - T) = U := by omega
  have hp := BirthTwoStageEscape.alive_pad step Good (U - T) T C
  rw [hsum] at hp
  calc
    Q * aliveCount step Good C U
        ≤ Q * (aliveCount step Good C T * n ^ (U - T)) :=
      Nat.mul_le_mul_left Q hp
    _ = (Q * aliveCount step Good C T) * n ^ (U - T) := by
      rw [Nat.mul_assoc]
    _ ≤ ((Q - 1) * n ^ T) * n ^ (U - T) :=
      Nat.mul_le_mul_right _ hbase
    _ = (Q - 1) * n ^ U := by
      rw [Nat.mul_assoc, ← Nat.pow_add, hsum]

private theorem request_exit_alive_mass (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (I : Interval ring) (Target : PConfig n P → Prop)
    (req : List (Fin n)) (C : PConfig n P)
    (L M : Nat) (hM : 1 ≤ M) (hlen : req.length ≤ L)
    (ht : touchCount (touchOf ring (support I)) ≤ M)
    (hC : HostLeaderless view C) (hne : req ≠ [])
    (hint : InternalWord I req) (hlocal : HostIntervalLocal I Target)
    (hexit : HostExit host view ring I Target (runHost host ring req C)) :
    (4 * M) ^ L * aliveCount (B9Host.hostStep host ring)
        (HostPending view ring Target) C (2 * n * req.length) ≤
      ((4 * M) ^ L - 1) * n ^ (2 * n * req.length) := by
  classical
  let touch : Fin n → Bool := touchOf ring (support I)
  let st : PConfig n P → Fin n → PConfig n P := B9Host.hostStep host ring
  let H := 2 * n * req.length
  let A := aliveCount st (HostPending view ring Target) C H
  let W := wordSum n H (fun u =>
    successWeight (runStopped (ordStep touch) (.active req) u))
  let N := n ^ H
  let Q := (4 * M) ^ L
  have hmass := B9OrderedWindowMatcher.ordered_mass touch req hne
    (fun e he => internal_touch I e (hint e he))
  rw [← B9SpliceMatcherMass.wordSum_success_eq_successCount] at hmass
  change 3 ^ req.length * N ≤
    (4 * touchCount touch) ^ req.length * W at hmass
  have hpair : A + W ≤ N := by
    change wordSum n H (aliveBit st (HostPending view ring Target) C) +
      wordSum n H (fun u =>
        successWeight (runStopped (ordStep touch) (.active req) u)) ≤ n ^ H
    apply BirthCheckChainR1Mass.wordSum_pair_le
    intro u
    by_cases hsu : runStopped (ordStep touch) (.active req) u = StopNode.success
    · have hs : B9SpliceTripleHitWords.runNode
          (ordStep touch) (.active req) u = StopNode.success := by
        rw [B9SpliceMatcherMass.runNode_eq_runStopped]
        exact hsu
      have hz := matcher_success_not_pending host view ring I Target req C
        hC hne hint hlocal hexit u hs
      change aliveBit st (HostPending view ring Target) C u = 0 at hz
      rw [hz, hsu]
      exact Nat.le_refl 1
    · have hzero : successWeight (runStopped (ordStep touch)
          (.active req) u) = 0 := by
        cases hu : runStopped (ordStep touch) (.active req) u with
        | active x => rfl
        | success => exact (hsu hu).elim
        | failure => rfl
      rw [hzero, Nat.add_zero]
      exact aliveBit_le_one st (HostPending view ring Target) C u
  have hbase : 4 * touchCount touch ≤ 4 * M := Nat.mul_le_mul_left 4 ht
  have hcoef : (4 * touchCount touch) ^ req.length ≤ Q :=
    Nat.le_trans (Nat.pow_le_pow_left hbase req.length)
      (power_mono_exp (4 * M) req.length L (by omega) hlen)
  have hthree : 1 ≤ 3 ^ req.length := Nat.pow_pos (by omega)
  have hN : N ≤ 3 ^ req.length * N := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right N hthree
  have hscale : N ≤ Q * W :=
    Nat.le_trans hN (Nat.le_trans hmass (Nat.mul_le_mul_right W hcoef))
  change Q * A ≤ (Q - 1) * N
  exact disjoint_escape A W N Q hpair hscale

theorem hostRequest_mass (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (I : Interval ring)
    (Target : PConfig n P → Prop) (w : List (Fin n)) (C : PConfig n P)
    (L M : Nat) (hM : 1 ≤ M) (hL : w.length ≤ L)
    (ht : touchCount (touchOf ring (support I)) ≤ M)
    (hC : HostLeaderless view C) (hlocal : HostIntervalLocal I Target)
    (hreq : HostRequest host view ring I Target w C) :
    (4 * M) ^ L * avoidCount (B9Host.hostStep host ring)
        (HostAlive view ring) Target C (2 * n * L) ≤
      ((4 * M) ^ L - 1) * n ^ (2 * n * L) := by
  rcases hreq with ⟨hint, hexit⟩
  rw [avoidCount_eq_hostPending host view ring Target C (2 * n * L)]
  by_cases hw0 : w = []
  · have hbad : ¬ HostPending view ring Target C := by
      apply hostExit_not_pending host view ring I Target C
      simpa only [hw0, runHost, List.foldl_nil] using hexit
    rw [BirthTwoStageEscape.aliveCount_not_good
      (B9Host.hostStep host ring) (HostPending view ring Target)
      C hbad (2 * n * L), Nat.mul_zero]
    exact Nat.zero_le _
  · have hm := request_exit_alive_mass host view ring I Target w C L M
      hM hL ht hC hw0 hint hlocal hexit
    exact alive_mass_pad (B9Host.hostStep host ring)
      (HostPending view ring Target) C
      (2 * n * w.length) (2 * n * L) ((4 * M) ^ L)
      (Nat.mul_le_mul_left (2 * n) hL) hm

private theorem escape_denominator_mono
    (A N q Q : Nat) (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (hA : A ≤ N) (h : q * A ≤ (q - 1) * N) :
    Q * A ≤ (Q - 1) * N := by
  have hsum : q + (Q - q) = Q := by omega
  have hsum' : (q - 1) + (Q - q) = Q - 1 := by omega
  have hleft : Q * A = (q + (Q - q)) * A :=
    congrArg (fun z : Nat => z * A) hsum.symm
  have hright : ((q - 1) + (Q - q)) * N = (Q - 1) * N :=
    congrArg (fun z : Nat => z * N) hsum'
  calc
    Q * A = (q + (Q - q)) * A := hleft
    _ = q * A + (Q - q) * A := Nat.add_mul _ _ _
    _ ≤ (q - 1) * N + (Q - q) * N :=
      Nat.add_le_add h (Nat.mul_le_mul_left _ hA)
    _ = ((q - 1) + (Q - q)) * N := (Nat.add_mul _ _ _).symm
    _ = (Q - 1) * N := hright

theorem hostRequest_mass_of_budget (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (I : Interval ring) (Target : PConfig n P → Prop)
    (w : List (Fin n)) (C : PConfig n P)
    (L M B Q : Nat)
    (hbudget : B6EntranceCompose.EscapeBudget n L M B Q)
    (hL : w.length ≤ L)
    (ht : touchCount (touchOf ring (support I)) ≤ M)
    (hC : HostLeaderless view C) (hlocal : HostIntervalLocal I Target)
    (hreq : HostRequest host view ring I Target w C) :
    Q * avoidCount (B9Host.hostStep host ring)
        (HostAlive view ring) Target C B ≤ (Q - 1) * n ^ B := by
  rcases hbudget with ⟨hM, _, hB, hqQ⟩
  subst B
  have hbase := hostRequest_mass host view ring I Target w C L M
    hM hL ht hC hlocal hreq
  rw [avoidCount_eq_hostPending host view ring Target C (2 * n * L)] at hbase ⊢
  have hq : 1 ≤ (4 * M) ^ L := Nat.pow_pos (by omega)
  exact escape_denominator_mono
    (aliveCount (B9Host.hostStep host ring)
      (HostPending view ring Target) C (2 * n * L))
    (n ^ (2 * n * L)) ((4 * M) ^ L) Q hq hqQ
    (BirthTwoStageEscape.aliveCount_le_pow
      (B9Host.hostStep host ring) (HostPending view ring Target)
      C (2 * n * L)) hbase

/-! ## Fixed-X tail construction and two-stage composition -/

theorem envelope_touch_le (X : Workspace ring ψ) :
    touchCount (touchOf ring (support X.env.I)) ≤ envelopeTouchBound ψ := by
  have h := B6LocalReverseFill.touchCount_support_le X.env.I
  unfold envelopeTouchBound
  rw [X.env.size_eq] at h
  exact h

private theorem continue_request (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
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
      refine ⟨u ++ v, internalWord_append I u v huI hvI, ?_, ?_⟩
      · simp only [List.length_append]
        omega
      · rw [runHost_append]
        exact hvE
    · have hlen : u.length ≤ Lu + Lv := by omega
      exact ⟨u, huI, hlen, Or.inr (Or.inr hD)⟩
  · have hlen : u.length ≤ Lu + Lv := by omega
    exact ⟨u, huI, hlen, Or.inr (Or.inl hHit)⟩
  · have hlen : u.length ≤ Lu + Lv := by omega
    exact ⟨u, huI, hlen, Or.inr (Or.inr hBirth)⟩

theorem coreStageWord_stage (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (WP : WriterProtected ring ψ P)
    (From To : Workspace ring ψ → PConfig n P → Prop) (L : Nat)
    (h : HostCoreStageWord host view ring WP From To L) :
    HostStageWord host view ring WP From To L := by
  intro X C hC hFrom
  obtain ⟨w, hE, _, hL, hExit⟩ := h X C hC hFrom
  exact ⟨w, hE, hL, hExit⟩

theorem postWriterRequest (hψ : 0 < ψ) (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (WP : WriterProtected ring ψ P) (b : EntranceBudgets)
    (hTraffic : HostDirectionalTrafficExit host view ring WP b.traffic.L)
    (hExpiry : HostComparisonExpiryWord host view ring WP b.expiry.L)
    (hK2 : HostK2ClearableOrLeader host view ring WP b.k2.L)
    (hRuler : HostRulerWord hψ host view ring WP b.ruler.L)
    (hRoute : HostRouteWord hψ host view ring WP b.route.L)
    (X : Workspace ring ψ) (C : PConfig n P)
    (hC : HostLeaderless view C) (hW : WriterAt WP X C) :
    ∃ w : List (Fin n), InternalWord X.env.I w ∧
      w.length ≤ postWriterL b ∧
      HostExit host view ring X.env.I (fun _ => False)
        (runHost host ring w C) := by
  obtain ⟨u, huI, huL, huE⟩ := hTraffic X C hC hW
  obtain ⟨u1, hu1I, hu1L, hu1E⟩ :=
    continue_request host view ring X.env.I
      (TrafficAt view WP X) (ExpiryAt view WP X)
      C u b.traffic.L b.expiry.L huI huL huE
      (fun D hD hT => hExpiry X D hD hT)
  obtain ⟨u2, hu2I, hu2L, hu2E⟩ :=
    continue_request host view ring X.env.I
      (ExpiryAt view WP X) (SanitizedAt view WP X)
      C u1 (b.traffic.L + b.expiry.L) b.k2.L hu1I hu1L hu1E
      (fun D hD hE => hK2 X D hD hE)
  have hRuler' := coreStageWord_stage host view ring WP
    (SanitizedAt view WP) (CorePrepared hψ view WP) b.ruler.L hRuler
  obtain ⟨u3, hu3I, hu3L, hu3E⟩ :=
    continue_request host view ring X.env.I
      (SanitizedAt view WP X) (CorePrepared hψ view WP X)
      C u2 ((b.traffic.L + b.expiry.L) + b.k2.L) b.ruler.L
      hu2I hu2L hu2E (fun D hD hS => hRuler' X D hD hS)
  have hRoute' := coreStageWord_stage host view ring WP
    (CorePrepared hψ view WP) (fun _ _ => False) b.route.L hRoute
  obtain ⟨u4, hu4I, hu4L, hu4E⟩ :=
    continue_request host view ring X.env.I
      (CorePrepared hψ view WP X) (fun _ => False)
      C u3 (((b.traffic.L + b.expiry.L) + b.k2.L) + b.ruler.L)
      b.route.L hu3I hu3L hu3E
      (fun D hD hP => hRoute' X D hD hP)
  exact ⟨u4, hu4I, hu4L, hu4E⟩

def WriterStage (WP : WriterProtected ring ψ P) (C : PConfig n P) : Prop :=
  ∃ X : Workspace ring ψ, WriterAt WP X C

theorem writerAdmission_mass (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (WP : WriterProtected ring ψ P)
    (b : EntranceBudgets)
    (hbud : b.writer.Valid n)
    (hTouch : envelopeTouchBound ψ ≤ b.writer.M)
    (hlocal : HostWriterProtectedLocal WP)
    (hword : HostWriterAdmission host view ring WP b.writer.L) :
    ∀ C : PConfig n P, HostAlive view ring C →
      b.writer.Q * avoidCount (B9Host.hostStep host ring)
          (HostAlive view ring) (WriterStage WP) C b.writer.B ≤
        (b.writer.Q - 1) * n ^ b.writer.B := by
  intro C hC
  obtain ⟨X, w, hI, hL, hExit⟩ := hword C hC.1
  have ht : touchCount (touchOf ring (support X.env.I)) ≤ b.writer.M :=
    Nat.le_trans (envelope_touch_le X) hTouch
  have hm := hostRequest_mass_of_budget host view ring X.env.I
    (WriterAt WP X) w C b.writer.L b.writer.M b.writer.B b.writer.Q
    hbud hL ht hC.1 (hlocal X) ⟨hI, hExit⟩
  have hmono := B6EntranceCompose.avoidCount_mono_target
    (B9Host.hostStep host ring) (HostAlive view ring)
    (WriterAt WP X) (WriterStage WP)
    (fun D hD => ⟨X, hD⟩) C b.writer.B
  exact Nat.le_trans (Nat.mul_le_mul_left b.writer.Q hmono) hm

theorem postWriter_mass (hψ : 0 < ψ) (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (WP : WriterProtected ring ψ P) (b : EntranceBudgets)
    (hpostQ : 1 ≤ postWriterQ b)
    (hpostMatch : (4 * envelopeTouchBound ψ) ^ postWriterL b ≤ postWriterQ b)
    (hTraffic : HostDirectionalTrafficExit host view ring WP b.traffic.L)
    (hExpiry : HostComparisonExpiryWord host view ring WP b.expiry.L)
    (hK2 : HostK2ClearableOrLeader host view ring WP b.k2.L)
    (hRuler : HostRulerWord hψ host view ring WP b.ruler.L)
    (hRoute : HostRouteWord hψ host view ring WP b.route.L) :
    ∀ (X : Workspace ring ψ) (C : PConfig n P),
      HostAlive view ring C → WriterAt WP X C →
      postWriterQ b * aliveCount (B9Host.hostStep host ring)
          (HostAlive view ring) C (postWriterB n b) ≤
        (postWriterQ b - 1) * n ^ (postWriterB n b) := by
  intro X C hC hW
  obtain ⟨w, hI, hL, hExit⟩ := postWriterRequest hψ host view ring WP b
    hTraffic hExpiry hK2 hRuler hRoute X C hC.1 hW
  have hM : 1 ≤ envelopeTouchBound ψ := by
    unfold envelopeTouchBound envelopeWidth coreWidth collarWidth
    omega
  have hbudget : B6EntranceCompose.EscapeBudget n
      (postWriterL b) (envelopeTouchBound ψ)
      (postWriterB n b) (postWriterQ b) :=
    ⟨hM, hpostQ, rfl, hpostMatch⟩
  have hm := hostRequest_mass_of_budget host view ring X.env.I
    (fun _ => False) w C (postWriterL b) (envelopeTouchBound ψ)
    (postWriterB n b) (postWriterQ b) hbudget hL
    (envelope_touch_le X) hC.1
    (by intro A D _; simp) ⟨hI, hExit⟩
  rw [avoidCount_eq_hostPending host view ring (fun _ => False)
    C (postWriterB n b)] at hm
  have hPendingFalse :
      (HostPending view ring (fun _ : PConfig n P => False)) =
        HostAlive view ring := by
    funext D
    simp only [HostPending, not_false_eq_true, and_true]
  rw [hPendingFalse] at hm
  exact hm


def UniformHostReadyWindowEscape (host : HostRow P)
    (view : P → Phys ψ κ τ) (ring : DirectedRing n)
    (B Q : Nat) : Prop :=
  ∀ C : PConfig n P, HostLeaderless view C →
    Q * avoidCount (B9Host.hostStep host ring)
        (HostLeaderless view) (HostReadyWindow view ring) C B ≤
      (Q - 1) * n ^ B

theorem uniformReadyWindowEscape_of_obligations
    (hψ : 0 < ψ) (host : HostRow P) (view : P → Phys ψ κ τ)
    (ring : DirectedRing n) (WP : WriterProtected ring ψ P)
    (b : EntranceBudgets) (hbud : b.Valid n ψ)
    (hlaws : EntranceHostLaws hψ host view ring WP b) :
    UniformHostReadyWindowEscape host view ring (entranceB n b) (entranceQ b) := by
  rcases hbud with
    ⟨hBw, hTouch, _, _, _, _, _, hPostQ, hPostMatch⟩
  have hQw : 1 ≤ b.writer.Q := hBw.2.1
  have hWriter := writerAdmission_mass host view ring WP b hBw hTouch
    hlaws.writerLocal hlaws.writerAdmission
  have hTail : ∀ C : PConfig n P, HostAlive view ring C → WriterStage WP C →
      postWriterQ b * aliveCount (B9Host.hostStep host ring)
          (HostAlive view ring) C (postWriterB n b) ≤
        (postWriterQ b - 1) * n ^ (postWriterB n b) := by
    intro C hC hStage
    rcases hStage with ⟨X, hX⟩
    exact postWriter_mass hψ host view ring WP b hPostQ hPostMatch
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

/-! ## Instance obligations

Compiled R1 leaves already available are intentionally recorded only as
supporting facts, not as proofs of the whole V2 contracts:
* `B9Host.hostStep_pairLocal`: complete, host-generic pair locality.
* `B6WriterSilence.row_empty_of_left_follower`: full R1 bit/path3 preservation
  on the two-empty-endpoint mode.
* `B6WriterSilence.stationaryPersistentAuthorizedRow_blocked`: blocked mode
  only at the stationary writer, not the full R1 row.
* `PPLLPathStallComparisonRepair.pathExpireOne_decreases_of_static`,
  `pathExpireOne_succ_of_static`, and `pathExpireOne_zero_clears`: timer leaves.
* `B6LocalRulerWord.local_ruler_word_sharp` plus `B6LocalRulerE` ordinary
  label-or-leader leaves: the R1 ruler engine, but not the V2 preservation,
  absolute-anchor, or cover bridge.
No compiled theorem at this snapshot supplies the entire R1
`HostWriterAdmission`, `HostDirectionalTrafficExit`,
`HostComparisonExpiryWord`, `HostK2ClearableOrLeader`, `HostRulerWord`, or
`HostRouteWord` contract.
-/

def R1InstanceObligations
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (WP : WriterProtected ring ψ (Phys ψ ψ (16 * ψ)))
    (b : EntranceBudgets) : Prop :=
  b.Valid n ψ ∧
  EntranceHostLaws hψ
    (B9Host.r1Host (kappa := ψ) (tau := 16 * ψ) hψ h2)
    (fun q : Phys ψ ψ (16 * ψ) => q) ring WP b


/-- R2 remains an abstract instance obligation.  The current producer-repair
candidate is deliberately not imported here; once its carrier compiles, use
its `.base` projection as `view2` and its repaired binary row as `host2`. -/
def R2InstanceObligations
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (P2 : Type) (view2 : P2 → Phys ψ ψ (16 * ψ))
    (host2 : HostRow P2)
    (WP : WriterProtected ring ψ P2) (b : EntranceBudgets) : Prop :=
  b.Valid n ψ ∧ EntranceHostLaws hψ host2 view2 ring WP b

end B6EntranceV2
