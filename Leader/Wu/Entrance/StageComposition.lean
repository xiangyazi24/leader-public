import Leader.Wu.Entrance.LocalRuler
import Leader.Wu.Entrance.LocalRulerExceptional
import Leader.Wu.Entrance.WriterSilence
import Leader.Wu.Entrance.Sanitation
import Leader.Core.CyclicBitCover

/-!
# B6 entrance composition

Stopped-prefix composition for the S-keep entrance.  This file contains only
compiled-style definitions and consequences of named obligation Props.  The
physical producers of those Props remain separate proof obligations.

The stage order is:

  writer silence -> joint sanitation/ruler -> final ruler + bit cover -> routing.

No stage predicate is assumed to persist until a fixed block endpoint.  Each
composition below stops at the first reached stage and uses
`BirthTwoStageEscape.two_stage_escape` on the complement alive class.
-/

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceCompose

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
  BirthCheckChainR1PerBlock BirthCheckChainR1Mass
open BirthTwoStageEscape BirthLeaderlessBirthMassRenewal
open FiniteUniformStoppingTree FixedSpanRenewalPayload
open B6WindowLocality B9OrderedWindowMatcher
open B6LocalReverseFill

variable {n ψ κ τ : Nat}

abbrev Config (n ψ κ τ : Nat) :=
  BirthCheckPermitRepairLeaf.FC n ψ κ τ

/-- Full successor chain on the physical arc, including its first edge. -/
def CanonicalArc (hψ : 0 < ψ) (ring : DirectedRing n)
    (I : Interval ring) (C : Config n ψ κ τ) : Prop :=
  ∀ k : Nat, k + 1 < I.size ->
    (B6Sanitation.rawCell (C (cell ring I.first (k + 1)))).label =
      B6LocalRuler.nextLabel hψ
        (B6Sanitation.rawCell (C (cell ring I.first k))).label

/-- Number of complete ψ-cell bit blocks readable from the interval. -/
def arcBlockCount (ψ : Nat) {ring : DirectedRing n}
    (I : Interval ring) : Nat :=
  I.size / ψ

/-- Read the resident bit vector block-by-block only at the reached state. -/
def arcReadBits (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) :
    B6BitCover.Word (arcBlockCount ψ I) ψ :=
  fun j k =>
    (B6Sanitation.rawCell
      (C (cell ring I.first (j.val * ψ + k.val)))).bit

/--
A covered target whose entire 2ψ predecessor radius is physically to its left
inside the arc.  The `Covered` witness is computed from the endpoint bits.
-/
def LocalCover (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  ∃ j : Fin (arcBlockCount ψ I),
    2 * ψ ≤ j.val ∧
    (j.val + 1) * ψ ≤ I.size ∧
    B6BitCover.Covered (arcReadBits ring I C) (2 * ψ) j

/--
Prepared endpoint for route selection.  `SanNF` already carries its own ruler
and writer conjuncts; the explicit successor-chain and writer conjuncts are
kept here because they are the interfaces consumed by the ruler/router leaves.
-/
def Prepared (hψ : 0 < ψ) (ring : DirectedRing n)
    (I : Interval ring) (C : Config n ψ κ τ) : Prop :=
  CanonicalArc hψ ring I C ∧
  B6Sanitation.SanNF ring I C ∧
  B6Sanitation.WriterSilent ring I C ∧
  LocalCover ring I C

/-- First stopped stage: some bounded workspace has a bit-silent writer mode. -/
def WriterStage (ring : DirectedRing n) (W : Nat)
    (C : Config n ψ κ τ) : Prop :=
  ∃ I : Interval ring,
    I.size ≤ W ∧ B6Sanitation.WriterSilent ring I C

/-- Joint phase endpoint before the final global ruler sweep. -/
def JointStage (ring : DirectedRing n) (W : Nat)
    (C : Config n ψ κ τ) : Prop :=
  ∃ I : Interval ring,
    I.size ≤ W ∧
    B6Sanitation.WriterSilent ring I C ∧
    B6Sanitation.SanCells ring I C

/-- Final prepared stage; the target is selected only here. -/
def PreparedStage (hψ : 0 < ψ) (ring : DirectedRing n) (W : Nat)
    (C : Config n ψ κ τ) : Prop :=
  ∃ I : Interval ring, I.size ≤ W ∧ Prepared hψ ring I C

/-- Ordered-matcher bookkeeping carried by each physical entrance stage. -/
def EscapeBudget (n L M B Q : Nat) : Prop :=
  1 ≤ M ∧
  1 ≤ Q ∧
  B = 2 * n * L ∧
  (4 * M) ^ L ≤ Q

/-- Exact block length of a local routing certificate. -/
def RoutingBlock (n L : Nat) : Nat := 2 * n * L

/-- Exact coarse inverse mass of a local routing certificate. -/
def RoutingInverseMass (L M : Nat) : Nat := (4 * M) ^ L

/-- Uniform stopped escape from leaderless states to writer silence. -/
def WriterSilenceObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (W L M B Q : Nat) : Prop :=
  EscapeBudget n L M B Q ∧
  ∀ C : Config n ψ κ τ,
    BirthShortDoneTerminalFirstHit.Leaderless C ->
    Q * avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless
        (WriterStage ring W) C B ≤
      (Q - 1) * n ^ B

/-- From a stopped writer-silent state, reach the joint sanitation endpoint. -/
def SanitationWordObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (W L M B Q : Nat) : Prop :=
  EscapeBudget n L M B Q ∧
  ∀ C : Config n ψ κ τ,
    BirthShortDoneTerminalFirstHit.Leaderless C ->
    WriterStage ring W C ->
    Q * avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless
        (JointStage ring W) C B ≤
      (Q - 1) * n ^ B

/-- From a stopped joint state, finish the ruler and select a covered target. -/
def RulerWordObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (W L M B Q : Nat) : Prop :=
  EscapeBudget n L M B Q ∧
  ∀ C : Config n ψ κ τ,
    BirthShortDoneTerminalFirstHit.Leaderless C ->
    JointStage ring W C ->
    Q * avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless
        (PreparedStage hψ ring W) C B ≤
      (Q - 1) * n ^ B

/-- Every prepared endpoint admits the bounded local route. -/
def RoutingFromPreparedObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (W L M B Q : Nat) : Prop :=
  1 ≤ M ∧
  1 ≤ Q ∧
  B = RoutingBlock n L ∧
  Q = RoutingInverseMass L M ∧
  ∀ C : Config n ψ κ τ,
    PreparedStage hψ ring W C ->
      Routable hψ h2 ring L M C

-- END PART 1
/-! ## Generic monotonicity and stopped-prefix composition -/

private theorem one_le_mul_of_one_le {a b : Nat}
    (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  calc
    1 = 1 * 1 := by simp
    _ ≤ a * b := Nat.mul_le_mul ha hb

private theorem avoidAlong_mono_target {S : Type}
    (step : S -> Fin n -> S) (Good R R' : S -> Prop)
    (hRR' : ∀ x, R x -> R' x) (C : S) :
    ∀ w : List (Fin n),
      AvoidAlong step Good R' C w -> AvoidAlong step Good R C w
  | [], h => by
      exact ⟨h.1, fun hR => h.2 (hRR' C hR)⟩
  | e :: w, h => by
      exact ⟨⟨h.1.1, fun hR => h.1.2 (hRR' C hR)⟩,
        avoidAlong_mono_target step Good R R' hRR'
          (step C e) w h.2⟩

/-- If R implies R', avoiding R' is a subset of avoiding R. -/
theorem avoidCount_mono_target {S : Type}
    (step : S -> Fin n -> S) (Good R R' : S -> Prop)
    (hRR' : ∀ x, R x -> R' x) (C : S) (T : Nat) :
    avoidCount step Good R' C T ≤ avoidCount step Good R C T := by
  unfold avoidCount
  apply B9SpliceMatcherMass.wordSum_mono
  intro w
  classical
  unfold avoidBit
  by_cases h : AvoidAlong step Good R' C w
  · have h' := avoidAlong_mono_target step Good R R' hRR' C w h
    simp [h, h']
  · simp [h]

/-- Complement alive class after the joint sanitation target is removed. -/
def GoodToJoint (ring : DirectedRing n) (W : Nat)
    (C : Config n ψ κ τ) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless C ∧
  ¬ JointStage ring W C

/-- Complement alive class after the final prepared target is removed. -/
def GoodToPrepared (hψ : 0 < ψ) (ring : DirectedRing n) (W : Nat)
    (C : Config n ψ κ τ) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless C ∧
  ¬ PreparedStage hψ ring W C

private theorem goodToJoint_fun_eq
    (ring : DirectedRing n) (W : Nat) :
    (GoodToJoint (ψ := ψ) (κ := κ) (τ := τ) ring W :
        Config n ψ κ τ -> Prop) =
      (fun C : Config n ψ κ τ =>
        BirthShortDoneTerminalFirstHit.Leaderless C ∧
          ¬ JointStage ring W C) := by
  rfl

private theorem goodToPrepared_fun_eq
    (hψ : 0 < ψ) (ring : DirectedRing n) (W : Nat) :
    (GoodToPrepared (ψ := ψ) (κ := κ) (τ := τ) hψ ring W :
        Config n ψ κ τ -> Prop) =
      (fun C : Config n ψ κ τ =>
        BirthShortDoneTerminalFirstHit.Leaderless C ∧
          ¬ PreparedStage hψ ring W C) := by
  rfl

theorem uniformRouteEntrance_of_obligations
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (W : Nat)
    (Lw Mw Bw Qw : Nat)
    (Ls Ms Bs Qs : Nat)
    (Lr Mr Br Qr : Nat)
    (Lroute Mroute Broute Qroute : Nat)
    (hWriter : WriterSilenceObligation (κ := κ) (τ := τ)
      hψ h2 ring W Lw Mw Bw Qw)
    (hSan : SanitationWordObligation (κ := κ) (τ := τ)
      hψ h2 ring W Ls Ms Bs Qs)
    (hRuler : RulerWordObligation (κ := κ) (τ := τ)
      hψ h2 ring W Lr Mr Br Qr)
    (hRoute : RoutingFromPreparedObligation (κ := κ) (τ := τ)
      hψ h2 ring W Lroute Mroute Broute Qroute) :
    UniformRouteEntrance (κ := κ) (τ := τ)
      hψ h2 ring Lroute Mroute
      (Bw + Bs + Br) (Qw * Qs * Qr) := by
  rcases hWriter with ⟨⟨_, hQw, _, _⟩, hWriterMass⟩
  rcases hSan with ⟨⟨_, hQs, _, _⟩, hSanMass⟩
  rcases hRuler with ⟨⟨_, hQr, _, _⟩, hRulerMass⟩
  rcases hRoute with ⟨_, _, _, _, hPreparedRoute⟩

  have hWriterFirst :
      ∀ C : Config n ψ κ τ, GoodToJoint ring W C ->
        Qw * avoidCount (step1 hψ h2 ring)
            (GoodToJoint ring W) (WriterStage ring W) C Bw ≤
          (Qw - 1) * n ^ Bw := by
    intro C hC
    rcases hC with ⟨hLead, _⟩
    have hmono := B6LocalReverseFill.avoidCount_mono_good
      (step1 hψ h2 ring)
      (GoodToJoint ring W)
      BirthShortDoneTerminalFirstHit.Leaderless
      (WriterStage ring W)
      (fun D hD => hD.1) C Bw
    exact Nat.le_trans (Nat.mul_le_mul_left Qw hmono)
      (hWriterMass C hLead)

  have hSanSecond :
      ∀ C : Config n ψ κ τ, GoodToJoint ring W C ->
        WriterStage ring W C ->
        Qs * aliveCount (step1 hψ h2 ring)
            (GoodToJoint ring W) C Bs ≤
          (Qs - 1) * n ^ Bs := by
    intro C hC hWriterC
    rcases hC with ⟨hLead, _⟩
    have hs := hSanMass C hLead hWriterC
    rw [B6LocalReverseFill.avoidCount_eq_alive_complement
      (step1 hψ h2 ring)
      BirthShortDoneTerminalFirstHit.Leaderless
      (JointStage ring W) C Bs] at hs
    rw [goodToJoint_fun_eq
      (ψ := ψ) (κ := κ) (τ := τ) ring W]
    exact hs

  have hWriterSan :
      UniformEscapeMass (step1 hψ h2 ring)
        (GoodToJoint ring W) (Bw + Bs) (Qw * Qs) :=
    BirthTwoStageEscape.two_stage_escape
      (step1 hψ h2 ring)
      (GoodToJoint ring W) (WriterStage ring W)
      Bw Bs Qw Qs hQw hQs hWriterFirst hSanSecond

  have hQws : 1 ≤ Qw * Qs :=
    one_le_mul_of_one_le hQw hQs

  have hBeforeRuler :
      ∀ C : Config n ψ κ τ, GoodToPrepared hψ ring W C ->
        (Qw * Qs) * avoidCount (step1 hψ h2 ring)
            (GoodToPrepared hψ ring W) (JointStage ring W)
            C (Bw + Bs) ≤
          (Qw * Qs - 1) * n ^ (Bw + Bs) := by
    intro C hC
    rcases hC with ⟨hLead, hNotPrepared⟩
    by_cases hJoint : JointStage ring W C
    · have hz := BirthTwoStageEscape.avoidCount_zero_of
        (step1 hψ h2 ring)
        (GoodToPrepared hψ ring W) (JointStage ring W) C
        (fun h => h.2 hJoint) (Bw + Bs)
      rw [hz, Nat.mul_zero]
      exact Nat.zero_le _
    · have hmono := B6LocalReverseFill.avoidCount_mono_good
        (step1 hψ h2 ring)
        (GoodToPrepared hψ ring W)
        BirthShortDoneTerminalFirstHit.Leaderless
        (JointStage ring W)
        (fun D hD => hD.1) C (Bw + Bs)
      have hesc := hWriterSan C ⟨hLead, hJoint⟩
      have hesc' :
          (Qw * Qs) * avoidCount (step1 hψ h2 ring)
              BirthShortDoneTerminalFirstHit.Leaderless
              (JointStage ring W) C (Bw + Bs) ≤
            (Qw * Qs - 1) * n ^ (Bw + Bs) := by
        rw [B6LocalReverseFill.avoidCount_eq_alive_complement
          (step1 hψ h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless
          (JointStage ring W) C (Bw + Bs)]
        rw [← goodToJoint_fun_eq
          (ψ := ψ) (κ := κ) (τ := τ) ring W]
        exact hesc
      exact Nat.le_trans (Nat.mul_le_mul_left (Qw * Qs) hmono) hesc'

  have hRulerSecond :
      ∀ C : Config n ψ κ τ, GoodToPrepared hψ ring W C ->
        JointStage ring W C ->
        Qr * aliveCount (step1 hψ h2 ring)
            (GoodToPrepared hψ ring W) C Br ≤
          (Qr - 1) * n ^ Br := by
    intro C hC hJoint
    rcases hC with ⟨hLead, _⟩
    have hr := hRulerMass C hLead hJoint
    rw [B6LocalReverseFill.avoidCount_eq_alive_complement
      (step1 hψ h2 ring)
      BirthShortDoneTerminalFirstHit.Leaderless
      (PreparedStage hψ ring W) C Br] at hr
    rw [goodToPrepared_fun_eq
      (ψ := ψ) (κ := κ) (τ := τ) hψ ring W]
    exact hr

  have hPreparedEscape :
      UniformEscapeMass (step1 hψ h2 ring)
        (GoodToPrepared hψ ring W)
        ((Bw + Bs) + Br) ((Qw * Qs) * Qr) :=
    BirthTwoStageEscape.two_stage_escape
      (step1 hψ h2 ring)
      (GoodToPrepared hψ ring W) (JointStage ring W)
      (Bw + Bs) Br (Qw * Qs) Qr hQws hQr
      hBeforeRuler hRulerSecond

  intro C hLead
  by_cases hPrepared : PreparedStage hψ ring W C
  · have hRout := hPreparedRoute C hPrepared
    have hz := BirthTwoStageEscape.avoidCount_zero_of
      (step1 hψ h2 ring)
      BirthShortDoneTerminalFirstHit.Leaderless
      (Routable hψ h2 ring Lroute Mroute) C
      (fun h => h.2 hRout) (Bw + Bs + Br)
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _
  · have hmono := avoidCount_mono_target
      (step1 hψ h2 ring)
      BirthShortDoneTerminalFirstHit.Leaderless
      (PreparedStage hψ ring W)
      (Routable hψ h2 ring Lroute Mroute)
      hPreparedRoute C (Bw + Bs + Br)
    have hesc := hPreparedEscape C ⟨hLead, hPrepared⟩
    have hprep :
        (Qw * Qs * Qr) * avoidCount (step1 hψ h2 ring)
            BirthShortDoneTerminalFirstHit.Leaderless
            (PreparedStage hψ ring W) C (Bw + Bs + Br) ≤
          (Qw * Qs * Qr - 1) * n ^ (Bw + Bs + Br) := by
      rw [B6LocalReverseFill.avoidCount_eq_alive_complement
        (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless
        (PreparedStage hψ ring W) C (Bw + Bs + Br)]
      rw [← goodToPrepared_fun_eq
        (ψ := ψ) (κ := κ) (τ := τ) hψ ring W]
      exact hesc
    exact Nat.le_trans
      (Nat.mul_le_mul_left (Qw * Qs * Qr) hmono) hprep


-- END PART 2
/-! ## Export the exact h1 currency -/

theorem h1_of_obligations
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (W : Nat)
    (Lw Mw Bw Qw : Nat)
    (Ls Ms Bs Qs : Nat)
    (Lr Mr Br Qr : Nat)
    (Lroute Mroute Broute Qroute : Nat)
    (hWriter : WriterSilenceObligation (κ := κ) (τ := τ)
      hψ h2 ring W Lw Mw Bw Qw)
    (hSan : SanitationWordObligation (κ := κ) (τ := τ)
      hψ h2 ring W Ls Ms Bs Qs)
    (hRuler : RulerWordObligation (κ := κ) (τ := τ)
      hψ h2 ring W Lr Mr Br Qr)
    (hRoute : RoutingFromPreparedObligation (κ := κ) (τ := τ)
      hψ h2 ring W Lroute Mroute Broute Qroute) :
    ∀ C : Config n ψ κ τ,
      BirthShortDoneTerminalFirstHit.Leaderless C ->
      ((Qw * Qs * Qr) * Qroute) *
          avoidCount (step1 hψ h2 ring)
            BirthShortDoneTerminalFirstHit.Leaderless
            (ReadyWindow ring) C
            ((Bw + Bs + Br) + Broute) ≤
        ((Qw * Qs * Qr) * Qroute - 1) *
          n ^ ((Bw + Bs + Br) + Broute) := by
  have hentr := uniformRouteEntrance_of_obligations
    hψ h2 ring W
    Lw Mw Bw Qw Ls Ms Bs Qs Lr Mr Br Qr
    Lroute Mroute Broute Qroute
    hWriter hSan hRuler hRoute
  rcases hWriter with ⟨⟨_, hQw, _, _⟩, _⟩
  rcases hSan with ⟨⟨_, hQs, _, _⟩, _⟩
  rcases hRuler with ⟨⟨_, hQr, _, _⟩, _⟩
  rcases hRoute with
    ⟨hMroute, _, hBroute, hQroute, _⟩
  have hQws : 1 ≤ Qw * Qs :=
    one_le_mul_of_one_le hQw hQs
  have hQentr : 1 ≤ Qw * Qs * Qr :=
    one_le_mul_of_one_le hQws hQr
  have hbase := B6LocalReverseFill.h1_of_route_entrance
    (κ := κ) (τ := τ)
    hψ h2 ring Lroute Mroute
    (Bw + Bs + Br) (Qw * Qs * Qr)
    hMroute hQentr hentr
  simpa [RoutingBlock, RoutingInverseMass,
    hBroute, hQroute, Nat.add_assoc] using hbase

/-!
PLAN -- producers only; no theorem or axiom is introduced here.

1. `WriterSilenceObligation` should be discharged from the two physical
   bit-silent modes in `B6WriterSilence`, with the selected workspace fixed
   before the ordered-matcher block.
2. `SanitationWordObligation` should be discharged by the local two-port
   absorber and `B6Sanitation.SanitationWord`; joint ruler repairs may be
   interleaved, but the success event is stopped and does not assume no-reentry.
3. `RulerWordObligation` should use `B6LocalRuler` plus the class-E frame in
   `B6LocalRulerE`, then the ring-label geometry to obtain the full
   `CanonicalArc`/`SanNF` endpoint.  Only after that endpoint is reached, read
   `arcReadBits`; `B6BitCover.covered_count_ge` and `cover_map` supply the
   deterministic `LocalCover` target.  No scheduler mass is spent selecting it.
4. `RoutingFromPreparedObligation` should package the local route into
   `Routable hψ h2 ring Lroute Mroute`.

Budget audit:

  Bentr  = Bw + Bs + Br
  Qentr  = Qw * Qs * Qr
  Broute = 2*n*Lroute
  Qroute = (4*Mroute)^Lroute
  B1     = Bentr + Broute
  Q1     = Qentr * Qroute

The existing second ready-window stage has

  B2 = 2*n*(ψ-1)

and may use the smallest integral Q2 satisfying

  (4*(ψ+1))^(ψ-1) ≤ 3^(ψ-1) * Q2.

Thus the later leaf horizon is the existing

  3 * Q1 * Q2 * (B1 + B2),

and the finite/asymptotic audit must bound the complete product

  Qw * Qs * Qr * (4*Mroute)^Lroute,

not any one entrance stage in isolation.  This is the same stopped-prefix
accounting: products of inverse masses, sums of block lengths, and no
preservation assumption after a stage is first hit.
-/

end B6EntranceCompose

-- END PART 3
