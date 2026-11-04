import Leader.Wu.Birth.WidthTwoWaitBlockProgress
import Leader.Wu.Birth.CapToFirstBirth
import Leader.Wu.Birth.ShortDoneTerminalNoHitCount


namespace BirthPhaseFirstLeaderComposition


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthSigMoveDisposalRepair


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau


/-- One extra Bellman half-life beyond the generic `1/n` setting. -/
def halfBudgetK (n Q : Nat) : Nat :=
  BirthPhaseGenericRenewal.renewalK Q (Nat.log2 n + 2)


/-- B5 first-cap prefix horizon at failure budget `1/(2n)`. -/
def firstCapHorizon (n kappa : Nat) : Nat :=
  halfBudgetK n BirthPhaseWait2BlockProgress.Q *
    BirthPhaseWait2BlockProgress.L n *
    BirthPhaseWait2BlockProgress.R kappa


/-- B6 charged suffix horizon at failure budget `1/(2n)`.
`chargedHorizon` itself is the one-edge raw charged block. -/
def firstBirthHorizon (n psi kappa tau : Nat) : Nat :=
  halfBudgetK n
      (BirthPhaseCapToFirstBirth.massConstant n psi kappa tau) *
    BirthPhaseCapToFirstBirth.chargedHorizon n psi kappa tau *
    BirthPhaseCapToFirstBirth.R6


/-- B7 fixed original-scheduler horizon. -/
def firstLeaderHorizon (n psi kappa tau : Nat) : Nat :=
  firstCapHorizon n kappa + firstBirthHorizon n psi kappa tau


/-- The new B7 suffix definition is definitionally the B6 half-budget horizon. -/
theorem firstBirthHorizon_eq_halfBudgetHorizon
    (n psi kappa tau : Nat) :
    firstBirthHorizon n psi kappa tau =
      BirthPhaseCapToFirstBirth.halfBudgetHorizon n psi kappa tau := by
  rfl


/-- Exact B7 failure numerator on literal original scheduler words. -/
noncomputable def firstLeaderFailureNumerator
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T
    (BirthShortDoneTerminalNoHitCount.physicalNoHitBit
      hpsi (by decide : 0 < 2) h2 ring C)


/-- Metadata no-birth numerator on the same original words. -/
noncomputable def firstLeaderNoBirthNumerator
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T
    (BirthShortDoneTerminalNoHitCount.noBirthBit
      hpsi (by decide : 0 < 2) h2 ring C)


/-- Exact prepared-responder writer premise requested by the corrected B6
handoff: every currently certified bit-flipping lane needs at least one of
`path3`, `write`, or `write_state` to be non-idle. -/
def CorrectedWriterPremiseAt
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) : Prop :=
  let r := (prepareExpiringDisposal hpsi u).core.erase.core
  r.path3 = none ∧ r.write = .none ∧ r.write_state = .none


/-- Named B3 pointwise bridge consumed by B4's existing
`hgood_of_dirty_bridge`. -/
def B3DirtySuccessBridge
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 4 ≤ n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau) : Prop :=
  ∀ x : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Allowed
        hpsi h2 hn kappa tau ring anchor x →
    ∀ u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n →
      DirtySuccess x u →
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring x u = true ∨
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor x <
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (BirthPhaseGenericRenewal.rawEndpoint
              (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
              x u)


/-- The corrected writer premise must hold at every no-birth cap row that the
B5/B7 composition may expose. -/
def HWriterAtCap
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (kappa tau : Nat) (ring : DirectedRing n) : Prop :=
  ∀ (D : FC n psi kappa tau) (e : Fin n),
    BirthShortDoneTerminalFirstHit.Leaderless D →
    BirthShortDoneTerminalPassiveR4.RowCap2
      hpsi h2 kappa ring D e →
    BirthShortDoneTerminalObserver.birthEvent
      hpsi (by decide : 0 < 2) h2
      (D e) (D (ring.rightNeighbor e)) = false →
    CorrectedWriterPremiseAt hpsi (D (ring.rightNeighbor e))


/-- Missing deterministic cap-to-B6 bridge.  On a no-birth cap row, the
corrected writer premise must make the literal successor a B6 carrier. -/
def HCapToB6
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (kappa tau : Nat) (ring : DirectedRing n) : Prop :=
  ∀ (D : FC n psi kappa tau) (e : Fin n),
    BirthShortDoneTerminalFirstHit.Leaderless D →
    BirthShortDoneTerminalPassiveR4.RowCap2
      hpsi h2 kappa ring D e →
    BirthShortDoneTerminalObserver.birthEvent
      hpsi (by decide : 0 < 2) h2
      (D e) (D (ring.rightNeighbor e)) = false →
    CorrectedWriterPremiseAt hpsi (D (ring.rightNeighbor e)) →
    BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring
      (BirthPhaseCapToFirstBirth.currentStep hpsi h2 ring D e)


/-- Generic one-extra-half-life tail: the target failure numerator gets a
`2*n` coefficient instead of only `n`. -/
theorem target_failure_le_half_budget
    {S : Type} {n L Q R : Nat}
    (step : S → Fin n → S)
    (Carrier Reacquire : S → Prop)
    [DecidablePred Carrier] [DecidablePred Reacquire]
    (rank : S → Nat)
    (target good : S → List (Fin n) → Bool)
    (hclosed : ∀ x,
      BirthPhaseGenericRenewal.RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        BirthPhaseGenericRenewal.RenewalAllowed Carrier Reacquire
          (BirthPhaseGenericRenewal.rawEndpoint step x u))
    (hpos : ∀ x,
      BirthPhaseGenericRenewal.RenewalAllowed Carrier Reacquire x →
        1 ≤ rank x)
    (hbound : ∀ x,
      BirthPhaseGenericRenewal.RenewalAllowed Carrier Reacquire x →
        rank x ≤ R)
    (hmono : ∀ x,
      BirthPhaseGenericRenewal.RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        rank (BirthPhaseGenericRenewal.rawEndpoint step x u) ≤ rank x)
    (hgood : ∀ x,
      BirthPhaseGenericRenewal.RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → good x u = true →
        target x u = true ∨
          rank (BirthPhaseGenericRenewal.rawEndpoint step x u) < rank x)
    (hmass : ∀ x,
      BirthPhaseGenericRenewal.RenewalAllowed Carrier Reacquire x →
        n ^ L ≤ Q *
          FixedSpanRenewalPayload.wordSum n L
            (BirthPhaseGenericRenewal.goodWeight good x))
    (hn : 2 ≤ n) (hQ : 0 < Q)
    (x : S) (hx : Carrier x) :
    2 * n *
        BirthPhaseGenericRenewal.targetFailureNumerator
          step Carrier Reacquire target hclosed
          (⟨x, Or.inl hx⟩ :
            BirthPhaseGenericRenewal.RenewalState Carrier Reacquire)
          (halfBudgetK n Q * R) ≤
      n ^ (halfBudgetK n Q * L * R) := by
  let s := Nat.log2 n + 2
  have ht := BirthPhaseGenericRenewal.target_failure_geometric
    step Carrier Reacquire rank target good
    hclosed hpos hbound hmono hgood hmass
    (by omega) hQ x hx s
  have ht' :
      2 ^ s *
          BirthPhaseGenericRenewal.targetFailureNumerator
            step Carrier Reacquire target hclosed
            (⟨x, Or.inl hx⟩ :
              BirthPhaseGenericRenewal.RenewalState Carrier Reacquire)
            (halfBudgetK n Q * R) ≤
        n ^ (halfBudgetK n Q * L * R) := by
    simpa [s, halfBudgetK] using ht
  have hbase : n ≤ 2 ^ (Nat.log2 n + 1) :=
    (LeaderCountDyadicTail.log_parameters n hn).2.2.2
  have hpow : 2 * n ≤ 2 ^ s := by
    calc
      2 * n ≤ 2 * 2 ^ (Nat.log2 n + 1) :=
        Nat.mul_le_mul_left 2 hbase
      _ = 2 ^ s := by
        dsimp [s]
        simp only [Nat.pow_succ]
        omega
  have hscaled := Nat.mul_le_mul_right
    (BirthPhaseGenericRenewal.targetFailureNumerator
      step Carrier Reacquire target hclosed
      (⟨x, Or.inl hx⟩ :
        BirthPhaseGenericRenewal.RenewalState Carrier Reacquire)
      (halfBudgetK n Q * R)) hpow
  exact Nat.le_trans hscaled ht'


/-- B5 target-failure numerator at the B7 half-budget prefix horizon. -/
noncomputable def firstCapFailureNumerator
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 4 ≤ n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hclosed4 : BirthPhaseWait2BlockProgress.HClosed
      hpsi h2 hn kappa tau ring anchor)
    (C : FC n psi kappa tau)
    (hC : BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C) : Nat :=
  BirthPhaseGenericRenewal.targetFailureNumerator
    (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
    (BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor)
    (BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor)
    (BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring)
    hclosed4
    (⟨C, Or.inl hC⟩ : BirthPhaseGenericRenewal.RenewalState
      (BirthPhaseWait2BlockProgress.Carrier
        hpsi h2 hn ring anchor)
      (BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor))
    (halfBudgetK n BirthPhaseWait2BlockProgress.Q *
      BirthPhaseWait2BlockProgress.R kappa)


/-- B5 immediately gets its `1/(2n)` target tail from the certified generic
renewal theorem once the remaining B4 inputs and B3 bridge are supplied. -/
theorem firstCap_failure_le_half_budget
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 4 ≤ n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau)
    (hclosed4 : BirthPhaseWait2BlockProgress.HClosed
      hpsi h2 hn kappa tau ring anchor)
    (hmono4 : BirthPhaseWait2BlockProgress.HMono
      hpsi h2 hn kappa tau ring anchor)
    (hB3 : B3DirtySuccessBridge
      hpsi h2 hn kappa tau ring anchor DirtySuccess)
    (hmass4 : BirthPhaseWait2BlockProgress.HMass
      hpsi h2 hn kappa tau ring anchor DirtySuccess)
    (C : FC n psi kappa tau)
    (hC : BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C) :
    2 * n * firstCapFailureNumerator
        hpsi h2 hn kappa tau ring anchor hclosed4 C hC ≤
      n ^ firstCapHorizon n kappa := by
  classical
  have hgood4 := BirthPhaseWait2BlockProgress.hgood_of_dirty_bridge
    hpsi h2 hn kappa tau ring anchor DirtySuccess hB3
  have ht := target_failure_le_half_budget
    (n := n)
    (L := BirthPhaseWait2BlockProgress.L n)
    (Q := BirthPhaseWait2BlockProgress.Q)
    (R := BirthPhaseWait2BlockProgress.R kappa)
    (step := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
    (Carrier := BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor)
    (Reacquire := BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor)
    (rank := BirthPhaseWait2BlockProgress.rank kappa ring anchor)
    (target := BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring)
    (good := BirthPhaseWait2BlockProgress.good DirtySuccess)
    hclosed4
    (BirthPhaseWait2BlockProgress.hpos_proved
      hpsi h2 hn kappa tau ring anchor)
    (BirthPhaseWait2BlockProgress.hbound_proved
      hpsi h2 hn kappa tau ring anchor)
    hmono4 hgood4 hmass4
    (by omega) BirthPhaseWait2BlockProgress.Q_pos C hC
  simpa [firstCapFailureNumerator, firstCapHorizon] using ht


/-- B6 target-failure numerator at the charged half-budget suffix horizon. -/
noncomputable def firstBirthFailureNumerator
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (hclosed6 : BirthPhaseCapToFirstBirth.hclosed6
      (n := n) (kappa := kappa) (tau := tau) hpsi h2 ring)
    (D : FC n psi kappa tau)
    (hD : BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring D) : Nat :=
  BirthPhaseGenericRenewal.targetFailureNumerator
    (BirthPhaseCapToFirstBirth.currentStep hpsi h2 ring)
    (BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring)
    (BirthPhaseCapToFirstBirth.B6ReacquireCarrier hpsi h2 ring)
    (BirthPhaseCapToFirstBirth.firstBirthGoodBit hpsi h2 ring)
    hclosed6
    (⟨D, Or.inl hD⟩ : BirthPhaseGenericRenewal.RenewalState
      (BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring)
      (BirthPhaseCapToFirstBirth.B6ReacquireCarrier hpsi h2 ring))
    (halfBudgetK n (BirthPhaseCapToFirstBirth.Q6 n psi kappa tau) *
      BirthPhaseCapToFirstBirth.R6)


/-- B6 immediately gets its `1/(2n)` target tail once its two still-open
charged-block hypotheses `hclosed6` and `hmass6` are supplied. -/
theorem firstBirth_failure_le_half_budget
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hclosed6 : BirthPhaseCapToFirstBirth.hclosed6
      (n := n) (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hmass6 : BirthPhaseCapToFirstBirth.hmass6
      (n := n) (kappa := kappa) (tau := tau) hpsi h2 ring)
    (D : FC n psi kappa tau)
    (hD : BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring D) :
    2 * n * firstBirthFailureNumerator hpsi h2 ring hclosed6 D hD ≤
      n ^ firstBirthHorizon n psi kappa tau := by
  classical
  have ht := target_failure_le_half_budget
    (n := n)
    (L := BirthPhaseCapToFirstBirth.L6 n psi kappa tau)
    (Q := BirthPhaseCapToFirstBirth.Q6 n psi kappa tau)
    (R := BirthPhaseCapToFirstBirth.R6)
    (step := BirthPhaseCapToFirstBirth.currentStep hpsi h2 ring)
    (Carrier := BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring)
    (Reacquire := BirthPhaseCapToFirstBirth.B6ReacquireCarrier hpsi h2 ring)
    (rank := BirthPhaseCapToFirstBirth.rank6)
    (target := BirthPhaseCapToFirstBirth.firstBirthGoodBit hpsi h2 ring)
    (good := BirthPhaseCapToFirstBirth.firstBirthGoodBit hpsi h2 ring)
    hclosed6
    (fun x _ => BirthPhaseCapToFirstBirth.rank6_pos x)
    (fun x _ => BirthPhaseCapToFirstBirth.rank6_bound x)
    (fun x _ u _ _ =>
      BirthPhaseCapToFirstBirth.rank6_mono hpsi h2 ring x u)
    (fun x _ u _ hg =>
      BirthPhaseCapToFirstBirth.rank6_good hpsi h2 ring x u hg)
    hmass6 hn
    (BirthPhaseCapToFirstBirth.Q6_pos ring psi kappa tau)
    D hD
  simpa [firstBirthFailureNumerator, firstBirthHorizon,
    BirthPhaseCapToFirstBirth.massConstant,
    BirthPhaseCapToFirstBirth.chargedHorizon] using ht


/-- Exact same-original-word no-hit/no-birth count equality at any horizon. -/
theorem firstLeaderFailureNumerator_eq_noBirthNumerator
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : FC n psi kappa tau)
    (h0 : BirthShortDoneTerminalFirstHit.Leaderless C)
    (T : Nat) :
    firstLeaderFailureNumerator hpsi h2 ring C T =
      firstLeaderNoBirthNumerator hpsi h2 ring C T := by
  simpa [firstLeaderFailureNumerator, firstLeaderNoBirthNumerator] using
    (BirthShortDoneTerminalNoHitCount.physicalNoHit_wordSum_eq_noBirth_wordSum
      hpsi (by decide : 0 < 2) h2 ring hn C h0 T)


/-- Pure cross-multiplied union-bound arithmetic:
`a/A ≤ 1/(2n)` and `b/B ≤ 1/(2n)` imply
`a/A + b/B ≤ 1/n`. -/
theorem half_plus_half_stays_within_one_over_n
    {n a b A B : Nat}
    (ha : 2 * n * a ≤ A)
    (hb : 2 * n * b ≤ B) :
    n * (a * B + A * b) ≤ A * B := by
  have haB : (2 * n * a) * B ≤ A * B :=
    Nat.mul_le_mul_right B ha
  have hAb : A * (2 * n * b) ≤ A * B :=
    Nat.mul_le_mul_left A hb
  have htwice :
      2 * (n * (a * B + A * b)) ≤ 2 * (A * B) := by
    calc
      2 * (n * (a * B + A * b)) =
          (2 * n) * (a * B + A * b) := by ac_rfl
      _ = (2 * n) * (a * B) + (2 * n) * (A * b) := by
        rw [Nat.mul_add]
      _ = (2 * n * a) * B + A * (2 * n * b) := by
        ac_rfl
      _ ≤ A * B + A * B := Nat.add_le_add haB hAb
      _ = 2 * (A * B) := (Nat.two_mul _).symm
  exact Nat.le_of_mul_le_mul_left htwice (by omega)


/-- The same arithmetic specialized to original-word power denominators. -/
theorem two_half_budgets_stay_within_one_over_n
    {n a b T5 T6 : Nat}
    (h5 : 2 * n * a ≤ n ^ T5)
    (h6 : 2 * n * b ≤ n ^ T6) :
    n * (a * n ^ T6 + n ^ T5 * b) ≤ n ^ (T5 + T6) := by
  simpa [Nat.pow_add] using
    (half_plus_half_stays_within_one_over_n
      (n := n) (a := a) (b := b)
      (A := n ^ T5) (B := n ^ T6) h5 h6)


/-- Remaining original-word bookkeeping seam.


B5's current stopped tree proves the first-cap tail but erases the successful
cap endpoint.  This proposition is the exact missing prefix/suffix statement:
from an initially leaderless B4 carrier, the corrected writer/handoff bridge
and a uniform B6 half-tail bound control the no-birth original words of the
concatenated horizon.  It is deliberately separate from the probability
arithmetic above. -/
def HOriginalWordSplice
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 4 ≤ n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hclosed4 : BirthPhaseWait2BlockProgress.HClosed
      hpsi h2 hn kappa tau ring anchor)
    (C : FC n psi kappa tau)
    (hC : BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C)
    (hclosed6 : BirthPhaseCapToFirstBirth.hclosed6
      (n := n) (kappa := kappa) (tau := tau) hpsi h2 ring) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless C →
  HWriterAtCap hpsi h2 kappa tau ring →
  HCapToB6 hpsi h2 kappa tau ring →
  (∀ (D : FC n psi kappa tau)
      (hD : BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring D),
      2 * n * firstBirthFailureNumerator
          hpsi h2 ring hclosed6 D hD ≤
        n ^ firstBirthHorizon n psi kappa tau) →
  2 * n * firstLeaderNoBirthNumerator hpsi h2 ring C
      (firstLeaderHorizon n psi kappa tau) ≤
    (2 * n * firstCapFailureNumerator
        hpsi h2 hn kappa tau ring anchor hclosed4 C hC) *
        n ^ firstBirthHorizon n psi kappa tau +
      n ^ firstCapHorizon n kappa *
        n ^ firstBirthHorizon n psi kappa tau


/-- B7 theorem.  Every currently missing protocol/composition input is named:
B4 closure/monotonicity/mass, the B3 pointwise bridge, B6 closure/mass, the
corrected writer premise, the deterministic cap-to-B6 bridge, the B4 sub-cap
start fact, and the endpoint-carrying original-word splice. -/
theorem firstPhysicalLeader_failure_le_one_over_n
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 4 ≤ n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (h0 : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hcarrier : BirthPhaseWait2Transfer.LocalWait2Carrier
      hpsi h2 hn ring anchor C)
    (hsubcap : BirthPhaseWait2BlockProgress.shortCountAt
      ring anchor C < kappa)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau)
    (hclosed4 : BirthPhaseWait2BlockProgress.HClosed
      hpsi h2 hn kappa tau ring anchor)
    (hmono4 : BirthPhaseWait2BlockProgress.HMono
      hpsi h2 hn kappa tau ring anchor)
    (hB3 : B3DirtySuccessBridge
      hpsi h2 hn kappa tau ring anchor DirtySuccess)
    (hmass4 : BirthPhaseWait2BlockProgress.HMass
      hpsi h2 hn kappa tau ring anchor DirtySuccess)
    (hclosed6 : BirthPhaseCapToFirstBirth.hclosed6
      (n := n) (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hmass6 : BirthPhaseCapToFirstBirth.hmass6
      (n := n) (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hWriter : HWriterAtCap hpsi h2 kappa tau ring)
    (hCapToB6 : HCapToB6 hpsi h2 kappa tau ring)
    (hsplice : HOriginalWordSplice
      hpsi h2 hn kappa tau ring anchor hclosed4 C
      ⟨hcarrier, hsubcap⟩ hclosed6) :
    n * firstLeaderFailureNumerator hpsi h2 ring C
        (firstLeaderHorizon n psi kappa tau) ≤
      n ^ firstLeaderHorizon n psi kappa tau := by
  have h5 := firstCap_failure_le_half_budget
    hpsi h2 hn kappa tau ring anchor DirtySuccess
    hclosed4 hmono4 hB3 hmass4 C ⟨hcarrier, hsubcap⟩
  have h6 :
      ∀ (D : FC n psi kappa tau)
        (hD : BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring D),
        2 * n * firstBirthFailureNumerator
            hpsi h2 ring hclosed6 D hD ≤
          n ^ firstBirthHorizon n psi kappa tau := by
    intro D hD
    exact firstBirth_failure_le_half_budget
      hpsi h2 (by omega) ring hclosed6 hmass6 D hD
  have hs := hsplice h0 hWriter hCapToB6 h6
  have h5scaled :
      (2 * n * firstCapFailureNumerator
          hpsi h2 hn kappa tau ring anchor hclosed4 C
            ⟨hcarrier, hsubcap⟩) *
          n ^ firstBirthHorizon n psi kappa tau ≤
        n ^ firstCapHorizon n kappa *
          n ^ firstBirthHorizon n psi kappa tau :=
    Nat.mul_le_mul_right
      (n ^ firstBirthHorizon n psi kappa tau) h5
  have htwice :
      2 * (n * firstLeaderNoBirthNumerator hpsi h2 ring C
          (firstLeaderHorizon n psi kappa tau)) ≤
        2 * (n ^ firstCapHorizon n kappa *
          n ^ firstBirthHorizon n psi kappa tau) := by
    calc
      2 * (n * firstLeaderNoBirthNumerator hpsi h2 ring C
          (firstLeaderHorizon n psi kappa tau)) =
        2 * n * firstLeaderNoBirthNumerator hpsi h2 ring C
          (firstLeaderHorizon n psi kappa tau) := by ac_rfl
      _ ≤
        (2 * n * firstCapFailureNumerator
            hpsi h2 hn kappa tau ring anchor hclosed4 C
              ⟨hcarrier, hsubcap⟩) *
            n ^ firstBirthHorizon n psi kappa tau +
          n ^ firstCapHorizon n kappa *
            n ^ firstBirthHorizon n psi kappa tau := hs
      _ ≤
        n ^ firstCapHorizon n kappa *
            n ^ firstBirthHorizon n psi kappa tau +
          n ^ firstCapHorizon n kappa *
            n ^ firstBirthHorizon n psi kappa tau :=
        Nat.add_le_add h5scaled (Nat.le_refl _)
      _ = 2 * (n ^ firstCapHorizon n kappa *
          n ^ firstBirthHorizon n psi kappa tau) := (Nat.two_mul _).symm
  have hnoBirth :
      n * firstLeaderNoBirthNumerator hpsi h2 ring C
          (firstLeaderHorizon n psi kappa tau) ≤
        n ^ firstCapHorizon n kappa *
          n ^ firstBirthHorizon n psi kappa tau :=
    Nat.le_of_mul_le_mul_left htwice (by omega)
  have hcount := firstLeaderFailureNumerator_eq_noBirthNumerator
    hpsi h2 ring (by omega : 1 < n) C h0
      (firstLeaderHorizon n psi kappa tau)
  rw [hcount]
  calc
    n * firstLeaderNoBirthNumerator hpsi h2 ring C
        (firstLeaderHorizon n psi kappa tau) ≤
      n ^ firstCapHorizon n kappa *
        n ^ firstBirthHorizon n psi kappa tau := hnoBirth
    _ = n ^ (firstCapHorizon n kappa +
        firstBirthHorizon n psi kappa tau) := by
      rw [Nat.pow_add]
    _ = n ^ firstLeaderHorizon n psi kappa tau := by rfl


end BirthPhaseFirstLeaderComposition


#print axioms BirthPhaseFirstLeaderComposition.firstBirthHorizon_eq_halfBudgetHorizon
#print axioms BirthPhaseFirstLeaderComposition.target_failure_le_half_budget
#print axioms BirthPhaseFirstLeaderComposition.firstCap_failure_le_half_budget
#print axioms BirthPhaseFirstLeaderComposition.firstBirth_failure_le_half_budget
#print axioms BirthPhaseFirstLeaderComposition.firstLeaderFailureNumerator_eq_noBirthNumerator
#print axioms BirthPhaseFirstLeaderComposition.half_plus_half_stays_within_one_over_n
#print axioms BirthPhaseFirstLeaderComposition.two_half_budgets_stay_within_one_over_n
#print axioms BirthPhaseFirstLeaderComposition.firstPhysicalLeader_failure_le_one_over_n
