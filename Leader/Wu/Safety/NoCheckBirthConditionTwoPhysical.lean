import Leader.Wu.Safety.NoCheckBirthConditionTwoWriteFrames

/-!
# Physical boundary reduction for corrected condition 2

The exact authorized normal branch is projected to the five fields used by
peaceful bullets.  From `OutputSafeConfig`, P'_ψ is idempotent on leaders and
labels; all other pre-Algorithm-15 stages frame the projection.  This connects
the finite physical branch to the isolated no-collision kernel.
-/

namespace PPLLNoCheckBirthConditionTwoPhysical

open PPLL PPLLRepair PPLLVerify PPLLNoCheckBirthRepair
  PPLLNoCheckBirthLeaderFrames PPLLNoCheckBirthBoundaryFrames
  PPLLNoCheckBirthConditionOne PPLLNoCheckBirthPhysicalConditionOne
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoWriteFrames
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair

/-- All state fields read or written by the peaceful-bullet kernel. -/
structure PeaceView (ψ : Nat) where
  leader : Bool
  label : Fin ψ
  shield : Bool
  bullet : Fin 3
  signal_B : Fin 2
  deriving DecidableEq

/-- Project one audit state to its condition-2 fields. -/
def PeaceView.ofState (u : AgentState ψ) : PeaceView ψ :=
  ⟨u.leader, u.label, u.shield, u.bullet, u.signal_B⟩

/-- Project both endpoints. -/
def peaceViewPair (q : AgentState ψ × AgentState ψ) :
    PeaceView ψ × PeaceView ψ :=
  (PeaceView.ofState q.1, PeaceView.ofState q.2)

/-- Project the cores of an authorized pair. -/
def authorizedPeaceViewPair
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    PeaceView ψ × PeaceView ψ :=
  peaceViewPair (q.1.core, q.2.core)

theorem PeaceView.ext (a b : PeaceView ψ)
    (h1 : a.leader = b.leader) (h2 : a.label = b.label)
    (h3 : a.shield = b.shield) (h4 : a.bullet = b.bullet)
    (h5 : a.signal_B = b.signal_B) : a = b := by
  cases a
  cases b
  simp_all

/-- On an output-safe edge, P'_ψ changes neither endpoint's leader or label. -/
theorem pPsi_leader_label_of_paperSafe
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (e : Fin n) :
    let r := ring.rightNeighbor e
    let q := pPsi hψ (C e) (C r)
    q.1.leader = (C e).leader ∧ q.1.label = (C e).label ∧
      q.2.leader = (C r).leader ∧ q.2.label = (C r).label := by
  let r := ring.rightNeighbor e
  let q := pPsi hψ (C e) (C r)
  have hleftLeader := pPsi_initiator_leader_eq hψ (C e) (C r)
  have hleftLabel := pPsi_initiator_label_eq hψ (C e) (C r)
  have hrightLeader : q.2.leader = (C r).leader := by
    cases hr : (C r).leader
    · cases hq : q.2.leader
      · rfl
      · have hbirth := pPsi_new_responder_leader_requires_probe_barrier
          hψ (C e) (C r) hq hr
        have hold := hSafe.no_free_barrier e hbirth.2
        change (C r).leader = true at hold
        rw [hr] at hold
        simp at hold
    · exact pPsi_responder_leader_of_true hψ (C e) (C r) hr
  have hrightLabel : q.2.label = (C r).label := by
    by_cases hbarrier : isBarrier hψ (C e) (C r)
    · have hright := hSafe.no_free_barrier e hbarrier
      change (C r).leader = true at hright
      have hzero := paperSafe_unique_leader_label_zero
        hψ ring C hSafe r (by simpa [AgentState.isLeader] using hright)
      exact pPsi_responder_label_of_leader_zero
        hψ (C e) (C r) hright hzero
    · exact pPsi_responder_label_of_nonbarrier
        hψ (C e) (C r) hbarrier
  exact ⟨hleftLeader, hleftLabel, hrightLeader, hrightLabel⟩

attribute [local irreducible]
  noCheckBirthAuthorizedBeforeEliminate noCheckBirthBeforeEliminate

/-- The exact normalized authorized boundary before Algorithm 15 has the same
five-field projection as its inputs whenever P'_ψ frames endpoint leaders and
labels.  This edge-local form is independent of global safety. -/
theorem authorizedBoundary_peaceView_of_pPsi_frame
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hp : (pPsi hψ l.core r.core).1.leader = l.core.leader ∧
      (pPsi hψ l.core r.core).1.label = l.core.label ∧
      (pPsi hψ l.core r.core).2.leader = r.core.leader ∧
      (pPsi hψ l.core r.core).2.label = r.core.label) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let boundary := noCheckBirthAuthorizedBeforeEliminate hψ κ l0 r0
    authorizedPeaceViewPair boundary = authorizedPeaceViewPair (l, r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let boundary := noCheckBirthAuthorizedBeforeEliminate hψ κ l0 r0
  have hphysical := noCheckBirthAuthorizedBeforeEliminate_boundary hψ κ l0 r0
  have hnormalize := noCheckBirthSourceBoundary_normalizeDeletion hψ κ l r
  have hproject : authorizedBoundaryProjection boundary =
      boundaryProjection (noCheckBirthBeforeEliminate hψ κ l.core r.core) :=
    hphysical.trans hnormalize
  have hsourceLeaders := noCheckBirthBeforeEliminate_leaders
    hψ κ l.core r.core
  have hsourceLabels := noCheckBirthBeforeEliminate_labels
    hψ κ l.core r.core
  have hsourceLL := congrArg Prod.fst hsourceLeaders
  have hsourceRL := congrArg Prod.snd hsourceLeaders
  have hsourceRLabel := congrArg Prod.snd hsourceLabels
  unfold leaderPair at hsourceLL hsourceRL
  unfold labelPair at hsourceRLabel
  dsimp only at hsourceLL hsourceRL hsourceRLabel
  have hproj := hproject
  unfold authorizedBoundaryProjection boundaryProjection at hproj
  have hleftLeader := (congrArg (fun v => v.1) hproj).trans
    (hsourceLL.trans hp.1)
  have hrightLeader := (congrArg (fun v => v.2.1) hproj).trans
    (hsourceRL.trans hp.2.2.1)
  have hrightLabel := (congrArg (fun v => v.2.2.1) hproj).trans
    (hsourceRLabel.trans hp.2.2.2)
  have hleftLabel0 := conditionTwoAuthorizedBeforeEliminate_left_label
    hψ κ l0 r0
  have hleftLabel : boundary.1.core.label = l.core.label := by
    exact hleftLabel0.trans (by
      unfold l0 normalizeDeletion
      split <;> rfl)
  have hbullets := conditionTwoAuthorizedBeforeEliminate_bulletFieldPair
    hψ κ l0 r0
  have hnormalizeBullets : authorizedBulletFieldPair (l0, r0) =
      authorizedBulletFieldPair (l, r) := by
    apply Prod.ext
    · exact normalizeDeletion_bulletFields l
    · exact normalizeDeletion_bulletFields r
  have hbulletFields := hbullets.trans hnormalizeBullets
  apply Prod.ext <;> apply PeaceView.ext
  · exact hleftLeader
  · exact hleftLabel
  · exact congrArg (fun v => v.1.shield) hbulletFields
  · exact congrArg (fun v => v.1.bullet) hbulletFields
  · exact congrArg (fun v => v.1.signal_B) hbulletFields
  · exact hrightLeader
  · exact hrightLabel
  · exact congrArg (fun v => v.2.shield) hbulletFields
  · exact congrArg (fun v => v.2.bullet) hbulletFields
  · exact congrArg (fun v => v.2.signal_B) hbulletFields

/-- Output safety supplies the P'_ψ frame needed by the edge-local boundary
lemma.  The historical theorem name is retained for compatibility. -/
theorem authorizedBoundary_peaceView_of_paperSafe
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (e : Fin n) (permitL permitR : Bool) :
    let l : AuthorizedAgentState ψ := ⟨C e, permitL⟩
    let r : AuthorizedAgentState ψ :=
      ⟨C (ring.rightNeighbor e), permitR⟩
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let boundary := noCheckBirthAuthorizedBeforeEliminate hψ κ l0 r0
    authorizedPeaceViewPair boundary = authorizedPeaceViewPair (l, r) := by
  let l : AuthorizedAgentState ψ := ⟨C e, permitL⟩
  let r : AuthorizedAgentState ψ :=
    ⟨C (ring.rightNeighbor e), permitR⟩
  exact authorizedBoundary_peaceView_of_pPsi_frame hψ κ l r
    (pPsi_leader_label_of_paperSafe hψ ring C hSafe e)

end PPLLNoCheckBirthConditionTwoPhysical
