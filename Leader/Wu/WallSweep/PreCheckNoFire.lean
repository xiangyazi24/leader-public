import Leader.Wu.WallSweep.UnshieldedRetry

/-!
# Full source-covered no-fire edge

This module lifts the raw Algorithm-14 exact reset/echo rule and the
Algorithm-15 zero-bullet no-fire frame through the complete pre-CHECK
authorized, bounded, and path-stall transition.  Follower absence signals are
arbitrary; only the responder signal may change.
-/

namespace PPLLWallSweepPreCheckNoFire

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLWallSweepPreCheckResetContracts
  PPLLNoCheckBirthLeaderFrames
  PPLLNoCheckBirthBoundaryFrames
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoKernel

variable {psi kappa tau : Nat}

/-! ## Opaque projection adapters

The named transition boundaries below are intentionally large.  Projecting a
pair equality through these generic adapters keeps the boundary opaque and
prevents elaboration from reducing the complete protocol merely to recognize a
single state field. -/

private theorem authorizedPeaceViewPair_left_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    PeaceView.ofState a.1.core = PeaceView.ofState b.1.core :=
  congrArg Prod.fst h

private theorem authorizedPeaceViewPair_right_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    PeaceView.ofState a.2.core = PeaceView.ofState b.2.core :=
  congrArg Prod.snd h

/-- Cross the authorized/raw PeaceView boundary while both endpoints are still
abstract variables.  This keeps callers from unfolding their concrete
transition expressions merely to expose `AuthorizedAgentState.core`. -/
private theorem authorizedPeaceViewPair_core_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    peaceViewPair (a.1.core, a.2.core) =
      peaceViewPair (b.1.core, b.2.core) :=
  h

private theorem peaceViewPair_trans_authorizedCore
    {q : AgentState psi × AgentState psi}
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hq : peaceViewPair q = peaceViewPair (a.1.core, a.2.core))
    (ha : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    peaceViewPair q = peaceViewPair (b.1.core, b.2.core) :=
  hq.trans (authorizedPeaceViewPair_core_eq ha)

private theorem authorizedPeaceViewPair_left_leader_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.1.core.leader = b.1.core.leader :=
  congrArg (fun v => v.1.leader) h

private theorem authorizedPeaceViewPair_right_leader_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.2.core.leader = b.2.core.leader :=
  congrArg (fun v => v.2.leader) h

private theorem authorizedPeaceViewPair_left_label_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.1.core.label = b.1.core.label :=
  congrArg (fun v => v.1.label) h

private theorem authorizedPeaceViewPair_right_label_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.2.core.label = b.2.core.label :=
  congrArg (fun v => v.2.label) h

private theorem authorizedPeaceViewPair_left_shield_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.1.core.shield = b.1.core.shield :=
  congrArg (fun v => v.1.shield) h

private theorem authorizedPeaceViewPair_right_shield_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.2.core.shield = b.2.core.shield :=
  congrArg (fun v => v.2.shield) h

private theorem authorizedPeaceViewPair_left_bullet_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.1.core.bullet = b.1.core.bullet :=
  congrArg (fun v => v.1.bullet) h

private theorem authorizedPeaceViewPair_right_bullet_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.2.core.bullet = b.2.core.bullet :=
  congrArg (fun v => v.2.bullet) h

private theorem authorizedPeaceViewPair_left_signal_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.1.core.signal_B = b.1.core.signal_B :=
  congrArg (fun v => v.1.signal_B) h

private theorem authorizedPeaceViewPair_right_signal_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.2.core.signal_B = b.2.core.signal_B :=
  congrArg (fun v => v.2.signal_B) h

private theorem authorizedPeaceViewPair_raw_left_leader_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    a.1.core.leader = b.1.leader :=
  congrArg (fun v => v.1.leader) h

private theorem authorizedPeaceViewPair_raw_right_leader_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    a.2.core.leader = b.2.leader :=
  congrArg (fun v => v.2.leader) h

private theorem authorizedPeaceViewPair_raw_left_label_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    a.1.core.label = b.1.label :=
  congrArg (fun v => v.1.label) h

private theorem authorizedPeaceViewPair_raw_right_label_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    a.2.core.label = b.2.label :=
  congrArg (fun v => v.2.label) h

private theorem authorizedPeaceViewPair_raw_left_shield_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    a.1.core.shield = b.1.shield :=
  congrArg (fun v => v.1.shield) h

private theorem authorizedPeaceViewPair_raw_right_shield_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    a.2.core.shield = b.2.shield :=
  congrArg (fun v => v.2.shield) h

private theorem authorizedPeaceViewPair_raw_left_bullet_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    a.1.core.bullet = b.1.bullet :=
  congrArg (fun v => v.1.bullet) h

private theorem authorizedPeaceViewPair_raw_right_bullet_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    a.2.core.bullet = b.2.bullet :=
  congrArg (fun v => v.2.bullet) h

private theorem authorizedPeaceViewPair_raw_left_signal_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    a.1.core.signal_B = b.1.signal_B :=
  congrArg (fun v => v.1.signal_B) h

private theorem authorizedPeaceViewPair_raw_right_signal_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    a.2.core.signal_B = b.2.signal_B :=
  congrArg (fun v => v.2.signal_B) h

private theorem peaceViewPair_left_leader_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    a.1.leader = b.1.leader :=
  congrArg (fun v => v.1.leader) h

private theorem peaceViewPair_right_leader_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    a.2.leader = b.2.leader :=
  congrArg (fun v => v.2.leader) h

private theorem peaceViewPair_left_label_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    a.1.label = b.1.label :=
  congrArg (fun v => v.1.label) h

private theorem peaceViewPair_right_label_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    a.2.label = b.2.label :=
  congrArg (fun v => v.2.label) h

private theorem peaceViewPair_left_shield_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    a.1.shield = b.1.shield :=
  congrArg (fun v => v.1.shield) h

private theorem peaceViewPair_right_shield_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    a.2.shield = b.2.shield :=
  congrArg (fun v => v.2.shield) h

private theorem peaceViewPair_left_bullet_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    a.1.bullet = b.1.bullet :=
  congrArg (fun v => v.1.bullet) h

private theorem peaceViewPair_right_bullet_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    a.2.bullet = b.2.bullet :=
  congrArg (fun v => v.2.bullet) h

private theorem peaceViewPair_left_signal_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    a.1.signal_B = b.1.signal_B :=
  congrArg (fun v => v.1.signal_B) h

private theorem peaceViewPair_right_signal_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    a.2.signal_B = b.2.signal_B :=
  congrArg (fun v => v.2.signal_B) h

private theorem authorizedResetEchoPair_left_reset_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair a = authorizedResetEchoPair b) :
    a.1.core.reset_cmd = b.1.core.reset_cmd :=
  congrArg (fun v => v.1.1) h

private theorem authorizedResetEchoPair_left_echo_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair a = authorizedResetEchoPair b) :
    a.1.core.echo = b.1.core.echo :=
  congrArg (fun v => v.1.2) h

private theorem authorizedResetEchoPair_right_echo_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair a = authorizedResetEchoPair b) :
    a.2.core.echo = b.2.core.echo :=
  congrArg (fun v => v.2.2) h

private theorem authorizedReconcile_left_core_eq
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).1.core = (f l.core r.core).1 := by
  rfl

private theorem authorizedReconcile_right_core_eq
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).2.core = (f l.core r.core).2 := by
  rfl

private theorem leaderFireDisabled_of_frame
    {a b : AgentState psi}
    (hleader : a.leader = b.leader)
    (hsignal : a.signal_B = b.signal_B)
    (h : LeaderFireDisabled b) :
    LeaderFireDisabled a := by
  rcases h with hFollower | hSilent
  · exact .inl (hleader.trans hFollower)
  · exact .inr (hsignal.trans hSilent)

/-- Exact source-covered fields on the authorized carrier. -/
structure AuthorizedSourceCoveredNoFireOutput
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  left_neutral : ComparisonNeutral q.1.core
  right_neutral : ComparisonNeutral q.2.core
  left_leader : q.1.core.leader = l.core.leader
  right_leader : q.2.core.leader = r.core.leader
  left_label : q.1.core.label = l.core.label
  right_label : q.2.core.label = r.core.label
  left_shield : q.1.core.shield = l.core.shield
  right_shield : q.2.core.shield = r.core.shield
  left_bullet_zero : q.1.core.bullet = ⟨0, by omega⟩
  right_bullet_zero : q.2.core.bullet = ⟨0, by omega⟩
  left_signal : q.1.core.signal_B = l.core.signal_B
  right_signal_one_of_source :
    (l.core.leader = true ∨ l.core.signal_B = ⟨1, by omega⟩) →
      q.2.core.signal_B = ⟨1, by omega⟩
  left_reset_false : q.1.core.reset_cmd = false
  right_reset_exact : q.2.core.reset_cmd = !r.core.echo
  right_echo_false : q.2.core.echo = false
  left_echo_exact : q.1.core.echo =
    if l.core.leader = true then false
    else if r.core.label = ⟨psi - 1, by omega⟩ then true
    else l.core.echo

/-- Exact source-covered fields after bounded reification and path-stall
expiry.  The record deliberately leaves the responder signal unrestricted. -/
structure SourceCoveredNoFireOutput
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  left_neutral : ComparisonNeutral q.1.core.erase.core
  right_neutral : ComparisonNeutral q.2.core.erase.core
  left_leader : q.1.core.erase.core.leader = l.core.erase.core.leader
  right_leader : q.2.core.erase.core.leader = r.core.erase.core.leader
  left_label : q.1.core.erase.core.label = l.core.erase.core.label
  right_label : q.2.core.erase.core.label = r.core.erase.core.label
  left_shield : q.1.core.erase.core.shield = l.core.erase.core.shield
  right_shield : q.2.core.erase.core.shield = r.core.erase.core.shield
  left_bullet_zero : q.1.core.erase.core.bullet = ⟨0, by omega⟩
  right_bullet_zero : q.2.core.erase.core.bullet = ⟨0, by omega⟩
  left_signal : q.1.core.erase.core.signal_B = l.core.erase.core.signal_B
  right_signal_one_of_source :
    (l.core.erase.core.leader = true ∨
      l.core.erase.core.signal_B = ⟨1, by omega⟩) →
      q.2.core.erase.core.signal_B = ⟨1, by omega⟩
  left_reset_false : q.1.core.erase.core.reset_cmd = false
  right_reset_exact : q.2.core.erase.core.reset_cmd = !r.core.erase.core.echo
  right_echo_false : q.2.core.erase.core.echo = false
  left_echo_exact : q.1.core.erase.core.echo =
    if l.core.erase.core.leader = true then false
    else if r.core.erase.core.label = ⟨psi - 1, by omega⟩ then true
    else l.core.erase.core.echo

/-- Structural output for the unavoidable nondivisible closing barrier.  The
whole physical `PeaceView` is framed, while comparison and reset/echo controls
are exposed separately.  In particular the returning absence signal is
blocked rather than promoted to one. -/
structure AuthorizedSourceCoveredBarrierOutput
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  peace : authorizedPeaceViewPair q = authorizedPeaceViewPair (l, r)
  left_neutral : ComparisonNeutral q.1.core
  right_neutral : ComparisonNeutral q.2.core
  left_reset_false : q.1.core.reset_cmd = false
  right_reset_exact : q.2.core.reset_cmd = !r.core.echo
  right_echo_false : q.2.core.echo = false
  left_echo_exact : q.1.core.echo =
    if l.core.leader = true then false
    else if r.core.label = ⟨psi - 1, by omega⟩ then true
    else l.core.echo

/-- Bounded/path-stall lift of the structural closing-barrier output. -/
structure SourceCoveredBarrierOutput
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  peace : peaceViewPair
      (q.1.core.erase.core, q.2.core.erase.core) =
    peaceViewPair (l.core.erase.core, r.core.erase.core)
  left_neutral : ComparisonNeutral q.1.core.erase.core
  right_neutral : ComparisonNeutral q.2.core.erase.core
  left_reset_false : q.1.core.erase.core.reset_cmd = false
  right_reset_exact : q.2.core.erase.core.reset_cmd =
    !r.core.erase.core.echo
  right_echo_false : q.2.core.erase.core.echo = false
  left_echo_exact : q.1.core.erase.core.echo =
    if l.core.erase.core.leader = true then false
    else if r.core.erase.core.label = ⟨psi - 1, by omega⟩ then true
    else l.core.erase.core.echo

private theorem normalizeDeletion_reset_eq
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.reset_cmd = u.core.reset_cmd := by
  unfold normalizeDeletion
  split <;> rfl

private theorem normalizeDeletion_echo_eq
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.echo = u.core.echo := by
  unfold normalizeDeletion
  split <;> rfl

private theorem normalTail_eq_postSuppress
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
    wallSweepPreCheckResetNormalTail hpsi kappa l r =
      authorizedPostSuppress hpsi after.1 after.2 := by
  rfl

/-- Named normalized pre-Algorithm-14 boundary for the source-covered proof. -/
def sourcePreStage
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  wallSweepPreCheckResetBeforeSuppress hpsi kappa
    (normalizeDeletion l) (normalizeDeletion r)

/-- All source, PeaceView, reset, and echo facts at the normalized
pre-Algorithm-14 boundary. -/
structure AuthorizedSourcePreOutput
    (l r : AuthorizedAgentState psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  peace : authorizedPeaceViewPair q = authorizedPeaceViewPair (l, r)
  source : q.1.core.leader = true ∨ q.1.core.reset_cmd = true
  left_reset : q.1.core.reset_cmd = l.core.reset_cmd
  left_echo : q.1.core.echo = l.core.echo
  right_echo : q.2.core.echo = r.core.echo

/-- Assemble the normalized source boundary from its two structural frames.
The carrier is kept abstract so this proof never unfolds the full pre-CHECK
prefix merely to recover its leader/reset source. -/
theorem AuthorizedSourcePreOutput.of_frames
    (l r : AuthorizedAgentState psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hpeace : authorizedPeaceViewPair q = authorizedPeaceViewPair (l, r))
    (hreset : q.1.core.reset_cmd = l.core.reset_cmd)
    (hlecho : q.1.core.echo = l.core.echo)
    (hrecho : q.2.core.echo = r.core.echo)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true) :
    AuthorizedSourcePreOutput l r q := by
  have hleader := authorizedPeaceViewPair_left_leader_eq hpeace
  have hsourceQ : q.1.core.leader = true ∨
      q.1.core.reset_cmd = true := by
    rcases hsource with hleaderL | hresetL
    · exact .inl (hleader.trans hleaderL)
    · exact .inr (hreset.trans hresetL)
  exact ⟨hpeace, hsourceQ, hreset, hlecho, hrecho⟩

/-- Exact physical and control fields immediately after repaired Algorithm 14.
This boundary keeps the expensive prefix proof separate from Algorithm 15 and
the post-suppress suffix. -/
structure AuthorizedAfterSuppressNoFireOutput
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  left_neutral : ComparisonNeutral q.1.core
  right_neutral : ComparisonNeutral q.2.core
  left_leader : q.1.core.leader = l.core.leader
  right_leader : q.2.core.leader = r.core.leader
  left_label : q.1.core.label = l.core.label
  right_label : q.2.core.label = r.core.label
  left_shield : q.1.core.shield = l.core.shield
  right_shield : q.2.core.shield = r.core.shield
  left_bullet_zero : q.1.core.bullet = ⟨0, by omega⟩
  right_bullet_zero : q.2.core.bullet = ⟨0, by omega⟩
  left_signal : q.1.core.signal_B = l.core.signal_B
  right_signal : q.2.core.signal_B = r.core.signal_B
  left_reset_false : q.1.core.reset_cmd = false
  right_reset_exact : q.2.core.reset_cmd = !r.core.echo
  right_echo_false : q.2.core.echo = false
  left_echo_exact : q.1.core.echo =
    if l.core.leader = true then false
    else if r.core.label = ⟨psi - 1, by omega⟩ then true
    else l.core.echo

/-- Raw repaired-Algorithm-14 frame before authorization is reconciled. -/
structure RawSuppressNoFireOutput
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (q : AgentState psi × AgentState psi) : Prop where
  left_neutral : ComparisonNeutral q.1
  right_neutral : ComparisonNeutral q.2
  left_leader : q.1.leader = l.core.leader
  right_leader : q.2.leader = r.core.leader
  left_label : q.1.label = l.core.label
  right_label : q.2.label = r.core.label
  left_shield : q.1.shield = l.core.shield
  right_shield : q.2.shield = r.core.shield
  left_bullet_zero : q.1.bullet = ⟨0, by omega⟩
  right_bullet_zero : q.2.bullet = ⟨0, by omega⟩
  left_signal : q.1.signal_B = l.core.signal_B
  right_signal : q.2.signal_B = r.core.signal_B
  left_reset_false : q.1.reset_cmd = false
  right_reset_exact : q.2.reset_cmd = !r.core.echo
  right_echo_false : q.2.echo = false
  left_echo_exact : q.1.echo =
    if l.core.leader = true then false
    else if r.core.label = ⟨psi - 1, by omega⟩ then true
    else l.core.echo

/-- Reset/echo and comparison-neutral half of the raw suppression frame. -/
structure RawSuppressControlOutput
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (q : AgentState psi × AgentState psi) : Prop where
  left_neutral : ComparisonNeutral q.1
  right_neutral : ComparisonNeutral q.2
  left_reset_false : q.1.reset_cmd = false
  right_reset_exact : q.2.reset_cmd = !r.core.echo
  right_echo_false : q.2.echo = false
  left_echo_exact : q.1.echo =
    if l.core.leader = true then false
    else if r.core.label = ⟨psi - 1, by omega⟩ then true
    else l.core.echo

/-- PeaceView half of the raw suppression frame. -/
structure RawSuppressPeaceOutput
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (q : AgentState psi × AgentState psi) : Prop where
  left_leader : q.1.leader = l.core.leader
  right_leader : q.2.leader = r.core.leader
  left_label : q.1.label = l.core.label
  right_label : q.2.label = r.core.label
  left_shield : q.1.shield = l.core.shield
  right_shield : q.2.shield = r.core.shield
  left_bullet_zero : q.1.bullet = ⟨0, by omega⟩
  right_bullet_zero : q.2.bullet = ⟨0, by omega⟩
  left_signal : q.1.signal_B = l.core.signal_B
  right_signal : q.2.signal_B = r.core.signal_B

/-- Stable aligned source coverage preserves the complete physical PeaceView
through the normalized prefix. -/
theorem sourcePreStage_peace
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true) :
    authorizedPeaceViewPair (sourcePreStage hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := sourcePreStage hpsi kappa l r
  have hlView := normalizeDeletion_peaceView l
  have hrView := normalizeDeletion_peaceView r
  have hlLabel := congrArg PeaceView.label hlView
  have hrLabel := congrArg PeaceView.label hrView
  change l0.core.label = l.core.label at hlLabel
  change r0.core.label = r.core.label at hrLabel
  have halign0 : r0.core.label =
      ⟨(l0.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    apply Fin.ext
    have hlVal := congrArg Fin.val hlLabel
    have hrVal := congrArg Fin.val hrLabel
    have haVal := congrArg Fin.val halign
    dsimp only at haVal
    calc
      r0.core.label.val = r.core.label.val := hrVal
      _ = (l.core.label.val + 1) % psi := haVal
      _ = (l0.core.label.val + 1) % psi := by rw [hlVal]
  have hlLeader := congrArg PeaceView.leader hlView
  change l0.core.leader = l.core.leader at hlLeader
  have hsource0 : l0.core.leader = true ∨ l0.core.reset_cmd = true := by
    rcases hsource with hleader | hreset
    · exact .inl (hlLeader.trans hleader)
    · exact .inr ((normalizeDeletion_reset_eq l).trans hreset)
  have hpreCert :=
    wallSweepPreCheckResetBeforeSuppress_peaceFrame_of_aligned_source
      hpsi kappa l0 r0 halign0 hsource0
  have hprePV0 := AuthorizedPeaceFrame.exact_eq hpreCert
  change authorizedPeaceViewPair pre =
    authorizedPeaceViewPair (l0, r0) at hprePV0
  have hnorm : authorizedPeaceViewPair (l0, r0) =
      authorizedPeaceViewPair (l, r) := Prod.ext hlView hrView
  exact hprePV0.trans hnorm

/-- Reset and echo are framed together across normalization and the complete
pre-Algorithm-14 prefix. -/
theorem sourcePreStage_resetEchoPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (sourcePreStage hpsi kappa l r) =
      authorizedResetEchoPair (l, r) := by
  exact (wallSweepPreCheckResetBeforeSuppress_resetEchoPair hpsi kappa
    (normalizeDeletion l) (normalizeDeletion r)).trans
      (normalizeDeletionPair_resetEcho l r)

/-- The initiator reset bit is framed by the normalized prefix. -/
theorem sourcePreStage_left_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    (sourcePreStage hpsi kappa l r).1.core.reset_cmd =
      l.core.reset_cmd :=
  authorizedResetEchoPair_left_reset_eq
    (sourcePreStage_resetEchoPair hpsi kappa l r)

/-- The initiator echo bit is framed by the normalized prefix. -/
theorem sourcePreStage_left_echo
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    (sourcePreStage hpsi kappa l r).1.core.echo = l.core.echo :=
  authorizedResetEchoPair_left_echo_eq
    (sourcePreStage_resetEchoPair hpsi kappa l r)

/-- The responder echo bit is framed by the normalized prefix. -/
theorem sourcePreStage_right_echo
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    (sourcePreStage hpsi kappa l r).2.core.echo = r.core.echo :=
  authorizedResetEchoPair_right_echo_eq
    (sourcePreStage_resetEchoPair hpsi kappa l r)

/-- Source coverage itself survives the normalized prefix. -/
theorem sourcePreStage_source
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true) :
    (sourcePreStage hpsi kappa l r).1.core.leader = true ∨
      (sourcePreStage hpsi kappa l r).1.core.reset_cmd = true := by
  have hprePV := sourcePreStage_peace hpsi kappa l r halign hsource
  have hpreLLeader := authorizedPeaceViewPair_left_leader_eq hprePV
  have hpreLReset := sourcePreStage_left_reset hpsi kappa l r
  rcases hsource with hleader | hreset
  · exact .inl (hpreLLeader.trans hleader)
  · exact .inr (hpreLReset.trans hreset)

/-- Stable aligned source coverage produces the complete normalized prefix
frame used by the no-fire suffix proof. -/
theorem sourcePreStage_frame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true) :
    AuthorizedSourcePreOutput l r (sourcePreStage hpsi kappa l r) := by
  have hprePV := sourcePreStage_peace hpsi kappa l r halign hsource
  have hpreSource := sourcePreStage_source hpsi kappa l r halign hsource
  have hpreLReset := sourcePreStage_left_reset hpsi kappa l r
  have hpreLEcho := sourcePreStage_left_echo hpsi kappa l r
  have hpreREcho := sourcePreStage_right_echo hpsi kappa l r
  exact ⟨hprePV, hpreSource, hpreLReset, hpreLEcho, hpreREcho⟩

/-- An existing responder leader makes the normalized P-prime prefix a
physical frame even when the edge is the nondivisible closing barrier. -/
theorem sourcePreStage_peace_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true) :
    authorizedPeaceViewPair (sourcePreStage hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := sourcePreStage hpsi kappa l r
  have hlView := normalizeDeletion_peaceView l
  have hrView := normalizeDeletion_peaceView r
  have hlLeader := congrArg PeaceView.leader hlView
  have hrLeaderEq := congrArg PeaceView.leader hrView
  change l0.core.leader = l.core.leader at hlLeader
  change r0.core.leader = r.core.leader at hrLeaderEq
  have hrLeader0 : r0.core.leader = true := hrLeaderEq.trans hrLeader
  have hsource0 : l0.core.leader = true ∨ l0.core.reset_cmd = true := by
    rcases hsource with hleader | hreset
    · exact .inl (hlLeader.trans hleader)
    · exact .inr ((normalizeDeletion_reset_eq l).trans hreset)
  have hppsi :=
    pPsiLeaderProbeWall_responder_frame_of_responder_leader
      hpsi l0.core r0.core hrLeader0
  have hpreCert :=
    wallSweepPreCheckResetBeforeSuppress_peaceFrame_of_ppsi_source
      hpsi kappa l0 r0 hppsi.1 hppsi.2 hsource0
  have hprePV0 := AuthorizedPeaceFrame.exact_eq hpreCert
  change authorizedPeaceViewPair pre =
    authorizedPeaceViewPair (l0, r0) at hprePV0
  have hnorm : authorizedPeaceViewPair (l0, r0) =
      authorizedPeaceViewPair (l, r) := Prod.ext hlView hrView
  exact hprePV0.trans hnorm

/-- The normalized prefix has the same source/PeaceView frame when its
responder is an existing leader.  This is the nondivisible closing-edge
specialization: the edge may be a barrier, so no cyclic label alignment is
assumed. -/
theorem sourcePreStage_frame_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true) :
    AuthorizedSourcePreOutput l r (sourcePreStage hpsi kappa l r) := by
  exact AuthorizedSourcePreOutput.of_frames l r
    (sourcePreStage hpsi kappa l r)
    (sourcePreStage_peace_of_responder_leader
      hpsi kappa l r hrLeader hsource)
    (sourcePreStage_left_reset hpsi kappa l r)
    (sourcePreStage_left_echo hpsi kappa l r)
    (sourcePreStage_right_echo hpsi kappa l r)
    hsource

/-- Algorithm 14's control behavior depends only on the named normalized
source frame, not on how the P-prime prefix established that frame. -/
theorem suppressSigResetKill_control_of_frame
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (pre : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hpre : AuthorizedSourcePreOutput l r pre) :
    RawSuppressControlOutput hpsi l r
      (suppressSigResetKill hpsi pre.1.core pre.2.core) := by
  rcases hpre with
    ⟨hprePV, hpreSource, _, hpreLEcho, hpreREcho⟩
  let raw := suppressSigResetKill hpsi pre.1.core pre.2.core
  have hrawExact := suppressSigResetKill_source_reset_echo_exact
    hpsi pre.1.core pre.2.core hpreSource
  change raw.1.reset_cmd = false ∧
      raw.2.reset_cmd = !pre.2.core.echo ∧ raw.2.echo = false ∧
      raw.1.echo = if pre.1.core.leader = true then false
        else if pre.2.core.label = ⟨psi - 1, by omega⟩ then true
        else pre.1.core.echo at hrawExact
  rcases hrawExact with
    ⟨hRawLReset, hRawRReset0, hRawREcho, hRawLEcho0⟩
  have hpreLLeader := authorizedPeaceViewPair_left_leader_eq hprePV
  have hpreRLabel := authorizedPeaceViewPair_right_label_eq hprePV
  have hRawRReset : raw.2.reset_cmd = !r.core.echo := by
    calc
      raw.2.reset_cmd = !pre.2.core.echo := hRawRReset0
      _ = !r.core.echo := by rw [hpreREcho]
  have hRawLEcho : raw.1.echo =
      if l.core.leader = true then false
      else if r.core.label = ⟨psi - 1, by omega⟩ then true
      else l.core.echo := by
    calc
      raw.1.echo = if pre.1.core.leader = true then false
          else if pre.2.core.label = ⟨psi - 1, by omega⟩ then true
          else pre.1.core.echo := hRawLEcho0
      _ = if l.core.leader = true then false
          else if r.core.label = ⟨psi - 1, by omega⟩ then true
          else l.core.echo := by
        rw [hpreLLeader, hpreRLabel, hpreLEcho]
  have hrawNeutral : ComparisonNeutral raw.1 ∧ ComparisonNeutral raw.2 := by
    by_cases he : pre.2.core.echo = true
    · have hc := suppressSigResetKill_source_echo_collision
        hpsi pre.1.core pre.2.core hpreSource he
      exact ⟨hc.1, hc.2.1⟩
    · have he0 : pre.2.core.echo = false := by
        cases h : pre.2.core.echo
        · rfl
        · exact (he h).elim
      rcases hpreSource with hleader | hreset
      · exact suppressSigResetKill_leader_reseed_neutral
          hpsi pre.1.core pre.2.core hleader he0
      · have hn := suppressSigResetKill_handoff
          hpsi pre.1.core pre.2.core hreset he0
        exact ⟨hn.1, hn.2.1⟩
  exact {
    left_neutral := hrawNeutral.1
    right_neutral := hrawNeutral.2
    left_reset_false := hRawLReset
    right_reset_exact := hRawRReset
    right_echo_false := hRawREcho
    left_echo_exact := hRawLEcho
  }

/-- Specialization of the abstract Algorithm-14 control frame to the named
normalized pre-stage. -/
theorem sourcePreStage_suppressSigResetKill_control_of_frame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hpre : AuthorizedSourcePreOutput l r
      (sourcePreStage hpsi kappa l r)) :
    let pre := sourcePreStage hpsi kappa l r
    RawSuppressControlOutput hpsi l r
      (suppressSigResetKill hpsi pre.1.core pre.2.core) := by
  exact suppressSigResetKill_control_of_frame hpsi l r
    (sourcePreStage hpsi kappa l r) hpre

/-- Source coverage determines the complete raw reset/echo behavior and makes
both suppression outputs comparison-neutral. -/
theorem sourcePreStage_suppressSigResetKill_control
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true) :
    let pre := sourcePreStage hpsi kappa l r
    RawSuppressControlOutput hpsi l r
      (suppressSigResetKill hpsi pre.1.core pre.2.core) := by
  let pre := sourcePreStage hpsi kappa l r
  have hpre : AuthorizedSourcePreOutput l r pre := by
    simpa only [pre] using sourcePreStage_frame hpsi kappa l r halign hsource
  simpa only [pre] using
    sourcePreStage_suppressSigResetKill_control_of_frame
      hpsi kappa l r hpre

/-- Compose an opaque raw PeaceView frame with any named normalized source
frame.  The raw pair remains abstract, so elaboration does not reopen the
concrete Algorithm-14 transition. -/
theorem sourcePreStage_peace_of_raw_frame_from_pre
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hpre : AuthorizedSourcePreOutput l r
      (sourcePreStage hpsi kappa l r))
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩)
    (q : AgentState psi × AgentState psi)
    (hq : peaceViewPair q = peaceViewPair
      ((sourcePreStage hpsi kappa l r).1.core,
        (sourcePreStage hpsi kappa l r).2.core)) :
    RawSuppressPeaceOutput hpsi l r q := by
  have hrawPV : peaceViewPair q = peaceViewPair (l.core, r.core) :=
    peaceViewPair_trans_authorizedCore hq hpre.peace
  exact {
    left_leader := peaceViewPair_left_leader_eq hrawPV
    right_leader := peaceViewPair_right_leader_eq hrawPV
    left_label := peaceViewPair_left_label_eq hrawPV
    right_label := peaceViewPair_right_label_eq hrawPV
    left_shield := peaceViewPair_left_shield_eq hrawPV
    right_shield := peaceViewPair_right_shield_eq hrawPV
    left_bullet_zero := (peaceViewPair_left_bullet_eq hrawPV).trans hlBullet
    right_bullet_zero := (peaceViewPair_right_bullet_eq hrawPV).trans hrBullet
    left_signal := peaceViewPair_left_signal_eq hrawPV
    right_signal := peaceViewPair_right_signal_eq hrawPV
  }

/-- Aligned-edge wrapper for the abstract raw PeaceView composition. -/
theorem sourcePreStage_peace_of_raw_frame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩)
    (q : AgentState psi × AgentState psi)
    (hq : peaceViewPair q = peaceViewPair
      ((sourcePreStage hpsi kappa l r).1.core,
        (sourcePreStage hpsi kappa l r).2.core)) :
    RawSuppressPeaceOutput hpsi l r q := by
  have hpre := sourcePreStage_frame hpsi kappa l r halign hsource
  exact sourcePreStage_peace_of_raw_frame_from_pre
    hpsi kappa l r hpre hlBullet hrBullet q hq

/-- Raw repaired Algorithm 14 frames all fields consumed by the no-collision
kernel from any certified normalized source prefix. -/
theorem sourcePreStage_suppressSigResetKill_source_frame_of_pre
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hpre : AuthorizedSourcePreOutput l r
      (sourcePreStage hpsi kappa l r))
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩) :
    let pre := sourcePreStage hpsi kappa l r
    RawSuppressNoFireOutput hpsi l r
      (suppressSigResetKill hpsi pre.1.core pre.2.core) := by
  let pre := sourcePreStage hpsi kappa l r
  let raw := suppressSigResetKill hpsi pre.1.core pre.2.core
  have hcontrol : RawSuppressControlOutput hpsi l r raw := by
    simpa only [pre, raw] using
      sourcePreStage_suppressSigResetKill_control_of_frame
        hpsi kappa l r hpre
  have hrawPV := suppressSigResetKill_peaceViewPair
    hpsi pre.1.core pre.2.core
  change peaceViewPair raw = peaceViewPair (pre.1.core, pre.2.core) at hrawPV
  have hpeace : RawSuppressPeaceOutput hpsi l r raw := by
    apply sourcePreStage_peace_of_raw_frame_from_pre
      hpsi kappa l r hpre hlBullet hrBullet raw
    simpa only [pre] using hrawPV
  have hrawOut : RawSuppressNoFireOutput hpsi l r raw := {
    left_neutral := hcontrol.left_neutral
    right_neutral := hcontrol.right_neutral
    left_leader := hpeace.left_leader
    right_leader := hpeace.right_leader
    left_label := hpeace.left_label
    right_label := hpeace.right_label
    left_shield := hpeace.left_shield
    right_shield := hpeace.right_shield
    left_bullet_zero := hpeace.left_bullet_zero
    right_bullet_zero := hpeace.right_bullet_zero
    left_signal := hpeace.left_signal
    right_signal := hpeace.right_signal
    left_reset_false := hcontrol.left_reset_false
    right_reset_exact := hcontrol.right_reset_exact
    right_echo_false := hcontrol.right_echo_false
    left_echo_exact := hcontrol.left_echo_exact
  }
  simpa only [pre, raw] using hrawOut

/-- Aligned source-covered specialization of the raw Algorithm-14 frame. -/
theorem sourcePreStage_suppressSigResetKill_source_frame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩) :
    let pre := sourcePreStage hpsi kappa l r
    RawSuppressNoFireOutput hpsi l r
      (suppressSigResetKill hpsi pre.1.core pre.2.core) := by
  have hpre := sourcePreStage_frame hpsi kappa l r halign hsource
  exact sourcePreStage_suppressSigResetKill_source_frame_of_pre
    hpsi kappa l r hpre hlBullet hrBullet

/-- Any certified source-covered zero-bullet prefix reaches repaired Algorithm
14 with neutral comparisons and every later no-fire field exposed exactly. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_source_frame_of_pre
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hpre : AuthorizedSourcePreOutput l r
      (sourcePreStage hpsi kappa l r))
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩) :
    AuthorizedAfterSuppressNoFireOutput hpsi l r
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let pre := sourcePreStage hpsi kappa l r
  let raw := suppressSigResetKill hpsi pre.1.core pre.2.core
  have hraw : RawSuppressNoFireOutput hpsi l r raw := by
    simpa only [pre, raw] using
      sourcePreStage_suppressSigResetKill_source_frame_of_pre
        hpsi kappa l r hpre hlBullet hrBullet
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafterEq := wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
    hpsi kappa l r
  change after = authorizedReconcile
    (suppressSigResetKill hpsi) pre.1 pre.2 at hafterEq
  have hafterLCore : after.1.core = raw.1 := by
    exact (congrArg (fun q => q.1.core) hafterEq).trans
      (authorizedReconcile_left_core_eq
        (suppressSigResetKill hpsi) pre.1 pre.2)
  have hafterRCore : after.2.core = raw.2 := by
    exact (congrArg (fun q => q.2.core) hafterEq).trans
      (authorizedReconcile_right_core_eq
        (suppressSigResetKill hpsi) pre.1 pre.2)
  exact {
    left_neutral := by rw [hafterLCore]; exact hraw.left_neutral
    right_neutral := by rw [hafterRCore]; exact hraw.right_neutral
    left_leader := (congrArg AgentState.leader hafterLCore).trans hraw.left_leader
    right_leader := (congrArg AgentState.leader hafterRCore).trans hraw.right_leader
    left_label := (congrArg AgentState.label hafterLCore).trans hraw.left_label
    right_label := (congrArg AgentState.label hafterRCore).trans hraw.right_label
    left_shield := (congrArg AgentState.shield hafterLCore).trans hraw.left_shield
    right_shield := (congrArg AgentState.shield hafterRCore).trans hraw.right_shield
    left_bullet_zero :=
      (congrArg AgentState.bullet hafterLCore).trans hraw.left_bullet_zero
    right_bullet_zero :=
      (congrArg AgentState.bullet hafterRCore).trans hraw.right_bullet_zero
    left_signal :=
      (congrArg AgentState.signal_B hafterLCore).trans hraw.left_signal
    right_signal :=
      (congrArg AgentState.signal_B hafterRCore).trans hraw.right_signal
    left_reset_false :=
      (congrArg AgentState.reset_cmd hafterLCore).trans hraw.left_reset_false
    right_reset_exact :=
      (congrArg AgentState.reset_cmd hafterRCore).trans hraw.right_reset_exact
    right_echo_false :=
      (congrArg AgentState.echo hafterRCore).trans hraw.right_echo_false
    left_echo_exact :=
      (congrArg AgentState.echo hafterLCore).trans hraw.left_echo_exact
  }

private theorem authorizedReconcile_suppress_right_leader_of_peace
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (pre : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hpeace : authorizedPeaceViewPair pre =
      authorizedPeaceViewPair (l, r)) :
    (authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2).2.core.leader =
      r.core.leader := by
  let raw := suppressSigResetKill hpsi pre.1.core pre.2.core
  have hrawPV : peaceViewPair raw =
      peaceViewPair (pre.1.core, pre.2.core) := by
    simpa only [raw] using suppressSigResetKill_peaceViewPair
      hpsi pre.1.core pre.2.core
  exact (congrArg AgentState.leader
      (authorizedReconcile_right_core_eq
        (suppressSigResetKill hpsi) pre.1 pre.2)).trans
    ((peaceViewPair_right_leader_eq hrawPV).trans
      (authorizedPeaceViewPair_right_leader_eq hpeace))

/-- The repaired Algorithm-14 boundary frames the responder leader bit from
any certified source prefix; no bullet or fire premise is needed. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_right_leader_of_pre
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hpre : AuthorizedSourcePreOutput l r
      (sourcePreStage hpsi kappa l r)) :
    (wallSweepPreCheckResetNormalAfterSuppress
      hpsi kappa l r).2.core.leader = r.core.leader := by
  let pre := sourcePreStage hpsi kappa l r
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafterEq := wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
    hpsi kappa l r
  change after = authorizedReconcile
    (suppressSigResetKill hpsi) pre.1 pre.2 at hafterEq
  exact (congrArg (fun q => q.2.core.leader) hafterEq).trans
    (authorizedReconcile_suppress_right_leader_of_peace
      hpsi l r pre hpre.peace)

/-- Aligned source-covered specialization of the repaired Algorithm-14
physical/control frame. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_source_frame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩) :
    AuthorizedAfterSuppressNoFireOutput hpsi l r
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  have hpre := sourcePreStage_frame hpsi kappa l r halign hsource
  exact wallSweepPreCheckResetNormalAfterSuppress_source_frame_of_pre
    hpsi kappa l r hpre hlBullet hrBullet

/-- The ordinary source-covered no-fire tail before the proof-only birth marker.
The responder may itself be the designated label-zero leader, provided its
fire guard is disabled. -/
theorem wallSweepPreCheckResetNormalTail_source_noFire_zeroResponder
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hlFire : LeaderFireDisabled l.core)
    (hrFire : LeaderFireDisabled r.core)
    (hrZero : r.core.leader = true → r.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩) :
    AuthorizedSourceCoveredNoFireOutput hpsi l r
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafter : AuthorizedAfterSuppressNoFireOutput hpsi l r after := by
    simpa only [after] using
      wallSweepPreCheckResetNormalAfterSuppress_source_frame
        hpsi kappa l r halign hsource hlBullet hrBullet
  have hafterNeutral : ComparisonNeutral after.1.core ∧
      ComparisonNeutral after.2.core := ⟨hafter.left_neutral, hafter.right_neutral⟩
  have hafterLLeader := hafter.left_leader
  have hafterRLeader := hafter.right_leader
  have hafterLLabel := hafter.left_label
  have hafterRLabel := hafter.right_label
  have hafterLShield := hafter.left_shield
  have hafterRShield := hafter.right_shield
  have hafterLBullet := hafter.left_bullet_zero
  have hafterRBullet := hafter.right_bullet_zero
  have hafterLSignal := hafter.left_signal
  have hafterRSignal := hafter.right_signal
  have hafterLReset := hafter.left_reset_false
  have hafterRReset := hafter.right_reset_exact
  have hafterREcho := hafter.right_echo_false
  have hafterLEcho := hafter.left_echo_exact
  have hafterLFire : LeaderFireDisabled after.1.core :=
    leaderFireDisabled_of_frame hafterLLeader hafterLSignal hlFire
  have hafterRFire : LeaderFireDisabled after.2.core :=
    leaderFireDisabled_of_frame hafterRLeader hafterRSignal hrFire
  have hnc := noCollision_zero_bullets_noFire_frame
    hpsi after.1.core after.2.core
      hafterLFire hafterRFire hafterLBullet hafterRBullet
  dsimp only at hnc
  rcases hnc with ⟨hncLL, hncRL, hncLLabel, hncRLabel,
    hncLS, hncRS, hncLB, hncRB, hncLSignal⟩
  have hzero :
      let q := eliminateLeadersNoCollision hpsi after.1.core after.2.core
      q.2.leader = true → q.2.label = ⟨0, hpsi⟩ := by
    dsimp only
    intro hleader
    have hrLeader : r.core.leader = true :=
      (hncRL.trans hafterRLeader).symm.trans hleader
    exact (hncRLabel.trans hafterRLabel).trans (hrZero hrLeader)
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have hpostPV := authorizedPostSuppress_peaceView_eq_noCollision
    hpsi after.1 after.2 hzero
  have htailEq : tail = authorizedPostSuppress hpsi after.1 after.2 := by
    simpa only [tail, after] using normalTail_eq_postSuppress hpsi kappa l r
  have htailPV := (congrArg authorizedPeaceViewPair htailEq).trans hpostPV
  have htailLLeader := authorizedPeaceViewPair_raw_left_leader_eq htailPV
  have htailRLeader := authorizedPeaceViewPair_raw_right_leader_eq htailPV
  have htailLLabel := authorizedPeaceViewPair_raw_left_label_eq htailPV
  have htailRLabel := authorizedPeaceViewPair_raw_right_label_eq htailPV
  have htailLShield := authorizedPeaceViewPair_raw_left_shield_eq htailPV
  have htailRShield := authorizedPeaceViewPair_raw_right_shield_eq htailPV
  have htailLBullet := authorizedPeaceViewPair_raw_left_bullet_eq htailPV
  have htailRBullet := authorizedPeaceViewPair_raw_right_bullet_eq htailPV
  have htailLSignal := authorizedPeaceViewPair_raw_left_signal_eq htailPV
  have htailRSignal := authorizedPeaceViewPair_raw_right_signal_eq htailPV
  have htailControl := postSuppress_normalReset_handoff
    hpsi after.1 after.2 hafterNeutral.1 hafterNeutral.2
  change ComparisonNeutral tail.1.core ∧ ComparisonNeutral tail.2.core ∧
      tail.1.core.reset_cmd = after.1.core.reset_cmd ∧
      tail.2.core.reset_cmd = after.2.core.reset_cmd ∧
      tail.1.core.echo = after.1.core.echo ∧
      tail.2.core.echo = after.2.core.echo at htailControl
  have htailOut : AuthorizedSourceCoveredNoFireOutput hpsi l r tail := by
    exact {
      left_neutral := htailControl.1
      right_neutral := htailControl.2.1
      left_leader := htailLLeader.trans (hncLL.trans hafterLLeader)
      right_leader := htailRLeader.trans (hncRL.trans hafterRLeader)
      left_label := htailLLabel.trans (hncLLabel.trans hafterLLabel)
      right_label := htailRLabel.trans (hncRLabel.trans hafterRLabel)
      left_shield := htailLShield.trans (hncLS.trans hafterLShield)
      right_shield := htailRShield.trans (hncRS.trans hafterRShield)
      left_bullet_zero := htailLBullet.trans hncLB
      right_bullet_zero := htailRBullet.trans hncRB
      left_signal := htailLSignal.trans (hncLSignal.trans hafterLSignal)
      right_signal_one_of_source := by
        intro hsignalSource
        have hafterSource : after.1.core.leader = true ∨
            after.1.core.signal_B = ⟨1, by omega⟩ := by
          rcases hsignalSource with hleader | hsignal
          · exact .inl (hafterLLeader.trans hleader)
          · exact .inr (hafterLSignal.trans hsignal)
        have hafterAlign : after.2.core.label =
            ⟨(after.1.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := by
          apply Fin.ext
          have hleftVal := congrArg Fin.val hafterLLabel
          have hrightVal := congrArg Fin.val hafterRLabel
          have halignVal := congrArg Fin.val halign
          dsimp only at halignVal
          calc
            after.2.core.label.val = r.core.label.val := hrightVal
            _ = (l.core.label.val + 1) % psi := halignVal
            _ = (after.1.core.label.val + 1) % psi := by rw [hleftVal]
        have hrightSignal :=
          noCollision_right_signal_one_of_aligned_source_noFire
            hpsi after.1.core after.2.core hafterAlign hafterRBullet
              hafterRFire hafterSource
        exact htailRSignal.trans hrightSignal
      left_reset_false := htailControl.2.2.1.trans hafterLReset
      right_reset_exact := htailControl.2.2.2.1.trans hafterRReset
      right_echo_false := htailControl.2.2.2.2.2.trans hafterREcho
      left_echo_exact := htailControl.2.2.2.2.1.trans hafterLEcho
    }
  simpa only [tail] using htailOut

/-- Algorithm 15 frames the physical state on the follower-to-leader closing
barrier.  This isolated boundary records both the blocked signal and the
label-zero witness needed by gated WRITE. -/
theorem noCollision_barrier_frame_of_afterSuppress
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (after : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hafter : AuthorizedAfterSuppressNoFireOutput hpsi l r after)
    (hbarrier : isBarrier hpsi l.core r.core)
    (hlFollower : l.core.leader = false)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩)
    (hrSignal : r.core.signal_B = ⟨0, by omega⟩) :
    let nc := eliminateLeadersNoCollision hpsi after.1.core after.2.core
    peaceViewPair nc = peaceViewPair (l.core, r.core) ∧
      (nc.2.leader = true → nc.2.label = ⟨0, hpsi⟩) := by
  have hafterLFire : LeaderFireDisabled after.1.core :=
    .inl (hafter.left_leader.trans hlFollower)
  have hafterRFire : LeaderFireDisabled after.2.core :=
    .inr (hafter.right_signal.trans hrSignal)
  have hafterBarrier : isBarrier hpsi after.1.core after.2.core := by
    intro halign
    apply hbarrier
    have hleftVal := congrArg Fin.val hafter.left_label
    have hrightVal := congrArg Fin.val hafter.right_label
    apply Fin.ext
    have halignVal := congrArg Fin.val halign
    dsimp only at halignVal
    calc
      r.core.label.val = after.2.core.label.val := hrightVal.symm
      _ = (after.1.core.label.val + 1) % psi := halignVal
      _ = (l.core.label.val + 1) % psi := by rw [hleftVal]
  have hnc := noCollision_zero_bullets_noFire_frame
    hpsi after.1.core after.2.core hafterLFire hafterRFire
      hafter.left_bullet_zero hafter.right_bullet_zero
  dsimp only at hnc
  rcases hnc with ⟨hncLL, hncRL, hncLLabel, hncRLabel,
    hncLS, hncRS, hncLB, hncRB, hncLSignal⟩
  have hncRSignal :
      (eliminateLeadersNoCollision hpsi after.1.core after.2.core).2.signal_B =
        ⟨0, by omega⟩ :=
    noCollision_right_signal_zero_of_barrier_follower
      hpsi after.1.core after.2.core hafterBarrier
        (hafter.left_leader.trans hlFollower)
        hafter.right_bullet_zero (hafter.right_signal.trans hrSignal)
  let nc := eliminateLeadersNoCollision hpsi after.1.core after.2.core
  have hncLeaders : leaderPair nc =
      leaderPair (after.1.core, after.2.core) :=
    Prod.ext hncLL hncRL
  have hncLabels : labelPair nc =
      labelPair (after.1.core, after.2.core) :=
    Prod.ext hncLLabel hncRLabel
  have hncBullets : bulletFieldPair nc =
      bulletFieldPair (after.1.core, after.2.core) := by
    apply Prod.ext
    · exact BulletFields.ext _ _ hncLS
        (hncLB.trans hafter.left_bullet_zero.symm) hncLSignal
    · exact BulletFields.ext _ _ hncRS
        (hncRB.trans hafter.right_bullet_zero.symm)
        (hncRSignal.trans (hafter.right_signal.trans hrSignal).symm)
  have hncPV : peaceViewPair nc =
      peaceViewPair (after.1.core, after.2.core) :=
    peaceViewPair_eq_of_frames hncLeaders hncLabels hncBullets
  have hafterLeaders : leaderPair (after.1.core, after.2.core) =
      leaderPair (l.core, r.core) :=
    Prod.ext hafter.left_leader hafter.right_leader
  have hafterLabels : labelPair (after.1.core, after.2.core) =
      labelPair (l.core, r.core) :=
    Prod.ext hafter.left_label hafter.right_label
  have hafterBullets : bulletFieldPair (after.1.core, after.2.core) =
      bulletFieldPair (l.core, r.core) := by
    apply Prod.ext
    · exact BulletFields.ext _ _ hafter.left_shield
        (hafter.left_bullet_zero.trans hlBullet.symm) hafter.left_signal
    · exact BulletFields.ext _ _ hafter.right_shield
        (hafter.right_bullet_zero.trans hrBullet.symm) hafter.right_signal
  have hafterPV : peaceViewPair (after.1.core, after.2.core) =
      peaceViewPair (l.core, r.core) :=
    peaceViewPair_eq_of_frames hafterLeaders hafterLabels hafterBullets
  have hzero : nc.2.leader = true → nc.2.label = ⟨0, hpsi⟩ := by
    intro _
    exact hncRLabel.trans (hafter.right_label.trans hrZero)
  exact ⟨hncPV.trans hafterPV, hzero⟩

/-- The post-suppression suffix consumes an abstract closing-barrier frame
without reopening Algorithm 14 or Algorithm 15. -/
theorem authorizedPostSuppress_barrier_output_of_afterSuppress
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (after : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hafter : AuthorizedAfterSuppressNoFireOutput hpsi l r after)
    (hncPV : peaceViewPair
        (eliminateLeadersNoCollision hpsi after.1.core after.2.core) =
      peaceViewPair (l.core, r.core))
    (hzero :
      (eliminateLeadersNoCollision hpsi after.1.core after.2.core).2.leader =
          true →
        (eliminateLeadersNoCollision hpsi after.1.core after.2.core).2.label =
          ⟨0, hpsi⟩) :
    AuthorizedSourceCoveredBarrierOutput hpsi l r
      (authorizedPostSuppress hpsi after.1 after.2) := by
  have hpostPV := authorizedPostSuppress_peaceView_eq_noCollision
    hpsi after.1 after.2 hzero
  have htailControl := postSuppress_normalReset_handoff
    hpsi after.1 after.2 hafter.left_neutral hafter.right_neutral
  exact {
    peace := hpostPV.trans hncPV
    left_neutral := htailControl.1
    right_neutral := htailControl.2.1
    left_reset_false := htailControl.2.2.1.trans hafter.left_reset_false
    right_reset_exact := htailControl.2.2.2.1.trans hafter.right_reset_exact
    right_echo_false := htailControl.2.2.2.2.2.trans hafter.right_echo_false
    left_echo_exact := htailControl.2.2.2.2.1.trans hafter.left_echo_exact
  }

/-- On the nondivisible closing edge, the responder leader covers the barrier
and the repaired prefix/suffix still clears both comparison endpoints.  The
paper's Algorithm 15 intentionally blocks the returning absence signal here,
so the conclusion frames the whole physical `PeaceView` instead of asserting
signal propagation. -/
theorem wallSweepPreCheckResetNormalTail_source_barrier_responder
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hbarrier : isBarrier hpsi l.core r.core)
    (hlReset : l.core.reset_cmd = true)
    (hlFollower : l.core.leader = false)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩)
    (hrSignal : r.core.signal_B = ⟨0, by omega⟩) :
    AuthorizedSourceCoveredBarrierOutput hpsi l r
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hpre := sourcePreStage_frame_of_responder_leader
    hpsi kappa l r hrLeader (.inr hlReset)
  have hafter : AuthorizedAfterSuppressNoFireOutput hpsi l r after := by
    simpa only [after] using
      wallSweepPreCheckResetNormalAfterSuppress_source_frame_of_pre
        hpsi kappa l r hpre hlBullet hrBullet
  have hnc := noCollision_barrier_frame_of_afterSuppress
    hpsi l r after hafter hbarrier hlFollower hrZero
      hlBullet hrBullet hrSignal
  dsimp only at hnc
  have hpost := authorizedPostSuppress_barrier_output_of_afterSuppress
    hpsi l r after hafter hnc.1 hnc.2
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have htailEq : tail = authorizedPostSuppress hpsi after.1 after.2 := by
    simpa only [tail, after] using normalTail_eq_postSuppress hpsi kappa l r
  change AuthorizedSourceCoveredBarrierOutput hpsi l r tail
  rw [htailEq]
  exact hpost

/-- One source-covered no-fire edge through the complete authorized transition.
The neutral ordinary tail makes its proof-only leader-birth marker inert. -/
theorem wallSweepPreCheckResetAuthorized_source_noFire_zeroResponder
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hlFire : LeaderFireDisabled l.core)
    (hrFire : LeaderFireDisabled r.core)
    (hrZero : r.core.leader = true → r.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩) :
    AuthorizedSourceCoveredNoFireOutput hpsi l r
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have htailOut : AuthorizedSourceCoveredNoFireOutput hpsi l r tail := by
    simpa only [tail] using
      wallSweepPreCheckResetNormalTail_source_noFire_zeroResponder
        hpsi kappa l r halign hsource hlFire hrFire hrZero hlBullet hrBullet
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hmark := markLeaderBirth_eq_of_neutral born tail
    htailOut.left_neutral htailOut.right_neutral
  have heq := wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
    hpsi kappa l r hopen
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  rw [heq, hmark]
  exact htailOut

/-- Priority-open lift of the nondivisible closing-barrier frame.  The
proof-only birth marker is inert because Algorithm 14/15 left both comparison
outputs neutral. -/
theorem wallSweepPreCheckResetAuthorized_source_barrier_responder
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hbarrier : isBarrier hpsi l.core r.core)
    (hlReset : l.core.reset_cmd = true)
    (hlFollower : l.core.leader = false)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩)
    (hrSignal : r.core.signal_B = ⟨0, by omega⟩) :
    AuthorizedSourceCoveredBarrierOutput hpsi l r
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have htail : AuthorizedSourceCoveredBarrierOutput hpsi l r tail := by
    simpa only [tail] using
      wallSweepPreCheckResetNormalTail_source_barrier_responder
        hpsi kappa l r hbarrier hlReset hlFollower hrLeader hrZero
          hlBullet hrBullet hrSignal
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hmark := markLeaderBirth_eq_of_neutral born tail
    htail.left_neutral htail.right_neutral
  have heq := wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
    hpsi kappa l r hopen
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  rw [heq, hmark]
  exact htail

/-- Follower-responder specialization of the exact authorized source frame. -/
theorem wallSweepPreCheckResetAuthorized_source_noFire
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hlFire : LeaderFireDisabled l.core)
    (hrFollower : r.core.leader = false)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩) :
    AuthorizedSourceCoveredNoFireOutput hpsi l r
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  apply wallSweepPreCheckResetAuthorized_source_noFire_zeroResponder
    hpsi kappa l r hopen halign hsource hlFire (.inl hrFollower)
  · intro hleader
    have hbad : (false : Bool) = true := hrFollower.symm.trans hleader
    simp at hbad
  · exact hlBullet
  · exact hrBullet

/-- Source-covered priority-open execution through bounded reification and
path-stall expiry, including the final label-zero leader responder. -/
theorem wallSweepPreCheckResetPathStall_source_noFire_zeroResponder
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (halign : r.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.erase.core.leader = true ∨
      l.core.erase.core.reset_cmd = true)
    (hlFire : LeaderFireDisabled l.core.erase.core)
    (hrFire : LeaderFireDisabled r.core.erase.core)
    (hrZero : r.core.erase.core.leader = true →
      r.core.erase.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.erase.core.bullet = ⟨0, by omega⟩) :
    SourceCoveredNoFireOutput hpsi l r
      (wallSweepPreCheckResetPathStallTransition
        hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha := wallSweepPreCheckResetAuthorized_source_noFire_zeroResponder
    hpsi kappa l.core.erase r.core.erase hopen halign hsource
      hlFire hrFire hrZero hlBullet hrBullet
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbaseLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.left_neutral
  have hbaseRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.right_neutral
  have hLf := deletionPriorityExpireOne_neutral_fields
    l lBase hbaseLNeutral
  have hRf := deletionPriorityExpireOne_neutral_fields
    r rBase hbaseRNeutral
  have hLPV := deletionPriorityExpireOne_peaceView_frame l lBase
  have hRPV := deletionPriorityExpireOne_peaceView_frame r rBase
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  refine {
    left_neutral := hLf.1
    right_neutral := hRf.1
    left_leader := hLf.2.1.trans ?_
    right_leader := hRf.2.1.trans ?_
    left_label := hLf.2.2.1.trans ?_
    right_label := hRf.2.2.1.trans ?_
    left_shield := hLf.2.2.2.2.2.trans ?_
    right_shield := hRf.2.2.2.2.2.trans ?_
    left_bullet_zero := (congrArg PeaceView.bullet hLPV).trans ?_
    right_bullet_zero := (congrArg PeaceView.bullet hRPV).trans ?_
    left_signal := (congrArg PeaceView.signal_B hLPV).trans ?_
    right_signal_one_of_source := ?_
    left_reset_false := hLf.2.2.2.1.trans ?_
    right_reset_exact := hRf.2.2.2.1.trans ?_
    right_echo_false := hRf.2.2.2.2.1.trans ?_
    left_echo_exact := hLf.2.2.2.2.1.trans ?_
  }
  · change bounded.1.erase.core.leader = l.core.erase.core.leader
    rw [hL]
    exact ha.left_leader
  · change bounded.2.erase.core.leader = r.core.erase.core.leader
    rw [hR]
    exact ha.right_leader
  · change bounded.1.erase.core.label = l.core.erase.core.label
    rw [hL]
    exact ha.left_label
  · change bounded.2.erase.core.label = r.core.erase.core.label
    rw [hR]
    exact ha.right_label
  · change bounded.1.erase.core.shield = l.core.erase.core.shield
    rw [hL]
    exact ha.left_shield
  · change bounded.2.erase.core.shield = r.core.erase.core.shield
    rw [hR]
    exact ha.right_shield
  · change bounded.1.erase.core.bullet = ⟨0, by omega⟩
    rw [hL]
    exact ha.left_bullet_zero
  · change bounded.2.erase.core.bullet = ⟨0, by omega⟩
    rw [hR]
    exact ha.right_bullet_zero
  · change bounded.1.erase.core.signal_B = l.core.erase.core.signal_B
    rw [hL]
    exact ha.left_signal
  · intro hsignalSource
    have hbase : bounded.2.erase.core.signal_B = ⟨1, by omega⟩ := by
      rw [hR]
      exact ha.right_signal_one_of_source hsignalSource
    exact (congrArg PeaceView.signal_B hRPV).trans hbase
  · change bounded.1.erase.core.reset_cmd = false
    rw [hL]
    exact ha.left_reset_false
  · change bounded.2.erase.core.reset_cmd = !r.core.erase.core.echo
    rw [hR]
    exact ha.right_reset_exact
  · change bounded.2.erase.core.echo = false
    rw [hR]
    exact ha.right_echo_false
  · change bounded.1.erase.core.echo = _
    rw [hL]
    exact ha.left_echo_exact

/-- Bounded/path-stall lift of the nondivisible closing-barrier frame. -/
theorem wallSweepPreCheckResetPathStall_source_barrier_responder
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hbarrier : isBarrier hpsi l.core.erase.core r.core.erase.core)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hlFollower : l.core.erase.core.leader = false)
    (hrLeader : r.core.erase.core.leader = true)
    (hrZero : r.core.erase.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrSignal : r.core.erase.core.signal_B = ⟨0, by omega⟩) :
    SourceCoveredBarrierOutput hpsi l r
      (wallSweepPreCheckResetPathStallTransition
        hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha := wallSweepPreCheckResetAuthorized_source_barrier_responder
    hpsi kappa l.core.erase r.core.erase hopen hbarrier hlReset
      hlFollower hrLeader hrZero hlBullet hrBullet hrSignal
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbaseLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.left_neutral
  have hbaseRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.right_neutral
  have hLf := deletionPriorityExpireOne_neutral_fields l lBase hbaseLNeutral
  have hRf := deletionPriorityExpireOne_neutral_fields r rBase hbaseRNeutral
  have hLPV := deletionPriorityExpireOne_peaceView_frame l lBase
  have hRPV := deletionPriorityExpireOne_peaceView_frame r rBase
  have hbasePV : peaceViewPair
      (lBase.core.erase.core, rBase.core.erase.core) =
      peaceViewPair (l.core.erase.core, r.core.erase.core) := by
    change authorizedPeaceViewPair (bounded.1.erase, bounded.2.erase) =
      authorizedPeaceViewPair (l.core.erase, r.core.erase)
    exact (congrArg authorizedPeaceViewPair he).trans ha.peace
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  refine {
    peace := ?_
    left_neutral := hLf.1
    right_neutral := hRf.1
    left_reset_false := hLf.2.2.2.1.trans ?_
    right_reset_exact := hRf.2.2.2.1.trans ?_
    right_echo_false := hRf.2.2.2.2.1.trans ?_
    left_echo_exact := hLf.2.2.2.2.1.trans ?_
  }
  · exact (Prod.ext hLPV hRPV).trans hbasePV
  · change bounded.1.erase.core.reset_cmd = false
    rw [hL]
    exact ha.left_reset_false
  · change bounded.2.erase.core.reset_cmd = !r.core.erase.core.echo
    rw [hR]
    exact ha.right_reset_exact
  · change bounded.2.erase.core.echo = false
    rw [hR]
    exact ha.right_echo_false
  · change bounded.1.erase.core.echo = _
    rw [hL]
    exact ha.left_echo_exact

/-- Follower-responder specialization used by every non-wrap retry edge. -/
theorem wallSweepPreCheckResetPathStall_source_noFire
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (halign : r.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.erase.core.leader = true ∨
      l.core.erase.core.reset_cmd = true)
    (hlFire : LeaderFireDisabled l.core.erase.core)
    (hrFollower : r.core.erase.core.leader = false)
    (hlBullet : l.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.erase.core.bullet = ⟨0, by omega⟩) :
    SourceCoveredNoFireOutput hpsi l r
      (wallSweepPreCheckResetPathStallTransition
        hpsi kappa tau l r) := by
  apply wallSweepPreCheckResetPathStall_source_noFire_zeroResponder
    hpsi l r hopen halign hsource hlFire (.inl hrFollower)
  · intro hleader
    have hbad : (false : Bool) = true := hrFollower.symm.trans hleader
    simp at hbad
  · exact hlBullet
  · exact hrBullet

/-! ## Leader-sink noninterference on follower responders -/

private theorem leaderSinkNormalTail_eq_of_after_responder_follower
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrFollower :
      (wallSweepPreCheckResetNormalAfterSuppress
        hpsi kappa l r).2.core.leader = false) :
    wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      wallSweepPreCheckResetNormalTail hpsi kappa l r := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  change authorizedPostSuppressLeaderSink hpsi after.1 after.2 =
    authorizedPostSuppress hpsi after.1 after.2
  exact authorizedPostSuppressLeaderSink_eq_of_responder_follower
    hpsi after.1 after.2 hrFollower

/-- On every source-covered edge whose responder is a follower, the complete
rooted leader-sink repair is exactly the established pre-CHECK-reset
transition. -/
theorem wallSweepPreCheckResetLeaderSinkAuthorized_eq_of_source_follower
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa l r =
      wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hpre := sourcePreStage_frame hpsi kappa l r halign hsource
  have hafterFollower : after.2.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_right_leader_of_pre
      hpsi kappa l r hpre).trans hrFollower
  have htail := leaderSinkNormalTail_eq_of_after_responder_follower
    hpsi kappa l r hafterFollower
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hnew :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  have hold := wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
    hpsi kappa l r hopen
  change wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born
      (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) at hnew
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) at hold
  exact hnew.trans ((congrArg (markLeaderBirth born) htail).trans hold.symm)

private theorem authorizedBounded_erase_injective :
    Function.Injective
      (@AuthorizedBoundedAgentState.erase psi kappa) := by
  intro a b h
  cases a with
  | mk ac ap =>
      cases b with
      | mk bc bp =>
          have hcoreErase : ac.erase = bc.erase :=
            congrArg (fun u : AuthorizedAgentState psi => u.core) h
          have hcore : ac = bc := by
            apply BoundedAgentState.eraseToDomain_bijective.1
            apply Subtype.ext
            exact hcoreErase
          have hpermit : ap = bp :=
            congrArg (fun u : AuthorizedAgentState psi => u.path0Crossed) h
          cases hcore
          cases hpermit
          rfl

/-- Exact source/follower agreement survives finite reification. -/
theorem wallSweepPreCheckResetLeaderSinkBounded_eq_of_source_follower
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hopen : AuthorizedPriorityOpen l.erase r.erase)
    (halign : r.erase.core.label =
      ⟨(l.erase.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.erase.core.leader = true ∨
      l.erase.core.reset_cmd = true)
    (hrFollower : r.erase.core.leader = false) :
    wallSweepPreCheckResetLeaderSinkBoundedTransition hpsi kappa l r =
      wallSweepPreCheckResetBoundedTransition hpsi kappa l r := by
  let qNew := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  let qOld := wallSweepPreCheckResetBoundedTransition hpsi kappa l r
  have hNew := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  have hOld := erase_wallSweepPreCheckResetBoundedTransition hpsi kappa l r
  have hAuth :=
    wallSweepPreCheckResetLeaderSinkAuthorized_eq_of_source_follower
      hpsi kappa l.erase r.erase hopen halign hsource hrFollower
  change (qNew.1.erase, qNew.2.erase) =
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.erase r.erase at hNew
  change (qOld.1.erase, qOld.2.erase) =
    wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.erase r.erase at hOld
  have hErase : (qNew.1.erase, qNew.2.erase) =
      (qOld.1.erase, qOld.2.erase) :=
    hNew.trans (hAuth.trans hOld.symm)
  apply Prod.ext
  · exact authorizedBounded_erase_injective (congrArg Prod.fst hErase)
  · exact authorizedBounded_erase_injective (congrArg Prod.snd hErase)

/-- Exact source/follower agreement survives path-stall expiry. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_eq_of_source_follower
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (halign : r.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.erase.core.leader = true ∨
      l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false) :
    wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r =
      wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r := by
  have hbase :=
    wallSweepPreCheckResetLeaderSinkBounded_eq_of_source_follower
      hpsi kappa l.core r.core hopen halign hsource hrFollower
  unfold wallSweepPreCheckResetLeaderSinkPathStallTransition
    wallSweepPreCheckResetPathStallTransition
  rw [hbase]

/-- Every nonclosing source-covered step of the rooted repair inherits the
complete established no-fire frame. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_source_noFire
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (halign : r.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.erase.core.leader = true ∨
      l.core.erase.core.reset_cmd = true)
    (hlFire : LeaderFireDisabled l.core.erase.core)
    (hrFollower : r.core.erase.core.leader = false)
    (hlBullet : l.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.erase.core.bullet = ⟨0, by omega⟩) :
    SourceCoveredNoFireOutput hpsi l r
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_of_source_follower
    hpsi kappa tau l r hopen halign hsource hrFollower]
  exact wallSweepPreCheckResetPathStall_source_noFire
    hpsi l r hopen halign hsource hlFire hrFollower hlBullet hrBullet

end PPLLWallSweepPreCheckNoFire
