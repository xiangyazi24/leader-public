import Leader.Wu.WallSweep.PreCheckResetContractsFirstBirth

/-!
# Pre-CHECK reset contracts: AuthorizedBullet

This module is one dependency-ordered part of the former contract monolith.
-/

namespace PPLLWallSweepPreCheckResetContracts

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLRepair PPLLWriteIncrementGate
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLTerminalEqualSupportRepair
  PPLLWallSweepNormalResetContract PPLLWallSweepEchoDrain
  PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthLeaderFrames
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoKernel
  PPLLNoCheckBirthConditionTwoPhysical

variable {psi kappa tau : Nat}

/-- Structured live-bullet rank comparison between two authorized pairs. -/
structure AuthorizedBulletTwoPairNonincrease
    (input output : AuthorizedAgentState psi ×
      AuthorizedAgentState psi) : Prop where
  le : bulletTwoPairMass output.1.core output.2.core ≤
    bulletTwoPairMass input.1.core input.2.core

/-- Structured strict live-bullet rank decrease between two authorized pairs. -/
structure AuthorizedBulletTwoPairDecrease
    (input output : AuthorizedAgentState psi ×
      AuthorizedAgentState psi) : Prop where
  lt : bulletTwoPairMass output.1.core output.2.core <
    bulletTwoPairMass input.1.core input.2.core
  inputInitiatorUnshielded : input.1.core.shield = false
  inputResponderLive : input.2.core.bullet = ⟨2, by omega⟩
  outputInitiatorFollower : output.1.core.leader = false
  outputResponderFollower : output.2.core.leader = false

/-- If the real-CHECK output has a follower initiator, the complete rooted
post-CHECK suffix cannot increase live-bullet mass.  Every stage before
Algorithm 15 frames bullet fields, and Algorithm 15 supplies the inequality. -/
theorem wallSweepLeaderSinkAfterCheckSuffix_left_follower_bulletTwoPair_le
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false) :
    let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
    bulletTwoPairMass out.1.core out.2.core ≤
      bulletTwoPairMass l.core r.core := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSig hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let raw := eliminateLeadersNoCollisionLeaderSink
    hpsi q2.1.core q2.2.core
  let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
  have h0Fields : authorizedBulletFieldPair q0 =
      authorizedBulletFieldPair (l, r) :=
    disappear_bulletFieldPair hpsi l.core r.core
  have h1Fields : authorizedBulletFieldPair q1 =
      authorizedBulletFieldPair q0 :=
    authorizedCompareSig_bulletFieldPair hpsi q0.1 q0.2
  have h2Fields : authorizedBulletFieldPair q2 =
      authorizedBulletFieldPair q1 :=
    authorizedSuppressSigResetKill_bulletFieldPair hpsi q1.1 q1.2
  have hq0Follower : q0.1.core.leader = false :=
    (authorizedDisappear_leaders_eq hpsi l r).1.trans hlFollower
  have hq1Follower : q1.1.core.leader = false :=
    (authorizedCompareSig_leaders_eq hpsi q0.1 q0.2).1.trans
      hq0Follower
  have hsuppressLeaders := suppressSigResetKill_leaders_eq
    hpsi q1.1.core q1.2.core
  have hq2Follower : q2.1.core.leader = false :=
    (authorizedReconcile_leaders_eq
      (suppressSigResetKill hpsi) q1.1 q1.2).1.trans
        (hsuppressLeaders.1.trans hq1Follower)
  have hkernel : bulletTwoPairMass raw.1 raw.2 ≤
      bulletTwoPairMass q2.1.core q2.2.core :=
    eliminateLeadersNoCollisionLeaderSink_left_follower_bulletTwoPair_le
      hpsi q2.1.core q2.2.core hq2Follower
  have houtFields : authorizedBulletFieldPair out =
      bulletFieldPair raw := by
    exact authorizedPostSuppressLeaderSink_bulletFieldPair
      hpsi q2.1 q2.2
  have houtL := congrArg (fun q => q.1.bullet) houtFields
  have houtR := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtL houtR
  dsimp only at houtL houtR
  have houtMass : bulletTwoPairMass out.1.core out.2.core =
      bulletTwoPairMass raw.1 raw.2 :=
    bulletTwoPairMass_eq_of_bullets_eq houtL houtR
  have hinputFields : authorizedBulletFieldPair q2 =
      authorizedBulletFieldPair (l, r) :=
    h2Fields.trans (h1Fields.trans h0Fields)
  have hinputL := congrArg (fun q => q.1.bullet) hinputFields
  have hinputR := congrArg (fun q => q.2.bullet) hinputFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hinputL hinputR
  dsimp only at hinputL hinputR
  have hinputMass : bulletTwoPairMass q2.1.core q2.2.core =
      bulletTwoPairMass l.core r.core :=
    bulletTwoPairMass_eq_of_bullets_eq hinputL hinputR
  calc
    bulletTwoPairMass out.1.core out.2.core =
        bulletTwoPairMass raw.1 raw.2 := houtMass
    _ ≤ bulletTwoPairMass q2.1.core q2.2.core := hkernel
    _ = bulletTwoPairMass l.core r.core := hinputMass

/-- On an already aligned follower/reset/follower edge, the complete rooted
post-CHECK suffix either delivers the positive absence signal or moves a
blocking dummy bullet one edge counterclockwise.  DISAPPEAR, COMPARE, repaired
Algorithm 14, authorization reconciliation, and gated WRITE only transport
the three bullet fields around the raw Algorithm-15 dichotomy. -/
theorem wallSweepLeaderSinkAfterCheckSuffix_signal_or_dummy_moves
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hrFollower : r.core.leader = false)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩)
    (hrNotLive : r.core.bullet ≠ ⟨2, by omega⟩) :
    let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
    out.2.core.signal_B = ⟨1, by omega⟩ ∨
      (r.core.bullet = ⟨1, by omega⟩ ∧
        out.1.core.bullet = ⟨1, by omega⟩ ∧
        out.2.core.bullet = ⟨0, by omega⟩) := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSig hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let raw := eliminateLeadersNoCollisionLeaderSink hpsi q2.1.core q2.2.core
  let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
  have h0Fields : authorizedBulletFieldPair q0 =
      authorizedBulletFieldPair (l, r) :=
    disappear_bulletFieldPair hpsi l.core r.core
  have h1Fields : authorizedBulletFieldPair q1 =
      authorizedBulletFieldPair q0 :=
    authorizedCompareSig_bulletFieldPair hpsi q0.1 q0.2
  have h2Fields : authorizedBulletFieldPair q2 =
      authorizedBulletFieldPair q1 :=
    authorizedSuppressSigResetKill_bulletFieldPair hpsi q1.1 q1.2
  have hinputFields : authorizedBulletFieldPair q2 =
      authorizedBulletFieldPair (l, r) :=
    h2Fields.trans (h1Fields.trans h0Fields)
  have hq2LeftSignal := congrArg (fun q => q.1.signal_B) hinputFields
  have hq2RightBullet := congrArg (fun q => q.2.bullet) hinputFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hq2LeftSignal hq2RightBullet
  dsimp only at hq2LeftSignal hq2RightBullet
  have h0Followers : q0.1.core.leader = false ∧
      q0.2.core.leader = false :=
    ⟨(authorizedDisappear_leaders_eq hpsi l r).1.trans hlFollower,
      (authorizedDisappear_leaders_eq hpsi l r).2.trans hrFollower⟩
  have h1Followers : q1.1.core.leader = false ∧
      q1.2.core.leader = false :=
    ⟨(authorizedCompareSig_leaders_eq hpsi q0.1 q0.2).1.trans
        h0Followers.1,
      (authorizedCompareSig_leaders_eq hpsi q0.1 q0.2).2.trans
        h0Followers.2⟩
  have hsuppressLeaders := suppressSigResetKill_leaders_eq
    hpsi q1.1.core q1.2.core
  have hq2Followers : q2.1.core.leader = false ∧
      q2.2.core.leader = false :=
    ⟨(authorizedReconcile_leaders_eq
        (suppressSigResetKill hpsi) q1.1 q1.2).1.trans
          (hsuppressLeaders.1.trans h1Followers.1),
      (authorizedReconcile_leaders_eq
        (suppressSigResetKill hpsi) q1.1 q1.2).2.trans
          (hsuppressLeaders.2.trans h1Followers.2)⟩
  have h0Labels := authorizedDisappear_labels_eq hpsi l r
  have h1LabelPair :=
    PPLLNoCheckBirthConditionTwoFrames.authorizedCompareSig_labels
      hpsi q0.1 q0.2
  have h1Labels : q1.1.core.label = q0.1.core.label ∧
      q1.2.core.label = q0.2.core.label :=
    ⟨congrArg Prod.fst h1LabelPair, congrArg Prod.snd h1LabelPair⟩
  have h2Labels : q2.1.core.label = l.core.label ∧
      q2.2.core.label = r.core.label :=
    ⟨(suppressSigResetKill_left_label_eq
        hpsi q1.1.core q1.2.core).trans (h1Labels.1.trans h0Labels.1),
      (suppressSigResetKill_right_label_eq
        hpsi q1.1.core q1.2.core).trans (h1Labels.2.trans h0Labels.2)⟩
  have hq2Align : q2.2.core.label =
      ⟨(q2.1.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    rw [h2Labels.1, h2Labels.2]
    exact halign
  have hq2NotLive : q2.2.core.bullet ≠ ⟨2, by omega⟩ := by
    intro hlive
    apply hrNotLive
    exact hq2RightBullet.symm.trans hlive
  have hkernel :=
    eliminateLeadersNoCollisionLeaderSink_aligned_signal_or_dummy_moves
      hpsi q2.1.core q2.2.core hq2Followers.1 hq2Followers.2
        hq2Align (hq2LeftSignal.trans hlSignal) hq2NotLive
  change raw.2.signal_B = ⟨1, by omega⟩ ∨
      (q2.2.core.bullet = ⟨1, by omega⟩ ∧
        raw.1.bullet = ⟨1, by omega⟩ ∧
        raw.2.bullet = ⟨0, by omega⟩) at hkernel
  have houtFields : authorizedBulletFieldPair out =
      bulletFieldPair raw :=
    authorizedPostSuppressLeaderSink_bulletFieldPair hpsi q2.1 q2.2
  have houtRightSignal := congrArg (fun q => q.2.signal_B) houtFields
  have houtLeftBullet := congrArg (fun q => q.1.bullet) houtFields
  have houtRightBullet := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtRightSignal houtLeftBullet houtRightBullet
  dsimp only at houtRightSignal houtLeftBullet houtRightBullet
  rcases hkernel with hsignal | hdummy
  · exact .inl (houtRightSignal.trans hsignal)
  · exact .inr ⟨hq2RightBullet.symm.trans hdummy.1,
      houtLeftBullet.trans hdummy.2.1,
      houtRightBullet.trans hdummy.2.2⟩

/-- Exact dummy-bullet transport through the complete rooted post-CHECK
suffix.  On an aligned follower edge without a live responder bullet, a
responder dummy moves to the initiator and the responder is cleared; a zero
responder leaves the initiator bullet unchanged.  The other suffix stages
only frame these bullet fields. -/
theorem wallSweepLeaderSinkAfterCheckSuffix_aligned_follower_bullets
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hrFollower : r.core.leader = false)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hrNotLive : r.core.bullet ≠ ⟨2, by omega⟩) :
    let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
    out.1.core.bullet =
        (if r.core.bullet = ⟨1, by omega⟩ then ⟨1, by omega⟩
          else l.core.bullet) ∧
      out.2.core.bullet = ⟨0, by omega⟩ := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSig hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let raw := eliminateLeadersNoCollisionLeaderSink hpsi q2.1.core q2.2.core
  let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
  have h0Fields : authorizedBulletFieldPair q0 =
      authorizedBulletFieldPair (l, r) :=
    disappear_bulletFieldPair hpsi l.core r.core
  have h1Fields : authorizedBulletFieldPair q1 =
      authorizedBulletFieldPair q0 :=
    authorizedCompareSig_bulletFieldPair hpsi q0.1 q0.2
  have h2Fields : authorizedBulletFieldPair q2 =
      authorizedBulletFieldPair q1 :=
    authorizedSuppressSigResetKill_bulletFieldPair hpsi q1.1 q1.2
  have hinputFields : authorizedBulletFieldPair q2 =
      authorizedBulletFieldPair (l, r) :=
    h2Fields.trans (h1Fields.trans h0Fields)
  have hq2LeftBullet := congrArg (fun q => q.1.bullet) hinputFields
  have hq2RightBullet := congrArg (fun q => q.2.bullet) hinputFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hq2LeftBullet hq2RightBullet
  dsimp only at hq2LeftBullet hq2RightBullet
  have hq2Followers : q2.1.core.leader = false ∧
      q2.2.core.leader = false := by
    have h0Followers : q0.1.core.leader = false ∧
        q0.2.core.leader = false :=
      ⟨(authorizedDisappear_leaders_eq hpsi l r).1.trans hlFollower,
        (authorizedDisappear_leaders_eq hpsi l r).2.trans hrFollower⟩
    have h1Followers : q1.1.core.leader = false ∧
        q1.2.core.leader = false :=
      ⟨(authorizedCompareSig_leaders_eq hpsi q0.1 q0.2).1.trans
          h0Followers.1,
        (authorizedCompareSig_leaders_eq hpsi q0.1 q0.2).2.trans
          h0Followers.2⟩
    have hsuppressLeaders := suppressSigResetKill_leaders_eq
      hpsi q1.1.core q1.2.core
    exact
      ⟨(authorizedReconcile_leaders_eq
          (suppressSigResetKill hpsi) q1.1 q1.2).1.trans
            (hsuppressLeaders.1.trans h1Followers.1),
        (authorizedReconcile_leaders_eq
          (suppressSigResetKill hpsi) q1.1 q1.2).2.trans
            (hsuppressLeaders.2.trans h1Followers.2)⟩
  have h0Labels := authorizedDisappear_labels_eq hpsi l r
  have h1LabelPair :=
    PPLLNoCheckBirthConditionTwoFrames.authorizedCompareSig_labels
      hpsi q0.1 q0.2
  have h1Labels : q1.1.core.label = q0.1.core.label ∧
      q1.2.core.label = q0.2.core.label :=
    ⟨congrArg Prod.fst h1LabelPair, congrArg Prod.snd h1LabelPair⟩
  have h2Labels : q2.1.core.label = l.core.label ∧
      q2.2.core.label = r.core.label :=
    ⟨(suppressSigResetKill_left_label_eq
        hpsi q1.1.core q1.2.core).trans (h1Labels.1.trans h0Labels.1),
      (suppressSigResetKill_right_label_eq
        hpsi q1.1.core q1.2.core).trans (h1Labels.2.trans h0Labels.2)⟩
  have hq2Align : q2.2.core.label =
      ⟨(q2.1.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    rw [h2Labels.1, h2Labels.2]
    exact halign
  have hq2NotLive : q2.2.core.bullet ≠ ⟨2, by omega⟩ := by
    intro hlive
    apply hrNotLive
    exact hq2RightBullet.symm.trans hlive
  have hkernel :=
    eliminateLeadersNoCollisionLeaderSink_aligned_follower_bullets
      hpsi q2.1.core q2.2.core hq2Followers.1 hq2Followers.2
        hq2Align hq2NotLive
  change raw.1.bullet =
        (if q2.2.core.bullet = ⟨1, by omega⟩ then ⟨1, by omega⟩
          else q2.1.core.bullet) ∧
      raw.2.bullet = ⟨0, by omega⟩ at hkernel
  have houtFields : authorizedBulletFieldPair out =
      bulletFieldPair raw :=
    authorizedPostSuppressLeaderSink_bulletFieldPair hpsi q2.1 q2.2
  have houtLeftBullet := congrArg (fun q => q.1.bullet) houtFields
  have houtRightBullet := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtLeftBullet houtRightBullet
  dsimp only at houtLeftBullet houtRightBullet
  constructor
  · rw [houtLeftBullet, hkernel.1, hq2LeftBullet, hq2RightBullet]
  · exact houtRightBullet.trans hkernel.2

/-- Exact live-bullet transport through the complete rooted post-CHECK
suffix.  On an aligned follower edge, a live responder bullet moves to the
initiator and the responder is cleared; the comparison and authorization
stages frame the two bullet fields. -/
theorem wallSweepLeaderSinkAfterCheckSuffix_aligned_follower_live_bullets
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hrFollower : r.core.leader = false)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hrLive : r.core.bullet = ⟨2, by omega⟩) :
    let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
    out.1.core.bullet = ⟨2, by omega⟩ ∧
      out.2.core.bullet = ⟨0, by omega⟩ := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSig hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let raw := eliminateLeadersNoCollisionLeaderSink hpsi q2.1.core q2.2.core
  let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
  have h0Fields : authorizedBulletFieldPair q0 =
      authorizedBulletFieldPair (l, r) :=
    disappear_bulletFieldPair hpsi l.core r.core
  have h1Fields : authorizedBulletFieldPair q1 =
      authorizedBulletFieldPair q0 :=
    authorizedCompareSig_bulletFieldPair hpsi q0.1 q0.2
  have h2Fields : authorizedBulletFieldPair q2 =
      authorizedBulletFieldPair q1 :=
    authorizedSuppressSigResetKill_bulletFieldPair hpsi q1.1 q1.2
  have hinputFields : authorizedBulletFieldPair q2 =
      authorizedBulletFieldPair (l, r) :=
    h2Fields.trans (h1Fields.trans h0Fields)
  have hq2RightBullet := congrArg (fun q => q.2.bullet) hinputFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hq2RightBullet
  dsimp only at hq2RightBullet
  have hq2Followers : q2.1.core.leader = false ∧
      q2.2.core.leader = false := by
    have h0Followers : q0.1.core.leader = false ∧
        q0.2.core.leader = false :=
      ⟨(authorizedDisappear_leaders_eq hpsi l r).1.trans hlFollower,
        (authorizedDisappear_leaders_eq hpsi l r).2.trans hrFollower⟩
    have h1Followers : q1.1.core.leader = false ∧
        q1.2.core.leader = false :=
      ⟨(authorizedCompareSig_leaders_eq hpsi q0.1 q0.2).1.trans
          h0Followers.1,
        (authorizedCompareSig_leaders_eq hpsi q0.1 q0.2).2.trans
          h0Followers.2⟩
    have hsuppressLeaders := suppressSigResetKill_leaders_eq
      hpsi q1.1.core q1.2.core
    exact
      ⟨(authorizedReconcile_leaders_eq
          (suppressSigResetKill hpsi) q1.1 q1.2).1.trans
            (hsuppressLeaders.1.trans h1Followers.1),
        (authorizedReconcile_leaders_eq
          (suppressSigResetKill hpsi) q1.1 q1.2).2.trans
            (hsuppressLeaders.2.trans h1Followers.2)⟩
  have h0Labels := authorizedDisappear_labels_eq hpsi l r
  have h1LabelPair :=
    PPLLNoCheckBirthConditionTwoFrames.authorizedCompareSig_labels
      hpsi q0.1 q0.2
  have h1Labels : q1.1.core.label = q0.1.core.label ∧
      q1.2.core.label = q0.2.core.label :=
    ⟨congrArg Prod.fst h1LabelPair, congrArg Prod.snd h1LabelPair⟩
  have h2Labels : q2.1.core.label = l.core.label ∧
      q2.2.core.label = r.core.label :=
    ⟨(suppressSigResetKill_left_label_eq
        hpsi q1.1.core q1.2.core).trans (h1Labels.1.trans h0Labels.1),
      (suppressSigResetKill_right_label_eq
        hpsi q1.1.core q1.2.core).trans (h1Labels.2.trans h0Labels.2)⟩
  have hq2Align : q2.2.core.label =
      ⟨(q2.1.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    rw [h2Labels.1, h2Labels.2]
    exact halign
  have hq2Live : q2.2.core.bullet = ⟨2, by omega⟩ :=
    hq2RightBullet.trans hrLive
  have hkernel :=
    eliminateLeadersNoCollisionLeaderSink_aligned_follower_live_bullets
      hpsi q2.1.core q2.2.core hq2Followers.1 hq2Followers.2
        hq2Align hq2Live
  change raw.1.bullet = ⟨2, by omega⟩ ∧
      raw.2.bullet = ⟨0, by omega⟩ at hkernel
  have houtFields : authorizedBulletFieldPair out =
      bulletFieldPair raw :=
    authorizedPostSuppressLeaderSink_bulletFieldPair hpsi q2.1 q2.2
  have houtLeftBullet := congrArg (fun q => q.1.bullet) houtFields
  have houtRightBullet := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtLeftBullet houtRightBullet
  dsimp only at houtLeftBullet houtRightBullet
  exact ⟨houtLeftBullet.trans hkernel.1,
    houtRightBullet.trans hkernel.2⟩

/-- Priority-open branch selection, birth marking, and gated WRITE expose the
same bullet fields as the rooted Algorithm-15 output. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_bulletFieldPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
    let raw := eliminateLeadersNoCollisionLeaderSink
      hpsi after.1.core after.2.core
    let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    authorizedBulletFieldPair out = bulletFieldPair raw := by
  let after : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let raw : AgentState psi × AgentState psi :=
    eliminateLeadersNoCollisionLeaderSink
      hpsi after.1.core after.2.core
  let tail : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa l r
  have htailFields : authorizedBulletFieldPair tail =
      bulletFieldPair raw :=
    authorizedPostSuppressLeaderSink_bulletFieldPair
      hpsi after.1 after.2
  have hstage :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  have houtFields : authorizedBulletFieldPair out =
      authorizedBulletFieldPair tail :=
    (congrArg authorizedBulletFieldPair hstage).trans
      (markLeaderBirth_bulletFieldPair _ tail)
  exact houtFields.trans htailFields

/-- A live bullet at the responder of the complete priority-open rooted
transition was already live at that responder before the interaction.  In
particular, a leader-source reseed cannot create a new live bullet away from
the source leader. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_live_origin
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (houtLive :
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r).2.core.bullet = ⟨2, by omega⟩) :
    r.core.bullet = ⟨2, by omega⟩ := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let raw := eliminateLeadersNoCollisionLeaderSink
    hpsi after.1.core after.2.core
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have houtFields :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_bulletFieldPair
      hpsi kappa l r hopen
  change authorizedBulletFieldPair out = bulletFieldPair raw at houtFields
  have hrightOut := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hrightOut
  dsimp only at hrightOut
  have hrawLive : raw.2.bullet = ⟨2, by omega⟩ :=
    hrightOut.symm.trans houtLive
  have hsinkBullets := eliminateLeadersNoCollisionLeaderSink_bullets_eq
    hpsi after.1.core after.2.core
  have hnormalLive :
      (eliminateLeadersNoCollision hpsi
        after.1.core after.2.core).2.bullet = ⟨2, by omega⟩ :=
    hsinkBullets.2.symm.trans hrawLive
  have hafterLive :=
    (noCollision_right_live_origin
      hpsi after.1.core after.2.core hnormalLive).1
  have hinputFields :=
    wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair
      hpsi kappa l r
  change authorizedBulletFieldPair after =
    authorizedBulletFieldPair (l, r) at hinputFields
  have hrightInput := congrArg (fun q => q.2.bullet) hinputFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hrightInput
  dsimp only at hrightInput
  exact hrightInput.symm.trans hafterLive

/-- **Pair-level, source-free.**  A label-zero responder leader that already
carries the absence signal stays a leader at label zero and loses its shield
under the complete priority-open rooted leader-sink transition.  The initiator
is entirely unconstrained: no leader, reset, barrier, bullet, echo or
neutrality premise is consumed.  This produces no live bullet, delivers none,
and deletes no leader. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_zero_unshield
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hrSignal : r.core.signal_B = ⟨1, by omega⟩) :
    let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    out.2.core.leader = true ∧
      out.2.core.label = ⟨0, hpsi⟩ ∧
      out.2.core.shield = false := by
  dsimp only
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let raw := eliminateLeadersNoCollisionLeaderSink
    hpsi after.1.core after.2.core
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have hafterAnchor : ResponderZeroAnchor hpsi after.2.core :=
    wallSweepPreCheckResetNormalAfterSuppress_responder_zero_anchor
      hpsi kappa l r ⟨hrLeader, hrZero⟩
  have hinputFields :=
    wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair hpsi kappa l r
  change authorizedBulletFieldPair after =
    authorizedBulletFieldPair (l, r) at hinputFields
  have hafterSignalEq := congrArg (fun q => q.2.signal_B) hinputFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState
    at hafterSignalEq
  dsimp only at hafterSignalEq
  have hafterSignal : after.2.core.signal_B = ⟨1, by omega⟩ :=
    hafterSignalEq.trans hrSignal
  have hrawUnshield :=
    eliminateLeadersNoCollisionLeaderSink_responder_signal_one_unshielded
      hpsi after.1.core after.2.core hafterAnchor.1 hafterSignal
  change raw.2.leader = true ∧ raw.2.shield = false at hrawUnshield
  have houtFields :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_bulletFieldPair
      hpsi kappa l r hopen
  change authorizedBulletFieldPair out = bulletFieldPair raw at houtFields
  have houtShield := congrArg (fun q => q.2.shield) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState
    at houtShield
  dsimp only at houtShield
  have htailAnchor : authorizedResponderZeroAnchor hpsi tail :=
    authorizedPostSuppressLeaderSink_responder_zero_anchor
      hpsi after.1 after.2 hafterAnchor
  have hstage :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  have hstageLeader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) hstage
  have hstageLabel := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.label) hstage
  have hmarkLeaders := markLeaderBirth_leaders_eq
    (leaderBirthBeforeOrAtCheck
      (normalizeDeletion l) (normalizeDeletion r)
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))) tail
  have hmarkLabels := markLeaderBirth_labels_eq
    (leaderBirthBeforeOrAtCheck
      (normalizeDeletion l) (normalizeDeletion r)
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))) tail
  exact ⟨hstageLeader.trans (hmarkLeaders.2.trans htailAnchor.1),
    hstageLabel.trans (hmarkLabels.2.trans htailAnchor.2),
    houtShield.trans hrawUnshield.2⟩

/-- **Pair-level, source-free.**  Bounded reification and deletion-priority
expiry frame leader, host label and shield exactly, so the source-free
unshielding contract survives to the physical path-stall transition. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_zero_unshield
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hrLeader : r.core.erase.core.leader = true)
    (hrZero : r.core.erase.core.label = ⟨0, hpsi⟩)
    (hrSignal : r.core.erase.core.signal_B = ⟨1, by omega⟩) :
    let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    out.2.core.erase.core.leader = true ∧
      out.2.core.erase.core.label = ⟨0, hpsi⟩ ∧
      out.2.core.erase.core.shield = false := by
  dsimp only
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_zero_unshield
      hpsi kappa l.core.erase r.core.erase hopen hrLeader hrZero hrSignal
  have he := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hR := congrArg Prod.snd he
  change bounded.2.erase =
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hf := deletionPriorityExpireOne_path_frame r rBase
  have hs := deletionPriorityExpireOne_shield_frame r rBase
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  refine ⟨hf.2.1.trans ?_, hf.2.2.1.trans ?_, hs.trans ?_⟩
  · change bounded.2.erase.core.leader = true
    rw [hR]
    exact ha.1
  · change bounded.2.erase.core.label = ⟨0, hpsi⟩
    rw [hR]
    exact ha.2.1
  · change bounded.2.erase.core.shield = false
    rw [hR]
    exact ha.2.2

/-- On a priority-open source-covered edge, the complete authorized
transition leaves the follower responder a follower. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_follower_of_initiator_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlLeader : l.core.leader = true)
    (hrFollower : r.core.leader = false) :
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r).2.core.leader = false := by
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have hstage :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  have hstageRight := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) hstage
  have hmark := markLeaderBirth_leaders_eq
    (leaderBirthBeforeOrAtCheck
      (normalizeDeletion l) (normalizeDeletion r)
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))) tail
  have htail : tail.2.core.leader = false :=
    wallSweepPreCheckResetLeaderSinkNormalTail_responder_follower_of_initiator_leader
      hpsi kappa l r hlLeader hrFollower
  exact hstageRight.trans (hmark.2.trans htail)

/-- A priority-open rooted interaction initiated by an existing leader clears
the initiator's absence signal, regardless of whether the input signal was
zero or one. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_left_signal_zero_of_left_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlLeader : l.core.leader = true) :
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r).1.core.signal_B = ⟨0, by omega⟩ := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let raw := eliminateLeadersNoCollisionLeaderSink
    hpsi after.1.core after.2.core
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have hafterLeader : after.1.core.leader = true :=
    (wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r).trans hlLeader
  have hkernel : raw.1.signal_B = ⟨0, by omega⟩ :=
    noCollisionLeaderSink_left_signal_zero_of_leader
      hpsi after.1.core after.2.core hafterLeader
  have houtFields :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_bulletFieldPair
      hpsi kappa l r hopen
  change authorizedBulletFieldPair out = bulletFieldPair raw at houtFields
  have houtSignal := congrArg (fun q => q.1.signal_B) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtSignal
  dsimp only at houtSignal
  exact houtSignal.trans hkernel

/-- A surviving leader source writes the positive absence signal at its
follower responder whenever that responder does not carry a live bullet.
The corrected pre-CHECK prefix frames bullet fields and leader bits; the
rooted Algorithm-15 suffix supplies the signal write, and gated WRITE frames
the resulting bullet fields. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_right_signal_one_of_left_leader_not_live
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlLeader : l.core.leader = true)
    (hrFollower : r.core.leader = false)
    (hrNotLive : r.core.bullet ≠ ⟨2, by omega⟩) :
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r).2.core.signal_B = ⟨1, by omega⟩ := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let raw := eliminateLeadersNoCollisionLeaderSink
    hpsi after.1.core after.2.core
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have hafterLeft : after.1.core.leader = true :=
    (wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r).trans hlLeader
  have hafterRight : after.2.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_responder_leader_eq_of_initiator_leader
      hpsi kappa l r hlLeader).trans hrFollower
  have hinputFields :=
    wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair
      hpsi kappa l r
  change authorizedBulletFieldPair after =
    authorizedBulletFieldPair (l, r) at hinputFields
  have hrightInput := congrArg (fun q => q.2.bullet) hinputFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hrightInput
  dsimp only at hrightInput
  have hafterNotLive : after.2.core.bullet ≠ ⟨2, by omega⟩ := by
    intro hlive
    exact hrNotLive (hrightInput.symm.trans hlive)
  have hkernelBase :=
    eliminateLeadersNoCollision_right_signal_of_left_leader_not_live
      hpsi after.1.core after.2.core hafterLeft hafterRight hafterNotLive
  have hkernelEq :=
    eliminateLeadersNoCollisionLeaderSink_eq_of_responder_follower
      hpsi after.1.core after.2.core hafterRight
  have hkernel : raw.2.signal_B = ⟨1, by omega⟩ := by
    change (eliminateLeadersNoCollisionLeaderSink
      hpsi after.1.core after.2.core).2.signal_B = ⟨1, by omega⟩
    rw [hkernelEq]
    exact hkernelBase
  have houtFields :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_bulletFieldPair
      hpsi kappa l r hopen
  change authorizedBulletFieldPair out = bulletFieldPair raw at houtFields
  have houtRightSignal := congrArg (fun q => q.2.signal_B) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtRightSignal
  dsimp only at houtRightSignal
  exact houtRightSignal.trans hkernel


end PPLLWallSweepPreCheckResetContracts
