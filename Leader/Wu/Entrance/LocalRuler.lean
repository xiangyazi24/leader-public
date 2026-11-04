import Leader.Wu.Birth.CheckPermitRepairLeaf
import Leader.Wu.Birth.ShortDoneTerminalDeletionRank
import Leader.Wu.Splice.OrdinaryHostLabelFrame
import Leader.Wu.Entrance.LocalReverseFill

/-!
# B6 local ruler for the R1 host

This file isolates the R1-specific physical leaves needed by the local-ruler
part of the S-keep entrance.

Compiled declarations below contain no `sorry`.  Statements still requiring a
new proof are written only inside `PLAN` block comments.

The intended workspace is a `B6LocalReverseFill.Interval`.  Offset zero is the
unused leftmost service cell.  The ruler chain is required only on offsets
1,...,W-1.  Prepared-active interior victims are served as responders by their
left predecessor; hence every requested deletion edge stays internal.
-/

set_option autoImplicit false
set_option Elab.async false

namespace B6LocalRuler

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
open PPLLRepair PPLLDomain ExpiringK2Projection K2BirthLeaderNormalize K2BirthDispatcher
  BirthShortDoneTerminalHost
open BirthSigMoveDisposalRepair
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
open BirthShortDoneTerminalDeletionRank
open BirthShortDoneTerminalOrdinaryLabelR1
open B6LocalReverseFill B6WindowLocality

variable {n psi kappa tau width : Nat}

abbrev Config (n psi kappa tau : Nat) :=
  BirthCheckPermitRepairLeaf.FC n psi kappa tau

/-- The label demanded immediately to the right of `a`. -/
def nextLabel (hpsi : 0 < psi) (a : Fin psi) : Fin psi :=
  ⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩

/-- A completed physical leader occurs somewhere in the workspace. -/
def WorkspaceLeader (ring : DirectedRing n)
    (I : B6LocalReverseFill.Interval ring)
    (C : Config n psi kappa tau) : Prop :=
  ∃ k : Nat, k < I.size ∧
    (C (cell ring I.first k)).core.core.leader = true

/-- Consecutive successor labels on the workspace with offset zero omitted. -/
def TailSuccessorChain (hpsi : 0 < psi) (ring : DirectedRing n)
    (I : B6LocalReverseFill.Interval ring)
    (C : Config n psi kappa tau) : Prop :=
  ∀ k : Nat, 1 ≤ k → k + 1 < I.size →
    (C (cell ring I.first (k + 1))).core.core.label =
      nextLabel hpsi (C (cell ring I.first k)).core.core.label

/-- The local ruler has either stopped early at a leader or completed its tail. -/
def RulerSuccess (hpsi : 0 < psi) (ring : DirectedRing n)
    (I : B6LocalReverseFill.Interval ring)
    (C : Config n psi kappa tau) : Prop :=
  WorkspaceLeader ring I C ∨ TailSuccessorChain hpsi ring I C

/-- Deliberately loose local word budget. -/
def rulerBudget (W : Nat) : Nat := (W + 1) * W + W

/-- Main-path population on the ruler tail, excluding the sacrificial offset 0.
This is the well-founded rank intended for the local deletion recursion. -/
def interiorPathCount (ring : DirectedRing n)
    (I : B6LocalReverseFill.Interval ring)
    (C : Config n psi kappa tau) : Nat :=
  (List.range (I.size - 1)).foldl
    (fun acc k => acc +
      PPLLWallSweepFiniteCleanup.comparisonPathMass
        (C (cell ring I.first (k + 1)))) 0

/-- Every edge between consecutive workspace offsets is an internal R1 edge. -/
theorem internal_cell_edge (ring : DirectedRing n)
    (I : B6LocalReverseFill.Interval ring) (k : Nat)
    (hk : k + 1 < I.size) :
    B6LocalReverseFill.internal I (cell ring I.first k) := by
  apply (B6LocalReverseFill.internal_iff I _).2
  constructor
  · exact B6LocalReverseFill.support_cell I (by omega)
  · rw [BirthCheckChainR1Ring.right_cell]
    exact B6LocalReverseFill.support_cell I hk

/-- Ruler success depends only on complete records in the workspace. -/
theorem rulerSuccess_of_agree
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (I : B6LocalReverseFill.Interval ring)
    (C D : Config n psi kappa tau)
    (hCD : ∀ i, B6LocalReverseFill.support I i = true → C i = D i)
    (h : RulerSuccess hpsi ring I C) :
    RulerSuccess hpsi ring I D := by
  rcases h with hleader | hchain
  · left
    rcases hleader with ⟨k, hk, hlead⟩
    refine ⟨k, hk, ?_⟩
    rw [← hCD (cell ring I.first k)
      (B6LocalReverseFill.support_cell I hk)]
    exact hlead
  · right
    intro k hk1 hk2
    have hk : k < I.size := by omega
    rw [← hCD (cell ring I.first (k + 1))
        (B6LocalReverseFill.support_cell I hk2),
      ← hCD (cell ring I.first k)
        (B6LocalReverseFill.support_cell I hk)]
    exact hchain k hk1 hk2

/-! ## R1 responder-deletion branch -/

/-- At the R1-only CHECK repair point, even the exceptional E case changes no
physical core field; in particular it changes no label. -/
theorem permitFix_label (c : AuthorizedAgentState psi) :
    (BirthCheckPermitRepair.permitFix c).core.label = c.core.label := by
  rw [BirthCheckPermitRepair.permitFix_core]

/-- Before finite reification, the prepared responder-deletion branch is
literally the same branch in R1 and in the TerminalHost. -/
private theorem r1_authorized_eq_host_of_responder_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AuthorizedAgentState psi)
    (hdel : deletionActive (normalizeDeletion r) = true) :
    BirthCheckPermitRepair.authorized hpsi hwidth hle kappa l r =
      BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
        hpsi hwidth hle kappa l r := by
  unfold BirthCheckPermitRepair.authorized
    BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
  dsimp only
  rw [hdel]
  simp

/-- The same equality survives exact bounded reification. -/
private theorem r1_bounded_eq_host_of_responder_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hdel : deletionActive (normalizeDeletion r.erase) = true) :
    BirthCheckPermitRepair.bounded hpsi hwidth hle l r =
      BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
        hpsi hwidth hle l r := by
  unfold BirthCheckPermitRepair.bounded
    BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
  dsimp only
  exact BirthCheckPermitRepairAgree.reify_congr
    (r1_authorized_eq_host_of_responder_delete
      (kappa := kappa) hpsi hwidth hle l.erase r.erase hdel)
    (BirthCheckPermitRepair.authorized_domain hpsi hwidth hle l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain)
    (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth_domain
      hpsi hwidth hle l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain)

/-- The equality survives the two role-local expiry calls. -/
private theorem r1_expiring_eq_host_of_responder_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hdel : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true) :
    BirthCheckPermitRepair.expiring hpsi hwidth hle l r =
      BirthShortDoneTerminalHost.doneMetadataEntryWidth
        hpsi hwidth hle l r := by
  have hb :
      BirthCheckPermitRepair.bounded hpsi hwidth hle
          (prepareExpiringDisposal hpsi l).core (prepareExpiringDisposal hpsi r).core =
        BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
          hpsi hwidth hle (prepareExpiringDisposal hpsi l).core
          (prepareExpiringDisposal hpsi r).core :=
    r1_bounded_eq_host_of_responder_delete
      hpsi hwidth hle (prepareExpiringDisposal hpsi l).core
      (prepareExpiringDisposal hpsi r).core hdel
  unfold BirthCheckPermitRepair.expiring
    BirthShortDoneTerminalHost.doneMetadataEntryWidth
  simp only [hb]

/-- Hence a prepared responder deletion makes the entire R1 physical row
identical to the current TerminalHost physical row. -/
theorem r1_row_eq_host_of_responder_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hdel : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true) :
    BirthCheckPermitRepair.row hpsi hwidth hle l r =
      BirthShortDoneTerminalHost.row hpsi hwidth hle l r := by
  have he := r1_expiring_eq_host_of_responder_delete
    hpsi hwidth hle l r hdel
  unfold BirthCheckPermitRepair.row
    BirthShortDoneTerminalHost.row BirthShortDoneTerminalHost.metadata
  rw [he]

/-- R1 responder-deletion cannot manufacture a main path: the left path is
retained or cleared and the active responder path is cleared. -/
theorem r1_prepared_responder_delete_paths
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hactive : CurrentPreparedDeletionActive hpsi r) :
    let q := BirthCheckPermitRepair.row hpsi hwidth hle l r
    (q.1.core.erase.core.path = l.core.erase.core.path ∨
      q.1.core.erase.core.path = .bot) ∧
      q.2.core.erase.core.path = .bot := by
  have hdel : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true := by
    simpa [CurrentPreparedDeletionActive] using hactive
  dsimp only
  rw [r1_row_eq_host_of_responder_delete hpsi hwidth hle l r hdel]
  exact row_prepared_responder_delete_paths
    hpsi hwidth hle l r hactive

/-- In particular the existing two-endpoint occupied-path rank strictly
contracts on every prepared-active responder service. -/
theorem r1_prepared_responder_delete_contract
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hactive : CurrentPreparedDeletionActive hpsi r) :
    let q := BirthCheckPermitRepair.row hpsi hwidth hle l r
    comparisonPathMass q.1 + comparisonPathMass q.2 <
        comparisonPathMass l + comparisonPathMass r ∧
      comparisonPathMass q.1 ≤ comparisonPathMass l ∧
      comparisonPathMass q.2 < comparisonPathMass r := by
  have hdel : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true := by
    simpa [CurrentPreparedDeletionActive] using hactive
  dsimp only
  rw [r1_row_eq_host_of_responder_delete hpsi hwidth hle l r hdel]
  exact row_prepared_responder_delete_contract
    hpsi hwidth hle l r hactive

/-- On the responder-deletion branch the pre-normalization metadata leader bits
are exactly the input leader bits.  This is the responder-only specialization
of the source argument already used privately in `B9SpliceV8DeletionCase`. -/
private theorem host_responder_delete_metadata_leaders
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hdel : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true) :
    let q := BirthShortDoneTerminalHost.doneMetadataEntryWidth
      hpsi hwidth hle l r
    q.1.core.core.leader = l.core.core.leader ∧
      q.2.core.core.leader = r.core.core.leader := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let q := BirthShortDoneTerminalHost.doneMetadataEntryWidth
    hpsi hwidth hle l r
  have hr0 : deletionActive (normalizeDeletion pr.core.erase) = true := by
    simpa only [pr] using hdel
  have hauth :
      K2BirthDispatcher.authSignalPair
          (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
            hpsi hwidth hle kappa pl.core.erase pr.core.erase) =
        K2BirthDispatcher.authSignalPair (pl.core.erase, pr.core.erase) := by
    unfold BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
    dsimp only
    rw [hr0]
    exact (K2BirthDispatcher.eliminate_signal hpsi
      (normalizeDeletion pl.core.erase) (normalizeDeletion pr.core.erase)).trans
      (K2BirthDispatcher.normalize_pair_signal pl.core.erase pr.core.erase)
  have hentry :=
    BirthShortDoneTerminalConsumer.doneMetadataEntryWidth_observation
      hpsi hwidth hle l r
  have hsignal :
      (ExpiringK2Projection.observeCell q.1,
        ExpiringK2Projection.observeCell q.2) =
      (ExpiringK2Projection.observeCell l,
        ExpiringK2Projection.observeCell r) := by
    calc
      (ExpiringK2Projection.observeCell q.1,
          ExpiringK2Projection.observeCell q.2) =
          K2BirthDispatcher.authSignalPair
            (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
              hpsi hwidth hle kappa pl.core.erase pr.core.erase) := by
        simpa only [q, pl, pr] using hentry
      _ = K2BirthDispatcher.authSignalPair (pl.core.erase, pr.core.erase) := hauth
      _ = (ExpiringK2Projection.observeCell pl,
          ExpiringK2Projection.observeCell pr) := rfl
      _ = (ExpiringK2Projection.observeCell l,
          ExpiringK2Projection.observeCell r) :=
        Prod.ext (K2BirthDispatcher.prepareExpiring_signal hpsi l)
          (K2BirthDispatcher.prepareExpiring_signal hpsi r)
  have hL := congrArg
    (fun z : AgentState 1 × AgentState 1 => z.1.leader) hsignal
  have hR := congrArg
    (fun z : AgentState 1 × AgentState 1 => z.2.leader) hsignal
  change q.1.core.core.leader = l.core.core.leader at hL
  change q.2.core.core.leader = r.core.core.leader at hR
  exact ⟨hL, hR⟩

/-- Sound final-row deletion label frame for the ruler induction.  The follower
hypotheses are essential: a leader can be relabelled to zero by normalization. -/
theorem r1_prepared_responder_delete_labels_of_followers
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hactive : CurrentPreparedDeletionActive hpsi r) :
    let q := BirthCheckPermitRepair.row hpsi hwidth hle l r
    q.1.core.core.label = l.core.core.label ∧
      q.2.core.core.label = r.core.core.label := by
  have hdel : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true := by
    simpa [CurrentPreparedDeletionActive] using hactive
  let d := BirthShortDoneTerminalHost.doneMetadataEntryWidth
    hpsi hwidth hle l r
  have hdLeaders := host_responder_delete_metadata_leaders
    (kappa := kappa) (tau := tau) hpsi hwidth hle l r hdel
  change d.1.core.core.leader = l.core.core.leader ∧
    d.2.core.core.leader = r.core.core.leader at hdLeaders
  have hdLabels := B9SpliceV8LabelFrame.host_responder_deletion_label_frame
    (kappa := kappa) (tau := tau) hpsi hwidth hle l r hdel
  change d.1.core.core.label = l.core.core.label ∧
    d.2.core.core.label = r.core.core.label at hdLabels
  have hrow := B9SpliceV8LabelFrame.hostRow_labels_metadata
    (kappa := kappa) (tau := tau) hpsi hwidth hle l r
  have heq := r1_row_eq_host_of_responder_delete
    hpsi hwidth hle l r hdel
  dsimp only
  rw [heq]
  constructor
  · calc
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1.core.core.label =
          (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1.core.core.label :=
        hrow.1
      _ = d.1.core.core.label := by
        change (K2BirthLeaderNormalize.normalizeLeader hpsi d.1).core.core.label =
          d.1.core.core.label
        simp [K2BirthLeaderNormalize.normalizeLeader, hdLeaders.1.trans hl]
      _ = l.core.core.label := hdLabels.1
  · calc
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.label =
          (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2.core.core.label :=
        hrow.2
      _ = d.2.core.core.label := by
        change (K2BirthLeaderNormalize.normalizeLeader hpsi d.2).core.core.label =
          d.2.core.core.label
        simp [K2BirthLeaderNormalize.normalizeLeader, hdLeaders.2.trans hr]
      _ = r.core.core.label := hdLabels.2

/-! ## Ordinary R1 rows off the exceptional equal class -/

/-- Off E, the full R1 row is the TerminalHost row, so a false current birth
event gives the exact P-prime label refinement. -/
theorem r1_ordinary_labels_of_no_equal_no_birth
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hopen : PreparedOrdinaryOpen hpsi l r)
    (hne : BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r)
    (hb : BirthShortDoneTerminalObserver.birthEvent
      hpsi (by decide : 0 < 2) h2 l r = false) :
    let q := BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r
    q.1.core.core.label = l.core.core.label ∧
      q.2.core.core.label = nextLabel hpsi l.core.core.label := by
  have hrow := BirthCheckPermitRepairAgree.row_eq
    (kappa := kappa) (tau := tau) hpsi h2 l r hne
  dsimp only
  rw [hrow]
  exact BirthShortDoneTerminalOrdinaryLabelR1.ordinary_row_labels_of_no_birth
    hpsi (by decide : 0 < 2) h2 l r hl hr hopen hb

/-- Off E, an ordinary open follower/follower pair either exposes a physical
leader on this completed row or has exactly the desired two labels. -/
theorem r1_ordinary_label_or_leader_of_no_equal
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hopen : PreparedOrdinaryOpen hpsi l r)
    (hne : BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r) :
    let q := BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r
    q.1.core.core.leader = true ∨
      q.2.core.core.leader = true ∨
      (q.1.core.core.label = l.core.core.label ∧
        q.2.core.core.label = nextLabel hpsi l.core.core.label) := by
  have hrow := BirthCheckPermitRepairAgree.row_eq
    (kappa := kappa) (tau := tau) hpsi h2 l r hne
  cases hb : BirthShortDoneTerminalObserver.birthEvent
      hpsi (by decide : 0 < 2) h2 l r with
  | false =>
      exact Or.inr (Or.inr
        (r1_ordinary_labels_of_no_equal_no_birth
          hpsi h2 l r hl hr hopen hne hb))
  | true =>
      have hh := BirthShortDoneTerminalBirthPhysical.birthEvent_true_row_has_physical_leader
        hpsi (by decide : 0 < 2) h2 l r hb
      dsimp only
      rw [hrow]
      rcases hh with hL | hR
      · exact Or.inl hL
      · exact Or.inr (Or.inl hR)

/-!
PLAN — the one missing row interface: exceptional class E.

The following is deliberately commented out; it is a theorem target, not an
assumption and not compiled code.

```
theorem r1_ordinary_label_or_leader
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hopen : PreparedOrdinaryOpen hpsi l r) :
    let q := BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r
    q.1.core.core.leader = true ∨
      q.2.core.core.leader = true ∨
      (q.1.core.core.label = l.core.core.label ∧
        q.2.core.core.label = nextLabel hpsi l.core.core.label) := by
  ...
```

Proof plan, with no new protocol assumption:

* Let `pl/pr` be `prepareExpiringDisposal`, then `l0/r0 := normalizeDeletion`.
  `hopen` removes both deletion-priority branches, so R1 reaches
  `BirthCheckPermitRepair.ordinary`.
* Split on
  `(doneThroughCheckEntryWidth hpsi 2 h2 kappa l0 r0).1.core.state = .equal`.
  The negative branch is exactly `r1_ordinary_label_or_leader_of_no_equal`.
* In the positive branch E, use `BirthCheckPermitRepair.permitFix_core`:
  `permitFix` changes only `path0Crossed`; its complete `AgentState` core,
  including both endpoint labels, is unchanged at the CHECK cut.
* Export (or duplicate) the already-checked label-only suffix helpers currently
  private in `BirthShortDoneTerminalOrdinaryLabelR1.lean`:
  `beforeWrite_labels`, `stationaryPersistentAuthorizedRow_labels`,
  `afterCheck_labels`, and the `markLeaderBirth_labels_eq` step.  The same
  ingredients are repeated in `B9SpliceV8LeftFollowerLabelFrame.lean`.
  They show that `afterCheckMetadataWidth` cannot alter either label for either
  permit value.  Therefore E and non-E have the same labels after the ordinary
  metadata row even though they can have different comparison states/permits.
* Reuse `doneMetadataBoundedEntryWidth_erase`,
  `deletionPriorityExpireOne_label_frame`, and
  `B9SpliceV8LabelFrame.hostRow_labels_metadata` for reification/expiry/final
  physical framing.  Case-split on the two completed R1 leader bits.  If either
  is true, take the success branch; otherwise `normalizeLeader` is label-id and
  P-prime supplies the labels.
* For the P-prime step itself use the source guard in `Algorithm.lean` and the
  already-proved private helper
  `BirthShortDoneTerminalOrdinaryLabelR1.pprime_labels_of_follower_output` as
  the proof template: with follower inputs, a follower responder output has
  label `nextLabel hpsi l.label`; a mismatch+probe case that does not remain a
  follower is exactly the early-leader alternative.

Thus E is not a suspected counterexample: the missing work is an export-level
full-row label proof, not a new semantic hypothesis.
-/

/-!
PLAN — local deletion drain and ruler word.

Again these signatures are comments only until the E theorem above is closed.

```
theorem local_ruler_word
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (I : B6LocalReverseFill.Interval ring)
    (hW : 2 ≤ I.size)
    (C : Config n psi kappa tau) :
    ∃ w : List (Fin n),
      B6LocalReverseFill.InternalWord I w ∧
      w.length ≤ rulerBudget I.size ∧
      RulerSuccess hpsi ring I
        (B6LocalReverseFill.runR hpsi h2 ring w C) := by
  ...
```

There should be **no additional initial cleanliness premise**.  The proof is a
local rank induction:

1. If `WorkspaceLeader ring I C`, take `w=[]`.
2. Otherwise every workspace cell is a follower.  Define the active search only
   over offsets `1,...,W-1`.  If offset `k>0` is currently
   `CurrentPreparedDeletionActive`, request the predecessor edge
   `cell ring I.first (k-1)`.  `internal_cell_edge` proves the request internal.
3. On that row, `r1_prepared_responder_delete_paths` says no main path is
   generated and the victim path is cleared.  `step1_other` frames every other
   workspace cell.  Therefore `interiorPathCount` strictly decreases.  The
   proof is the interval-restricted analogue of
   `BirthShortDoneTerminalDeletionRank.localStep_prepared_responder_delete_count_lt`;
   use `B6LocalReverseFill.interval_cells_injective` instead of the global
   `rightNeighbor_ne_self` case split.  Since each summand is 0/1,
   `interiorPathCount ≤ W-1 < W`, so one drain uses at most `W` requests.
4. If the deletion service exposes a workspace leader, stop.  Otherwise the
   touched endpoints remain followers, and
   `r1_prepared_responder_delete_labels_of_followers` plus `step1_other` gives a
   pointwise workspace label frame.  Consequently every already constructed
   ruler prefix survives the drain.  Activity is allowed to propagate onto
   offset zero; no ordinary ruler edge uses offset zero.
5. When no interior prepared deletion remains, every intended ruler edge
   `(k,k+1)` for `1 ≤ k` satisfies `PreparedOrdinaryOpen`, because both endpoints
   are interior.  Request that edge.  Apply the completed
   `r1_ordinary_label_or_leader`: stop on a leader; otherwise the initiator label
   is framed and the responder becomes its successor.  `step1_other` preserves
   the previously processed prefix.
6. Repeat from left to right through the tail.  There are at most `W` ordinary
   requests.  A deliberately loose accounting permits one initial drain and
   one drain around every ordinary request: at most `(W+1)*W` deletion letters
   plus `W` ordinary letters, exactly `rulerBudget W`.
7. For `W=2`, `TailSuccessorChain` is vacuous and `[]` already proves the quiet
   branch; the same bound covers it.

This is the localized replacement for importing the old global
`BirthPhaseWait2Transfer` / `BirthB1CapstoneDrainLength` consumer proof.  Those
files remain useful proof templates, especially
`BirthB1CapstoneDrainLength.interleaved_bounded` and
`BirthShortDoneTerminalB1NextGateR2.currentRawAlignedPrefix_of_label_frame`, but
no transition equality to R1 is assumed across ordinary E rows.
-/

/-!
PLAN — ordered-matcher mass consequence.

Define the quiet target simply as the tail chain:

```
def RulerReady (hpsi : 0 < psi) (ring : DirectedRing n)
    (I : B6LocalReverseFill.Interval ring)
    (C : Config n psi kappa tau) : Prop :=
  TailSuccessorChain hpsi ring I C
```

For any concrete internal ruler word `w` ending in `RulerSuccess`, prove the
same coarse original-word inequality as `B6LocalReverseFill.localReverseFill_mass`:

```
theorem localRuler_mass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (I : B6LocalReverseFill.Interval ring)
    (w : List (Fin n)) (C : Config n psi kappa tau)
    (L M : Nat) (hM : 1 ≤ M)
    (hL : w.length ≤ L)
    (ht : B9OrderedWindowMatcher.touchCount
      (B6WindowLocality.touchOf ring (B6LocalReverseFill.support I)) ≤ M)
    (hint : B6LocalReverseFill.InternalWord I w)
    (hhit : RulerSuccess hpsi ring I
      (B6LocalReverseFill.runR hpsi h2 ring w C)) :
    (4 * M) ^ L *
      FiniteUniformStoppingTree.avoidCount
        (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless
        (RulerReady hpsi ring I) C (2 * n * L) ≤
      ((4 * M) ^ L - 1) * n ^ (2 * n * L) := by
  ...
```

Proof pattern, line-for-line the B6 reverse-fill argument:

* If `w=[]`, `hhit` already makes the alive event impossible: a workspace leader
  contradicts `Leaderless`; a tail chain contradicts `¬ RulerReady`.
* Otherwise apply `B9OrderedWindowMatcher.ordered_mass` to `w`, with
  `touch := touchOf ring (support I)`.  `InternalWord` plus
  `B6LocalReverseFill.internal_touch` supplies the matcher's touch premise.
* For every successful matcher word, use
  `B6WindowLocality.success_prefix_agrees` with
  `BirthCheckPermitRepairLeaf.step1_pairLocal`.  Its returned random prefix
  agrees with the requested endpoint on **all complete workspace records**.
  Transfer `hhit` with `rulerSuccess_of_agree`.  A transferred workspace leader
  violates `Leaderless`; a transferred chain violates `¬ RulerReady`.
* Use the same disjoint-success counting algebra as
  `B6LocalReverseFill.request_hit_alive_mass`, then pad from
  `2*n*w.length` to `2*n*L` exactly as its private `alive_mass_pad` helper does.
  No independence assumption is introduced.
* For the theorem produced by `local_ruler_word`, take
  `L = rulerBudget I.size` and `M = I.size + 1`; the latter follows immediately
  from `B6LocalReverseFill.touchCount_support_le I`.

This mass theorem is intentionally left in PLAN until `local_ruler_word` and the
E ordinary-row label export are closed; proving the counting shell first would
not reduce the physical gap.
-/

end B6LocalRuler
