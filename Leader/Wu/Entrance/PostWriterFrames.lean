import Leader.Wu.Entrance.PreWriterFramesCheck

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6PostWriterThreading

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair BirthShortDoneCuts BirthStationaryWrite
  BirthShortDoneTerminalHost
open K2BirthDispatcher ExpiringK2Projection K2BirthLeaderNormalize
open B6MicroAlg18Disabled B6PreWriterFramesC

variable {ψ κ τ width : Nat}

/-- The literal stationary-writer output on the ordinary prepared branch. -/
def writerOutput
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let p := rowPreWriterInput hψ hwidth hle κ l r
  stationaryPersistentAuthorizedRow hψ p.1 p.2

/-- Side conditions needed after the writer in this micro-round. -/
def PostWriterRightHypotheses
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) (b : Bool) : Prop :=
  let w := writerOutput hψ hwidth hle κ l r
  authBirth (normalizeDeletion l) (normalizeDeletion r) w = false ∧
    deletionActive w.2 = false ∧
    w.2.core.leader = false ∧ w.2.core.bit = b

/-- Birth marking is a stutter when the computed pair birth event is false. -/
theorem markLeaderBirth_frame_of_no_birth
    (born : Bool) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (hborn : born = false) : markLeaderBirth born q = q := by
  simp [markLeaderBirth, hborn]

/-- Finite reification preserves the entire erased responder, hence its bit. -/
theorem boundedReification_right_erase
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    (doneMetadataBoundedEntryWidth hψ hwidth hle l r).2.erase =
      (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l.erase r.erase).2 := by
  exact congrArg Prod.snd
    (doneMetadataBoundedEntryWidth_erase hψ hwidth hle l r)

/-- Closed deletion priority falls through to path expiry; every branch,
including zero-budget clearing, frames leader and bit. -/
theorem deletionPriorityExpireOne_leader_bit_of_closed
    (old out : ExpiringAgentState ψ κ τ)
    (hclosed : deletionActive out.core.erase = false) :
    let q := deletionPriorityExpireOne τ old out
    q.core.core.leader = out.core.core.leader ∧
      q.core.core.bit = out.core.core.bit := by
  unfold deletionPriorityExpireOne
  simp only [hclosed, Bool.false_eq_true, if_false]
  unfold PPLLPathStallComparisonRepair.pathExpireOne
    PPLLExpiringComparisonRepair.clearComparisonCarrier
  dsimp only
  repeat (first | exact ⟨rfl, rfl⟩ | split)

/-- A follower skips leader normalization, so in particular its bit is framed. -/
theorem normalizeLeader_frame_of_follower
    (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ)
    (hfollower : q.core.core.leader = false) :
    normalizeLeader hψ q = q := by
  simp [normalizeLeader, hfollower]

/-- The final newborn/collision/K2 tail writes only signal fields, not `bit`. -/
theorem finalPhysical_right_bit
    (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    (finalPhysical hψ oldL oldR metaL metaR).2.core.core.bit =
      metaR.core.core.bit := by
  have h := (finalPhysical_frame hψ oldL oldR metaL metaR).2
  have hb := congrArg
    (fun u : ExpiringAgentState ψ κ τ => u.core.core.bit) h
  simpa [ExpiringK2Projection.putSignals] using hb

private theorem ordinaryMetadata_is_marked_writer
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneOrdinaryMetadataEntryWidth hψ hwidth hle κ
        (normalizeDeletion l) (normalizeDeletion r) =
      let w := writerOutput hψ hwidth hle κ l r
      markLeaderBirth
        (authBirth (normalizeDeletion l) (normalizeDeletion r) w) w := by
  rfl

/-- Composition seam for 3c-3: once the actual writer output has responder
bit `b` and the stated tail guards, the complete physical row also has bit `b`. -/
theorem row_right_bit_of_writer_output
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) (b : Bool)
    (hstage : Stage3PreparedHypotheses
      (preparedEndpoint hψ l) (preparedEndpoint hψ r))
    (hpost : PostWriterRightHypotheses hψ hwidth hle κ
      (preparedEndpoint hψ l) (preparedEndpoint hψ r) b) :
    (row hψ hwidth hle l r).2.core.erase.core.bit = b := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let lp := l0.core.erase
  let rp := r0.core.erase
  let w := writerOutput hψ hwidth hle κ lp rp
  have hs : Stage3PreparedHypotheses lp rp := by
    simpa [lp, rp, l0, r0, preparedEndpoint] using hstage
  have hopen := stage3_priority_open lp rp hs
  have hp : PostWriterRightHypotheses hψ hwidth hle κ lp rp b := by
    simpa [lp, rp, l0, r0, preparedEndpoint] using hpost
  change authBirth (normalizeDeletion lp) (normalizeDeletion rp) w = false ∧
    deletionActive w.2 = false ∧ w.2.core.leader = false ∧
      w.2.core.bit = b at hp
  have hmeta :
      doneMetadataAuthorizedEntryWidth hψ hwidth hle κ lp rp = w := by
    unfold doneMetadataAuthorizedEntryWidth
    dsimp only
    simp only [hopen.2, Bool.false_eq_true, if_false, hopen.1]
    rw [ordinaryMetadata_is_marked_writer hψ hwidth hle κ lp rp]
    exact markLeaderBirth_frame_of_no_birth _ w hp.1
  let q := doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core
  have hr : q.2.erase = w.2 := by
    have he := boundedReification_right_erase hψ hwidth hle l0.core r0.core
    have he' : q.2.erase =
        (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ lp rp).2 := by
      simpa [q, lp, rp] using he
    exact he'.trans (congrArg Prod.snd hmeta)
  let baseR : ExpiringAgentState ψ κ τ := ⟨q.2, r0.stall⟩
  have hc : deletionActive baseR.core.erase = false := by
    change deletionActive q.2.erase = false
    rw [hr]
    exact hp.2.1
  let eR := deletionPriorityExpireOne τ r0 baseR
  have he := deletionPriorityExpireOne_leader_bit_of_closed r0 baseR hc
  change eR.core.core.leader = baseR.core.core.leader ∧
    eR.core.core.bit = baseR.core.core.bit at he
  have hfollow : eR.core.core.leader = false := by
    have hb := congrArg (fun u : AuthorizedAgentState ψ => u.core.leader) hr
    change q.2.core.leader = w.2.core.leader at hb
    exact he.1.trans (hb.trans hp.2.2.1)
  have hn := normalizeLeader_frame_of_follower hψ eR hfollow
  let baseL : ExpiringAgentState ψ κ τ := ⟨q.1, l0.stall⟩
  let eL := deletionPriorityExpireOne τ l0 baseL
  have hrow : row hψ hwidth hle l r =
      finalPhysical hψ l r (normalizeLeader hψ eL) (normalizeLeader hψ eR) := by
    simpa [l0, r0, q, baseL, baseR, eL, eR] using
      (row_real_host_witness hψ hwidth hle l r)
  rw [hrow]
  change (finalPhysical hψ l r
    (normalizeLeader hψ eL) (normalizeLeader hψ eR)).2.core.core.bit = b
  calc
    _ = (normalizeLeader hψ eR).core.core.bit :=
      finalPhysical_right_bit hψ l r _ _
    _ = eR.core.core.bit := by rw [hn]
    _ = baseR.core.core.bit := he.2
    _ = q.2.core.bit := rfl
    _ = w.2.core.bit := by
      have hb := congrArg (fun u : AuthorizedAgentState ψ => u.core.bit) hr
      exact hb
    _ = b := hp.2.2.2

end B6PostWriterThreading

#print axioms B6PostWriterThreading.markLeaderBirth_frame_of_no_birth
#print axioms B6PostWriterThreading.boundedReification_right_erase
#print axioms B6PostWriterThreading.deletionPriorityExpireOne_leader_bit_of_closed
#print axioms B6PostWriterThreading.normalizeLeader_frame_of_follower
#print axioms B6PostWriterThreading.finalPhysical_right_bit
#print axioms B6PostWriterThreading.row_right_bit_of_writer_output
