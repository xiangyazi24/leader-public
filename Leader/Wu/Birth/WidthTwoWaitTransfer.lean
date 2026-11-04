import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleRotation
import Leader.Wu.Elimination.BirthDispatcherWitnesses

/-!
# Local restartable WAIT2 transfer for the actual terminal host

The Local3 carrier is closed only away from its two crossing edges.  Hence the
correct local transfer stops before either a genuine width-two cap row or a
boundary crossing.  Internal p0/p1 rows receive the exact accepted
`RowProjection2`; disjoint safe rows frame the tracked triple and need no fake
projection theorem.

The final finite witness shows that the outgoing crossing edge really can
break the carrier even when that edge is pre-cap.  Therefore the boundary stop
is semantic, not merely an artifact of the existing Local3 proof.
-/

namespace BirthPhaseWait2Transfer

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair

open BirthWaitPassive BirthShortWait BirthShortWaitProjection
  BirthShortWaitTerminalEntryRepair

open BirthShortDoneTerminalPassiveR1
  BirthShortDoneTerminalPassiveR4
  BirthShortDoneTerminalPassiveLocal3
  BirthShortDoneTerminalPassiveLocal3Rotation

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {psi kappa tau n : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau

/-- Fully typed local name for the actual R4 host step.  The explicit binders
are required because the imported definition's `{n psi kappa tau}` are all
implicit and cannot be inferred at the abbreviation declaration itself. -/
abbrev hostStep
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (e : Fin n) :
    FC n psi kappa tau :=
  BirthShortDoneTerminalPassiveR4.hostStep hpsi h2 ring C e

/-- The exact B2 restart source.  No state outside the physical three-cell
Local3 frame is constrained.  The width proof is retained in the signature so
later width-two bricks can use one uniform interface. -/
def LocalWait2Carrier
    (hpsi : 0 < psi) (_h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  LocalLine3At hpsi hn ring anchor C

/-- A cap stop is relevant only on one of the two internal Local3 service
edges.  The cap edge itself has not yet been executed. -/
def LocalWait2CapNow
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  InternalLine3EdgeAt hn ring anchor e /\
    RowCap2 hpsi h2 kappa ring C e

/-- The exact Local3 renewal boundary: either of the two physical crossing
edges excluded by `SafeLine3EdgeAt`. -/
def LocalWait2BoundaryNow
    (hn : 4 <= n) (ring : DirectedRing n)
    (anchor e : Fin n) : Prop :=
  ¬ SafeLine3EdgeAt hn ring anchor e

/-- B2 stops before executing either a cap edge or a Local3 boundary edge. -/
def LocalWait2StopNow
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  LocalWait2CapNow hpsi h2 hn kappa tau ring anchor C e \/
    LocalWait2BoundaryNow hn ring anchor e

/-- Projection along the literal physical word, but only on the two physical
internal service edges.  Safe disjoint outside edges frame the Local3 cells and
there is no reason to demand R4's global `RowProjection2` on those unrelated
endpoints. -/
def LocalProjectionAlong2At
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : List (Fin n) -> Prop
  | [] => True
  | e :: es =>
      (InternalLine3EdgeAt hn ring anchor e ->
        RowProjection2 hpsi h2 kappa tau ring C e) /\
      LocalProjectionAlong2At hpsi h2 hn kappa tau ring anchor
        (hostStep hpsi h2 ring C e) es

/-- Exact executable-word source for a B2 continuation.  Every charged letter
is the original physical scheduler letter.  The recursion refuses to execute
the first cap or crossing edge; that edge is the renewal event for B3/B4. -/
def LocalWait2RunSource
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : List (Fin n) -> Prop
  | [] => True
  | e :: es =>
      ¬ LocalWait2StopNow
        hpsi h2 hn kappa tau ring anchor C e /\
      LocalWait2RunSource hpsi h2 hn kappa tau ring anchor
        (hostStep hpsi h2 ring C e) es

/-- Converse coordinate bridge used locally below.  The repository exports the
forward bridge `localLine3At_rotateConfig`; this converse is immediate from the
same three `rotateIndex_p*` equations. -/
private theorem localLine3At_of_rotateConfig
    (hpsi : 0 < psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (h : LocalLine3 hpsi hn (rotateConfig ring anchor C)) :
    LocalLine3At hpsi hn ring anchor C := by
  refine {
    pass0 := ?_
    pass1 := ?_
    pass2 := ?_
    lab0 := ?_
    lab1 := ?_
    lab2 := ?_ }
  · have hp := h.pass0
    change Passive (raw (C (rotateIndex ring anchor (p0 hn)))) at hp
    rw [rotateIndex_p0 hn ring anchor] at hp
    exact hp
  · have hp := h.pass1
    change Passive (raw (C (rotateIndex ring anchor (p1 hn)))) at hp
    rw [rotateIndex_p1 hn ring anchor] at hp
    exact hp
  · have hp := h.pass2
    change Passive (raw (C (rotateIndex ring anchor (p2 hn)))) at hp
    rw [rotateIndex_p2 hn ring anchor] at hp
    exact hp
  · have hl := h.lab0
    change
      (raw (C (rotateIndex ring anchor (p0 hn)))).label.val = 0 at hl
    rw [rotateIndex_p0 hn ring anchor] at hl
    exact hl
  · have hl := h.lab1
    change
      (raw (C (rotateIndex ring anchor (p1 hn)))).label.val = 1 at hl
    rw [rotateIndex_p1 hn ring anchor] at hl
    exact hl
  · have hl := h.lab2
    change
      (raw (C (rotateIndex ring anchor (p2 hn)))).label.val =
        2 % psi at hl
    rw [rotateIndex_p2 hn ring anchor] at hl
    exact hl

/-- One actual repaired full-host edge at an arbitrary physical anchor.

`SafeLine3EdgeAt` is the exact locality condition.  If the edge is internal,
its only additional premise is the literal current `RowPreCap2`; then the
existing `local3_one_step` supplies both passive/label closure and the accepted
`RowProjection2`.  If the edge is disjoint, the same theorem closes the triple
by physical framing and the projection implication is vacuous. -/
theorem local_wait2_one_edge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hC : LocalWait2Carrier hpsi h2 hn ring anchor C)
    (e : Fin n)
    (hsafe : SafeLine3EdgeAt hn ring anchor e)
    (hpre : InternalLine3EdgeAt hn ring anchor e ->
      RowPreCap2 hpsi h2 kappa ring C e) :
    LocalWait2Carrier hpsi h2 hn ring anchor
        (hostStep hpsi h2 ring C e) /\
      (InternalLine3EdgeAt hn ring anchor e ->
        RowProjection2 hpsi h2 kappa tau ring C e) := by
  let ec : Fin n := unrotateIndex ring anchor e
  have hline :
      LocalLine3 hpsi hn (rotateConfig ring anchor C) :=
    localLine3At_rotateConfig hpsi hn ring anchor C hC
  have hsafeC : SafeLine3Edge hn ec := by
    simpa [SafeLine3EdgeAt, ec] using hsafe
  have hpreC :
      InternalLine3Edge hn ec ->
        RowPreCap2 hpsi h2 kappa ring
          (rotateConfig ring anchor C) ec := by
    intro hint
    have hintAt : InternalLine3EdgeAt hn ring anchor e := by
      simpa [InternalLine3EdgeAt, ec] using hint
    apply
      (rowPreCap2_rotateConfig_iff hpsi h2
        (by omega : 2 <= n) kappa tau ring anchor C ec).2
    simpa [ec] using hpre hintAt
  have hs :=
    local3_one_step hpsi h2 hn kappa tau ring
      (rotateConfig ring anchor C) ec hline hsafeC hpreC
  have hstep :
      hostStep hpsi h2 ring (rotateConfig ring anchor C) ec =
        rotateConfig ring anchor
          (hostStep hpsi h2 ring C e) := by
    simpa [hostStep, ec] using
      (hostStep_rotateConfig
        hpsi h2 hn kappa tau ring anchor C ec)
  constructor
  · unfold LocalWait2Carrier
    apply localLine3At_of_rotateConfig hpsi hn ring anchor
      (hostStep hpsi h2 ring C e)
    rw [<- hstep]
    exact hs.1
  · intro hintAt
    have hint : InternalLine3Edge hn ec := by
      simpa [InternalLine3EdgeAt, ec] using hintAt
    have hpC := hs.2 hint
    have hp :=
      (rowProjection2_rotateConfig_iff hpsi h2
        (by omega : 2 <= n) kappa tau ring anchor C ec).1 hpC
    simpa [ec] using hp

/-- Same one-edge theorem in the form B3/B4 should consume.  Absence of the
explicit stop event supplies both safety and, on an internal edge, pre-cap. -/
theorem local_wait2_one_edge_until_stop
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hC : LocalWait2Carrier hpsi h2 hn ring anchor C)
    (e : Fin n)
    (hgo : ¬ LocalWait2StopNow
      hpsi h2 hn kappa tau ring anchor C e) :
    LocalWait2Carrier hpsi h2 hn ring anchor
        (hostStep hpsi h2 ring C e) /\
      (InternalLine3EdgeAt hn ring anchor e ->
        RowProjection2 hpsi h2 kappa tau ring C e) := by
  have hsafe : SafeLine3EdgeAt hn ring anchor e := by
    by_cases hs : SafeLine3EdgeAt hn ring anchor e
    · exact hs
    · have hstop : LocalWait2StopNow
          hpsi h2 hn kappa tau ring anchor C e := by
        unfold LocalWait2StopNow LocalWait2BoundaryNow
        exact Or.inr hs
      exact False.elim (hgo hstop)
  have hpre :
      InternalLine3EdgeAt hn ring anchor e ->
        RowPreCap2 hpsi h2 kappa ring C e := by
    intro hint
    unfold RowPreCap2
    intro hcap
    apply hgo
    unfold LocalWait2StopNow LocalWait2CapNow
    exact Or.inl <| And.intro hint hcap
  exact local_wait2_one_edge
    hpsi h2 hn kappa tau ring anchor C hC e hsafe hpre

/-- Fold the literal original physical word.  This is the corrected B2 theorem:
no global `HostPassive`, no global `HostCyclic`, and no scheduler reweighting.
The output is again the exact `LocalLine3At` restart carrier, while the second
conjunct records the accepted WAIT clock/count projection on every internal
service edge actually executed before the first cap/boundary stop. -/
theorem local_wait2_transfer_until_stop
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hC : LocalWait2Carrier hpsi h2 hn ring anchor C)
    (es : List (Fin n))
    (hrun : LocalWait2RunSource
      hpsi h2 hn kappa tau ring anchor C es) :
    LocalWait2Carrier hpsi h2 hn ring anchor
        (es.foldl (hostStep hpsi h2 ring) C) /\
      LocalProjectionAlong2At
        hpsi h2 hn kappa tau ring anchor C es := by
  induction es generalizing C with
  | nil =>
      change LocalWait2Carrier hpsi h2 hn ring anchor C /\ True
      exact And.intro hC True.intro
  | cons e rest ih =>
      change
        (¬ LocalWait2StopNow
          hpsi h2 hn kappa tau ring anchor C e) /\
        LocalWait2RunSource hpsi h2 hn kappa tau ring anchor
          (hostStep hpsi h2 ring C e) rest at hrun
      have hs := local_wait2_one_edge_until_stop
        hpsi h2 hn kappa tau ring anchor C hC e hrun.1
      have ht := ih
        (C := hostStep hpsi h2 ring C e) hs.1 hrun.2
      change
        LocalWait2Carrier hpsi h2 hn ring anchor
            (rest.foldl (hostStep hpsi h2 ring)
              (hostStep hpsi h2 ring C e)) /\
          ((InternalLine3EdgeAt hn ring anchor e ->
              RowProjection2 hpsi h2 kappa tau ring C e) /\
            LocalProjectionAlong2At hpsi h2 hn kappa tau ring anchor
              (hostStep hpsi h2 ring C e) rest)
      exact And.intro ht.1 (And.intro hs.2 ht.2)

/-! ## Concrete boundary no-go

The outgoing crossing edge is not safely absorbable into the Local3 carrier.
The right endpoint below is the repository's public, real responder-disposal
fixture.  The left endpoint is a passive label-zero Local3 cell.  On edge 2,
the actual TerminalHost sees the responder's prepared terminal disposal and
propagates the elimination marker to the left endpoint. -/

private theorem hpsi2 : 0 < 2 := by decide
private theorem hw2 : 2 <= 2 := by decide
private theorem hn4 : 4 <= 4 := by decide

def boundaryRing4 : DirectedRing 4 := ⟨by decide⟩
def boundaryAnchor4 : Fin 4 := 0
def boundaryEdge4 : Fin 4 := 2

private def boundaryRegs0 : Registers 2 where
  label := 0
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

private def boundaryRegs1 : Registers 2 where
  label := 1
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

private def boundaryRegs2 : Registers 2 where
  label := 0
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

private theorem boundaryRegs0_domain :
    (cell boundaryRegs0).inProtocolDomain 2 := by
  simp [boundaryRegs0, AgentState.inProtocolDomain, cell]

private theorem boundaryRegs1_domain :
    (cell boundaryRegs1).inProtocolDomain 2 := by
  simp [boundaryRegs1, AgentState.inProtocolDomain, cell]

private theorem boundaryRegs2_domain :
    (cell boundaryRegs2).inProtocolDomain 2 := by
  simp [boundaryRegs2, AgentState.inProtocolDomain, cell]

private def packPassive
    (d : Registers 2) (hd : (cell d).inProtocolDomain 2) :
    ExpiringAgentState 2 2 3 :=
  ⟨⟨BoundedAgentState.ofDomain (cell d) hd, false⟩, 3⟩

@[simp] private theorem raw_packPassive
    (d : Registers 2) (hd : (cell d).inProtocolDomain 2) :
    raw (packPassive d hd) = cell d := by
  simp [packPassive, raw, BoundedAgentState.erase_ofDomain]

/-- Sites 0,1,2 are the Local3 triple.  Site 3 is a genuine current-repository
responder disposal state, not a synthetic transition law. -/
def boundaryConfig4 : FC 4 2 2 3 :=
  fun i =>
    if i.val = 0 then packPassive boundaryRegs0 boundaryRegs0_domain
    else if i.val = 1 then packPassive boundaryRegs1 boundaryRegs1_domain
    else if i.val = 2 then packPassive boundaryRegs2 boundaryRegs2_domain
    else K2BirthDispatcher.Witnesses.responderDisposal

private theorem boundary_right0 :
    boundaryRing4.rightNeighbor boundaryAnchor4 = (1 : Fin 4) := by
  decide

private theorem boundary_right1 :
    boundaryRing4.rightNeighbor
        (boundaryRing4.rightNeighbor boundaryAnchor4) = (2 : Fin 4) := by
  decide

private theorem boundary_source_carrier :
    LocalWait2Carrier hpsi2 hw2 hn4
      boundaryRing4 boundaryAnchor4 boundaryConfig4 := by
  unfold LocalWait2Carrier
  refine {
    pass0 := ?_
    pass1 := ?_
    pass2 := ?_
    lab0 := ?_
    lab1 := ?_
    lab2 := ?_ }
  · change Passive (raw (boundaryConfig4 boundaryAnchor4))
    simp [boundaryAnchor4, boundaryConfig4, boundaryRegs0,
      Passive, InertWriter, Metadata, registers, cell]
  · rw [boundary_right0]
    simp [boundaryConfig4, boundaryRegs1,
      Passive, InertWriter, Metadata, registers, cell]
  · rw [boundary_right1]
    simp [boundaryConfig4, boundaryRegs2,
      Passive, InertWriter, Metadata, registers, cell]
  · change (raw (boundaryConfig4 boundaryAnchor4)).label.val = 0
    simp [boundaryAnchor4, boundaryConfig4, boundaryRegs0, cell]
  · rw [boundary_right0]
    simp [boundaryConfig4, boundaryRegs1, cell]
  · rw [boundary_right1]
    simp [boundaryConfig4, boundaryRegs2, cell]

/-- This crossing row is genuinely pre-cap: the dirty right endpoint is not
preloaded at width-two count cap 2. -/
private theorem boundary_preCap :
    RowPreCap2 hpsi2 hw2 2 boundaryRing4 boundaryConfig4 boundaryEdge4 := by
  unfold RowPreCap2 RowCap2
  decide

/-- Edge 2 is the outgoing Local3 crossing edge at anchor zero. -/
private theorem boundary_not_safe :
    ¬ SafeLine3EdgeAt hn4
      boundaryRing4 boundaryAnchor4 boundaryEdge4 := by
  unfold SafeLine3EdgeAt SafeLine3Edge
  decide

/-- Literal evaluation of the actual full TerminalHost row: responder deletion
propagates `.eliminate_signal` onto the passive site-2 initiator.  Positive
stall keeps that non-K2 state through expiry; the final physical K2 stage
frames it. -/
private theorem boundary_left_state_after_cross :
    (raw
      ((hostStep hpsi2 hw2 boundaryRing4 boundaryConfig4 boundaryEdge4)
        (2 : Fin 4))).state = .eliminate_signal := by
  decide

private theorem boundary_destroyed :
    ¬ LocalWait2Carrier hpsi2 hw2 hn4 boundaryRing4 boundaryAnchor4
      (hostStep hpsi2 hw2 boundaryRing4 boundaryConfig4 boundaryEdge4) := by
  intro hline
  unfold LocalWait2Carrier at hline
  have hp := hline.pass2
  rw [boundary_right1] at hp
  rcases hp with ⟨hmeta, _hwait, _hwriter⟩
  unfold Metadata at hmeta
  have hs := congrArg (fun u : AgentState 2 => u.state) hmeta
  have hnone :
      (raw
        ((hostStep hpsi2 hw2 boundaryRing4 boundaryConfig4 boundaryEdge4)
          (2 : Fin 4))).state = .none := by
    simpa [cell] using hs
  rw [boundary_left_state_after_cross] at hnone
  cases hnone

/-- Concrete refutation of the no-cap-only Local3 closure proposed in the
roadmap.  The source is a genuine Local3 carrier and the scheduled crossing
edge is pre-cap, yet the actual repaired full host destroys the carrier. -/
theorem boundary_outgoing_preCap_destroys_carrier :
    LocalWait2Carrier hpsi2 hw2 hn4
        boundaryRing4 boundaryAnchor4 boundaryConfig4 /\
      RowPreCap2 hpsi2 hw2 2
        boundaryRing4 boundaryConfig4 boundaryEdge4 /\
      (¬ SafeLine3EdgeAt hn4
        boundaryRing4 boundaryAnchor4 boundaryEdge4) /\
      (¬ LocalWait2Carrier hpsi2 hw2 hn4
        boundaryRing4 boundaryAnchor4
        (hostStep hpsi2 hw2 boundaryRing4
          boundaryConfig4 boundaryEdge4)) := by
  exact And.intro boundary_source_carrier
    (And.intro boundary_preCap
      (And.intro boundary_not_safe boundary_destroyed))

end BirthPhaseWait2Transfer

#print axioms BirthPhaseWait2Transfer.local_wait2_one_edge
#print axioms BirthPhaseWait2Transfer.local_wait2_one_edge_until_stop
#print axioms BirthPhaseWait2Transfer.local_wait2_transfer_until_stop
#print axioms BirthPhaseWait2Transfer.boundary_outgoing_preCap_destroys_carrier
