import Leader.Wu.Birth.ReacquirePhaseMass


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthB1ReacquireFrontDrift


open PPLL PPLLRepair PPLLResearchFormulation
  PPLLExpiringComparisonRepair


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthB1ReacquirePhaseMass.FC n psi kappa tau


/-- The physical AgentState observed by the proof-side front. -/
def frontRaw
    (u : ExpiringAgentState psi kappa tau) : AgentState psi :=
  u.core.erase.core


/-- Offset zero is the protected tail `anchor+2`; offset `n-3` is the
closing site when `4 <= n`. -/
def drainSite
    (ring : DirectedRing n) (anchor : Fin n) (k : Nat) : Fin n :=
  groupOffset ring anchor (2 + k)


def protectedTail
    (ring : DirectedRing n) (anchor : Fin n) : Fin n :=
  groupOffset ring anchor 2


def middleSite
    (ring : DirectedRing n) (anchor : Fin n) : Fin n :=
  ring.rightNeighbor anchor


/-- Scan the legal right-drain offsets in increasing order and retain the
furthest offset carrying a physical reset command.  Zero is also the
no-reset/default value; `ScanResetLive` below separates those two cases. -/
def resetScan
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Nat :=
  (List.range (n - 2)).foldl
    (fun best k =>
      if (frontRaw (C (drainSite ring anchor k))).reset_cmd = true
      then k else best) 0


/-- Reverse-echo progress is charged only after the reset has reached the
closing site.  Tail echo has bonus zero, middle echo bonus one, anchor echo
bonus two.  The tests are ordered from most advanced to least advanced. -/
def echoBonus
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Nat :=
  if resetScan ring anchor C = n - 3 then
    if (frontRaw (C anchor)).echo = true then 2
    else if (frontRaw (C (middleSite ring anchor))).echo = true then 1
    else 0
  else 0


/-- Total proof-side front.  The clamp makes the bound independent of any
unproved geometric invariant and does not add protocol state. -/
def front
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Nat :=
  Nat.min (n - 1)
    (resetScan ring anchor C + echoBonus ring anchor C)


/-- Clause 1 does not need Reacquire: the front is globally bounded. -/
theorem front_lt
    (hn : 4 <= n) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) :
    front ring anchor C < n := by
  have hle : front ring anchor C <= n - 1 := by
    unfold front
    exact Nat.min_le_left _ _
  omega


/-- Exact one-row non-regression conclusion used by clause 2. -/
def NondecreasingStep
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e
  BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C [e] = true \/
    BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor D \/
    (BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor D /\
      front ring anchor C <= front ring anchor D)


/-- Exact one-row strict conclusion used by clause 3. -/
def StrictStep
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e
  BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C [e] = true \/
    BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor D \/
    (BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor D /\
      front ring anchor C < front ring anchor D)


/-- Clause 1 in exactly the shape required by `ReacquireFrontDrift`. -/
theorem front_clause1
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) :
    forall C : FC n psi kappa tau,
      BirthPhaseWait2BlockProgress.Reacquire
          hpsi h2 hn kappa tau ring anchor C ->
        front ring anchor C < n := by
  intro C _hR
  exact front_lt hn ring anchor C


/-! ## Clause 2: arbitrary-row non-regression -/


/-- The exact clause-2 proposition. -/
def FrontClause2
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall e : Fin n,
      NondecreasingStep
        hpsi h2 hn kappa tau ring anchor C e


/-- The two reverse-echo scheduler rows. -/
def AnchorRow (anchor : Fin n) (e : Fin n) : Prop :=
  e = anchor


def TailRow
    (ring : DirectedRing n) (anchor e : Fin n) : Prop :=
  e = middleSite ring anchor


/-- The maximal reset/echo collision row. -/
def closingEdge
    (ring : DirectedRing n) (anchor : Fin n) : Fin n :=
  drainSite ring anchor (n - 3)


def ClosingRow
    (ring : DirectedRing n) (anchor e : Fin n) : Prop :=
  e = closingEdge ring anchor


/-- The scheduler row sitting at the currently read reset front. -/
def ResetRow
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  e = drainSite ring anchor (resetScan ring anchor C)


/-- Everything else.  This is the true frame case: the row is neither of the
two protected echo rows, nor the closing row, nor the currently selected reset
row. -/
def OtherRow
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  Not (AnchorRow anchor e) /\
  Not (TailRow ring anchor e) /\
  Not (ClosingRow ring anchor e) /\
  Not (ResetRow ring anchor C e)


/-- The five full-consumer frame lemmas needed to close clause 2.  These are
stated separately so later rounds can prove them from the actual host stages
without changing the front definition. -/
def FrontFrameCases
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall e : Fin n,
      AnchorRow anchor e ->
      NondecreasingStep
        hpsi h2 hn kappa tau ring anchor C e) /\
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall e : Fin n,
      TailRow ring anchor e ->
      NondecreasingStep
        hpsi h2 hn kappa tau ring anchor C e) /\
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall e : Fin n,
      ClosingRow ring anchor e ->
      NondecreasingStep
        hpsi h2 hn kappa tau ring anchor C e) /\
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall e : Fin n,
      ResetRow ring anchor C e ->
      NondecreasingStep
        hpsi h2 hn kappa tau ring anchor C e) /\
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall e : Fin n,
      OtherRow ring anchor C e ->
      NondecreasingStep
        hpsi h2 hn kappa tau ring anchor C e)


/-- Pure case split: once the five row-frame lemmas exist, clause 2 follows. -/
theorem frontClause2_of_frames
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hframes : FrontFrameCases
      hpsi h2 hn kappa tau ring anchor) :
    FrontClause2 hpsi h2 hn kappa tau ring anchor := by
  unfold FrontFrameCases at hframes
  rcases hframes with
    ⟨hAnchor, hTail, hClosing, hReset, hOther⟩
  unfold FrontClause2
  intro C hR e
  by_cases ha : AnchorRow anchor e
  · exact hAnchor C hR e ha
  by_cases ht : TailRow ring anchor e
  · exact hTail C hR e ht
  by_cases hc : ClosingRow ring anchor e
  · exact hClosing C hR e hc
  by_cases hr : ResetRow ring anchor C e
  · exact hReset C hR e hr
  · exact hOther C hR e ⟨ha, ht, hc, hr⟩


/-! ## Clause 3: physical extraction + intended-row progress -/


/-- The scan really points at a live reset, rather than the default zero. -/
def ScanResetLive
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  (frontRaw (C (drainSite ring anchor
    (resetScan ring anchor C)))).reset_cmd = true


/-- Reset phase: the live reset has not yet reached the closing site. -/
def ResetReady
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  ScanResetLive ring anchor C /\
    resetScan ring anchor C < n - 3


/-- Common premise for the reverse-echo/collision phase. -/
def MaxResetLive
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  resetScan ring anchor C = n - 3 /\
    (frontRaw (C (closingEdge ring anchor))).reset_cmd = true


/-- Echo still at the protected tail.  No bonus has yet been earned. -/
def TailEchoReady
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  MaxResetLive ring anchor C /\
    (frontRaw (C anchor)).echo = false /\
    (frontRaw (C (middleSite ring anchor))).echo = false /\
    (frontRaw (C (protectedTail ring anchor))).echo = true


/-- Echo has moved one step back through the protected triple. -/
def MiddleEchoReady
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  MaxResetLive ring anchor C /\
    (frontRaw (C anchor)).echo = false /\
    (frontRaw (C (middleSite ring anchor))).echo = true


/-- Echo has reached the anchor; the next intended row is the closing
reset/echo collision. -/
def AnchorEchoReady
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  MaxResetLive ring anchor C /\
    (frontRaw (C anchor)).echo = true


/-- This is the missing entrance/extraction theorem exposed as a state-only
surface.  It says a broad Reacquire endpoint actually contains one of the
physical moving-front modes.  No `ResetFrontAt` witness or initial state is
stored in the conclusion. -/
def FrontExtraction
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      ResetReady ring anchor C \/
      TailEchoReady ring anchor C \/
      MiddleEchoReady ring anchor C \/
      AnchorEchoReady ring anchor C


/-- The four intended full-consumer row laws.  These are semantic laws, not
part of the front definition. -/
def FrontAdvanceLaws
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    ResetReady ring anchor C ->
      StrictStep hpsi h2 hn kappa tau ring anchor C
        (drainSite ring anchor (resetScan ring anchor C))) /\
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    TailEchoReady ring anchor C ->
      StrictStep hpsi h2 hn kappa tau ring anchor C
        (middleSite ring anchor)) /\
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    MiddleEchoReady ring anchor C ->
      StrictStep hpsi h2 hn kappa tau ring anchor C anchor) /\
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    AnchorEchoReady ring anchor C ->
      StrictStep hpsi h2 hn kappa tau ring anchor C
        (closingEdge ring anchor))


/-- Clause 3 in the exact `ReacquireFrontDrift` shape. -/
def FrontClause3
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    exists e : Fin n,
      StrictStep hpsi h2 hn kappa tau ring anchor C e


/-- Once extraction and the four intended-row laws are available, clause 3 is
formal: choose the row named by the extracted physical mode. -/
theorem frontClause3_of_extraction
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hextract : FrontExtraction
      hpsi h2 hn kappa tau ring anchor)
    (hlaws : FrontAdvanceLaws
      hpsi h2 hn kappa tau ring anchor) :
    FrontClause3 hpsi h2 hn kappa tau ring anchor := by
  unfold FrontExtraction at hextract
  unfold FrontAdvanceLaws at hlaws
  rcases hlaws with ⟨hReset, hTail, hMiddle, hAnchor⟩
  unfold FrontClause3
  intro C hR
  rcases hextract C hR with hr | ht | hm | ha
  · exact ⟨drainSite ring anchor (resetScan ring anchor C),
      hReset C hR hr⟩
  · exact ⟨middleSite ring anchor, hTail C hR ht⟩
  · exact ⟨anchor, hMiddle C hR hm⟩
  · exact ⟨closingEdge ring anchor, hAnchor C hR ha⟩


/-- Final adapter.  This does not hide the missing semantic work: the only
hypotheses are exactly the row frames, physical extraction, and intended-row
laws identified above. -/
theorem reacquireFrontDrift_of_interfaces
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hframes : FrontFrameCases
      hpsi h2 hn kappa tau ring anchor)
    (hextract : FrontExtraction
      hpsi h2 hn kappa tau ring anchor)
    (hlaws : FrontAdvanceLaws
      hpsi h2 hn kappa tau ring anchor) :
    BirthB1ReacquirePhaseMass.ReacquireFrontDrift
      hpsi h2 hn kappa tau ring anchor (front ring anchor) := by
  unfold BirthB1ReacquirePhaseMass.ReacquireFrontDrift
  refine ⟨front_clause1 hpsi h2 hn kappa tau ring anchor, ?_, ?_⟩
  · exact frontClause2_of_frames
      hpsi h2 hn kappa tau ring anchor hframes
  · exact frontClause3_of_extraction
      hpsi h2 hn kappa tau ring anchor hextract hlaws


/-! ## n = 4 executable checks -/


private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private theorem hn4 : 4 <= 4 := by decide


/-- The total executable front is below four on the real public Reacquire
fixture. -/
theorem ringFourReacquire_front_lt :
    front
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4
      BirthB1ReacquirePhaseMass.ringFourReacquire < 4 := by
  decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
/-- The same bound survives the public opposite-edge/pad row fixture. -/
theorem ringFourPad_front_lt :
    front
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4
      BirthB1ReacquirePhaseMass.ringFourPad < 4 := by
  decide


/-- On the minimum ring the original boundary crossing is exactly the first
right-drain edge. -/
theorem ringFour_boundary_edge_geometry :
    BirthPhaseWait2Transfer.boundaryEdge4 =
      drainSite
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4 0 := by
  decide


/-- The pad edge `3 -> 0` is exactly the closing geometric row. -/
theorem ringFour_pad_is_closing :
    ClosingRow
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4 (3 : Fin 4) := by
  unfold ClosingRow
  decide


/-- The two reverse-echo rows are 1 -> 2 and 0 -> 1 respectively. -/
theorem ringFour_echo_row_geometry :
    TailRow
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4 (1 : Fin 4) /\
      AnchorRow
        BirthPhaseWait2Transfer.boundaryAnchor4 (0 : Fin 4) := by
  unfold TailRow AnchorRow
  decide


end BirthB1ReacquireFrontDrift


#print axioms BirthB1ReacquireFrontDrift.front_lt
#print axioms BirthB1ReacquireFrontDrift.front_clause1
#print axioms BirthB1ReacquireFrontDrift.frontClause2_of_frames
#print axioms BirthB1ReacquireFrontDrift.frontClause3_of_extraction
#print axioms BirthB1ReacquireFrontDrift.reacquireFrontDrift_of_interfaces
#print axioms BirthB1ReacquireFrontDrift.ringFourReacquire_front_lt
#print axioms BirthB1ReacquireFrontDrift.ringFourPad_front_lt
#print axioms BirthB1ReacquireFrontDrift.ringFour_boundary_edge_geometry
#print axioms BirthB1ReacquireFrontDrift.ringFour_pad_is_closing
#print axioms BirthB1ReacquireFrontDrift.ringFour_echo_row_geometry
