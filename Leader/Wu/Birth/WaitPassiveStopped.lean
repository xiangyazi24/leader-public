import Leader.Wu.Birth.WaitPassiveCap
import Leader.Wu.Safety.SignalCoherence


namespace BirthWaitPassive


open PPLL PPLLRepair PPLLResearchFormulation PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLWriteIncrementGate
  PPLLCompleteMultiLeaderCleanup PPLLWallSweepNormalResetContract
  BirthCheckCongestGuardRepair BirthMismatchDisposalProducer
  BirthSigMoveDisposalRepair BirthArrivalCaptureRepair BirthGenerationControlRepair


set_option autoImplicit false
set_option Elab.async false


variable {psi kappa tau n : Nat}


/-- The cap row retains the actual terminal count for every nontrivial label
alphabet.  Only psi=2 needs the released-GEN endpoint calculation already
proved in BirthWaitPassiveCap. -/
theorem full_cap_terminal_count (hpsi : 0 < psi) (hsize : 2 <= psi)
    (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : Passive (raw l)) (hr : Passive (raw r))
    (hab : (raw r).label =
      ⟨((raw l).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hcap : Cap hpsi kappa
      (waitSaturated hpsi kappa (raw l) (raw r)).2) :
    let q := generationFullTransition hpsi kappa tau l r
    (raw q.2).count = kappa := by
  by_cases htwo : psi = 2
  · subst psi
    let a := registers (raw l)
    let b := registers (raw r)
    have hla : raw l = cell a := by
      change raw l = cell (registers (raw l))
      exact hl.1
    have hrb : raw r = cell b := by
      change raw r = cell (registers (raw r))
      exact hr.1
    have hab' : b.label =
        ⟨(a.label.val + 1) % 2, Nat.mod_lt _ (by decide : 0 < 2)⟩ := by
      simpa [a, b, registers] using hab
    have hcap' : Cap (by decide : 0 < 2) kappa
        (waitSaturated (by decide : 0 < 2) kappa (cell a) (cell b)).2 := by
      have hx := hcap
      change Cap (by decide : 0 < 2) kappa
        (waitSaturated (by decide : 0 < 2) kappa (raw l) (raw r)).2 at hx
      rw [hla, hrb] at hx
      exact hx
    simpa using
      (full_cap_two_terminal_count kappa tau l r a b hla hrb hab' hcap')
  · have hthree : 3 <= psi := by omega
    let a := registers (raw l)
    let b := registers (raw r)
    let w := waitSaturated hpsi kappa (cell a) (cell b)
    let q := generationFullTransition hpsi kappa tau l r
    change (raw q.2).count = kappa
    have hla : raw l = cell a := by
      change raw l = cell (registers (raw l))
      exact hl.1
    have hrb : raw r = cell b := by
      change raw r = cell (registers (raw r))
      exact hr.1
    have hab' : b.label =
        ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
      simpa [a, b, registers] using hab
    have hcapw := hcap
    rw [hla, hrb] at hcapw
    change Cap hpsi kappa w.2 at hcapw
    have hs := wait_static hpsi kappa (cell a) (cell b)
    change w.1.label = a.label ∧ w.2.label = b.label ∧
      w.1.count = a.count at hs
    have hnotroot : w.1.label ≠ ⟨0, hpsi⟩ := by
      intro hroot
      have ha0 : a.label = ⟨0, hpsi⟩ := hs.1.symm.trans hroot
      have hbt : b.label = ⟨psi - 1, by omega⟩ :=
        hs.2.1.symm.trans hcapw.1
      have hv := congrArg Fin.val hab'
      have hv' : psi - 1 = 1 := by
        simpa [ha0, hbt, Nat.mod_eq_of_lt (by omega : 1 < psi)] using hv
      omega
    have hrow := full_cell_row hpsi kappa tau l r a b hla hrb hab'
      (fun h => (hnotroot h).elim)
    change
      q.1.core.erase =
        ⟨cell {registers w.1 with writer := .none}, false⟩ ∧
      q.2.core.erase =
        ⟨cell {registers w.2 with writer :=
          if w.1.label < w.2.label ∨ w.2.label = ⟨0, hpsi⟩
          then .depart else .none}, false⟩ at hrow
    have hc := congrArg
      (fun s : AuthorizedAgentState psi => s.core.count) hrow.2
    have hout : (q.2.core.erase).core.count = w.2.count := by
      simpa [cell, registers] using hc
    change (q.2.core.erase).core.count = kappa
    exact hout.trans hcapw.2


/-- Before cap, the complete physical row and the literal WAIT row have exactly
the same observed clock/ruler registers. -/
theorem full_wait_clock_row_below (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : Passive (raw l)) (hr : Passive (raw r))
    (hab : (raw r).label =
      ⟨((raw l).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hbelow : Below hpsi kappa
      (waitSaturated hpsi kappa (raw l) (raw r)).2) :
    let w := waitSaturated hpsi kappa (raw l) (raw r)
    let q := generationFullTransition hpsi kappa tau l r
    clock (raw q.1) = clock w.1 ∧ clock (raw q.2) = clock w.2 := by
  let a := registers (raw l)
  let b := registers (raw r)
  let w := waitSaturated hpsi kappa (cell a) (cell b)
  let q := generationFullTransition hpsi kappa tau l r
  have hla : raw l = cell a := by
    change raw l = cell (registers (raw l))
    exact hl.1
  have hrb : raw r = cell b := by
    change raw r = cell (registers (raw r))
    exact hr.1
  have hab' : b.label =
      ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    simpa [a, b, registers] using hab
  have harm := wait_armed hpsi kappa (raw l) (raw r)
    hl.2.1 hr.2.1 hbelow
  rw [hla, hrb] at harm
  change w.1.wait = true ∧ w.2.wait = true at harm
  have hrow := full_cell_row hpsi kappa tau l r a b hla hrb hab'
    (fun _ => harm.1)
  change
    q.1.core.erase =
      ⟨cell {registers w.1 with writer := .none}, false⟩ ∧
    q.2.core.erase =
      ⟨cell {registers w.2 with writer :=
        if w.1.label < w.2.label ∨ w.2.label = ⟨0, hpsi⟩
        then .depart else .none}, false⟩ at hrow
  rw [hla, hrb]
  constructor
  · change clock ((q.1.core.erase).core) = clock w.1
    have h := congrArg
      (fun s : AuthorizedAgentState psi => clock s.core) hrow.1
    simpa [clock, cell, registers] using h
  · change clock ((q.2.core.erase).core) = clock w.2
    have h := congrArg
      (fun s : AuthorizedAgentState psi => clock s.core) hrow.2
    simpa [clock, cell, registers] using h


private theorem numeric_of_clock_eq {u v : AgentState psi}
    (h : clock u = clock v) : Numeric u = Numeric v := by
  have hx := congrArg
    (fun c : Clock psi => (c.label, c.h, c.carry, c.reset, c.count)) h
  simpa [clock, Numeric] using hx


abbrev FullConfig (n psi kappa tau : Nat) :=
  Fin n -> ExpiringAgentState psi kappa tau


abbrev WaitConfig (n psi : Nat) := Fin n -> AgentState psi


def rawConfig (C : FullConfig n psi kappa tau) : WaitConfig n psi :=
  fun i => raw (C i)


/-- Packaging only: the transition is literally generationFullTransition. -/
def fullProtocol (hpsi : 0 < psi) (kappa tau : Nat) : PopulationProtocol where
  Q := ExpiringAgentState psi kappa tau
  Y := Unit
  transition := generationFullTransition hpsi kappa tau
  output := fun _ => ()


/-- Proof projection only: the transition is literally waitSaturated. -/
def waitProtocol (hpsi : 0 < psi) (kappa : Nat) : PopulationProtocol where
  Q := AgentState psi
  Y := Unit
  transition := waitSaturated hpsi kappa
  output := fun _ => ()


private theorem step_left (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e : Fin n) :
    P.step ring C e e =
      (P.transition (C e) (C (ring.rightNeighbor e))).1 := by
  simp [PopulationProtocol.step]


private theorem step_right (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    P.step ring C e (ring.rightNeighbor e) =
      (P.transition (C e) (C (ring.rightNeighbor e))).2 := by
  simp [PopulationProtocol.step, hne]


private theorem step_other (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e k : Fin n)
    (hke : k ≠ e) (hkj : k ≠ ring.rightNeighbor e) :
    P.step ring C e k = C k := by
  simp [PopulationProtocol.step, hke, hkj]


def fullStep (hpsi : 0 < psi) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (e : Fin n) : FullConfig n psi kappa tau :=
  PopulationProtocol.step (fullProtocol hpsi kappa tau) ring C e


def waitStep (hpsi : 0 < psi) (kappa : Nat) (ring : DirectedRing n)
    (C : WaitConfig n psi) (e : Fin n) : WaitConfig n psi :=
  PopulationProtocol.step (waitProtocol hpsi kappa) ring C e


/-- The literal WAIT protocol step is the repository's actual two-position
updatePair on the same edge. -/
theorem waitStep_eq_updatePair (hpsi : 0 < psi) (hn : 1 < n)
    (ring : DirectedRing n) (kappa : Nat)
    (C : WaitConfig n psi) (e : Fin n) :
    waitStep hpsi kappa ring C e =
      updatePair C e (ring.rightNeighbor e)
        (waitSaturated hpsi kappa (C e) (C (ring.rightNeighbor e))) := by
  unfold waitStep
  funext k
  by_cases hke : k = e
  · subst k
    rw [step_left (waitProtocol hpsi kappa) ring C e,
      updatePair_initiator]
    rfl
  · by_cases hkj : k = ring.rightNeighbor e
    · subst k
      have hne := rightNeighbor_ne_self_of_one_lt ring hn e
      rw [step_right (waitProtocol hpsi kappa) ring C e hne,
        updatePair_responder _ _ _ _ hne]
      rfl
    · rw [step_other (waitProtocol hpsi kappa) ring C e k hke hkj,
        updatePair_other _ _ _ _ _ hke hkj]


def PassiveConfig (C : FullConfig n psi kappa tau) : Prop :=
  forall i, Passive (raw (C i))


def CyclicLabels (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) : Prop :=
  forall e, (raw (C (ring.rightNeighbor e))).label =
    ⟨((raw (C e)).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩


def NoCapConfig (hpsi : 0 < psi) (kappa : Nat)
    (C : FullConfig n psi kappa tau) : Prop :=
  ∀ i, ¬ Cap hpsi kappa (raw (C i))


def ClockAgree (C : FullConfig n psi kappa tau) (W : WaitConfig n psi) : Prop :=
  forall i, clock (raw (C i)) = clock (W i)


def NumericAgree (C : FullConfig n psi kappa tau) (W : WaitConfig n psi) : Prop :=
  forall i, Numeric (raw (C i)) = Numeric (W i)


def RowBelow (hpsi : 0 < psi) (kappa : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (e : Fin n) : Prop :=
  Below hpsi kappa
    (waitSaturated hpsi kappa (raw (C e))
      (raw (C (ring.rightNeighbor e)))).2


def RowCap (hpsi : 0 < psi) (kappa : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (e : Fin n) : Prop :=
  Cap hpsi kappa
    (waitSaturated hpsi kappa (raw (C e))
      (raw (C (ring.rightNeighbor e)))).2


private theorem numericAgree_of_clockAgree
    (C : FullConfig n psi kappa tau) (W : WaitConfig n psi)
    (h : ClockAgree C W) : NumericAgree C W := by
  intro i
  exact numeric_of_clock_eq (h i)


/-- One real physical step before cap advances in lockstep with one literal WAIT
step on the same edge.  All structural facts needed for the next row are proved
from the current row. -/
theorem full_wait_one_step_below (hpsi : 0 < psi) (hn : 1 < n)
    (ring : DirectedRing n) (kappa tau : Nat)
    (C : FullConfig n psi kappa tau) (W : WaitConfig n psi)
    (hpass : PassiveConfig C)
    (hlabels : CyclicLabels hpsi ring C)
    (hnocap : NoCapConfig hpsi kappa C)
    (hclock : ClockAgree C W)
    (e : Fin n) (hbelow : RowBelow hpsi kappa ring C e) :
    ClockAgree (fullStep hpsi kappa tau ring C e)
      (waitStep hpsi kappa ring W e) ∧
    PassiveConfig (fullStep hpsi kappa tau ring C e) ∧
    CyclicLabels hpsi ring (fullStep hpsi kappa tau ring C e) ∧
    NoCapConfig hpsi kappa (fullStep hpsi kappa tau ring C e) := by
  have hne := rightNeighbor_ne_self_of_one_lt ring hn e
  change Below hpsi kappa
    (waitSaturated hpsi kappa (raw (C e))
      (raw (C (ring.rightNeighbor e)))).2 at hbelow
  let q := generationFullTransition hpsi kappa tau
    (C e) (C (ring.rightNeighbor e))
  let w := waitSaturated hpsi kappa
    (raw (C e)) (raw (C (ring.rightNeighbor e)))
  let z := waitSaturated hpsi kappa
    (W e) (W (ring.rightNeighbor e))
  have hloc := full_wait_clock_row_below hpsi kappa tau
    (C e) (C (ring.rightNeighbor e))
    (hpass e) (hpass (ring.rightNeighbor e)) (hlabels e) hbelow
  change clock (raw q.1) = clock w.1 ∧
    clock (raw q.2) = clock w.2 at hloc
  have hproj := wait_clock_congr hpsi kappa
    (raw (C e)) (raw (C (ring.rightNeighbor e)))
    (W e) (W (ring.rightNeighbor e))
    (hclock e) (hclock (ring.rightNeighbor e))
  change clock w.1 = clock z.1 ∧ clock w.2 = clock z.2 at hproj
  have hp := full_passive_below hpsi kappa tau
    (C e) (C (ring.rightNeighbor e))
    (hpass e) (hpass (ring.rightNeighbor e)) (hlabels e) hbelow
  change Passive (raw q.1) ∧ Passive (raw q.2) at hp
  have hs := wait_static hpsi kappa
    (raw (C e)) (raw (C (ring.rightNeighbor e)))
  change w.1.label = (raw (C e)).label ∧
    w.2.label = (raw (C (ring.rightNeighbor e))).label ∧
    w.1.count = (raw (C e)).count at hs
  have hq1label : (raw q.1).label = (raw (C e)).label := by
    have h := congrArg (fun c : Clock psi => c.label) hloc.1
    have hx : (raw q.1).label = w.1.label := by simpa [clock] using h
    exact hx.trans hs.1
  have hq2label : (raw q.2).label =
      (raw (C (ring.rightNeighbor e))).label := by
    have h := congrArg (fun c : Clock psi => c.label) hloc.2
    have hx : (raw q.2).label = w.2.label := by simpa [clock] using h
    exact hx.trans hs.2.1
  have hq1count : (raw q.1).count = w.1.count := by
    have h := congrArg (fun c : Clock psi => c.count) hloc.1
    simpa [clock] using h
  have hq2count : (raw q.2).count = w.2.count := by
    have h := congrArg (fun c : Clock psi => c.count) hloc.2
    simpa [clock] using h
  have hclock' : ClockAgree (fullStep hpsi kappa tau ring C e)
      (waitStep hpsi kappa ring W e) := by
    intro k
    by_cases hke : k = e
    · subst k
      unfold fullStep waitStep
      rw [step_left (fullProtocol hpsi kappa tau) ring C e,
        step_left (waitProtocol hpsi kappa) ring W e]
      simpa [fullProtocol, waitProtocol, q, z] using
        hloc.1.trans hproj.1
    · by_cases hkj : k = ring.rightNeighbor e
      · subst k
        unfold fullStep waitStep
        rw [step_right (fullProtocol hpsi kappa tau) ring C e hne,
          step_right (waitProtocol hpsi kappa) ring W e hne]
        simpa [fullProtocol, waitProtocol, q, z] using
          hloc.2.trans hproj.2
      · unfold fullStep waitStep
        rw [step_other (fullProtocol hpsi kappa tau) ring C e k hke hkj,
          step_other (waitProtocol hpsi kappa) ring W e k hke hkj]
        exact hclock k
  have hpass' : PassiveConfig (fullStep hpsi kappa tau ring C e) := by
    intro k
    by_cases hke : k = e
    · subst k
      unfold fullStep
      rw [step_left (fullProtocol hpsi kappa tau) ring C e]
      simpa [fullProtocol, q] using hp.1
    · by_cases hkj : k = ring.rightNeighbor e
      · subst k
        unfold fullStep
        rw [step_right (fullProtocol hpsi kappa tau) ring C e hne]
        simpa [fullProtocol, q] using hp.2
      · unfold fullStep
        rw [step_other (fullProtocol hpsi kappa tau) ring C e k hke hkj]
        exact hpass k
  have hframe : forall k,
      (raw (fullStep hpsi kappa tau ring C e k)).label = (raw (C k)).label := by
    intro k
    by_cases hke : k = e
    · subst k
      unfold fullStep
      rw [step_left (fullProtocol hpsi kappa tau) ring C e]
      simpa [fullProtocol, q] using hq1label
    · by_cases hkj : k = ring.rightNeighbor e
      · subst k
        unfold fullStep
        rw [step_right (fullProtocol hpsi kappa tau) ring C e hne]
        simpa [fullProtocol, q] using hq2label
      · unfold fullStep
        rw [step_other (fullProtocol hpsi kappa tau) ring C e k hke hkj]
  have hlabels' : CyclicLabels hpsi ring
      (fullStep hpsi kappa tau ring C e) := by
    intro x
    apply Fin.ext
    calc
      (raw (fullStep hpsi kappa tau ring C e
        (ring.rightNeighbor x))).label.val =
          (raw (C (ring.rightNeighbor x))).label.val :=
        congrArg Fin.val (hframe (ring.rightNeighbor x))
      _ = ((raw (C x)).label.val + 1) % psi := by
        have h := congrArg Fin.val (hlabels x)
        simpa using h
      _ = ((raw (fullStep hpsi kappa tau ring C e x)).label.val + 1) % psi := by
        rw [hframe x]
  have hnocap' : NoCapConfig hpsi kappa
      (fullStep hpsi kappa tau ring C e) := by
    intro k
    by_cases hke : k = e
    · subst k
      unfold fullStep
      rw [step_left (fullProtocol hpsi kappa tau) ring C e]
      change ¬ (Cap hpsi kappa (raw q.1))
      intro hc
      apply hnocap e
      refine ⟨hq1label.symm.trans hc.1, ?_⟩
      exact (hq1count.trans hs.2.2).symm.trans hc.2
    · by_cases hkj : k = ring.rightNeighbor e
      · subst k
        unfold fullStep
        rw [step_right (fullProtocol hpsi kappa tau) ring C e hne]
        change ¬ (Cap hpsi kappa (raw q.2))
        intro hc
        have hb : w.2.count < kappa := hbelow (by
          have h := congrArg (fun c : Clock psi => c.label) hloc.2
          have hx : (raw q.2).label = w.2.label := by simpa [clock] using h
          exact hx.symm.trans hc.1)
        have hwcap : w.2.count = kappa := hq2count.symm.trans hc.2
        exact (Nat.ne_of_lt hb) hwcap
      · unfold fullStep
        rw [step_other (fullProtocol hpsi kappa tau) ring C e k hke hkj]
        exact hnocap k
  exact ⟨hclock', hpass', hlabels', hnocap'⟩


def fullRun (hpsi : 0 < psi) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) : List (Fin n) -> FullConfig n psi kappa tau
  | [] => C
  | e :: rest =>
      fullRun hpsi kappa tau ring (fullStep hpsi kappa tau ring C e) rest


def waitRun (hpsi : 0 < psi) (kappa : Nat) (ring : DirectedRing n)
    (C : WaitConfig n psi) : List (Fin n) -> WaitConfig n psi
  | [] => C
  | e :: rest => waitRun hpsi kappa ring (waitStep hpsi kappa ring C e) rest


/-- This is evaluated only on actual full-host prefixes. -/
def BeforeFirstCap (hpsi : 0 < psi) (kappa tau : Nat)
    (ring : DirectedRing n) (C : FullConfig n psi kappa tau) :
    List (Fin n) -> Prop
  | [] => True
  | e :: rest =>
      RowBelow hpsi kappa ring C e ∧
      BeforeFirstCap hpsi kappa tau ring
        (fullStep hpsi kappa tau ring C e) rest


/-- `pre` is strictly before the first cap-producing scheduled row, and `e` is
that row.  Both tests inspect the literal WAIT on real full prefixes. -/
def StopsAtCap (hpsi : 0 < psi) (kappa tau : Nat)
    (ring : DirectedRing n) (C : FullConfig n psi kappa tau)
    (pre : List (Fin n)) (e : Fin n) : Prop :=
  BeforeFirstCap hpsi kappa tau ring C pre ∧
  RowCap hpsi kappa ring (fullRun hpsi kappa tau ring C pre) e


/-- One pre-cap row, computed entirely on the literal WAIT execution. -/
def WaitRowBelow (hpsi : 0 < psi) (kappa : Nat)
    (ring : DirectedRing n) (W : WaitConfig n psi) (e : Fin n) : Prop :=
  Below hpsi kappa
    (waitSaturated hpsi kappa (W e) (W (ring.rightNeighbor e))).2

/-- One cap-producing row, computed entirely on the literal WAIT execution. -/
def WaitRowCap (hpsi : 0 < psi) (kappa : Nat)
    (ring : DirectedRing n) (W : WaitConfig n psi) (e : Fin n) : Prop :=
  Cap hpsi kappa
    (waitSaturated hpsi kappa (W e) (W (ring.rightNeighbor e))).2

/-- Every row in the word is strictly before the WAIT-side first cap. -/
def WaitBeforeFirstCap (hpsi : 0 < psi) (kappa : Nat)
    (ring : DirectedRing n) (W : WaitConfig n psi) :
    List (Fin n) → Prop
  | [] => True
  | e :: rest =>
      WaitRowBelow hpsi kappa ring W e ∧
      WaitBeforeFirstCap hpsi kappa ring
        (waitStep hpsi kappa ring W e) rest

/-- WAIT-side first-cap event on one exact edge word. -/
def WaitStopsAtCap (hpsi : 0 < psi) (kappa : Nat)
    (ring : DirectedRing n) (W : WaitConfig n psi)
    (pre : List (Fin n)) (e : Fin n) : Prop :=
  WaitBeforeFirstCap hpsi kappa ring W pre ∧
  WaitRowCap hpsi kappa ring (waitRun hpsi kappa ring W pre) e

private theorem below_iff_of_clock_eq (hpsi : 0 < psi) (kappa : Nat)
    {u v : AgentState psi} (h : clock u = clock v) :
    Below hpsi kappa u ↔ Below hpsi kappa v := by
  have hl : u.label = v.label :=
    congrArg (fun c : Clock psi => c.label) h
  have hc : u.count = v.count :=
    congrArg (fun c : Clock psi => c.count) h
  constructor
  · intro hu hvt
    have hx := hu (hl.trans hvt)
    rwa [hc] at hx
  · intro hv hut
    have hx := hv (hl.symm.trans hut)
    rwa [← hc] at hx

private theorem cap_iff_of_clock_eq (hpsi : 0 < psi) (kappa : Nat)
    {u v : AgentState psi} (h : clock u = clock v) :
    Cap hpsi kappa u ↔ Cap hpsi kappa v := by
  have hl : u.label = v.label :=
    congrArg (fun c : Clock psi => c.label) h
  have hc : u.count = v.count :=
    congrArg (fun c : Clock psi => c.count) h
  constructor
  · rintro ⟨ht, hk⟩
    exact ⟨hl.symm.trans ht, hc.symm.trans hk⟩
  · rintro ⟨ht, hk⟩
    exact ⟨hl.trans ht, hc.trans hk⟩

private theorem rowBelow_iff_waitRowBelow_of_clockAgree
    (hpsi : 0 < psi) (kappa : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (W : WaitConfig n psi)
    (hclock : ClockAgree C W) (e : Fin n) :
    RowBelow hpsi kappa ring C e ↔ WaitRowBelow hpsi kappa ring W e := by
  have h := wait_clock_congr hpsi kappa
    (raw (C e)) (raw (C (ring.rightNeighbor e)))
    (W e) (W (ring.rightNeighbor e))
    (hclock e) (hclock (ring.rightNeighbor e))
  have hr :
      clock (waitSaturated hpsi kappa
        (raw (C e)) (raw (C (ring.rightNeighbor e)))).2 =
      clock (waitSaturated hpsi kappa
        (W e) (W (ring.rightNeighbor e))).2 := h.2
  change
    Below hpsi kappa
        (waitSaturated hpsi kappa
          (raw (C e)) (raw (C (ring.rightNeighbor e)))).2 ↔
      Below hpsi kappa
        (waitSaturated hpsi kappa
          (W e) (W (ring.rightNeighbor e))).2
  exact below_iff_of_clock_eq hpsi kappa hr

private theorem rowCap_iff_waitRowCap_of_clockAgree
    (hpsi : 0 < psi) (kappa : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (W : WaitConfig n psi)
    (hclock : ClockAgree C W) (e : Fin n) :
    RowCap hpsi kappa ring C e ↔ WaitRowCap hpsi kappa ring W e := by
  have h := wait_clock_congr hpsi kappa
    (raw (C e)) (raw (C (ring.rightNeighbor e)))
    (W e) (W (ring.rightNeighbor e))
    (hclock e) (hclock (ring.rightNeighbor e))
  have hr :
      clock (waitSaturated hpsi kappa
        (raw (C e)) (raw (C (ring.rightNeighbor e)))).2 =
      clock (waitSaturated hpsi kappa
        (W e) (W (ring.rightNeighbor e))).2 := h.2
  change
    Cap hpsi kappa
        (waitSaturated hpsi kappa
          (raw (C e)) (raw (C (ring.rightNeighbor e)))).2 ↔
      Cap hpsi kappa
        (waitSaturated hpsi kappa
          (W e) (W (ring.rightNeighbor e))).2
  exact cap_iff_of_clock_eq hpsi kappa hr

/-- Inductively produce the real full-prefix facts from a WAIT-only pre-cap
word.  The clock relation is derived row by row and is not an event premise. -/
private theorem wait_before_first_cap_transfer
    (hpsi : 0 < psi) (hn : 1 < n) (ring : DirectedRing n)
    (kappa tau : Nat)
    (C : FullConfig n psi kappa tau) (W : WaitConfig n psi)
    (word : List (Fin n))
    (hpass : PassiveConfig C)
    (hlabels : CyclicLabels hpsi ring C)
    (hnocap : NoCapConfig hpsi kappa C)
    (hclock : ClockAgree C W)
    (hpre : WaitBeforeFirstCap hpsi kappa ring W word) :
    BeforeFirstCap hpsi kappa tau ring C word ∧
    ClockAgree (fullRun hpsi kappa tau ring C word)
      (waitRun hpsi kappa ring W word) ∧
    PassiveConfig (fullRun hpsi kappa tau ring C word) ∧
    CyclicLabels hpsi ring (fullRun hpsi kappa tau ring C word) ∧
    NoCapConfig hpsi kappa (fullRun hpsi kappa tau ring C word) := by
  induction word generalizing C W with
  | nil =>
      exact ⟨True.intro, hclock, hpass, hlabels, hnocap⟩
  | cons e rest ih =>
      change WaitRowBelow hpsi kappa ring W e ∧
        WaitBeforeFirstCap hpsi kappa ring
          (waitStep hpsi kappa ring W e) rest at hpre
      have hbelow : RowBelow hpsi kappa ring C e :=
        (rowBelow_iff_waitRowBelow_of_clockAgree
          hpsi kappa ring C W hclock e).2 hpre.1
      have hs := full_wait_one_step_below hpsi hn ring kappa tau C W
        hpass hlabels hnocap hclock e hbelow
      have ht := ih
        (C := fullStep hpsi kappa tau ring C e)
        (W := waitStep hpsi kappa ring W e)
        hs.2.1 hs.2.2.1 hs.2.2.2 hs.1 hpre.2
      refine ⟨?_, ?_⟩
      · change RowBelow hpsi kappa ring C e ∧
          BeforeFirstCap hpsi kappa tau ring
            (fullStep hpsi kappa tau ring C e) rest
        exact ⟨hbelow, ht.1⟩
      · simpa [fullRun, waitRun] using ht.2

/-- A first-cap event measured only on literal WAIT produces the corresponding
full-host first-cap prefix on the identical raw initial configuration and word. -/
theorem wait_stop_to_full_stop (hpsi : 0 < psi) (hn : 1 < n)
    (ring : DirectedRing n) (kappa tau : Nat)
    (C : FullConfig n psi kappa tau) (pre : List (Fin n)) (e : Fin n)
    (hpass : PassiveConfig C)
    (hlabels : CyclicLabels hpsi ring C)
    (hnocap : NoCapConfig hpsi kappa C)
    (hwait : WaitStopsAtCap hpsi kappa ring (rawConfig C) pre e) :
    StopsAtCap hpsi kappa tau ring C pre e := by
  change WaitBeforeFirstCap hpsi kappa ring (rawConfig C) pre ∧
    WaitRowCap hpsi kappa ring
      (waitRun hpsi kappa ring (rawConfig C) pre) e at hwait
  rcases hwait with ⟨hpre, hcap⟩
  have hclock0 : ClockAgree C (rawConfig C) := by
    intro i
    rfl
  have ht := wait_before_first_cap_transfer hpsi hn ring kappa tau
    C (rawConfig C) pre hpass hlabels hnocap hclock0 hpre
  change BeforeFirstCap hpsi kappa tau ring C pre ∧
    RowCap hpsi kappa ring (fullRun hpsi kappa tau ring C pre) e
  refine ⟨ht.1, ?_⟩
  have hiff := rowCap_iff_waitRowCap_of_clockAgree hpsi kappa ring
    (fullRun hpsi kappa tau ring C pre)
    (waitRun hpsi kappa ring (rawConfig C) pre) ht.2.1 e
  exact hiff.2 hcap

private theorem prefix_clock_contract (hpsi : 0 < psi) (hn : 1 < n)
    (ring : DirectedRing n) (kappa tau : Nat)
    (C : FullConfig n psi kappa tau) (W : WaitConfig n psi)
    (word : List (Fin n))
    (hpass : PassiveConfig C)
    (hlabels : CyclicLabels hpsi ring C)
    (hnocap : NoCapConfig hpsi kappa C)
    (hclock : ClockAgree C W)
    (hpre : BeforeFirstCap hpsi kappa tau ring C word) :
    ClockAgree (fullRun hpsi kappa tau ring C word)
      (waitRun hpsi kappa ring W word) ∧
    PassiveConfig (fullRun hpsi kappa tau ring C word) ∧
    CyclicLabels hpsi ring (fullRun hpsi kappa tau ring C word) ∧
    NoCapConfig hpsi kappa (fullRun hpsi kappa tau ring C word) := by
  induction word generalizing C W with
  | nil =>
      exact ⟨hclock, hpass, hlabels, hnocap⟩
  | cons e rest ih =>
      change RowBelow hpsi kappa ring C e ∧
        BeforeFirstCap hpsi kappa tau ring
          (fullStep hpsi kappa tau ring C e) rest at hpre
      have hs := full_wait_one_step_below hpsi hn ring kappa tau C W
        hpass hlabels hnocap hclock e hpre.1
      have ht := ih
        (C := fullStep hpsi kappa tau ring C e)
        (W := waitStep hpsi kappa ring W e)
        hs.2.1 hs.2.2.1 hs.2.2.2 hs.1 hpre.2
      simpa [fullRun, waitRun] using ht


/-- Same raw initial word, same edge word: before first cap the actual full
execution and literal WAIT execution agree on all numeric WAIT registers. -/
theorem same_raw_prefix_before_cap (hpsi : 0 < psi) (hn : 1 < n)
    (ring : DirectedRing n) (kappa tau : Nat)
    (C : FullConfig n psi kappa tau) (word : List (Fin n))
    (hpass : PassiveConfig C)
    (hlabels : CyclicLabels hpsi ring C)
    (hnocap : NoCapConfig hpsi kappa C)
    (hpre : BeforeFirstCap hpsi kappa tau ring C word) :
    NumericAgree (fullRun hpsi kappa tau ring C word)
      (waitRun hpsi kappa ring (rawConfig C) word) ∧
    PassiveConfig (fullRun hpsi kappa tau ring C word) ∧
    CyclicLabels hpsi ring (fullRun hpsi kappa tau ring C word) ∧
    NoCapConfig hpsi kappa (fullRun hpsi kappa tau ring C word) := by
  have hclock0 : ClockAgree C (rawConfig C) := by
    intro i
    rfl
  have h := prefix_clock_contract hpsi hn ring kappa tau
    C (rawConfig C) word hpass hlabels hnocap hclock0 hpre
  exact ⟨numericAgree_of_clockAgree _ _ h.1, h.2.1, h.2.2.1, h.2.2.2⟩


/-- Stopped contract: the proof-only literal WAIT run matches the same real
prefix numerically, while the actual full-host responder reaches the terminal
cap on exactly the stopping row.  No Passive conclusion is made after cap. -/
theorem stopped_wait_projection (hpsi : 0 < psi) (hsize : 2 <= psi)
    (hn : 1 < n) (ring : DirectedRing n) (kappa tau : Nat)
    (C : FullConfig n psi kappa tau) (pre : List (Fin n)) (e : Fin n)
    (hpass : PassiveConfig C)
    (hlabels : CyclicLabels hpsi ring C)
    (hnocap : NoCapConfig hpsi kappa C)
    (hstop : StopsAtCap hpsi kappa tau ring C pre e) :
    NumericAgree (fullRun hpsi kappa tau ring C pre)
      (waitRun hpsi kappa ring (rawConfig C) pre) ∧
    (raw (fullStep hpsi kappa tau ring
      (fullRun hpsi kappa tau ring C pre) e (ring.rightNeighbor e))).count =
        kappa := by
  rcases hstop with ⟨hpre, hcap⟩
  have hrun := same_raw_prefix_before_cap hpsi hn ring kappa tau
    C pre hpass hlabels hnocap hpre
  let F := fullRun hpsi kappa tau ring C pre
  have hpF : PassiveConfig F := by
    simpa [F] using hrun.2.1
  have hlF : CyclicLabels hpsi ring F := by
    simpa [F] using hrun.2.2.1
  have hcap' : Cap hpsi kappa
      (waitSaturated hpsi kappa (raw (F e))
        (raw (F (ring.rightNeighbor e)))).2 := by
    change RowCap hpsi kappa ring F e at hcap
    exact hcap
  have hlocal := full_cap_terminal_count hpsi hsize kappa tau
    (F e) (F (ring.rightNeighbor e))
    (hpF e) (hpF (ring.rightNeighbor e)) (hlF e) hcap'
  change (raw (generationFullTransition hpsi kappa tau
    (F e) (F (ring.rightNeighbor e))).2).count = kappa at hlocal
  have hne := rightNeighbor_ne_self_of_one_lt ring hn e
  constructor
  · exact hrun.1
  · unfold fullStep
    rw [step_right (fullProtocol hpsi kappa tau) ring F e hne]
    simpa [fullProtocol] using hlocal



/-- Event-facing stopped endpoint: the assumed first-cap event belongs only to
the literal WAIT execution; the full-host stop is produced by transfer. -/
theorem stopped_wait_projection_of_wait_stop
    (hpsi : 0 < psi) (hsize : 2 ≤ psi)
    (hn : 1 < n) (ring : DirectedRing n) (kappa tau : Nat)
    (C : FullConfig n psi kappa tau) (pre : List (Fin n)) (e : Fin n)
    (hpass : PassiveConfig C)
    (hlabels : CyclicLabels hpsi ring C)
    (hnocap : NoCapConfig hpsi kappa C)
    (hwait : WaitStopsAtCap hpsi kappa ring (rawConfig C) pre e) :
    NumericAgree (fullRun hpsi kappa tau ring C pre)
      (waitRun hpsi kappa ring (rawConfig C) pre) ∧
    (raw (fullStep hpsi kappa tau ring
      (fullRun hpsi kappa tau ring C pre) e
      (ring.rightNeighbor e))).count = kappa := by
  exact stopped_wait_projection hpsi hsize hn ring kappa tau C pre e
    hpass hlabels hnocap
    (wait_stop_to_full_stop hpsi hn ring kappa tau C pre e
      hpass hlabels hnocap hwait)

end BirthWaitPassive

#print axioms BirthWaitPassive.full_cap_terminal_count
#print axioms BirthWaitPassive.full_wait_clock_row_below
#print axioms BirthWaitPassive.full_wait_one_step_below
#print axioms BirthWaitPassive.same_raw_prefix_before_cap
#print axioms BirthWaitPassive.stopped_wait_projection
#print axioms BirthWaitPassive.wait_stop_to_full_stop
#print axioms BirthWaitPassive.stopped_wait_projection_of_wait_stop
