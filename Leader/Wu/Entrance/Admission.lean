import Leader.Wu.Entrance.ComposedRow


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open B9Host B9FullCarrierHost
open WriterProducerRepair
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape


variable {n ψ κ τ : Nat}


/-- No residual writer payload or command material remains anywhere.
This is the exact admission predicate: path3, write_state, write. -/
def FinalWriterClear (C : Config n ψ κ τ) : Prop :=
  ∀ i : Fin n,
    let u := R2Coherence.raw (C i).phys
    u.path3 = none ∧ u.write_state = .none ∧ u.write = .none


/-- Operational B7 admission class.
Every edge is presently a genuine HOST service, is outside final controller
recovery, is open at the R2C layer, and its current R2 proposal changes neither
resident bits nor labels. -/
def FinalB7Admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (C : Config n ψ κ τ) : Prop :=
  FinalNoProducer C ∧ FinalWriterClear C ∧ FinalAllOpen C ∧
  (∀ e : Fin n,
    ¬ FinalGarbage hψ (C e) (C (ring.rightNeighbor e)) ∧
    port.action (C e) (C (ring.rightNeighbor e)) = .host ∧
    R2Coherence.ProposalNoWrite hψ (by decide : 0 < 2) h2
      (C e).phys (C (ring.rightNeighbor e)).phys)


/-- The requested leaderless closure interface.  This is deliberately a
named Prop, not a theorem: the truth check at the end of this file shows that
the current parameterized `FullRowPort` interface does not imply it. -/
def FinalB7AdmissionClosedObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    FinalB7Admitted hψ h2 port ring C →
    FinalLeaderless C →
    HasLeader (stepFinal hψ h2 port ring C e) ∨
      FinalB7Admitted hψ h2 port ring
        (stepFinal hψ h2 port ring C e)


/-- Erase both controller layers but retain the literal bare-R1 carrier. -/
def finalBase (C : Config n ψ κ τ) :
    BirthCheckPermitRepairLeaf.FC n ψ κ τ :=
  R2Coherence.baseProject (physicalConfig C)


theorem finalLeaderless_iff_not_hasLeader (C : Config n ψ κ τ) :
    FinalLeaderless C ↔ ¬ HasLeader C := by
  constructor
  · intro h hL
    rcases hL with ⟨i, hi⟩
    have hz := h i
    rw [hz] at hi
    cases hi
  · intro h i
    cases hi : outputFinal (C i) with
    | false => rfl
    | true => exact False.elim (h ⟨i, hi⟩)



private theorem aliveAlong_iff_avoidAlong_complement
    {S : Type} {m : Nat}
    (step : S → Fin m → S) (Good Bad : S → Prop)
    (hiff : ∀ x, Good x ↔ ¬ Bad x) :
    ∀ (x : S) (w : List (Fin m)),
      AliveAlong step Good x w ↔
        AvoidAlong step (fun _ => True) Bad x w := by
  intro x w
  induction w generalizing x with
  | nil =>
      simp only [AliveAlong, AvoidAlong, true_and]
      exact hiff x
  | cons e w ih =>
      simp only [AliveAlong, AvoidAlong, true_and]
      rw [hiff x, ih (step x e)]


/-- The two first-hit currencies are definitionally counting the same words:
every prefix is leaderless iff every prefix avoids `HasLeader`. -/
theorem aliveCount_finalLeaderless_eq_avoidCount_hasLeader
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (C : Config n ψ κ τ) (T : Nat) :
    aliveCount (stepFinal hψ h2 port ring) FinalLeaderless C T =
      avoidCount (stepFinal hψ h2 port ring)
        (fun _ : Config n ψ κ τ => True) HasLeader C T := by
  unfold aliveCount avoidCount
  apply congrArg (FixedSpanRenewalPayload.wordSum n T)
  funext w
  classical
  unfold aliveBit avoidBit
  have hw := aliveAlong_iff_avoidAlong_complement
    (stepFinal hψ h2 port ring) FinalLeaderless HasLeader
    (fun X => finalLeaderless_iff_not_hasLeader X) C w
  by_cases ha : AliveAlong (stepFinal hψ h2 port ring)
      FinalLeaderless C w
  · have hb := hw.mp ha
    simp [ha, hb]
  · have hb : ¬ AvoidAlong (stepFinal hψ h2 port ring)
        (fun _ : Config n ψ κ τ => True) HasLeader C w :=
      fun h => ha (hw.mpr h)
    simp [ha, hb]


private theorem rightNeighbor_ne_of_two
    (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  have he := e.isLt
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega


/-- Under an admitted edge, the complete physical R2C configuration produced
by `stepFinal` is exactly one `R2Coherence.step`.  No controller-table
unfolding is used: `.host` plus `FullRowPort.physical_spec` identifies the
installed physical pair. -/
private theorem physicalConfig_stepFinal_of_admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : Config n ψ κ τ) (e : Fin n)
    (hA : FinalB7Admitted hψ h2 port ring C) :
    physicalConfig (stepFinal hψ h2 port ring C e) =
      R2Coherence.step hψ h2 ring (physicalConfig C) e := by
  classical
  have hs := rightNeighbor_ne_of_two ring hn e
  have hedge := hA.2.2.2 e
  have hg := hedge.1
  have ha := hedge.2.1
  have hf : finalAction hψ h2 port
      (C e) (C (ring.rightNeighbor e)) = .host := by
    unfold finalAction
    rw [if_neg hg, ha]
  have hrow : rowFinal hψ h2 port
      (C e) (C (ring.rightNeighbor e)) =
      port.row (C e) (C (ring.rightNeighbor e)) := by
    unfold rowFinal
    rw [hf]
  have hstep : stepFinal hψ h2 port ring C e =
      B9FullCarrierHost.writeAtP ring C e
        (port.row (C e) (C (ring.rightNeighbor e))) := by
    unfold stepFinal
    rw [if_neg hs, hrow]
  have hp := port.physical_spec (C e) (C (ring.rightNeighbor e))
  simp only [ha] at hp
  calc
    physicalConfig (stepFinal hψ h2 port ring C e) =
        physicalConfig (B9FullCarrierHost.writeAtP ring C e
          (port.row (C e) (C (ring.rightNeighbor e)))) :=
      congrArg (fun D : Config n ψ κ τ => physicalConfig D) hstep
    _ = B9Host.hostStep (hostR2C (κ := κ) (τ := τ) hψ h2)
        ring (physicalConfig C) e := by
      funext i
      change
        (B9FullCarrierHost.writeAtP ring C e
          (port.row (C e) (C (ring.rightNeighbor e))) i).phys =
        B9Host.hostStep (hostR2C (κ := κ) (τ := τ) hψ h2)
          ring (physicalConfig C) e i
      by_cases hi : i = e
      · subst i
        rw [B9Host.hostStep_left]
        simp only [B9FullCarrierHost.writeAtP, if_pos rfl]
        exact hp.1
      · by_cases hj : i = ring.rightNeighbor e
        · subst i
          rw [B9Host.hostStep_right
            (hostR2C (κ := κ) (τ := τ) hψ h2)
            ring (physicalConfig C) e hs]
          simp only [B9FullCarrierHost.writeAtP,
            if_neg hs, if_pos rfl]
          exact hp.2
        · rw [B9Host.hostStep_other
            (hostR2C (κ := κ) (τ := τ) hψ h2)
            ring (physicalConfig C) e i hi hj]
          simp only [B9FullCarrierHost.writeAtP,
            if_neg hi, if_neg hj]
          rfl
    _ = R2Coherence.step hψ h2 ring (physicalConfig C) e := by
      rfl


/-- Exact same-letter final→R2C→R2→bare-R1 simulation.


Hypotheses, all explicit:
* `hn : 2 ≤ n`, excluding the B9 self-edge stutter;
* `hR2 : R2Coherence.R2R1AgreementObligation ...`, the named physical
  R2→R1 agreement leaf already exposed by `R2Coherence`;
* `hA : FinalB7Admitted ... C`, supplying no final garbage, an actual HOST
  action on this edge, all-open quarantine controls, current ProposalNoWrite,
  FinalNoProducer, and FinalWriterClear;
* `hL : FinalLeaderless C`, supplying the leaderless premise of `hR2`;
* `e`, the literal scheduler letter.


The proof uses no stronger B9/controller theorem and does not assume the
admission predicate is closed after the service. -/
theorem stepFinal_base_eq_step1_of_admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : Config n ψ κ τ) (e : Fin n)
    (hA : FinalB7Admitted hψ h2 port ring C)
    (hL : FinalLeaderless C) :
    finalBase (stepFinal hψ h2 port ring C e) =
      BirthCheckPermitRepairLeaf.step1 hψ h2 ring (finalBase C) e := by
  have hphys := physicalConfig_stepFinal_of_admitted
    hψ h2 port ring hn C e hA
  have hOpen : R2Coherence.AllOpen (physicalConfig C) := by
    intro i
    exact hA.2.2.1 i
  have hNo : R2Coherence.NoHazardAt hψ h2 ring (physicalConfig C) e := by
    exact (hA.2.2.2 e).2.2
  have hLead : R2.Leaderless (R2Coherence.project (physicalConfig C)) := by
    intro i
    change outputFinal (C i) = false
    exact hL i
  have hProd : R2.NoProducer (R2Coherence.project (physicalConfig C)) := by
    intro i
    exact hA.1 i
  have hAgree := R2Coherence.leaderless_agreement
    hψ h2 ring hR2 (physicalConfig C) e hOpen hNo hLead hProd
  change R2Coherence.baseProject
      (physicalConfig (stepFinal hψ h2 port ring C e)) =
    BirthCheckPermitRepairLeaf.step1 hψ h2 ring
      (R2Coherence.baseProject (physicalConfig C)) e
  rw [hphys]
  exact hAgree


/-- Admission first-hit mass followed by a seven-eighths admitted-state leaf.
`two_stage_escape` adds the two horizons and multiplies the denominators.
No closure of `FinalB7Admitted` is needed by this stopped two-stage theorem:
the stage-two hypothesis is already a `UniformEscapeMassOn` statement from
every admitted leaderless landing state. -/
theorem b7ComposedMass_of_admission_and_r1
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n)
    (B_A Q_A B_R : Nat) (hQ_A : 1 ≤ Q_A)
    (hAdmission :
      ∀ C : Config n ψ κ τ, FinalLeaderless C →
        Q_A * avoidCount (stepFinal hψ h2 port ring)
          FinalLeaderless (FinalB7Admitted hψ h2 port ring)
          C B_A ≤ (Q_A - 1) * n ^ B_A)
    (hR1 : UniformEscapeMassOn
      (stepFinal hψ h2 port ring) FinalLeaderless
      (FinalB7Admitted hψ h2 port ring) B_R 8) :
    B7ComposedMassObligation hψ h2 port ring
      (fun _ => True) (B_A + B_R) (Q_A * 8) := by
  have hTwo : UniformEscapeMass
      (stepFinal hψ h2 port ring) FinalLeaderless
      (B_A + B_R) (Q_A * 8) :=
    BirthTwoStageEscape.two_stage_escape
      (stepFinal hψ h2 port ring)
      FinalLeaderless (FinalB7Admitted hψ h2 port ring)
      B_A B_R Q_A 8 hQ_A (by decide)
      hAdmission (fun C hL hA => hR1 C hA hL)
  have hQpos : 0 < Q_A := by omega
  constructor
  · exact Nat.mul_pos hQpos (by decide)
  · intro C hC
    have h := hTwo C hC.2
    rw [aliveCount_finalLeaderless_eq_avoidCount_hasLeader
      hψ h2 port ring C (B_A + B_R)] at h
    exact h


/-! ## Closed truth check: the current Port interface does not imply closure


This witness is intentionally tiny: n = 2, ψ = 2.  It is a legal
`FullRowPort` for the exact `hostR2C` carrier.  Its first action is HOST, and
its physical output is exactly the host output as required by `physical_spec`.
The HOST row changes only the outer left role to `.front`; the next action is
therefore KEEP.  Literal/field-level facts are checked with `decide +kernel`.
-/
namespace TruthCheck


private theorem hψ2 : 0 < 2 := by decide
private theorem h22 : 2 ≤ 2 := by decide
private def ring2 : DirectedRing 2 := ⟨by decide⟩


private def literalR2 (i : Fin 2) : R2.Cell 2 2 32 :=
  let seed := WriterProducerRegression.clean hψ2 (fun _ => false) i
  let b := seed.base.core.core
  let b' : BoundedAgentState 2 2 :=
    { b with leader := false, shield := false, gen_ws := false }
  ⟨⟨⟨b', false⟩, 0⟩, 0⟩


private def literalR2C (i : Fin 2) : P 2 2 32 :=
  ⟨literalR2 i, ⟨.open, .none⟩⟩


private def literalFinal (i : Fin 2) : Cell 2 2 32 :=
  ⟨literalR2C i, .none, false, false⟩


private def C2 : Config 2 2 2 32 := fun i => literalFinal i


private def unstableAction (l _r : Cell 2 2 32) :
    B9FullCarrierHost.PhysicalAction :=
  if l.spliceRole = .none then .host else .keep


private def unstableRow (l r : Cell 2 2 32) :
    Cell 2 2 32 × Cell 2 2 32 :=
  if l.spliceRole = .none then
    let q := (hostR2C (κ := 2) (τ := 32) hψ2 h22).row l.phys r.phys
    (B9FullCarrierHost.CellP.setRole
        (B9FullCarrierHost.CellP.setPhysical l q.1) .front,
      B9FullCarrierHost.CellP.setPhysical r q.2)
  else
    (l, r)


private theorem unstable_spec (l r : Cell 2 2 32) :
    let w := unstableRow l r
    match unstableAction l r with
    | .keep => w.1.phys = l.phys ∧ w.2.phys = r.phys
    | .host =>
        w.1.phys =
            ((hostR2C (κ := 2) (τ := 32) hψ2 h22).row l.phys r.phys).1 ∧
        w.2.phys =
            ((hostR2C (κ := 2) (τ := 32) hψ2 h22).row l.phys r.phys).2
    | .relabel =>
        w.1.phys = l.phys ∧
        w.2.phys = (carrierLaws (ψ := 2) (κ := 2) (τ := 32)).relabel
          hψ2 l.phys r.phys := by
  by_cases h : l.spliceRole = .none
  · simp [unstableAction, unstableRow, h]
  · simp [unstableAction, unstableRow, h]


private def unstablePort : Port (κ := 2) (τ := 32) hψ2 h22 where
  action := unstableAction
  row := unstableRow
  physical_spec := unstable_spec


private theorem ring2_01 : ring2.rightNeighbor (0 : Fin 2) = 1 := by decide


private theorem ring2_10 : ring2.rightNeighbor (1 : Fin 2) = 0 := by
  decide


private theorem fin2_cases (i : Fin 2) :
    i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
  have hi : i.val < 2 := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with h0 | h1
  · left
    apply Fin.ext
    exact h0
  · right
    apply Fin.ext
    exact h1


private theorem c2_noProducer : FinalNoProducer C2 := by
  unfold FinalNoProducer
  intro i
  rcases fin2_cases i with h0 | h1
  · subst i
    change WriterProducerRepair.producerActive
      (R2Coherence.raw (C2 (0 : Fin 2)).phys) = false
    decide +kernel
  · subst i
    change WriterProducerRepair.producerActive
      (R2Coherence.raw (C2 (1 : Fin 2)).phys) = false
    decide +kernel


private theorem c2_writerClear : FinalWriterClear C2 := by
  unfold FinalWriterClear
  intro i
  rcases fin2_cases i with h0 | h1
  · subst i
    change
      (R2Coherence.raw (C2 (0 : Fin 2)).phys).path3 = none ∧
      (R2Coherence.raw (C2 (0 : Fin 2)).phys).write_state = .none ∧
      (R2Coherence.raw (C2 (0 : Fin 2)).phys).write = .none
    decide +kernel
  · subst i
    change
      (R2Coherence.raw (C2 (1 : Fin 2)).phys).path3 = none ∧
      (R2Coherence.raw (C2 (1 : Fin 2)).phys).write_state = .none ∧
      (R2Coherence.raw (C2 (1 : Fin 2)).phys).write = .none
    decide +kernel


private theorem c2_allOpen : FinalAllOpen C2 := by
  unfold FinalAllOpen
  intro i
  rcases fin2_cases i with h0 | h1
  · subst i
    change R2Coherence.OpenControl (C2 (0 : Fin 2)).phys
    exact ⟨rfl, rfl⟩
  · subst i
    change R2Coherence.OpenControl (C2 (1 : Fin 2)).phys
    exact ⟨rfl, rfl⟩


private theorem c2_notBadTicket (i : Fin 2) :
    ¬ FinalBadTicket (C2 i) := by
  intro h
  change B9ControllerRecovery.BadTicket (oldCell (C2 i)) at h
  have ht := h.1
  change false = true at ht
  cases ht


private theorem c2_notBadBacking (i j : Fin 2) :
    ¬ FinalBadBacking (C2 i) (C2 j) := by
  intro h
  change B9ControllerRecovery.BadBacking
    (oldCell (C2 i)) (oldCell (C2 j)) at h
  have hr := h.1.1
  have hz :
      B9SpliceControllerR1Table.role (oldCell (C2 i)).carrier = .none := by
    rfl
  rw [hz] at hr
  cases hr


private theorem c2_01_notLocalBarrier :
    ¬ B9SpliceControllerR1Table.LocalPreparedBarrier hψ2
      (oldCell (C2 0)).carrier (oldCell (C2 1)).carrier := by
  unfold B9SpliceControllerR1Table.LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  decide +kernel


private theorem c2_10_notLocalBarrier :
    ¬ B9SpliceControllerR1Table.LocalPreparedBarrier hψ2
      (oldCell (C2 1)).carrier (oldCell (C2 0)).carrier := by
  unfold B9SpliceControllerR1Table.LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  decide +kernel


private theorem c2_01_notGarbage :
    ¬ FinalGarbage hψ2 (C2 0) (C2 1) := by
  intro h
  change B9ControllerRecovery.Garbage hψ2
    (oldCell (C2 0)) (oldCell (C2 1)) at h
  rcases h with hS | hH
  · rcases hS with hL | hR | hB
    · exact c2_notBadTicket 0 hL
    · exact c2_notBadTicket 1 hR
    · exact c2_notBadBacking 0 1 hB
  · have hD := hH.1
    exact c2_01_notLocalBarrier hD.2


private theorem c2_10_notGarbage :
    ¬ FinalGarbage hψ2 (C2 1) (C2 0) := by
  intro h
  change B9ControllerRecovery.Garbage hψ2
    (oldCell (C2 1)) (oldCell (C2 0)) at h
  rcases h with hS | hH
  · rcases hS with hL | hR | hB
    · exact c2_notBadTicket 1 hL
    · exact c2_notBadTicket 0 hR
    · exact c2_notBadBacking 1 0 hB
  · have hD := hH.1
    exact c2_10_notLocalBarrier hD.2


private theorem c2_01_host :
    unstablePort.action (C2 0) (C2 1) = .host := by
  decide +kernel


private theorem c2_10_host :
    unstablePort.action (C2 1) (C2 0) = .host := by
  decide +kernel


private theorem c2_01_noWrite :
    R2Coherence.ProposalNoWrite hψ2 (by decide : 0 < 2) h22
      (C2 0).phys (C2 1).phys := by
  unfold R2Coherence.ProposalNoWrite
  dsimp only
  decide +kernel


private theorem c2_10_noWrite :
    R2Coherence.ProposalNoWrite hψ2 (by decide : 0 < 2) h22
      (C2 1).phys (C2 0).phys := by
  unfold R2Coherence.ProposalNoWrite
  dsimp only
  decide +kernel


private theorem c2_out0 : outputFinal (C2 0) = false := by
  decide +kernel


private theorem c2_out1 : outputFinal (C2 1) = false := by
  decide +kernel

private theorem c2_global_fields :
    FinalNoProducer C2 ∧ FinalWriterClear C2 ∧ FinalAllOpen C2 := by
  exact ⟨c2_noProducer, c2_writerClear, c2_allOpen⟩



private theorem c2_edge_fields :
    ∀ e : Fin 2,
      ¬ FinalGarbage hψ2 (C2 e) (C2 (ring2.rightNeighbor e)) ∧
      unstablePort.action (C2 e) (C2 (ring2.rightNeighbor e)) = .host ∧
      R2Coherence.ProposalNoWrite hψ2 (by decide : 0 < 2) h22
        (C2 e).phys (C2 (ring2.rightNeighbor e)).phys := by
  intro e
  rcases fin2_cases e with h0 | h1
  · subst e
    rw [ring2_01]
    exact ⟨c2_01_notGarbage, c2_01_host, c2_01_noWrite⟩
  · subst e
    rw [ring2_10]
    exact ⟨c2_10_notGarbage, c2_10_host, c2_10_noWrite⟩



private theorem c2_leaderless_fields : FinalLeaderless C2 := by
  unfold FinalLeaderless
  intro i
  rcases fin2_cases i with h0 | h1
  · subst i
    exact c2_out0
  · subst i
    exact c2_out1



private theorem c2_admitted :
    FinalB7Admitted hψ2 h22 unstablePort ring2 C2 := by
  exact ⟨c2_global_fields.1, c2_global_fields.2.1,
    c2_global_fields.2.2, c2_edge_fields⟩


private def q2 : Cell 2 2 32 × Cell 2 2 32 :=
  unstablePort.row (C2 0) (C2 1)


/-- Closed pair-level witness: HOST service, leaderless physical result, then
`.keep` classification because the left outer role became `.front`. -/
private theorem q2_field_facts :
    q2.1.spliceRole = .front ∧
    unstablePort.action q2.1 q2.2 = .keep ∧
    outputFinal q2.1 = false ∧ outputFinal q2.2 = false := by
  decide +kernel


private theorem c2_finalAction_host :
    finalAction hψ2 h22 unstablePort (C2 0) (C2 1) = .host := by
  classical
  have h := c2_edge_fields (0 : Fin 2)
  rw [ring2_01] at h
  unfold finalAction
  rw [if_neg h.1, h.2.1]


private noncomputable def D2 : Config 2 2 2 32 :=
  stepFinal hψ2 h22 unstablePort ring2 C2 0



private theorem d2_left_eq_q2 : D2 0 = q2.1 := by
  classical
  have hs : ring2.rightNeighbor (0 : Fin 2) ≠ 0 := by decide
  unfold D2 stepFinal
  rw [if_neg hs, ring2_01]
  unfold B9FullCarrierHost.writeAtP
  rw [if_pos rfl]
  unfold rowFinal
  rw [c2_finalAction_host]
  rfl


private theorem d2_right_eq_q2 : D2 1 = q2.2 := by
  classical
  have hs : ring2.rightNeighbor (0 : Fin 2) ≠ 0 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  unfold D2 stepFinal
  rw [if_neg hs, ring2_01]
  unfold B9FullCarrierHost.writeAtP
  rw [ring2_01, if_neg h10, if_pos rfl]
  unfold rowFinal
  rw [c2_finalAction_host]
  rfl

private theorem d2_left_role : (D2 0).spliceRole = .front := by
  rw [d2_left_eq_q2]
  exact q2_field_facts.1



private theorem d2_left_leader : outputFinal (D2 0) = false := by
  rw [d2_left_eq_q2]
  exact q2_field_facts.2.2.1



private theorem d2_right_leader : outputFinal (D2 1) = false := by
  rw [d2_right_eq_q2]
  exact q2_field_facts.2.2.2



-- NOT A PATCH: minimal physical closure interface needed by the intended-port proof.
-- `WriterClearBase` abbreviates path3 = none ∧ write_state = .none ∧ write = .none.
def R1B7QuietPairFrame
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) : Prop :=
  ∀ (l r : ExpiringAgentState ψ κ τ),
    l.core.core.leader = false →
    r.core.core.leader = false →
    B9Host.Aligned l r →
    (l.core.core.path3 = none ∧
      l.core.core.write_state = .none ∧ l.core.core.write = .none) →
    (r.core.core.path3 = none ∧
      r.core.core.write_state = .none ∧ r.core.core.write = .none) →
    let q := BirthCheckPermitRepair.row
      hψ (by decide : 0 < 2) h2 l r
    q.1.core.core.leader = false →
    q.2.core.core.leader = false →
    (q.1.core.core.path3 = none ∧
      q.1.core.core.write_state = .none ∧ q.1.core.core.write = .none) ∧
    (q.2.core.core.path3 = none ∧
      q.2.core.core.write_state = .none ∧ q.2.core.core.write = .none) ∧
    q.1.core.core.bit = l.core.core.bit ∧
    q.2.core.core.bit = r.core.core.bit ∧
    q.1.core.core.label = l.core.core.label ∧
    q.2.core.core.label = r.core.core.label



private theorem d2_leaderless : FinalLeaderless D2 := by
  intro i
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with h0 | h1
  · have hi : i = (0 : Fin 2) := by
      apply Fin.ext
      exact h0
    subst i
    exact d2_left_leader
  · have hi : i = (1 : Fin 2) := by
      apply Fin.ext
      exact h1
    subst i
    exact d2_right_leader


private theorem d2_action_keep :
    unstablePort.action (D2 0) (D2 (ring2.rightNeighbor 0)) = .keep := by
  rw [ring2_01]
  simp [unstablePort, unstableAction, d2_left_role]


private theorem d2_not_admitted :
    ¬ FinalB7Admitted hψ2 h22 unstablePort ring2 D2 := by
  intro hA
  have hh := (hA.2.2.2 (0 : Fin 2)).2.1
  have hk := d2_action_keep
  have bad : B9FullCarrierHost.PhysicalAction.keep = .host := hk.symm.trans hh
  cases bad


/-- The requested closure is false for the present parameterized Port
interface, even at n=2, ψ=2, and even though the first HOST result is still
leaderless.  The failing admitted-field is the successor `.host` clause. -/
theorem unstable_port_breaks_admission_closure :
    ¬ FinalB7AdmissionClosedObligation hψ2 h22 unstablePort ring2 := by
  intro hClosed
  have h := hClosed C2 0 c2_admitted c2_leaderless_fields
  change HasLeader D2 ∨
    FinalB7Admitted hψ2 h22 unstablePort ring2 D2 at h
  rcases h with hLead | hAdmit
  · exact (finalLeaderless_iff_not_hasLeader D2).1 d2_leaderless hLead
  · exact d2_not_admitted hAdmit


end TruthCheck


end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
