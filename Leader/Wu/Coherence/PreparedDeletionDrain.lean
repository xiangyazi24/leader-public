import Leader.Wu.Birth.CheckPermitRepairBirth
import Leader.Wu.Birth.ShortDoneTerminalEntranceDrain
import Leader.Wu.Entrance.FinalRowNormalized
import Leader.Wu.Entrance.PassiveAdmission
import Leader.Wu.WallSweep.FiniteCleanup


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace R2PreparedDeletionDrainLift


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  PPLLWallSweepFiniteCleanup BirthSigMoveDisposalRepair
open ExpiringK2Projection K2BirthLeaderNormalize K2BirthDispatcher
open WriterProducerRepair
open BirthShortDoneTerminalDeletionRank
open PPLLWallSweepFiniteCleanup


variable {n ψ κ τ : Nat}


private theorem deletionActive_true_fields_local
    (u : AuthorizedAgentState ψ)
    (hactive : deletionActive u = true) :
    u.core.state = .eliminate_signal ∧ u.core.path ≠ .bot := by
  cases hpath : u.core.path with
  | bot => simp [deletionActive, pathPresent, hpath] at hactive
  | some label bit =>
      have hs : u.core.state = .eliminate_signal := by
        simpa [deletionActive, pathPresent, hpath] using hactive
      exact ⟨hs, by simp⟩


private theorem normalizeDeletion_path_local
    (u : AuthorizedAgentState ψ) :
    (normalizeDeletion u).core.path = u.core.path := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareExpiringDisposal_path_local
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    (prepareExpiringDisposal hψ u).core.erase.core.path =
      u.core.erase.core.path := by
  change (prepareBoundedDisposal hψ u.core).erase.core.path =
    u.core.erase.core.path
  exact
    (congrArg (fun a : AuthorizedAgentState ψ => a.core.path)
      (erase_prepareBoundedDisposal hψ u.core)).trans
      (prepareDisposal_path hψ u.core.erase)


private theorem normalizeLeader_path_local
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    (normalizeLeader hψ u).core.erase.core.path =
      u.core.erase.core.path := by
  unfold normalizeLeader
  split <;> rfl


private theorem nonK2_path_eq_local
    {a b : ExpiringAgentState ψ κ τ} (h : nonK2 a = nonK2 b) :
    a.core.erase.core.path = b.core.erase.core.path := by
  have hp := congrArg
    (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.path) h
  change a.core.erase.core.path = b.core.erase.core.path at hp
  exact hp

private theorem authorized_active_responder_paths
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r) = true) :
    let q := BirthCheckPermitRepair.authorized
      hψ (by decide : 0 < 2) h2 κ l r
    q.1.core.path = l.core.path ∧ q.2.core.path = .bot := by
  have hrs := deletionActive_true_fields_local (normalizeDeletion r) hr
  have hlpath := normalizeDeletion_path_local l
  unfold BirthCheckPermitRepair.authorized
  dsimp only
  rw [if_pos hr]
  unfold authorizedEliminateSig authorizedReconcile
  dsimp only
  unfold eliminateSig
  rw [if_pos hrs.1]
  dsimp only
  split <;> exact ⟨hlpath, rfl⟩


private theorem bounded_active_responder_paths
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ)
    (hr : deletionActive (normalizeDeletion r.erase) = true) :
    let q := BirthCheckPermitRepair.bounded
      hψ (by decide : 0 < 2) h2 l r
    q.1.erase.core.path = l.erase.core.path ∧
      q.2.erase.core.path = .bot := by
  have he := BirthCheckPermitRepairBirth.r1_bounded_erase hψ h2 l r
  have ha := authorized_active_responder_paths
    (κ := κ) hψ h2 l.erase r.erase hr
  dsimp only at ha
  have hL := congrArg
    (fun q : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
      q.1.core.path) he
  have hR := congrArg
    (fun q : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
      q.2.core.path) he
  exact ⟨hL.trans ha.1, hR.trans ha.2⟩


private theorem tick_core_path_local (u : WCell ψ κ) :
    (tick u).agent.core.path = u.agent.core.path := by
  unfold WriterProducerRepair.tick WriterProducerRepair.put
  dsimp only
  repeat (first | rfl | (split <;> try dsimp only))


private theorem tick_erase_path_local (u : WCell ψ κ) :
    (tick u).agent.erase.core.path = u.agent.erase.core.path := by
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase]
  rw [tick_core_path_local u]


private theorem r2_bounded_active_responder_paths
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : WCell ψ κ)
    (hr : deletionActive (normalizeDeletion r.agent.erase) = true) :
    let q := R2.bounded hψ (by decide : 0 < 2) h2 l r
    q.1.agent.erase.core.path = l.agent.erase.core.path ∧
      q.2.agent.erase.core.path = .bot := by
  let b := BirthCheckPermitRepair.bounded
    hψ (by decide : 0 < 2) h2 l.agent r.agent
  have hb := bounded_active_responder_paths hψ h2 l.agent r.agent hr
  change b.1.erase.core.path = l.agent.erase.core.path ∧
    b.2.erase.core.path = .bot at hb
  have hq : R2.bounded hψ (by decide : 0 < 2) h2 l r =
      (tick ⟨b.1, l.fuel⟩, tick ⟨b.2, r.fuel⟩) := by
    unfold R2.bounded
    dsimp only
    rw [hr]
    rfl
  dsimp only
  rw [hq]
  exact ⟨(tick_erase_path_local ⟨b.1, l.fuel⟩).trans hb.1,
    (tick_erase_path_local ⟨b.2, r.fuel⟩).trans hb.2⟩


/-- R2's producer timer does not destroy responder-deletion contraction. -/
theorem r2_row_prepared_responder_delete_paths
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2.Cell ψ κ τ)
    (hactive : CurrentPreparedDeletionActive hψ r.base) :
    ((R2.row hψ (by decide : 0 < 2) h2 l r).1.base.core.erase.core.path =
        l.base.core.erase.core.path ∨
      (R2.row hψ (by decide : 0 < 2) h2 l r).1.base.core.erase.core.path = .bot) ∧
    (R2.row hψ (by decide : 0 < 2) h2 l r).2.base.core.erase.core.path = .bot := by
  let l0 := prepareExpiringDisposal hψ l.base
  let r0 := prepareExpiringDisposal hψ r.base
  let b := R2.bounded hψ (by decide : 0 < 2) h2
    ⟨l0.core, l.fuel⟩ ⟨r0.core, r.fuel⟩
  let baseL : ExpiringAgentState ψ κ τ := ⟨b.1.agent, l0.stall⟩
  let baseR : ExpiringAgentState ψ κ τ := ⟨b.2.agent, r0.stall⟩
  let eL := deletionPriorityExpireOne τ l0 baseL
  let eR := deletionPriorityExpireOne τ r0 baseR
  let z := finalPhysical hψ l.base r.base
    (normalizeLeader hψ eL) (normalizeLeader hψ eR)


  have hactive0 : deletionActive (normalizeDeletion r0.core.erase) = true := by
    simpa [CurrentPreparedDeletionActive, r0] using hactive
  have hb := r2_bounded_active_responder_paths hψ h2
    ⟨l0.core, l.fuel⟩ ⟨r0.core, r.fuel⟩ hactive0
  change b.1.agent.erase.core.path = l0.core.erase.core.path ∧
    b.2.agent.erase.core.path = .bot at hb


  have hprepL := prepareExpiringDisposal_path_local hψ l.base
  change l0.core.erase.core.path = l.base.core.erase.core.path at hprepL
  have hbaseL : baseL.core.erase.core.path = l0.core.erase.core.path := by
    simpa [baseL] using hb.1
  have hbaseR : baseR.core.erase.core.path = .bot := by
    simpa [baseR] using hb.2


  have hEL := deletionPriorityExpireOne_path_frame l0 baseL
  have hER := deletionPriorityExpireOne_path_frame r0 baseR
  change (eL.core.erase.core.path = baseL.core.erase.core.path ∨
    eL.core.erase.core.path = .bot) ∧ _ at hEL
  change (eR.core.erase.core.path = baseR.core.erase.core.path ∨
    eR.core.erase.core.path = .bot) ∧ _ at hER


  have heL : eL.core.erase.core.path = l.base.core.erase.core.path ∨
      eL.core.erase.core.path = .bot := by
    rcases hEL.1 with hkeep | hclear
    · exact .inl (hkeep.trans (hbaseL.trans hprepL))
    · exact .inr hclear
  have heR : eR.core.erase.core.path = .bot := by
    rcases hER.1 with hkeep | hclear
    · exact hkeep.trans hbaseR
    · exact hclear


  have hnL := normalizeLeader_path_local hψ eL
  have hnR := normalizeLeader_path_local hψ eR
  have hf := finalPhysical_nonK2 hψ l.base r.base
    (normalizeLeader hψ eL) (normalizeLeader hψ eR)
  have hfL := nonK2_path_eq_local hf.1
  have hfR := nonK2_path_eq_local hf.2
  change z.1.core.erase.core.path =
    (normalizeLeader hψ eL).core.erase.core.path at hfL
  change z.2.core.erase.core.path =
    (normalizeLeader hψ eR).core.erase.core.path at hfR


  have hzL : z.1.core.erase.core.path = l.base.core.erase.core.path ∨
      z.1.core.erase.core.path = .bot := by
    rcases heL with hkeep | hclear
    · exact .inl (hfL.trans (hnL.trans hkeep))
    · exact .inr (hfL.trans (hnL.trans hclear))
  have hzR : z.2.core.erase.core.path = .bot :=
    hfR.trans (hnR.trans heR)
  simpa [R2.row, l0, r0, b, baseL, baseR, eL, eR, z] using
    And.intro hzL hzR


/-- Strict two-endpoint R2 path-rank contraction. -/
theorem r2_row_prepared_responder_delete_contract
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2.Cell ψ κ τ)
    (hactive : CurrentPreparedDeletionActive hψ r.base) :
    comparisonPathMass (R2.row hψ (by decide : 0 < 2) h2 l r).1.base +
        comparisonPathMass (R2.row hψ (by decide : 0 < 2) h2 l r).2.base <
      comparisonPathMass l.base + comparisonPathMass r.base ∧
    comparisonPathMass (R2.row hψ (by decide : 0 < 2) h2 l r).1.base ≤
      comparisonPathMass l.base ∧
    comparisonPathMass (R2.row hψ (by decide : 0 < 2) h2 l r).2.base <
      comparisonPathMass r.base := by
  have hp := r2_row_prepared_responder_delete_paths hψ h2 l r hactive
  have hactive' : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hψ r.base).core.erase) = true := by
    simpa [CurrentPreparedDeletionActive] using hactive
  have hpresent := (deletionActive_true_fields_local
    (normalizeDeletion (prepareExpiringDisposal hψ r.base).core.erase)
    hactive').2
  have hn := normalizeDeletion_path_local
    (prepareExpiringDisposal hψ r.base).core.erase
  have hp0 := prepareExpiringDisposal_path_local hψ r.base
  have hrPresent : r.base.core.erase.core.path ≠ .bot := by
    intro hbot
    apply hpresent
    calc
      (normalizeDeletion
        (prepareExpiringDisposal hψ r.base).core.erase).core.path =
          (prepareExpiringDisposal hψ r.base).core.erase.core.path := hn
      _ = r.base.core.erase.core.path := hp0
      _ = .bot := hbot


  have hleft : comparisonPathMass
      (R2.row hψ (by decide : 0 < 2) h2 l r).1.base ≤
      comparisonPathMass l.base := by
    cases hi : l.base.core.erase.core.path with
    | bot =>
        have ho := hp.1.elim (fun h => h.trans hi) id
        simp [comparisonPathMass, ho, hi]
    | some lab bit =>
        cases ho : (R2.row hψ (by decide : 0 < 2) h2 l r).1.base.core.erase.core.path <;>
          simp [comparisonPathMass, ho, hi]
  have hright : comparisonPathMass
      (R2.row hψ (by decide : 0 < 2) h2 l r).2.base <
      comparisonPathMass r.base := by
    cases hi : r.base.core.erase.core.path with
    | bot => exact (hrPresent hi).elim
    | some lab bit => simp [comparisonPathMass, hp.2, hi]
  exact ⟨by omega, hleft, hright⟩


def R2PathCount (C : R2.FC n ψ κ τ) : Nat :=
  (List.ofFn (fun i : Fin n => comparisonPathMass (C i).base)).sum


def R2NoPreparedDeletion
    (hψ : 0 < ψ) (C : R2.FC n ψ κ τ) : Prop :=
  ∀ i : Fin n, deletionActive
    (normalizeDeletion (prepareExpiringDisposal hψ (C i).base).core.erase) = false


def r2Run (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : R2.FC n ψ κ τ)
    (w : List (Fin n)) : R2.FC n ψ κ τ :=
  runLocalSchedule ring (R2.row hψ (by decide : 0 < 2) h2) C w


private theorem sum_ofFn_le_local
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hfg i.succ))


private theorem sum_ofFn_lt_of_le_of_lt_local
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i)
    (j : Fin n) (hj : f j < g j) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have ht := sum_ofFn_le_local
          (fun i : Fin n => f i.succ) (fun i : Fin n => g i.succ)
          (fun i => hfg i.succ)
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjs : j'.succ = j := by
          apply Fin.ext
          simp [j']
          omega
        have ht := ih (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ) (fun i => hfg i.succ)
          j' (by rw [hjs]; exact hj)
        have hh := hfg 0
        omega


theorem r2_localStep_prepared_responder_delete_count_lt
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : R2.FC n ψ κ τ) (e : Fin n)
    (hactive : CurrentPreparedDeletionActive hψ
      (C (ring.rightNeighbor e)).base) :
    let D := localStep ring (R2.row hψ (by decide : 0 < 2) h2) C e
    R2PathCount D < R2PathCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let q := R2.row hψ (by decide : 0 < 2) h2 (C e) (C j)
  have hp := r2_row_prepared_responder_delete_contract hψ h2
    (C e) (C j) (by simpa [j] using hactive)
  let D := localStep ring (R2.row hψ (by decide : 0 < 2) h2) C e
  have hleft : D e = q.1 := by simp [D, q, localStep, j]
  have hright : D j = q.2 := by simp [D, q, localStep, j, hje]
  have hle : ∀ i, comparisonPathMass (D i).base ≤
      comparisonPathMass (C i).base := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hp.2.1
    · by_cases hij : i = j
      · subst i; rw [hright]; exact Nat.le_of_lt hp.2.2
      · have hs : D i = C i := by simp [D, localStep, hie, hij, j]
        rw [hs]
        exact Nat.le_refl _
  have hlt : comparisonPathMass (D j).base <
      comparisonPathMass (C j).base := by
    rw [hright]
    exact hp.2.2
  unfold R2PathCount
  exact sum_ofFn_lt_of_le_of_lt_local
    (fun i => comparisonPathMass (D i).base)
    (fun i => comparisonPathMass (C i).base) hle j hlt

/-- The current-host finite drain lifts to literal R2. -/
theorem exists_r2PreparedDeletionDrain
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : R2.FC n ψ κ τ) :
    ∃ schedule : List (Fin n),
      schedule.length ≤ R2PathCount C ∧
      R2NoPreparedDeletion hψ (r2Run hψ h2 ring C schedule) := by
  generalize hk : R2PathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : R2NoPreparedDeletion hψ C
      · refine ⟨[], by simp, ?_⟩
        simpa [r2Run, runLocalSchedule] using hnone
      · have hexists : ∃ j : Fin n,
            CurrentPreparedDeletionActive hψ (C j).base := by
          apply Classical.byContradiction
          intro hnot
          apply hnone
          intro i
          cases hi : deletionActive
            (normalizeDeletion
              (prepareExpiringDisposal hψ (C i).base).core.erase) with
          | false => rfl
          | true =>
              exact False.elim (hnot ⟨i, by
                simpa [CurrentPreparedDeletionActive] using hi⟩)
        obtain ⟨j, hj⟩ := hexists
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j :=
          rightNeighbor_leftNeighbor_wall ring j
        let C₁ := localStep ring
          (R2.row hψ (by decide : 0 < 2) h2) C e
        have hstep := r2_localStep_prepared_responder_delete_count_lt
          hψ h2 ring hn C e (by simpa [hneighbor] using hj)
        change R2PathCount C₁ < R2PathCount C at hstep
        have hlt : R2PathCount C₁ < k := by rw [← hk]; exact hstep
        obtain ⟨tail, hlen, htail⟩ := ih (R2PathCount C₁) hlt C₁ rfl
        refine ⟨e :: tail, ?_, ?_⟩
        · simp only [List.length_cons]; omega
        · simpa [r2Run, C₁, runLocalSchedule] using htail


end R2PreparedDeletionDrainLift


namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open B9Host B9FullCarrierHost WriterProducerRepair
open BirthShortDoneTerminalDeletionRank
open PPLLWallSweepFiniteCleanup


variable {n ψ κ τ : Nat}


/-- Internal first-hit stage; not a restriction on the initial source. -/
def FinalPreparedDeletionDrained
    (hψ : 0 < ψ) (C : Config n ψ κ τ) : Prop :=
  R2PreparedDeletionDrainLift.R2NoPreparedDeletion hψ
    (fun i => (C i).phys.phys)


/-- Exact final HOST/non-garbage lift of the R2 deletion contraction.
The OPEN/no-write premises are branch-local and are discharged by case split. -/
theorem rowFinalNormalized_host_prepared_responder_delete_contract
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ)
    (hg : ¬ FinalGarbage hψ l r)
    (hhost : port.action l r = .host)
    (hl : R2Coherence.OpenControl l.phys)
    (hr : R2Coherence.OpenControl r.phys)
    (hsafe : R2Coherence.ProposalNoWrite
      hψ (by decide : 0 < 2) h2 l.phys r.phys)
    (hactive : CurrentPreparedDeletionActive hψ r.phys.phys.base) :
    comparisonPathMass
        (rowFinalNormalized hψ h2 port l r).1.phys.phys.base +
      comparisonPathMass
        (rowFinalNormalized hψ h2 port l r).2.phys.phys.base <
    comparisonPathMass l.phys.phys.base +
      comparisonPathMass r.phys.phys.base := by
  have hsweep : ¬ finalMalformedActiveSweep l.phys r.phys := by
    simp [finalMalformedActiveSweep, hl.2]
  have hrelease : ¬ finalMalformedActiveRelease l.phys r.phys := by
    simp [finalMalformedActiveRelease, hl.2]
  have hmixed : ¬ finalTokenFreeMixed l.phys r.phys := by
    simp [finalTokenFreeMixed, hl.1, hr.1, hl.2, hr.2]
  have hnorm := rowFinalNormalized_eq_rowFinal_of_no_normalization
    hψ h2 port l r hg hsweep hrelease hmixed
  have hrow : rowFinal hψ h2 port l r = port.row l r := by
    classical
    unfold rowFinal finalAction
    rw [if_neg hg, hhost]
  rw [hnorm, hrow]
  have hp := port.physical_spec l r
  simp only [hhost, hostR2C] at hp
  have hc := R2Coherence.row_phys_eq_r2_of_open_no_write
    hψ (by decide : 0 < 2) h2 l.phys r.phys
    hl.1 hr.1 hl.2 hr.2 hsafe
  dsimp only at hc
  have hcL := congrArg Prod.fst hc
  have hcR := congrArg Prod.snd hc
  have hbaseL :
      (port.row l r).1.phys.phys.base =
        (R2.row hψ (by decide : 0 < 2) h2
          l.phys.phys r.phys.phys).1.base := by
    calc
      (port.row l r).1.phys.phys.base =
          (R2Coherence.row hψ (by decide : 0 < 2) h2
            l.phys r.phys).1.phys.base := by
        exact congrArg
          (fun u : R2Coherence.Cell ψ κ τ => u.phys.base) hp.1
      _ = (R2.row hψ (by decide : 0 < 2) h2
            l.phys.phys r.phys.phys).1.base := by
        exact congrArg (fun u : R2.Cell ψ κ τ => u.base) hcL
  have hbaseR :
      (port.row l r).2.phys.phys.base =
        (R2.row hψ (by decide : 0 < 2) h2
          l.phys.phys r.phys.phys).2.base := by
    calc
      (port.row l r).2.phys.phys.base =
          (R2Coherence.row hψ (by decide : 0 < 2) h2
            l.phys r.phys).2.phys.base := by
        exact congrArg
          (fun u : R2Coherence.Cell ψ κ τ => u.phys.base) hp.2
      _ = (R2.row hψ (by decide : 0 < 2) h2
            l.phys.phys r.phys.phys).2.base := by
        exact congrArg (fun u : R2.Cell ψ κ τ => u.base) hcR
  have hcontract :=
    (R2PreparedDeletionDrainLift.r2_row_prepared_responder_delete_contract
      hψ h2 l.phys.phys r.phys.phys hactive).1
  calc
    comparisonPathMass (port.row l r).1.phys.phys.base +
        comparisonPathMass (port.row l r).2.phys.phys.base =
      comparisonPathMass
          (R2.row hψ (by decide : 0 < 2) h2
            l.phys.phys r.phys.phys).1.base +
        comparisonPathMass
          (R2.row hψ (by decide : 0 < 2) h2
            l.phys.phys r.phys.phys).2.base := by
      exact congr
        (congrArg (fun a b : Nat => a + b)
          (congrArg
            (fun u : ExpiringAgentState ψ κ τ => comparisonPathMass u) hbaseL))
        (congrArg
          (fun u : ExpiringAgentState ψ κ τ => comparisonPathMass u) hbaseR)
    _ < comparisonPathMass l.phys.phys.base +
          comparisonPathMass r.phys.phys.base := hcontract

/-- Proof-only normalized scheduler shadow; no existing executable definition is changed. -/
noncomputable def preparedDrainShadowStep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : Config n ψ κ τ) (e : Fin n) : Config n ψ κ τ := by
  classical
  exact if ring.rightNeighbor e = e then
    if FinalGarbage hψ (C e) (C e) then
      B9FullCarrierHost.writeAtP ring C e
        (clearFinalControl (C e), C e)
    else C
  else
    B9FullCarrierHost.writeAtP ring C e
      (rowFinalNormalized hψ h2
        (concretePortLocal (κ := κ) (τ := τ) hψ h2)
        (C e) (C (ring.rightNeighbor e)))


/-- The residual OPEN target after the internal prepared-deletion first hit. -/
def OpenNoGlobalFixedAfterPreparedDeletionDrain
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : Config n ψ κ τ,
    FinalLeaderless C →
    FinalAllOpen C →
    FinalPreparedDeletionDrained hψ C →
    ¬ ConcreteB7AdmittedPassive hψ h2 ring C →
    ∃ e : Fin n,
      preparedDrainShadowStep (κ := κ) (τ := τ) hψ h2 ring C e ≠ C


/-- Protocol-faithful global replacement for the false per-edge target:
leaderless + non-admitted implies progress on some scheduler edge. -/
def LeaderlessNonAdmittedSomeEdgeProgress
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : Config n ψ κ τ,
    FinalLeaderless C →
    ¬ ConcreteB7AdmittedPassive hψ h2 ring C →
    ∃ e : Fin n,
      preparedDrainShadowStep (κ := κ) (τ := τ) hψ h2 ring C e ≠ C


end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
