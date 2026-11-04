import Leader.Wu.Birth.ShortDoneTerminalHost
import Leader.Wu.WallSweep.FiniteCleanup
import Leader.Wu.Elimination.BirthDispatcherWitnesses


/-!
# Current TerminalHost responder-deletion rank contraction

This is a proof-only consumer of the existing current host.  The executable
transition remains `BirthShortDoneTerminalHost.row`.
-/


namespace BirthShortDoneTerminalDeletionRank


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  PPLLWallSweepFiniteCleanup BirthSigMoveDisposalRepair

open ExpiringK2Projection K2BirthLeaderNormalize K2BirthDispatcher
  BirthShortDoneTerminalHost


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


variable {ψ width κ τ n : Nat}


/-- Exactly the responder guard reached by the current host after disposal
preparation and its authorized `normalizeDeletion`. -/
def CurrentPreparedDeletionActive
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) : Prop :=
  deletionActive
    (normalizeDeletion (prepareExpiringDisposal hψ u).core.erase) = true


private theorem deletionActive_true_fields_local
    (u : AuthorizedAgentState ψ)
    (hactive : deletionActive u = true) :
    u.core.state = .eliminate_signal ∧ u.core.path ≠ .bot := by
  cases hpath : u.core.path with
  | bot =>
      simp [deletionActive, pathPresent, hpath] at hactive
  | some label bit =>
      have hstate : u.core.state = .eliminate_signal := by
        simpa [deletionActive, pathPresent, hpath] using hactive
      exact ⟨hstate, by simp⟩


private theorem normalizeDeletion_path_local
    (u : AuthorizedAgentState ψ) :
    (normalizeDeletion u).core.path = u.core.path := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareExpiringDisposal_path_local
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    (prepareExpiringDisposal hψ u).core.erase.core.path =
      u.core.erase.core.path := by
  change
    (prepareBoundedDisposal hψ u.core).erase.core.path =
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
    {a b : ExpiringAgentState ψ κ τ}
    (h : nonK2 a = nonK2 b) :
    a.core.erase.core.path = b.core.erase.core.path := by
  have hp := congrArg
    (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.path) h
  change a.core.erase.core.path = b.core.erase.core.path at hp
  exact hp


/-! ## The current authorized responder branch -/


/-- Under the literal current normalized responder guard, the current
TerminalHost authorized entry takes `authorizedEliminateSig`: the initiator
keeps its physical path and the responder loses its physical path.  No
ordinary DONE/CHECK branch is entered. -/
private theorem doneMetadataAuthorizedEntryWidth_active_responder_paths
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r) = true) :
    let q := doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r
    q.1.core.path = l.core.path ∧ q.2.core.path = .bot := by
  have hrs :=
    deletionActive_true_fields_local (normalizeDeletion r) hr
  have hlpath := normalizeDeletion_path_local l
  unfold doneMetadataAuthorizedEntryWidth
  dsimp only
  rw [if_pos hr]
  unfold authorizedEliminateSig authorizedReconcile
  dsimp only
  unfold eliminateSig
  rw [if_pos hrs.1]
  dsimp only
  split <;> exact ⟨hlpath, rfl⟩


/-- The current bounded reification is path-exact, so the same deletion fact
holds on its actual finite output. -/
private theorem doneMetadataBoundedEntryWidth_active_responder_paths
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ)
    (hr : deletionActive (normalizeDeletion r.erase) = true) :
    let q := doneMetadataBoundedEntryWidth hψ hwidth hle l r
    q.1.erase.core.path = l.erase.core.path ∧
      q.2.erase.core.path = .bot := by
  have he := doneMetadataBoundedEntryWidth_erase
    hψ hwidth hle l r
  have ha := doneMetadataAuthorizedEntryWidth_active_responder_paths
    hψ hwidth hle κ l.erase r.erase hr
  dsimp only at ha
  have hL := congrArg
    (fun q : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
      q.1.core.path) he
  have hR := congrArg
    (fun q : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
      q.2.core.path) he
  exact ⟨hL.trans ha.1, hR.trans ha.2⟩


/-! ## Full current row: preparation, reification, expiry, normalization, K2 -/


/-- The actual complete current row can only retain or clear the initiator
path, and it clears the active prepared responder path.  This statement is
about `BirthShortDoneTerminalHost.row`, after both expiry calls,
`normalizeLeader`, and `finalPhysical`. -/
theorem row_prepared_responder_delete_paths
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hactive : CurrentPreparedDeletionActive hψ r) :
    ((row hψ hwidth hle l r).1.core.erase.core.path =
        l.core.erase.core.path ∨
      (row hψ hwidth hle l r).1.core.erase.core.path = .bot) ∧
      (row hψ hwidth hle l r).2.core.erase.core.path = .bot := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let b := doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core
  let baseL : ExpiringAgentState ψ κ τ := ⟨b.1, l0.stall⟩
  let baseR : ExpiringAgentState ψ κ τ := ⟨b.2, r0.stall⟩
  let eL := deletionPriorityExpireOne τ l0 baseL
  let eR := deletionPriorityExpireOne τ r0 baseR

  have hactive0 :
      deletionActive (normalizeDeletion r0.core.erase) = true := by
    simpa [CurrentPreparedDeletionActive, r0] using hactive

  have hb := doneMetadataBoundedEntryWidth_active_responder_paths
    hψ hwidth hle l0.core r0.core hactive0
  change
    b.1.erase.core.path = l0.core.erase.core.path ∧
      b.2.erase.core.path = .bot at hb

  have hprepL := prepareExpiringDisposal_path_local hψ l
  change l0.core.erase.core.path = l.core.erase.core.path at hprepL

  have hbaseL :
      baseL.core.erase.core.path = l0.core.erase.core.path := by
    simpa [baseL] using hb.1
  have hbaseR : baseR.core.erase.core.path = .bot := by
    simpa [baseR] using hb.2

  have hEL := deletionPriorityExpireOne_path_frame l0 baseL
  change
    (eL.core.erase.core.path = baseL.core.erase.core.path ∨
      eL.core.erase.core.path = .bot) ∧ _ at hEL
  have hER := deletionPriorityExpireOne_path_frame r0 baseR
  change
    (eR.core.erase.core.path = baseR.core.erase.core.path ∨
      eR.core.erase.core.path = .bot) ∧ _ at hER

  have heL :
      eL.core.erase.core.path = l.core.erase.core.path ∨
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

  have hf := K2BirthDispatcher.finalPhysical_nonK2 hψ l r
    (normalizeLeader hψ eL) (normalizeLeader hψ eR)
  have hfL := nonK2_path_eq_local hf.1
  have hfR := nonK2_path_eq_local hf.2

  have hw :
      row hψ hwidth hle l r =
        K2BirthDispatcher.finalPhysical hψ l r
          (normalizeLeader hψ eL) (normalizeLeader hψ eR) := by
    simpa [l0, r0, b, baseL, baseR, eL, eR] using
      (row_real_host_witness hψ hwidth hle l r)

  rw [hw]
  constructor
  · rcases heL with hkeep | hclear
    · exact .inl (hfL.trans (hnL.trans hkeep))
    · exact .inr (hfL.trans (hnL.trans hclear))
  · exact hfR.trans (hnR.trans heR)


/-- Strict two-endpoint contraction of the original physical path rank for the
actual current complete row.  The responder is known to contribute one unit
on input because preparation and normalization preserve its present path. -/
theorem row_prepared_responder_delete_contract
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hactive : CurrentPreparedDeletionActive hψ r) :
    comparisonPathMass (row hψ hwidth hle l r).1 +
        comparisonPathMass (row hψ hwidth hle l r).2 <
      comparisonPathMass l + comparisonPathMass r ∧
      comparisonPathMass (row hψ hwidth hle l r).1 ≤
        comparisonPathMass l ∧
      comparisonPathMass (row hψ hwidth hle l r).2 <
        comparisonPathMass r := by
  have hp := row_prepared_responder_delete_paths
    hψ hwidth hle l r hactive

  have hactive' :
      deletionActive
        (normalizeDeletion (prepareExpiringDisposal hψ r).core.erase) = true := by
    simpa [CurrentPreparedDeletionActive] using hactive
  have hrPreparedPresent :=
    (deletionActive_true_fields_local
      (normalizeDeletion (prepareExpiringDisposal hψ r).core.erase)
      hactive').2
  have hrNormalize :=
    normalizeDeletion_path_local
      (prepareExpiringDisposal hψ r).core.erase
  have hrPrepare := prepareExpiringDisposal_path_local hψ r
  have hrInputPresent : r.core.erase.core.path ≠ .bot := by
    intro hrbot
    apply hrPreparedPresent
    calc
      (normalizeDeletion
          (prepareExpiringDisposal hψ r).core.erase).core.path =
          (prepareExpiringDisposal hψ r).core.erase.core.path :=
        hrNormalize
      _ = r.core.erase.core.path := hrPrepare
      _ = .bot := hrbot

  have hleftMass :
      comparisonPathMass (row hψ hwidth hle l r).1 ≤
        comparisonPathMass l := by
    cases hlIn : l.core.erase.core.path with
    | bot =>
        have hout :
            (row hψ hwidth hle l r).1.core.erase.core.path = .bot :=
          hp.1.elim (fun hkeep => hkeep.trans hlIn) id
        simp [comparisonPathMass, hout, hlIn]
    | some lLabel lBit =>
        cases hout :
            (row hψ hwidth hle l r).1.core.erase.core.path <;>
          simp [comparisonPathMass, hout, hlIn]

  have hrightMass :
      comparisonPathMass (row hψ hwidth hle l r).2 <
        comparisonPathMass r := by
    cases hrIn : r.core.erase.core.path with
    | bot => exact (hrInputPresent hrIn).elim
    | some rLabel rBit =>
        simp [comparisonPathMass, hp.2, hrIn]

  exact ⟨by omega, hleftMass, hrightMass⟩


/-! ## Exact global count lift -/


private theorem sum_ofFn_le_local
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))


private theorem sum_ofFn_lt_of_le_of_lt_local
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i)
    (j : Fin n) (hj : f j < g j) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail := sum_ofFn_le_local
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ)
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
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          simp [j']
          omega
        have htail := ih
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ)
          (fun i => hfg i.succ) j' (by rw [hjsucc]; exact hj)
        have hhead := hfg 0
        omega


/-- Scheduling a distinct predecessor of a current prepared-active responder
strictly decreases the existing global `comparisonPathCount`. -/
theorem localStep_prepared_responder_delete_count_lt
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hactive : CurrentPreparedDeletionActive hψ
      (C (ring.rightNeighbor e))) :
    let D := localStep ring
      (BirthShortDoneTerminalHost.row hψ hwidth hle) C e
    comparisonPathCount D < comparisonPathCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let q := BirthShortDoneTerminalHost.row hψ hwidth hle (C e) (C j)
  have hpair := row_prepared_responder_delete_contract
    hψ hwidth hle (C e) (C j) (by simpa [j] using hactive)
  change
    comparisonPathMass q.1 + comparisonPathMass q.2 <
        comparisonPathMass (C e) + comparisonPathMass (C j) ∧
      comparisonPathMass q.1 ≤ comparisonPathMass (C e) ∧
      comparisonPathMass q.2 < comparisonPathMass (C j) at hpair

  let D := localStep ring
    (BirthShortDoneTerminalHost.row hψ hwidth hle) C e
  have hleft : D e = q.1 := by
    simp [D, q, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]

  have hmassLe : ∀ i,
      comparisonPathMass (D i) ≤ comparisonPathMass (C i) := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hpair.2.1
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact Nat.le_of_lt hpair.2.2
      · have hsame : D i = C i := by
          simp [D, localStep, hie, hij, j]
        rw [hsame]
        exact Nat.le_refl _

  have hmassLt :
      comparisonPathMass (D j) < comparisonPathMass (C j) := by
    rw [hright]
    exact hpair.2.2

  change comparisonPathCount D < comparisonPathCount C
  unfold comparisonPathCount
  exact sum_ofFn_lt_of_le_of_lt_local
    (fun i => comparisonPathMass (D i))
    (fun i => comparisonPathMass (C i))
    hmassLe j hmassLt


/-! ## Existing concrete branch witness -/


/-- The repository's existing responder-disposal state inhabits the exact
prepared/normalized guard used above. -/
theorem responderDisposal_guard_witness :
    CurrentPreparedDeletionActive (by decide)
      K2BirthDispatcher.Witnesses.responderDisposal := by
  simpa [CurrentPreparedDeletionActive] using
    K2BirthDispatcher.Witnesses.disposal_responder_priority.1


/-- Consequently the actual current TerminalHost row on that existing witness
has strict two-endpoint path-rank contraction. -/
theorem responderDisposal_current_row_contract :
    let l := ExpiringK2Projection.Example.hostLeft
    let r := K2BirthDispatcher.Witnesses.responderDisposal
    let q := BirthShortDoneTerminalHost.row
      (by decide) (by decide) (Nat.le_refl 2) l r
    comparisonPathMass q.1 + comparisonPathMass q.2 <
      comparisonPathMass l + comparisonPathMass r := by
  dsimp only
  exact
    (row_prepared_responder_delete_contract
      (ψ := 2) (width := 2) (κ := 2) (τ := 3)
      (by decide) (by decide) (Nat.le_refl 2)
      ExpiringK2Projection.Example.hostLeft
      K2BirthDispatcher.Witnesses.responderDisposal
      responderDisposal_guard_witness).1


end BirthShortDoneTerminalDeletionRank
