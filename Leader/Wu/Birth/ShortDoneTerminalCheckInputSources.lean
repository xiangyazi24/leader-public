import Leader.Wu.Birth.ShortDoneTerminalBirthSources

namespace BirthShortDoneTerminalCheckInputSources

open PPLL PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthShortDoneTerminalEntryCut
open BirthShortDoneTerminalBirthSources

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ : Nat}

/-- Exact raw condition under which `checkSigSetReady` can present READY on a
fixed physical path.  The first disjunct permits an already-stale READY state;
the second is the literal SetReady guard. -/
def ReadyInputAt (u : AgentState ψ) (pathLabel : Nat) : Prop :=
  u.state = .CHECK_ready ∨
    (u.label.val = pathLabel ∧
      u.state ≠ .depart ∧ u.state ≠ .equal ∧
      u.state ≠ .larger ∧ u.state ≠ .less)

/-- Input-only necessary kernel guard for a new CHECK responder leader.
The one stage-local expression is the literal left CHECK prefix computed only
from the two raw input records; no CHECK output field occurs here. -/
def CheckFollowerBirthInput (hψ : 0 < ψ)
    (l r : AgentState ψ) : Prop :=
  r.leader = false ∧
  r.label = ⟨ψ - 1, by omega⟩ ∧
  (r.state = .equal ∨
    ∃ pathLabel pathBit : Nat,
      r.path = .some pathLabel pathBit ∧
      ReadyInputAt r pathLabel ∧
      (checkSigCheckL hψ (checkSigSetReady l)).label.val < ψ - 1 ∧
      (checkSigCheckL hψ (checkSigSetReady l)).state = .equal ∧
      checkBit r.bit pathBit = .equal)

private theorem setReady_path (u : AgentState ψ) :
    (checkSigSetReady u).path = u.path := by
  unfold checkSigSetReady
  repeat' (first | rfl | split)

private theorem setReady_bit (u : AgentState ψ) :
    (checkSigSetReady u).bit = u.bit := by
  unfold checkSigSetReady
  cases u.path <;> repeat (first | rfl | split)

private theorem setResult_state (u : AgentState ψ) :
    (checkSigSetResult u).state = u.state := by
  cases hstate : u.state <;> simp [checkSigSetResult, hstate]

private theorem input_equal_of_setReady_equal (u : AgentState ψ)
    (h : (checkSigSetReady u).state = .equal) : u.state = .equal := by
  cases hp : u.path with
  | bot => simpa [checkSigSetReady, hp] using h
  | some pathLabel pathBit =>
      by_cases hg :
          u.label.val = pathLabel ∧
            u.state ≠ .depart ∧ u.state ≠ .equal ∧
            u.state ≠ .larger ∧ u.state ≠ .less
      · have hf : False := by
          simpa [checkSigSetReady, hp, hg] using h
        exact hf.elim
      · simpa [checkSigSetReady, hp, hg] using h

private theorem readyInputAt_of_setReady
    (u : AgentState ψ) {pathLabel pathBit : Nat}
    (hp : u.path = .some pathLabel pathBit)
    (h : (checkSigSetReady u).state = .CHECK_ready) :
    ReadyInputAt u pathLabel := by
  unfold ReadyInputAt
  by_cases hg :
      u.label.val = pathLabel ∧
        u.state ≠ .depart ∧ u.state ≠ .equal ∧
        u.state ≠ .larger ∧ u.state ≠ .less
  · exact Or.inr hg
  · exact Or.inl (by simpa [checkSigSetReady, hp, hg] using h)

/-- Everything after `checkSigCheckR` changes responder state only via
`checkSigSetResult` (which frames state) and then the final leader assignment. -/
private theorem checkSig_responder_preLeader_state
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    (checkSig hψ l r).2.state =
      (checkSigCheckR hψ
        (checkSigCheckL hψ (checkSigSetReady l))
        (checkSigSetReady r)).state := by
  unfold checkSig
  dsimp only
  generalize checkSigCheckR hψ
      (checkSigCheckL hψ (checkSigSetReady l))
      (checkSigSetReady r) = q
  have hs := setResult_state q
  split <;> exact hs

/-- Literal raw Algorithm-11 necessity.  `PPLLVerify` supplies only the fact
that the final assignment must have seen terminal/equal; the proof below pulls
that equality back through SetResult and then classifies the actual SetReady /
CheckR inputs. -/
theorem checkSig_follower_birth_input
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hold : r.leader = false)
    (hout : (checkSig hψ l r).2.leader = true) :
    CheckFollowerBirthInput hψ l r := by
  have ht := PPLLVerify.checkSig_new_responder_leader_requires_terminal_equal
    hψ l r hout hold
  have hlabel := (PPLLVerify.checkSig_labels_eq hψ l r).2
  refine ⟨hold, hlabel.symm.trans ht.1, ?_⟩
  by_cases hstale : r.state = .equal
  · exact Or.inl hstale
  · right
    have heq :
        (checkSigCheckR hψ
          (checkSigCheckL hψ (checkSigSetReady l))
          (checkSigSetReady r)).state = .equal :=
      (checkSig_responder_preLeader_state hψ l r).symm.trans ht.2
    cases hp : r.path with
    | bot =>
        have heq' := heq
        unfold checkSigCheckR at heq'
        rw [setReady_path r, hp] at heq'
        dsimp only at heq'
        exact (hstale (input_equal_of_setReady_equal r heq')).elim
    | some pathLabel pathBit =>
        have heq' := heq
        unfold checkSigCheckR at heq'
        rw [setReady_path r, hp] at heq'
        dsimp only at heq'
        by_cases hl :
            (checkSigCheckL hψ (checkSigSetReady l)).label.val < ψ - 1 ∧
            (checkSigCheckL hψ (checkSigSetReady l)).state = .equal
        · rw [if_pos hl] at heq'
          by_cases hready : (checkSigSetReady r).state = .CHECK_ready
          · rw [if_pos hready] at heq'
            change checkBit (checkSigSetReady r).bit pathBit = .equal at heq'
            rw [setReady_bit r] at heq'
            exact ⟨pathLabel, pathBit, rfl,
              readyInputAt_of_setReady r hp hready,
              hl.1, hl.2, heq'⟩
          · rw [if_neg hready] at heq'
            exact (hstale (input_equal_of_setReady_equal r heq')).elim
        · rw [if_neg hl] at heq'
          exact (hstale (input_equal_of_setReady_equal r heq')).elim

/-- Authorized reconciliation does not alter the raw CHECK core. -/
theorem authorizedCheckSig_follower_birth_input
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hold : r.core.leader = false)
    (hout : (authorizedCheckSig hψ l r).2.core.leader = true) :
    CheckFollowerBirthInput hψ l.core r.core := by
  change (checkSig hψ l.core r.core).2.leader = true at hout
  exact checkSig_follower_birth_input hψ l.core r.core hold hout

/-- The no-DONE/no-TOSS/no-CONGEST guards are retained verbatim, but the
last conjunct is now entirely input-side. -/
def ActualCheckBirthInput (hψ : 0 < ψ)
    (b : AuthorizedAgentState ψ × AuthorizedAgentState ψ) : Prop :=
  b.1.core.state ≠ .done ∧ b.2.core.state ≠ .done ∧
  b.1.core.state ≠ .toss ∧ b.2.core.state ≠ .toss ∧
  b.1.core.state ≠ .congest ∧ b.2.core.state ≠ .congest ∧
  CheckFollowerBirthInput hψ b.1.core b.2.core

theorem actualCheckBirth_to_input (hψ : 0 < ψ)
    (b : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (h : ActualCheckBirth hψ b) : ActualCheckBirthInput hψ b := by
  rcases h with ⟨hdl, hdr, htl, htr, hcl, hcr, hf, hout⟩
  exact ⟨hdl, hdr, htl, htr, hcl, hcr,
    authorizedCheckSig_follower_birth_input hψ b.1 b.2 hf hout⟩

/-- Refine the green census on the same prepared/normalized finite
carrier.  No reachability or arbitrary-state exclusion is added. -/
theorem birthEvent_sources_input (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (h : BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle l r = true) :
    let pl := prepareExpiringDisposal hψ l
    let pr := prepareExpiringDisposal hψ r
    let l0 := normalizeDeletion pl.core.erase
    let r0 := normalizeDeletion pr.core.erase
    let b := doneBeforeCheckEntryWidth hψ hwidth hle κ l0 r0
    deletionActive r0 = false ∧ deletionActive l0 = false ∧
      (PPrimeBarrierBirthGuard hψ l0 r0 ∨ ActualCheckBirthInput hψ b) := by
  have hs := BirthShortDoneTerminalBirthSources.birthEvent_sources
    hψ hwidth hle l r h
  dsimp only at hs ⊢
  rcases hs with ⟨hr, hl, hp | hc⟩
  · exact ⟨hr, hl, Or.inl hp⟩
  · exact ⟨hr, hl, Or.inr (actualCheckBirth_to_input hψ _ hc)⟩

/-- Local contrapositive for constructing a `NoBirthAlong` clause: rule out
only the two source predicates on this actual prepared edge.  This is not an
unconditional arbitrary-state no-birth theorem. -/
theorem birthEvent_false_of_no_input_sources
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hp :
      let pl := prepareExpiringDisposal hψ l
      let pr := prepareExpiringDisposal hψ r
      let l0 := normalizeDeletion pl.core.erase
      let r0 := normalizeDeletion pr.core.erase
      ¬ PPrimeBarrierBirthGuard hψ l0 r0)
    (hc :
      let pl := prepareExpiringDisposal hψ l
      let pr := prepareExpiringDisposal hψ r
      let l0 := normalizeDeletion pl.core.erase
      let r0 := normalizeDeletion pr.core.erase
      let b := doneBeforeCheckEntryWidth hψ hwidth hle κ l0 r0
      ¬ ActualCheckBirthInput hψ b) :
    BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle l r = false := by
  cases hb : BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle l r with
  | false => rfl
  | true =>
      have hs := birthEvent_sources_input hψ hwidth hle l r hb
      dsimp only at hp hc hs
      rcases hs.2.2 with hP | hC
      · exact (hp hP).elim
      · exact (hc hC).elim

end BirthShortDoneTerminalCheckInputSources

#print axioms BirthShortDoneTerminalCheckInputSources.checkSig_follower_birth_input
#print axioms BirthShortDoneTerminalCheckInputSources.authorizedCheckSig_follower_birth_input
#print axioms BirthShortDoneTerminalCheckInputSources.actualCheckBirth_to_input
#print axioms BirthShortDoneTerminalCheckInputSources.birthEvent_sources_input
#print axioms BirthShortDoneTerminalCheckInputSources.birthEvent_false_of_no_input_sources
