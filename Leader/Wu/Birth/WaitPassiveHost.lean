import Leader.Wu.Birth.WaitPassiveRows
import Leader.Wu.Birth.WaitPassiveClock

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

variable {psi kappa tau : Nat}

def raw (u : ExpiringAgentState psi kappa tau) : AgentState psi := u.core.core.erase

theorem clear_erasure (s : AuthorizedBoundedAgentState psi kappa) :
    (clearComparisonCarrier s).erase =
      ⟨{ s.erase.core with
          state := .none
          path := .bot
          path2 := none
          path4 := none
          path5 := none
          p := false
          p_carry := false }, false⟩ := by
  rfl

/-- Expiry changes none of the WAIT or ruler observations, even at timer zero. -/
theorem expiry_clock (old out : ExpiringAgentState psi kappa tau) :
    clock (raw (deletionPriorityExpireOne tau old out)) = clock (raw out) := by
  unfold deletionPriorityExpireOne pathExpireOne
  repeat (first | rfl | split <;> try dsimp only)

/-- Empty metadata remains empty through every finite expiry branch. -/
theorem expiry_cell (old out : ExpiringAgentState psi kappa tau)
    (d : Registers psi) (h : out.core.erase = ⟨cell d,false⟩) :
    (deletionPriorityExpireOne tau old out).core.erase = ⟨cell d,false⟩ := by
  unfold deletionPriorityExpireOne
  rw [h, active_cell]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold pathExpireOne
  split
  · exact h
  · split
    · change (clearComparisonCarrier out.core).erase = _
      rw [clear_erasure,h]
      rfl
    · exact h

theorem prepared_erasure (hpsi : 0 < psi)
    (u : ExpiringAgentState psi kappa tau) (d : Registers psi)
    (h : raw u = cell d) :
    (prepareExpiringDisposal hpsi u).core.erase = ⟨cell d,u.core.path0Crossed⟩ := by
  change (prepareBoundedDisposal hpsi u.core).erase = _
  rw [erase_prepareBoundedDisposal]
  have hu : u.core.erase = ⟨cell d,u.core.path0Crossed⟩ := by
    exact congrArg (fun c => (⟨c,u.core.path0Crossed⟩ : AuthorizedAgentState psi)) h
  rw [hu]
  simp [prepareDisposal,pendingTerminalDisposal,cell]

/-- The full host's raw WAIT/ruler observation at its actual prepared input.
This equality is unconditional, including the cap-producing row. -/
theorem full_clock (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let l0 := prepareExpiringDisposal hpsi l
    let r0 := prepareExpiringDisposal hpsi r
    let a := generationGuardedAuthorizedTransition hpsi kappa l0.core.erase r0.core.erase
    let q := generationFullTransition hpsi kappa tau l r
    clock (raw q.1) = clock a.1.core ∧ clock (raw q.2) = clock a.2.core := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let b := generationGuardedBoundedTransition hpsi kappa l0.core r0.core
  let lo : ExpiringAgentState psi kappa tau := ⟨b.1,l0.stall⟩
  let ro : ExpiringAgentState psi kappa tau := ⟨b.2,r0.stall⟩
  have he := erase_generationGuardedBoundedTransition hpsi kappa l0.core r0.core
  have hl := congrArg (fun p => clock p.1.core) he
  have hr := congrArg (fun p => clock p.2.core) he
  have el := expiry_clock l0 lo
  have er := expiry_clock r0 ro
  unfold generationFullTransition initializeFollowerPairBirthSignals
  change let q := (deletionPriorityExpireOne tau l0 lo,
      deletionPriorityExpireOne tau r0 ro)
    clock (raw (if l0.core.core.leader = false ∧ r0.core.core.leader = false
      then (clearExpiringLeaderSignal q.1,clearExpiringLeaderSignal q.2) else q).1) = _ ∧
    clock (raw (if l0.core.core.leader = false ∧ r0.core.core.leader = false
      then (clearExpiringLeaderSignal q.1,clearExpiringLeaderSignal q.2) else q).2) = _
  split
  · have cf (u : ExpiringAgentState psi kappa tau) :
        clock (raw (clearExpiringLeaderSignal u)) = clock (raw u) := by
      unfold clearExpiringLeaderSignal
      split <;> rfl
    exact ⟨(cf _).trans (el.trans hl),(cf _).trans (er.trans hr)⟩
  · exact ⟨el.trans hl,er.trans hr⟩

private theorem full_cells (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (a b : Registers psi)
    (h : generationGuardedAuthorizedTransition hpsi kappa
      (prepareExpiringDisposal hpsi l).core.erase
      (prepareExpiringDisposal hpsi r).core.erase =
        (⟨cell a,false⟩,⟨cell b,false⟩)) :
    let q := generationFullTransition hpsi kappa tau l r
    q.1.core.erase = ⟨cell a,false⟩ ∧ q.2.core.erase = ⟨cell b,false⟩ := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let bnd := generationGuardedBoundedTransition hpsi kappa l0.core r0.core
  let lo : ExpiringAgentState psi kappa tau := ⟨bnd.1,l0.stall⟩
  let ro : ExpiringAgentState psi kappa tau := ⟨bnd.2,r0.stall⟩
  have he := (erase_generationGuardedBoundedTransition hpsi kappa l0.core r0.core).trans h
  have el := expiry_cell l0 lo a (congrArg Prod.fst he)
  have er := expiry_cell r0 ro b (congrArg Prod.snd he)
  have ell : (deletionPriorityExpireOne tau l0 lo).core.erase.core.leader = false :=
    congrArg (fun s => s.core.leader) el
  have err : (deletionPriorityExpireOne tau r0 ro).core.erase.core.leader = false :=
    congrArg (fun s => s.core.leader) er
  unfold generationFullTransition initializeFollowerPairBirthSignals
  change let q := (deletionPriorityExpireOne tau l0 lo,deletionPriorityExpireOne tau r0 ro)
    (if l0.core.core.leader = false ∧ r0.core.core.leader = false
      then (clearExpiringLeaderSignal q.1,clearExpiringLeaderSignal q.2) else q).1.core.erase = _ ∧
    (if l0.core.core.leader = false ∧ r0.core.core.leader = false
      then (clearExpiringLeaderSignal q.1,clearExpiringLeaderSignal q.2) else q).2.core.erase = _
  split
  · dsimp only
    rw [clearExpiringLeaderSignal_eq_of_follower _ ell,
      clearExpiringLeaderSignal_eq_of_follower _ err]
    exact ⟨el,er⟩
  · exact ⟨el,er⟩

/-- One literal full row before a root release, with exact erasure and no
restriction on expiry timers or incoming authorization bits. -/
theorem full_cell_row (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (a b : Registers psi)
    (hl : raw l = cell a) (hr : raw r = cell b)
    (hab : b.label = ⟨(a.label.val+1)%psi,Nat.mod_lt _ hpsi⟩)
    (hw : let w := waitSaturated hpsi kappa (cell a) (cell b)
      w.1.label = ⟨0,hpsi⟩ → w.1.wait = true) :
    let w := waitSaturated hpsi kappa (cell a) (cell b)
    let q := generationFullTransition hpsi kappa tau l r
    q.1.core.erase = ⟨cell {registers w.1 with writer := .none},false⟩ ∧
    q.2.core.erase = ⟨cell {registers w.2 with writer :=
      if w.1.label < w.2.label ∨ w.2.label = ⟨0,hpsi⟩ then .depart else .none},false⟩ := by
  apply full_cells
  rw [prepared_erasure hpsi l a hl,prepared_erasure hpsi r b hr]
  exact guarded_cell hpsi kappa a b _ _ hab hw

end BirthWaitPassive
