import Leader.Wu.Birth.ShortDoneTerminalCapEndpointWitness
import Leader.Wu.Birth.ShortDoneTerminalCapClock

namespace BirthShortDoneTerminalCapGeneralR1

open PPLL PPLLRepair PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthGenerationControlRepair BirthGenerationDone
open BirthWaitPassive BirthShortWait BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1
open BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHost
open K2BirthDispatcher K2BirthDispatcherDone ExpiringK2Projection
  K2BirthLeaderNormalize BirthShortDoneCuts

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

private theorem h2 : 0 < 2 := by decide
private theorem hle2 : 2 <= 2 := by decide

/-- Positive form of the literal repaired pre-Finish cap test. -/
def AtCapEntry2 (kappa : Nat) (l r : AgentState 2) : Prop :=
  let s := preFinishEntry2 h2 hle2 kappa l r
  s.2.label = widthTerminal h2 hle2 /\ s.2.count = kappa


/-- The literal repaired width-two Finish shape on a positive cap row. -/
theorem waitWidthEntry2_of_atCap
    (kappa : Nat) (l r : AgentState 2)
    (hab : r.label =
      ⟨(l.label.val + 1) % 2, Nat.mod_lt _ h2⟩)
    (hcap : AtCapEntry2 kappa l r) :
    let w := waitWidthEntry h2 h2 hle2 kappa l r
    w.1.label = 0 /\ w.2.label = 1 /\
      w.1.wait = false /\ w.2.wait = true /\
      w.2.count = kappa := by
  let s := preFinishEntry2 h2 hle2 kappa l r
  change s.2.label = widthTerminal h2 hle2 /\ s.2.count = kappa at hcap

  have hlabels : s.1.label = l.label /\ s.2.label = r.label := by
    unfold s preFinishEntry2
    simp [waitSaturatedPrepare, terminalInactiveClear,
      waitWidthCarry, waitWidthReset]

  have hterm : widthTerminal h2 hle2 = (1 : Fin 2) := by
    apply Fin.ext
    rfl

  have hr1 : r.label = 1 :=
    hlabels.2.symm.trans (hcap.1.trans hterm)

  have hl0 : l.label = 0 := by
    have hfin : l.label = 0 ∨ l.label = 1 := by
      have h : l.label.val = 0 ∨ l.label.val = 1 := by omega
      rcases h with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hfin with hl | hl
    · exact hl
    · exfalso
      have hv := congrArg Fin.val hab
      simpa [hl, hr1] using hv

  have hs0 : s.1.label = 0 := hlabels.1.trans hl0
  have hsne : s.1.label ≠ (⟨2 - 1, by omega⟩ : Fin 2) := by
    intro ht
    have hv := congrArg Fin.val (hs0.symm.trans ht)
    simpa using hv

  unfold waitWidthEntry
  change
    let p := waitSaturatedPrepare h2 l r
    let e := terminalInactiveClear h2 hle2 p.1 p.2
    let c := waitWidthCarry h2 hle2 kappa e.1 e.2
    let t := waitWidthReset h2 hle2 c.1 c.2
    let w := waitWidthFinish h2 h2 hle2 kappa t.1 t.2
    w.1.label = 0 /\ w.2.label = 1 /\
      w.1.wait = false /\ w.2.wait = true /\
      w.2.count = kappa
  change
    let w := waitWidthFinish h2 h2 hle2 kappa s.1 s.2
    w.1.label = 0 /\ w.2.label = 1 /\
      w.1.wait = false /\ w.2.wait = true /\
      w.2.count = kappa
  simp [waitWidthFinish, hcap.1, hcap.2, hterm, hs0, hsne]


/-- Proof-only spelling of the actual ordinary metadata tail from the post-WAIT cut. -/
def postWaitDone2
    (a b d e : Registers 2) (pa pb : Bool) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let g := genCleanAfterWait h2 (cell d) (cell e)
  let q1 := authorizedCleanSig h2 ⟨g.1, false⟩ ⟨g.2, false⟩
  let q2 := authorizedEliminateSig h2 q1.1 q1.2
  let q3 := authorizedDoneMove h2 q2.1 q2.2
  let q4 :=
    PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair h2
      (PPLLWallSweepPreCheckResetRepair.preCheckResetWall q3.1 q3.2)
  let q5 := preserveDoneCheck h2 q4.1 q4.2
  let q6 := afterCheckMetadataWidth h2 h2 hle2 q5.1 q5.2
  PPLLLeaderCreationCleanupRepair.markLeaderBirth
    (authBirth ⟨cell a, pa⟩ ⟨cell b, pb⟩ q6) q6


/-- Exact source fact needed by the full bounded host.
    The responder cap count survives and GEN re-arms both WAIT bits. -/
theorem postWaitDone2_cap_frame
    (a b d e : Registers 2) (pa pb : Bool)
    (hd : d.label = 0) (he : e.label = 1)
    (hwd : d.wait = false) (hwe : e.wait = true) :
    let q := postWaitDone2 a b d e pa pb
    q.2.core.count = e.count /\
      q.1.core.wait = true /\ q.2.core.wait = true := by
  -- Structural: R2-R4 factor the same metadata tail stage by stage
  -- (GEN/CLEAN/ELIMINATE, DONE move, pre-CHECK wall, CHECK, after-CHECK,
  -- birth marking), each stage proved once at variable registers.  The two
  -- `postWaitDone2` definitions have the same body, so the R4 frame applies
  -- by unfolding both.
  have h := BirthShortDoneTerminalCapGeneralR4.postWaitDone2_cap_frame
    a b d e pa pb hd he hwd hwe
  have heq : postWaitDone2 a b d e pa pb =
      BirthShortDoneTerminalCapGeneralR2.postWaitDone2 a b d e pa pb := rfl
  -- Rewrite inside the `let` value only; unifying a projection of the
  -- unreduced pair with the expanded goal would reduce the whole tail.
  rw [heq]
  exact h

#print axioms BirthShortDoneTerminalCapGeneralR1.waitWidthEntry2_of_atCap
#print axioms BirthShortDoneTerminalCapGeneralR1.postWaitDone2_cap_frame
end BirthShortDoneTerminalCapGeneralR1
