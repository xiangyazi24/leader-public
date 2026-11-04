import Leader.Wu.Birth.GenerationDoneHost

/-!
# Actual source-write, phase and acknowledgement interfaces

The source stages are the existing genClean writer, propagation and finish.
A backward writer records its own resident bit; no source epoch is assumed.
The remaining full-run obligation is to keep components associated with the
intended static source group while other real stages may clear or replace them.
-/

set_option autoImplicit false
namespace BirthGenerationDone

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair PPLLComparisonHistory
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepNormalResetContract
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair BirthDisposalRouteInvariant
  BirthMismatchDisposalProducer BirthArrivalCaptureRepair BirthGenerationControlRepair
  BirthTossCheckPreservationRepair BirthSingleUseReleaseRepair

variable {psi kappa tau : Nat}

/-- Exact current propagation/ACK row followed by the actual source finish.
The new component stores its own resident bit and clears its own control;
the responder's existing payload/control are retained while done becomes depart. -/
theorem gen_ack_finish (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.label.val < psi - 1) (hp : l.state = .produce) (hr : r.state = .done) :
    let g := genCleanPropagate hpsi l r
    genSigSaturatedFinish hpsi g.1 g.2 =
      (if l.label = ⟨0, hpsi⟩ then
        { l with
          state := .depart
          wait := true
          path := .some l.label.val (if l.bit then 1 else 0)
          path2 := none }
       else { l with
          state := .done
          path := .some l.label.val (if l.bit then 1 else 0)
          path2 := none },
       { r with state := .depart }) := by
  have hn : l.label ≠ ⟨psi - 1, by omega⟩ := by
    intro h; have hv : l.label.val = psi - 1 := congrArg Fin.val h; omega
  rw [genCleanPropagate_writer hpsi l r hn hp hr]
  simp only [genSigSaturatedFinish]
  split <;> simp_all

/-- A positive nonterminal writer waits in done; the current ready-bit
initializer cannot consume this newly generated phase. -/
theorem gen_nonzero_ack_check (hpsi : psi > 0) (l r : AgentState psi)
    (hz : 0 < l.label.val) (hl : l.label.val < psi - 1)
    (hp : l.state = .produce) (hr : r.state = .done) (lp rp : Bool) :
    let g := genCleanPropagate hpsi l r
    let f := genSigSaturatedFinish hpsi g.1 g.2
    f.1.state = .done ∧ f.1.path = .some l.label.val (if l.bit then 1 else 0) ∧
      f.1.path2 = none ∧ f.2 = { r with state := .depart } ∧
      preserveDoneCheck hpsi ⟨f.1, lp⟩ ⟨f.2, rp⟩ = (⟨f.1, lp⟩, ⟨f.2, rp⟩) := by
  have hn : l.label ≠ ⟨0, hpsi⟩ := by intro h; have hv : l.label.val = 0 := congrArg Fin.val h; omega
  dsimp only
  rw [gen_ack_finish hpsi l r hl hp hr]
  simp [hn, preserveDoneCheck]

/-- Source zero completes backward production immediately and rearms WAIT;
there is no new zero-labelled done waiting for another predecessor ACK. -/
theorem gen_zero_ack_finish (hpsi : psi > 0) (hwidth : 1 < psi)
    (l r : AgentState psi) (hz : l.label = ⟨0, hpsi⟩)
    (hp : l.state = .produce) (hr : r.state = .done) :
    let g := genCleanPropagate hpsi l r
    genSigSaturatedFinish hpsi g.1 g.2 =
      ({ l with
        state := .depart
        wait := true
        path := .some 0 (if l.bit then 1 else 0)
        path2 := none },
       { r with state := .depart }) := by
  have hb : l.label.val < psi - 1 := by rw [hz]; dsimp; omega
  dsimp only
  rw [gen_ack_finish hpsi l r hb hp hr]
  simp [hz]

/-- This read-only cut is precisely where the current complete source stage
passes its input to backward propagation and the following finish. -/
def genAckInput (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let w := waitSaturated hpsi kappa l r
  let s := genSigSaturatedStart hpsi w.1 w.2
  genCleanEmit hpsi s.1 s.2

theorem genClean_eq_ack_finish (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    let e := genAckInput hpsi kappa l r
    let g := genCleanPropagate hpsi e.1 e.2
    genClean hpsi kappa l r = genSigSaturatedFinish hpsi g.1 g.2 := by rfl

/-- Full current GEN, including WAIT and Start/Emit, produces a held phase
when its actual ACK cut has a positive nonterminal producer. No done result
or payload/control postcondition is supplied as an assumption. -/
theorem genClean_nonzero_ack (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi)
    (hz : 0 < (genAckInput hpsi kappa l r).1.label.val)
    (hl : (genAckInput hpsi kappa l r).1.label.val < psi - 1)
    (hp : (genAckInput hpsi kappa l r).1.state = .produce)
    (hr : (genAckInput hpsi kappa l r).2.state = .done) :
    let e := genAckInput hpsi kappa l r
    let q := genClean hpsi kappa l r
    q.1.state = .done ∧ q.1.path = .some e.1.label.val (if e.1.bit then 1 else 0) ∧
      q.1.path2 = none ∧ q.2 = { e.2 with state := .depart } := by
  have h := gen_nonzero_ack_check hpsi _ _ hz hl hp hr false false
  rw [genClean_eq_ack_finish hpsi kappa l r]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Every protected Step1 leaves the actual main carrier and phase in place,
while Steps2--5 continue to execute on its control fields. -/
theorem done_transfers_hold_phase (l r : AgentState psi) (hs : l.state = .done) :
    let q := doneTransfers l r
    q.1.state = .done ∧ q.1.path = l.path ∧ q.2.path = r.path := by
  rw [doneTransfers_of_done l r hs]
  have h := controlTransfers_phase_path l r
  exact ⟨h.1.trans hs, h.2.2.1, h.2.2.2⟩

/-- The old Step1 really can transport done; the new branch blocks exactly
this event. Its premise is a present payload/free receiver, not a future ACK. -/
theorem old_step1_moves_done (l r : AgentState psi) (label bit : Nat)
    (hs : l.state = .done) (hp : l.path = .some label bit) (hr : r.path = .bot)
    (hg : r.state ≠ .produce ∨ label ≠ psi - 1) :
    (captureStep1 l r).1.path = .bot ∧ (captureStep1 l r).2.path = l.path ∧
      holdDoneStep1 l r = (l, r) := by
  simp [captureStep1, hs, hp, hr, hg, holdDoneStep1]

/-- Psi one has no nonterminal backward writer. Existing GEN finish changes
an initiator done to depart without any predecessor-ACK requirement. -/
theorem psi_one_finish (l r : AgentState 1) (hs : l.state = .done) :
    genCleanPropagate (by decide) l r = (l, r) ∧
      genSigSaturatedFinish (by decide) l r = ({ l with state := .depart, wait := true }, r) := by
  have hz : l.label = ⟨0, by decide⟩ := Fin.ext (by have := l.label.isLt; omega)
  simp [genCleanPropagate, genSigSaturatedFinish, hz, hs]

/-- Psi two's sole backward writer is source zero. A positive nonterminal
done phase can first occur at psi three; no all-width claim is inferred from
the existing two-bit regressions. -/
theorem psi_two_backward_finishes (l r : AgentState 2)
    (hl : l.label.val < 1) (hp : l.state = .produce) (hr : r.state = .done) :
    let g := genCleanPropagate (by decide) l r
    genSigSaturatedFinish (by decide) g.1 g.2 =
      ({ l with
        state := .depart
        wait := true
        path := .some 0 (if l.bit then 1 else 0)
        path2 := none },
       { r with state := .depart }) := by
  exact gen_zero_ack_finish (by decide) (by decide) l r (Fin.ext (by change l.label.val = 0; omega)) hp hr

/-- Generation-control erasure gives the weak bit-coherence rule needed by a
static ruler: each new component contains that writer's current resident bit.
The sources of other components and their later locations are not inferred. -/
theorem gen_writer_matches_static_bit (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.label.val < psi - 1) (hp : l.state = .produce) (hr : r.state = .done)
    (sourceBit : Bool) (hb : l.bit = sourceBit) :
    (genCleanPropagate hpsi l r).1.path = .some l.label.val (if sourceBit then 1 else 0) ∧
      (genCleanPropagate hpsi l r).1.path2 = none := by
  have hn : l.label ≠ ⟨psi - 1, by omega⟩ := by intro h; have hv : l.label.val = psi - 1 := congrArg Fin.val h; omega
  rw [genCleanPropagate_writer hpsi l r hn hp hr]
  simp [hb]

end BirthGenerationDone
