import Leader.Wu.Protocol.Algorithm
import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Birth.WaitPassiveHost

set_option autoImplicit false

/-! # The leader's write-sequence generation completes in one interaction only when psi = 2

Algorithm 18 (GENSIG_WRITESEQ) spreads `write_state = produce` from label 0 to label psi - 1 one edge per
interaction and emits overwriting signals (`path3`) from the terminal back to label 0.  Algorithm 16 runs
SetWriteReady in the same interaction immediately after Algorithm 18; it resets `write_state` to `none` on every
cell without `path3`.  For psi = 2 the whole generation (produce, terminal emission, backward propagation) happens
inside the one call, so both cells receive `path3`.  For psi >= 3 the produce states are wiped before the next
interaction and no `path3` is ever emitted.

Kernel certificates (bits 0, clean registers, a leader with `gen_ws` at label 0):
* literal Algorithm 1 at psi = 2: one row on (label 0, label 1) gives both cells `path3`
  (`literal_psi2_one_row_emits`);
* literal Algorithm 1 at psi = 3: the same row leaves both cells without `path3` and label 0 not producing, with
  `gen_ws` still set (`literal_psi3_row_wipes_produce`);
* the width-two terminal consumer at psi = 3, kappa = 3, tau = 48: the same (`consumer_psi3_row_wipes_produce`). -/

namespace B10WriterGenerationPsi3

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair BirthWaitPassive

def lit (psi : Nat) (lab : Fin psi) (lead : Bool) : AgentState psi :=
  { leader := lead, probe := false, phase := false, bit := false, wait := true, state := .none,
    path := .bot, reset := false, carry := false, count := 0, label := lab, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false,
    write_state := .none, write := .none, last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := lead, ws_echo := false, signal_ws := false }

theorem literal_psi2_one_row_emits :
    let q := ppll (ψ := 2) (by decide) 1 (lit 2 0 true) (lit 2 1 false)
    q.1.path3.isSome = true ∧ q.2.path3.isSome = true := by
  decide

theorem literal_psi3_row_wipes_produce :
    let q := ppll (ψ := 3) (by decide) 1 (lit 3 0 true) (lit 3 1 false)
    q.1.path3 = none ∧ q.2.path3 = none ∧ q.1.write_state ≠ .produce ∧ q.2.write_state ≠ .produce ∧
      q.1.gen_ws = true := by
  decide

def regsB (lab : Fin 3) : Registers 3 :=
  { label := lab, h := false, carry := false, reset := false, count := 0, wait := true,
    bit := false, phase := false, writer := .none }

def genCell (lab : Fin 3) (lead : Bool) : AgentState 3 :=
  { cell (regsB lab) with leader := lead, gen_ws := lead }

theorem dom_gen (lab : Fin 3) (lead : Bool) : (genCell lab lead).inProtocolDomain 3 := by
  simp [genCell, cell, regsB, AgentState.inProtocolDomain]

def tok (lab : Fin 3) (lead : Bool) : ExpiringAgentState 3 3 48 :=
  ⟨⟨BoundedAgentState.ofDomain (genCell lab lead) (dom_gen lab lead), false⟩, Fin.last 48⟩

theorem consumer_psi3_row_wipes_produce :
    let q := BirthShortDoneTerminalHost.row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide)
      (by decide) (tok 0 true) (tok 1 false)
    q.1.core.core.path3 = none ∧ q.2.core.core.path3 = none ∧ q.1.core.core.write_state ≠ .produce ∧
      q.2.core.core.write_state ≠ .produce ∧ q.1.core.core.gen_ws = true := by
  decide +kernel

end B10WriterGenerationPsi3
