import Leader.Wu.WallSweep.PreCheckResetContractsDrain

/-!
# Writer-reset barrier

A tagged full-reset mode that clears all Algorithm-16–20 writer fields on
covered endpoints.  Ordinary reset stays comparison-only; an armed full
reset clears both comparison and writer state.
-/

namespace PPLLWriterResetBarrier

open PPLL PPLLResearchFormulation
open PPLLExpiringComparisonRepair
open PPLLAuthorizedComparisonRepair

variable {psi kappa tau n : Nat}

/-! ## Writer field clearing -/

def clearWriterState (u : AgentState psi) : AgentState psi :=
  { u with
    write_state := WriteState.none
    path3 := none
    write := WriteAction.none
    gen_ws := false
    signal_ws := false
    ws_echo := false
    b_carry := false
    last := false
    last_set := false
    last_unset := false }

def WriterNeutral (u : AgentState psi) : Prop :=
  u.write_state = .none ∧ u.path3 = none ∧ u.write = .none ∧
  u.gen_ws = false ∧ u.signal_ws = false ∧ u.ws_echo = false ∧
  u.b_carry = false ∧ u.last = false ∧ u.last_set = false ∧
  u.last_unset = false

theorem clearWriterState_neutral (u : AgentState psi) :
    WriterNeutral (clearWriterState u) := by
  simp [WriterNeutral, clearWriterState]

theorem clearWriterState_leader (u : AgentState psi) :
    (clearWriterState u).leader = u.leader := by rfl

theorem clearWriterState_label (u : AgentState psi) :
    (clearWriterState u).label = u.label := by rfl

theorem clearWriterState_shield (u : AgentState psi) :
    (clearWriterState u).shield = u.shield := by rfl

theorem clearWriterState_bullet (u : AgentState psi) :
    (clearWriterState u).bullet = u.bullet := by rfl

theorem clearWriterState_signal_B (u : AgentState psi) :
    (clearWriterState u).signal_B = u.signal_B := by rfl

theorem clearWriterState_bit (u : AgentState psi) :
    (clearWriterState u).bit = u.bit := by rfl

theorem clearWriterState_reset_cmd (u : AgentState psi) :
    (clearWriterState u).reset_cmd = u.reset_cmd := by rfl

theorem clearWriterState_echo (u : AgentState psi) :
    (clearWriterState u).echo = u.echo := by rfl

theorem clearWriterState_state (u : AgentState psi) :
    (clearWriterState u).state = u.state := by rfl

theorem clearWriterState_path (u : AgentState psi) :
    (clearWriterState u).path = u.path := by rfl

theorem clearWriterState_path2 (u : AgentState psi) :
    (clearWriterState u).path2 = u.path2 := by rfl

theorem clearWriterState_path4 (u : AgentState psi) :
    (clearWriterState u).path4 = u.path4 := by rfl

theorem clearWriterState_path5 (u : AgentState psi) :
    (clearWriterState u).path5 = u.path5 := by rfl

theorem clearWriterState_p (u : AgentState psi) :
    (clearWriterState u).p = u.p := by rfl

theorem clearWriterState_p_carry (u : AgentState psi) :
    (clearWriterState u).p_carry = u.p_carry := by rfl

theorem clearWriterState_idempotent (u : AgentState psi) :
    clearWriterState (clearWriterState u) = clearWriterState u := by
  simp [clearWriterState]

theorem clearWriterState_of_neutral (u : AgentState psi)
    (h : WriterNeutral u) :
    clearWriterState u = u := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only [clearWriterState]
  cases u
  simp_all

/-! ## Bounded-layer clearing -/

def clearWriterBoundedState
    (u : BoundedAgentState psi kappa) : BoundedAgentState psi kappa :=
  { u with
    write_state := WriteState.none
    path3 := none
    write := WriteAction.none
    gen_ws := false
    signal_ws := false
    ws_echo := false
    b_carry := false
    last := false
    last_set := false
    last_unset := false }

def clearWriterAuthorizedBoundedState
    (u : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa :=
  { u with core := clearWriterBoundedState u.core }

def clearWriterExpiringState
    (u : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau :=
  { u with core := clearWriterAuthorizedBoundedState u.core }

/-! ## Writer-reset fence -/

def writerResetFencePair
    (T : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (coverL coverR : Bool)
    (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let l0 := if coverL then clearWriterState l else l
  let r0 := if coverR then clearWriterState r else r
  let q := T l0 r0
  (if coverL then clearWriterState q.1 else q.1,
   if coverR then clearWriterState q.2 else q.2)

theorem writerResetFencePair_eq_of_not_covered
    (T : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AgentState psi) :
    writerResetFencePair T false false l r = T l r := by
  simp [writerResetFencePair]

/-! ## Global writer neutrality -/

def GloballyWriterNeutral
    (C : Fin n → AgentState psi) : Prop :=
  ∀ i, WriterNeutral (C i)

end PPLLWriterResetBarrier
