import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZLeaderGate

open PPLL

variable {ψ : Nat}

/-!
# The label-zero gate on leader migration

Semantic safety is exactly one leader together with a frozen output vector,
because the protocol output reads only the leader bit (`State.lean:172-173`).
`writeSeqLeaderMove` (`Algorithm.lean:1000-1003`) hands the leader bit to the
initiator whenever the responder is a leader off label zero, which flips two
entries of that vector.  So a safe configuration must keep its leader pinned at
label zero, and this file isolates that gate.
-/

/-- A responder at label zero cannot trigger the WRITE leader migration. -/
theorem writeSeqLeaderMove_inert
    (hψ : 0 < ψ) (l r : AgentState ψ) (hzero : r.label = ⟨0, hψ⟩) :
    writeSeqLeaderMove hψ l r = (l, r) := by
  have hmiss : ¬(r.leader = true ∧ r.label ≠ ⟨0, hψ⟩) := fun h => h.2 hzero
  simp only [writeSeqLeaderMove, hmiss, if_false]

/-- A non-leader responder cannot trigger it either. -/
theorem writeSeqLeaderMove_inert_of_follower
    (hψ : 0 < ψ) (l r : AgentState ψ) (hfol : r.leader = false) :
    writeSeqLeaderMove hψ l r = (l, r) := by
  have hmiss : ¬(r.leader = true ∧ r.label ≠ ⟨0, hψ⟩) := by
    intro h
    rw [hfol] at h
    exact Bool.noConfusion h.1
  simp only [writeSeqLeaderMove, hmiss, if_false]

/-- Conversely the migration does fire off label zero, so the gate is sharp and
the frame lemma above is not vacuous. -/
theorem writeSeqLeaderMove_fires
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hlead : r.leader = true) (hoff : r.label ≠ ⟨0, hψ⟩) :
    writeSeqLeaderMove hψ l r
      = ({ l with leader := true }, { r with leader := false }) := by
  simp only [writeSeqLeaderMove]
  rw [if_pos ⟨hlead, hoff⟩]

#print axioms writeSeqLeaderMove_inert
#print axioms writeSeqLeaderMove_inert_of_follower
#print axioms writeSeqLeaderMove_fires

end ZZLeaderGate
