import Leader.Wu.Safety.ConcreteProtocolProperties

/-!
# A local WRITE_SEQ leader frame for the reversed-path witness

The only leader-changing branch of `writeSeq` migrates a responder leader at
a nonzero label to the initiator.  Consequently both endpoint leader bits are
framed whenever the responder is a follower or is hosted at label zero.
-/

set_option autoImplicit false
set_option Elab.async false

namespace ZZSafeN4WriterFrame

open PPLL

/-- `WRITE_SEQ` preserves both leader bits unless it is presented with the
specific migration source: a responder leader at a nonzero label. -/
theorem writeSeq_leaders_eq_of_responder_follower_or_zero
    {ψ : Nat} (hψ : 0 < ψ) (l r : AgentState ψ)
    (hr : r.leader = false ∨ r.label = ⟨0, hψ⟩) :
    let q := writeSeq hψ l r
    q.1.leader = l.leader ∧ q.2.leader = r.leader := by
  constructor
  · cases hl : l.leader
    · cases hout : (writeSeq hψ l r).1.leader
      · rfl
      · have hmigrate :=
          PPLLVerify.writeSeq_new_initiator_requires_responder_leader
            hψ l r hout hl
        rcases hr with hrFollower | hrZero
        · have : False := by simpa [hrFollower] using hmigrate.1
          exact this.elim
        · exact (hmigrate.2 hrZero).elim
    · exact PPLLVerify.writeSeq_initiator_leader_of_true hψ l r hl
  · cases hrLeader : r.leader
    · cases hout : (writeSeq hψ l r).2.leader
      · rfl
      · have horigin :=
          PPLLVerify.writeSeq_responder_leader_was_leader hψ l r hout
        have : False := by simpa [hrLeader] using horigin
        exact this.elim
    · rcases hr with hrFollower | hrZero
      · have : False := by simpa [hrLeader] using hrFollower
        exact this.elim
      · exact PPLLVerify.writeSeq_responder_leader_of_label_zero
          hψ l r hrLeader hrZero

#print axioms writeSeq_leaders_eq_of_responder_follower_or_zero

end ZZSafeN4WriterFrame
