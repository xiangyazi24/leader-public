import Leader.Wu.ShortGap.LiteralGapRows

/-!
# Candidate persistence for the literal gap rows (P2, row level)

Row-level facts behind round-current candidate persistence: a held
candidate port is never rewritten by any row, never turned into a denial,
blocks the post-step JOIN, and freezes the endpoint's choice.  The proofs
concern the `row` table only; nothing about generations, rounds, or the ring is
stated.  The explicit `ch ≠ race` hypothesis is needed because the incidence
arms still apply `resolveInit`/`resolveResp`.
-/

namespace ShortGapLiteralGapRows

set_option autoImplicit false

/-- `heldCandidate` alone does not force the raw `Choice` field to be frozen.
The explicit non-`race` hypothesis is therefore needed for full-state
persistence across the root/root incidence arm. -/
theorem row_preserves_heldCandidate_cw
    (ch : Choice) (ccw : CcwPort) (b : Agent)
    (hch : ch ≠ Choice.race) :
    (row (.root ch CwPort.heldCandidate ccw) b).1 =
      .root ch CwPort.heldCandidate ccw := by
  cases b with
  | root ch2 cw2 ccw2 =>
      by_cases hfree : ccw2 = CcwPort.free <;>
        simp [row, resolveInit, hch, hfree]
  | interior slot =>
      cases slot <;> simp [row, resolveInit, hch]

/-- Symmetric persistence for a candidate held on the responder's
counterclockwise port.  The explicit non-`race` hypothesis is needed because
K4 still applies `resolveResp`. -/
theorem row_preserves_heldCandidate_ccw
    (ch : Choice) (cw : CwPort) (a : Agent)
    (hch : ch ≠ Choice.race) :
    (row a (.root ch cw CcwPort.heldCandidate)).2 =
      .root ch cw CcwPort.heldCandidate := by
  cases a with
  | root ch2 cw2 ccw2 =>
      by_cases hsend : cw2 = CwPort.toSend <;>
        simp [row, hsend]
  | interior slot =>
      cases slot <;> simp [row, resolveResp, hch]

/-- A clockwise `heldCandidate` is never rewritten into `heldDenial` by
`row`. -/
theorem row_never_writes_heldCandidate_to_denial
    (a b : Agent) (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (hrow : (row a b).1 = .root ch cw ccw)
    (hden : cw = CwPort.heldDenial) :
    ∀ ch' ccw', a ≠ .root ch' CwPort.heldCandidate ccw' := by
  intro ch' ccw' ha
  rw [ha] at hrow
  rw [hden] at hrow
  cases b with
  | root ch2 cw2 ccw2 =>
      by_cases hfree : ccw2 = CcwPort.free <;>
        simp [row, hfree] at hrow
  | interior slot =>
      cases slot <;> simp [row] at hrow

/-- A counterclockwise `heldCandidate` is never rewritten into `heldDenial`
by `row`. -/
theorem row_never_writes_heldCandidate_to_denial_ccw
    (a b : Agent) (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (hrow : (row a b).2 = .root ch cw ccw)
    (hden : ccw = CcwPort.heldDenial) :
    ∀ ch' cw', b ≠ .root ch' cw' CcwPort.heldCandidate := by
  intro ch' cw' hb
  rw [hb] at hrow
  rw [hden] at hrow
  cases a with
  | root ch2 cw2 ccw2 =>
      by_cases hsend : cw2 = CwPort.toSend <;>
        simp [row, hsend] at hrow
  | interior slot =>
      cases slot <;> simp [row] at hrow

/-- A root joins the next round only after both denial ports are held. -/
def joinA : Agent → Agent
  | .root _ CwPort.heldDenial CcwPort.heldDenial =>
      .root Choice.race CwPort.toSend CcwPort.free
  | a => a

/-- Either held-candidate port blocks `joinA`. -/
theorem heldCandidate_not_join
    (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (h : cw = CwPort.heldCandidate ∨
      ccw = CcwPort.heldCandidate) :
    joinA (.root ch cw ccw) = .root ch cw ccw := by
  rcases h with hcw | hccw
  · subst cw
    rfl
  · subst ccw
    cases cw <;> rfl

/-- On either candidate endpoint, a frozen root keeps the same held choice on
all rows incident to that candidate port. -/
theorem candidate_endpoints_frozen_choice
    (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (hch : ch ≠ Choice.race) :
    (cw = CwPort.heldCandidate →
      ∀ b, Agent.choice ((row (.root ch cw ccw) b).1) = some ch) ∧
    (ccw = CcwPort.heldCandidate →
      ∀ a, Agent.choice ((row a (.root ch cw ccw)).2) = some ch) := by
  constructor
  · intro hcw b
    subst cw
    rw [row_preserves_heldCandidate_cw ch ccw b hch]
    rfl
  · intro hccw a
    subst ccw
    rw [row_preserves_heldCandidate_ccw ch cw a hch]
    rfl

#print axioms row_preserves_heldCandidate_cw
#print axioms row_preserves_heldCandidate_ccw
#print axioms row_never_writes_heldCandidate_to_denial
#print axioms heldCandidate_not_join
#print axioms candidate_endpoints_frozen_choice

end ShortGapLiteralGapRows
