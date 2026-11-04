import Leader.Wu.Protocol.Repairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZStep6Gen

open PPLL

/-- Shape lemma (stage 1 of the two-stage recipe): an agent whose path carries
    the pair (pLabel, pBit), whose label value matches pLabel and whose state is
    .congest is written to .CHECK_ready by checkSigSetReady. -/
private theorem setReady_shape {ψ : Nat} (u : AgentState ψ) (pLabel pBit : Nat)
    (hpath : u.path = PathInfo.some pLabel pBit)
    (hlabel : u.label.val = pLabel)
    (hstate : u.state = .congest) :
    checkSigSetReady u = { u with state := .CHECK_ready } := by
  unfold checkSigSetReady
  rw [hpath]
  dsimp only
  rw [if_pos]
  · exact ⟨hlabel,
      by rw [hstate]; decide,
      by rw [hstate]; decide,
      by rw [hstate]; decide,
      by rw [hstate]; decide⟩

/-- Shape lemma: an agent already in .equal is left untouched by checkSigSetReady. -/
private theorem setReady_equal_self {ψ : Nat} (u : AgentState ψ) (h : u.state = .equal) :
    checkSigSetReady u = u := by
  unfold checkSigSetReady
  cases hu : u.path with
  | bot => rfl
  | some label pBit =>
    dsimp only
    rw [if_neg]
    rintro ⟨_, _, hne, _, _⟩
    exact hne h

/-- C5 step 6, generalized: the driving fields enter as hypotheses (never as
    overrides); psi is arbitrary.  Entry state .congest is written to
    .CHECK_ready by checkSigSetReady (first write) and then to .equal by
    checkSigCheckR (second write), provided the path carries (pLabel, pBit),
    the label value matches pLabel, the bit code matches pBit and the left end
    satisfies the CheckR guard l.label.val < psi - 1 (with l.state = .equal). -/
theorem checkSigCheckR_congest_to_equal_general
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) (pLabel pBit : Nat)
    (hpath : r.path = PathInfo.some pLabel pBit)
    (hlabel : r.label.val = pLabel)
    (hbit : (if r.bit then 1 else 0) = pBit)
    (hstate : r.state = .congest)
    (hcl : l.label.val < ψ - 1 ∧ l.state = .equal) :
    (checkSigCheckR hψ (checkSigSetReady l) (checkSigSetReady r)).state = .equal := by
  have hr1 : checkSigSetReady r = { r with state := .CHECK_ready } :=
    setReady_shape r pLabel pBit hpath hlabel hstate
  have hl0 : checkSigSetReady l = l := setReady_equal_self l hcl.2
  have hpath1 : (checkSigSetReady r).path = PathInfo.some pLabel pBit := by
    rw [hr1, hpath]
  have hstate1 : (checkSigSetReady r).state = .CHECK_ready := by rw [hr1]
  have hbit1 : (if (checkSigSetReady r).bit then 1 else 0) = pBit := by
    rw [hr1]; exact hbit
  unfold checkSigCheckR
  rw [hpath1]
  dsimp only
  rw [if_pos]
  · rw [hstate1]
    rw [if_pos]
    · show checkBit (checkSigSetReady r).bit pBit = .equal
      unfold checkBit
      dsimp only
      rw [hbit1]
      rw [if_pos rfl]
    · rfl
  · exact ⟨by rw [hl0]; exact hcl.1, by rw [hl0]; exact hcl.2⟩

#print axioms checkSigCheckR_congest_to_equal_general

end ZZStep6Gen
