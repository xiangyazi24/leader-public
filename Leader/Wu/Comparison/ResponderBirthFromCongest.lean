import Leader.Wu.Comparison.CheckRightTwoWrites
import Leader.Wu.Comparison.DepartToCongest
import Leader.Wu.Comparison.CheckBirthArm

set_option autoImplicit false
set_option Elab.async false

namespace ZZC5Compose

open PPLL

/-- checkSigSetReady writes only the state field: the label is untouched. -/
private theorem setReady_label {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).label = u.label := by
  unfold checkSigSetReady
  split
  · repeat (first | rfl | split)
  · rfl

/-- checkSigSetReady writes only the state field: the bit is untouched. -/
private theorem setReady_bit {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).bit = u.bit := by
  unfold checkSigSetReady
  split
  · repeat (first | rfl | split)
  · rfl

/-- checkSigSetReady writes only the state field: the path is untouched. -/
private theorem setReady_path {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).path = u.path := by
  unfold checkSigSetReady
  split
  · repeat (first | rfl | split)
  · rfl

/-- checkSigCheckR writes only the state field: the label is untouched. -/
private theorem checkR_label {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).label = r.label := by
  unfold checkSigCheckR
  split
  · repeat (first | rfl | split)
  · rfl

/-- checkSigCheckR writes only the state field: the bit is untouched. -/
private theorem checkR_bit {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).bit = r.bit := by
  unfold checkSigCheckR
  split
  · repeat (first | rfl | split)
  · rfl

/-- checkSigCheckR writes only the state field: the path is untouched. -/
private theorem checkR_path {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).path = r.path := by
  unfold checkSigCheckR
  split
  · repeat (first | rfl | split)
  · rfl

/-- C5 birth composition (6 -> 7), satisfiable form: the step 7 responder is an
    INDEPENDENT terminal-labelled congested agent q with a coherent payload; the
    step 6 chain drives it to .equal and the birth arm raises its leader flag.
    Step 5 is deliberately NOT chained here: its congestion lands on a
    label-zero successor, and the non-vacuity witness file ZZC5Witness.lean
    kernel-refutes the terminal label premise on that successor at psi = 3. -/
theorem responder_birth_from_congest
    {ψ : Nat} (hψ : ψ > 0) (m q : AgentState ψ) (pLabel pBit : Nat)
    (hqpath : q.path = PathInfo.some pLabel pBit)
    (hqlabel : q.label.val = pLabel)
    (hqbit : (if q.bit then 1 else 0) = pBit)
    (hqstate : q.state = .congest)
    (hqterm : q.label = ⟨ψ - 1, by omega⟩)
    (hm : m.label.val < ψ - 1 ∧ m.state = .equal) :
    (checkSig hψ m
      (checkSigCheckR hψ (checkSigSetReady m) (checkSigSetReady q))).2.leader =
      true := by
  have h6state :
      (checkSigCheckR hψ (checkSigSetReady m) (checkSigSetReady q)).state =
        .equal :=
    ZZStep6Gen.checkSigCheckR_congest_to_equal_general
      hψ m q pLabel pBit hqpath hqlabel hqbit hqstate hm
  have h6label :
      (checkSigCheckR hψ (checkSigSetReady m) (checkSigSetReady q)).label =
        ⟨ψ - 1, by omega⟩ := by
    rw [checkR_label, setReady_label, hqterm]
  exact ZZStep7.checkSig_birth_of_terminal_equal hψ m _ h6label h6state

#print axioms responder_birth_from_congest

end ZZC5Compose
