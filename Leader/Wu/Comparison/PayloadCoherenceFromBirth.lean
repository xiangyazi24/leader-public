import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZStep2Hub

open PPLL

/-!
# C5 step 2, restated

The original step 2 claimed that reaching `.congest` supplies the payload
coherence that CHECK requires.  That is refuted: none of the three source
assignments that can put an agent into `.congest` creates the relation between
the host fields and the frozen payload; each only preserves what was there.

Coherence is created exactly once, at token birth, where `genSig` writes the
payload from the creating host's own label and bit
(`Algorithm.lean:103-104` and `:109-110`).  Afterwards it can only be
preserved, and it is destroyed by three stages: `pPsi` rotates the label
(`:31`, `:41`), `sigMoveStep1` hands the payload to a neighbour without
touching that neighbour's label (`:464-470`), and the write sequence can flip
the bit.

So the usable form of step 2 is a preservation hub: any stage that writes none
of `path`, `label`, `bit` carries coherence through unchanged.  Every frame
lemma already proved in the layer-zero files instantiates it.
-/

/-- The three-part coherence predicate CHECK tests, as a standalone Prop. -/
def Coherent {ψ : Nat} (u : AgentState ψ) (pLabel pBit : Nat) : Prop :=
  u.path = PathInfo.some pLabel pBit ∧
  u.label.val = pLabel ∧
  (if u.bit then 1 else 0) = pBit

theorem coherent_preserved {ψ : Nat} (u u' : AgentState ψ) (pLabel pBit : Nat)
    (hco : Coherent u pLabel pBit)
    (hpath : u'.path = u.path)
    (hlabel : u'.label.val = u.label.val)
    (hbit : u'.bit = u.bit) :
    Coherent u' pLabel pBit := by
  obtain ⟨h1, h2, h3⟩ := hco
  refine ⟨?_, ?_, ?_⟩
  · rw [hpath, h1]
  · rw [hlabel, h2]
  · rw [hbit, h3]

/-- CHECK's readiness guard is exactly the first two components of coherence
    together with the four excluded states, so a coherent agent that is not in
    an excluded state is made ready. -/
theorem coherent_gives_ready {ψ : Nat} (u : AgentState ψ) (pLabel pBit : Nat)
    (hco : Coherent u pLabel pBit)
    (h1 : u.state ≠ MainState.depart) (h2 : u.state ≠ MainState.equal)
    (h3 : u.state ≠ MainState.larger) (h4 : u.state ≠ MainState.less) :
    (checkSigSetReady u).state = MainState.CHECK_ready := by
  obtain ⟨hp, hl, _⟩ := hco
  simp only [checkSigSetReady, hp]
  rw [if_pos ⟨hl, h1, h2, h3, h4⟩]

#print axioms coherent_preserved
#print axioms coherent_gives_ready

end ZZStep2Hub
