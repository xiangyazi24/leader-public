import Leader.Wu.Coherence.Controller

set_option autoImplicit false
set_option Elab.async false

namespace ZZStrandedNormalizerV32

variable {ψ κ τ : Nat}

/--
Exactly the stranded family: all six `rowV3` active-token guards fail,
but the pair is not token-free.

Token-level census:
  left  ∈ {none, seek, commit, scrubL}
  right ∈ {none, sweep, release, openR}
minus (none, none), hence 15 pairs.
-/
def StrandedTokenV3
    (l r : R2CoherenceV31.Cell ψ κ τ) : Prop :=
  r.ctl.tok ≠ .seek ∧
  l.ctl.tok ≠ .sweep ∧
  r.ctl.tok ≠ .commit ∧
  l.ctl.tok ≠ .release ∧
  r.ctl.tok ≠ .scrubL ∧
  l.ctl.tok ≠ .openR ∧
  ¬ (l.ctl.tok = .none ∧ r.ctl.tok = .none)

/-- Token-only, so the V3.2 wrapper can branch on this predicate directly. -/
instance strandedTokenV3Decidable
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    Decidable (StrandedTokenV3 l r) := by
  unfold StrandedTokenV3
  infer_instance

/--
Canonical V3.2 restart for every one of the 15 stranded token pairs.

Do not attempt to execute a directional stage on a token sitting on the wrong
endpoint.  Instead discard the uncaught left token, put both endpoints in the
closing lane, and launch the already-existing responder SEEK.  No physical
coordinate is changed here; the ordinary sweep will clear main material later.
-/
def normalizeStrandedV3
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    R2CoherenceV31.Cell ψ κ τ × R2CoherenceV31.Cell ψ κ τ :=
  (R2CoherenceV31.setControl l .closing .none,
   R2CoherenceV31.startClosing r)

@[simp] theorem normalizeStrandedV3_left_tok
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    (normalizeStrandedV3 l r).1.ctl.tok = .none := by
  rfl

@[simp] theorem normalizeStrandedV3_right_tok
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    (normalizeStrandedV3 l r).2.ctl.tok = .seek := by
  rfl

/-- The normalizer is controller-only on both endpoints. -/
theorem normalizeStrandedV3_physical
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    (normalizeStrandedV3 l r).1.phys = l.phys ∧
      (normalizeStrandedV3 l r).2.phys = r.phys := by
  exact ⟨rfl, rfl⟩

/--
The only fact needed for strict movement is that the input responder was not
already SEEK.  This is the first conjunct of `StrandedTokenV3`.
-/
theorem normalizeStrandedV3_moves_of_right_not_seek
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (h : r.ctl.tok ≠ .seek) :
    normalizeStrandedV3 l r ≠ (l, r) := by
  intro heq
  have ht :
      (normalizeStrandedV3 l r).2.ctl.tok = r.ctl.tok :=
    congrArg
      (fun p :
        R2CoherenceV31.Cell ψ κ τ × R2CoherenceV31.Cell ψ κ τ =>
        p.2.ctl.tok)
      heq
  apply h
  exact ht.symm.trans (normalizeStrandedV3_right_tok l r)

/-- All 15 stranded pairs move.  No residual case hypothesis remains. -/
theorem normalizeStrandedV3_moves
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    StrandedTokenV3 l r →
      normalizeStrandedV3 l r ≠ (l, r) := by
  intro h
  exact normalizeStrandedV3_moves_of_right_not_seek l r h.1

/--
Stronger than the requested conditional statement: the canonical output is
never stranded, for any input pair, because its responder is definitionally
SEEK and therefore satisfies `rowV3`'s first active-token guard.
-/
theorem normalizeStrandedV3_not_stranded
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    ¬ StrandedTokenV3
      (normalizeStrandedV3 l r).1
      (normalizeStrandedV3 l r).2 := by
  intro h
  exact h.1 (normalizeStrandedV3_right_tok l r)

#print axioms ZZStrandedNormalizerV32.normalizeStrandedV3_moves
#print axioms ZZStrandedNormalizerV32.normalizeStrandedV3_not_stranded

end ZZStrandedNormalizerV32
