import Leader.Wu.Coherence.QuarantineReach

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31QuarantineTokens

open R2CoherenceV31
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach

variable {n ψ κ τ : Nat}

@[simp] theorem quarantineInit_tok_none
    (C : FC n ψ κ τ) (i : Fin n) :
    (quarantineInitV31 C i).ctl.tok = .none := by
  simp [quarantineInitV31, setControl]

@[simp] theorem quarantineInit_mark_closing
    (C : FC n ψ κ τ) (i : Fin n) :
    (quarantineInitV31 C i).ctl.mark = .closing := by
  simp [quarantineInitV31, setControl]

/-- The four-way tokenless census collapses at quarantine: both marks are
closing, hence neither the sealed nor open sub-arm is available. -/
theorem branchAtV3_quarantineInit_mixed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) :
    branchAtV3 hψ h2
      (quarantineInitV31 C e)
      (quarantineInitV31 C (ring.rightNeighbor e)) = .mixed := by
  simp [branchAtV3, quarantineInitV31, setControl]

private theorem rowV3_closing_none_tok
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hlm : l.ctl.mark = .closing) (hrm : r.ctl.mark = .closing)
    (hlt : l.ctl.tok = .none) (hrt : r.ctl.tok = .none) :
    let q := rowV3 hψ (by decide : 0 < 2) h2 l r
    (q.1.ctl.tok = .none ∨ q.1.ctl.tok = .seek) ∧
      (q.2.ctl.tok = .none ∨ q.2.ctl.tok = .seek) := by
  have hr : rowV3 hψ (by decide : 0 < 2) h2 l r =
      normalizePassiveV3 l r := by
    simp [rowV3, ordinaryStageV3, hlt, hrt, hlm, hrm]
  rw [hr]
  unfold normalizePassiveV3
  split <;> simp [startClosing, setControl, hlt, hrt]

/-- Pair-local token result; no configuration-step unfolding occurs here. -/
theorem rowV3_quarantineInit_tok
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) :
    let q := rowV3 hψ (by decide : 0 < 2) h2
      (quarantineInitV31 C e)
      (quarantineInitV31 C (ring.rightNeighbor e))
    (q.1.ctl.tok = .none ∨ q.1.ctl.tok = .seek) ∧
      (q.2.ctl.tok = .none ∨ q.2.ctl.tok = .seek) := by
  apply rowV3_closing_none_tok hψ h2
  · exact quarantineInit_mark_closing C e
  · exact quarantineInit_mark_closing C (ring.rightNeighbor e)
  · exact quarantineInit_tok_none C e
  · exact quarantineInit_tok_none C (ring.rightNeighbor e)

/-- Global one-step result obtained only from pair locality plus `stepV3_other`. -/
theorem stepV3_from_quarantineInit_tok
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n) :
    (stepV3 hψ h2 ring (quarantineInitV31 C) e p).ctl.tok = .none ∨
      (stepV3 hψ h2 ring (quarantineInitV31 C) e p).ctl.tok = .seek := by
  have hp := rowV3_quarantineInit_tok hψ h2 ring C e
  by_cases hpe : p = e
  · subst p
    simpa [stepV3, protocolV3, PopulationProtocol.step] using hp.1
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      simpa [stepV3, protocolV3, PopulationProtocol.step, hpe] using hp.2
    · rw [stepV3_other hψ h2 ring (quarantineInitV31 C) e p hpe hpr]
      exact Or.inl (quarantineInit_tok_none C p)

/-- In particular the first quarantine service cannot create `scrubL`. -/
theorem stepV3_from_quarantineInit_no_scrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n) :
    (stepV3 hψ h2 ring (quarantineInitV31 C) e p).ctl.tok ≠ .scrubL := by
  rcases stepV3_from_quarantineInit_tok hψ h2 ring C e p with h | h
  · rw [h]; decide
  · rw [h]; decide

end R2CoherenceV31QuarantineTokens
