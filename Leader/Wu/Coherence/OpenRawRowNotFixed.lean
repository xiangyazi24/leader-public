import Leader.Wu.Coherence.SixTokenController
import Leader.Wu.Birth.ShortWaitTerminalEntryRepair

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceOpenRawRowNotFixed

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open BirthShortWait BirthShortWaitTerminalEntryRepair

variable {n psi kappa tau width : Nat}

/-! IMPORTANT: proof-level inequality below is `≠` (Prop), not `!=` (Bool). -/

private theorem terminalInactiveClear_left_h_field
    (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) :
    (terminalInactiveClear hwidth hle l r).1.h_field = l.h_field := by
  unfold terminalInactiveClear
  split <;> rfl

private theorem waitWidthCarry_left_h_field
    (hwidth : 0 < width) (hle : width <= psi) (cap : Nat)
    (l r : AgentState psi) :
    (waitWidthCarry hwidth hle cap l r).1.h_field = l.h_field := by
  unfold waitWidthCarry
  split
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl
  · rfl

private theorem waitWidthReset_left_h_field
    (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) :
    (waitWidthReset hwidth hle l r).1.h_field = l.h_field := by
  unfold waitWidthReset
  split
  · split <;> rfl
  · rfl

private theorem waitWidthFinish_left_h_field
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (cap : Nat) (l r : AgentState psi) :
    (waitWidthFinish hpsi hwidth hle cap l r).1.h_field = l.h_field := by
  by_cases hcap :
      r.label = widthTerminal hwidth hle ∧ r.count = cap
  · simp [waitWidthFinish, hcap]
  · simp [waitWidthFinish, hcap]

private theorem waitWidthEntry_left_h_field_eq_prepare
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (cap : Nat) (l r : AgentState psi) :
    (waitWidthEntry hpsi hwidth hle cap l r).1.h_field =
      (waitSaturatedPrepare hpsi l r).1.h_field := by
  unfold waitWidthEntry
  dsimp only
  rw [waitWidthFinish_left_h_field]
  rw [waitWidthReset_left_h_field]
  rw [waitWidthCarry_left_h_field]
  rw [terminalInactiveClear_left_h_field]

private theorem waitSaturatedPrepare_root_flips_left_h_field
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hroot : l.label.val = 0) :
    (waitSaturatedPrepare hpsi l r).1.h_field = !l.h_field := by
  have hz : l.label = (⟨0, hpsi⟩ : Fin psi) := by
    apply Fin.ext
    simpa using hroot
  cases hh : l.h_field <;>
    simp [waitSaturatedPrepare, hz, hh]

/-- Parametric WAIT fact needed by the open-plateau argument. No hypothesis
on carry/reset/count/wait or on the right endpoint is needed for the left
h-field: Prepare complements it at label zero and every later WAIT stage frames
that field. -/
theorem waitWidthEntry_root_flips_left_h_field
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (cap : Nat) (l r : AgentState psi)
    (hroot : l.label.val = 0) :
    (waitWidthEntry hpsi (by decide : 0 < 2) h2 cap l r).1.h_field =
      !l.h_field := by
  calc
    (waitWidthEntry hpsi (by decide : 0 < 2) h2 cap l r).1.h_field =
        (waitSaturatedPrepare hpsi l r).1.h_field :=
      waitWidthEntry_left_h_field_eq_prepare
        hpsi (by decide : 0 < 2) h2 cap l r
    _ = !l.h_field :=
      waitSaturatedPrepare_root_flips_left_h_field hpsi l r hroot

end R2CoherenceOpenRawRowNotFixed

