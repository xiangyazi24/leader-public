import Leader.Wu.Coherence.PassiveStutterController

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV3Recovery

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open BirthLeaderlessBirthMassRenewal
open R2CoherenceV3

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩

private def literal (lab : Fin 3)
    (path : BoundedPathInfo 3 := .bot) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := .none
      path := path
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

private def sealedCell (p : R2.Cell 3 3 48) : Cell 3 3 48 :=
  ⟨p, ⟨.sealed, .none⟩⟩

private def closingCell (p : R2.Cell 3 3 48) : Cell 3 3 48 :=
  ⟨p, ⟨.closing, .none⟩⟩

/-- Tokenless orphan-passive trap.  The sealed root is deliberately not
`MainClear`; the two closing cells prevent any sealed/sealed service. -/
private def orphanPassive : R2CoherenceV3.FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => sealedCell (literal 0 (.some 0 0))
  | 1 => closingCell (literal 1)
  | _ => closingCell (literal 2)

/-- Closed field image: all tokens are absent, and the sealed cell is dirty. -/
theorem orphanPassive_fields :
    (orphanPassive 0).ctl = ⟨.sealed, .none⟩ ∧
      (orphanPassive 1).ctl = ⟨.closing, .none⟩ ∧
      (orphanPassive 2).ctl = ⟨.closing, .none⟩ ∧
      (raw (orphanPassive 0)).path = .some 0 0 ∧
      (∀ i : Fin 3, (orphanPassive i).ctl.tok = .none) := by
  decide +kernel

/-- The trap is not exploiting bad post-birth geometry. -/
theorem orphanPassive_geometry :
    AdmittedPostBirthGeometryV3 h3 ring3 orphanPassive := by
  decide +kernel

/-- No cell is `.equal`, hence CHECK/ID coherence is vacuous. -/
theorem orphanPassive_coherent :
    CoherentPrefixesV3 ring3 orphanPassive := by
  decide +kernel

/-- The sealed cell requires a main-clear group, but its own `path` is live. -/
theorem orphanPassive_not_shape :
    ¬ ControllerShapeV3 ring3 orphanPassive := by
  decide +kernel

/-- Every scheduler letter is literally a self-loop. -/
theorem orphanPassive_step_fixed :
    ∀ e i : Fin 3,
      stepV3 h3 h23 ring3 orphanPassive e i = orphanPassive i := by
  decide +kernel

private theorem orphanPassive_step_eq (e : Fin 3) :
    stepV3 h3 h23 ring3 orphanPassive e = orphanPassive := by
  funext i
  exact orphanPassive_step_fixed e i

/-- Hence every finite scheduler word is a self-loop. -/
theorem orphanPassive_run_fixed :
    ∀ w : List (Fin 3),
      w.foldl (stepV3 h3 h23 ring3) orphanPassive = orphanPassive := by
  intro w
  induction w with
  | nil => rfl
  | cons e w ih =>
      simp only [List.foldl_cons]
      rw [orphanPassive_step_eq e]
      exact ih

/-- Empty word already witnesses failure of controller soundness. -/
theorem orphanPassive_not_sound :
    ¬ ControllerSoundV3 h3 h23 ring3 orphanPassive := by
  intro h
  exact orphanPassive_not_shape
    (controllerSoundV3_shape h3 h23 ring3 orphanPassive h)

/-- Geometry and coherence hold; only controller viability fails. -/
theorem orphanPassive_not_recovered :
    ¬ RecoveredV3 h3 h23 ring3 orphanPassive := by
  intro h
  exact orphanPassive_not_sound h.2.2

private def ExitFalse : R2CoherenceV3.FC 3 3 3 48 → Prop := fun _ => False
private abbrev Step3 := stepV3 (κ := 3) (τ := 48) h3 h23 ring3
private abbrev Good3 (C : R2CoherenceV3.FC 3 3 3 48) : Prop :=
  ¬ RecoveredV3 h3 h23 ring3 C ∧ ¬ ExitFalse C

private theorem orphanPassive_good : Good3 orphanPassive := by
  exact ⟨orphanPassive_not_recovered, by simp [ExitFalse]⟩

private theorem orphanPassive_alive :
    ∀ u : List (Fin 3),
      AliveAlong Step3 Good3 orphanPassive u := by
  intro u
  induction u with
  | nil => exact orphanPassive_good
  | cons e u ih =>
      simp only [AliveAlong]
      constructor
      · exact orphanPassive_good
      · have hfix : Step3 orphanPassive e = orphanPassive :=
          orphanPassive_step_eq e
        rw [hfix]
        exact ih

private theorem orphanPassive_aliveBit_one (u : List (Fin 3)) :
    aliveBit Step3 Good3 orphanPassive u = 1 := by
  classical
  unfold aliveBit
  rw [if_pos (orphanPassive_alive u)]

private theorem wordSum_congr_length_local
    {n T : Nat} (f g : List (Fin n) → Nat)
    (h : ∀ u : List (Fin n), u.length = T → f u = g u) :
    FixedSpanRenewalPayload.wordSum n T f =
      FixedSpanRenewalPayload.wordSum n T g := by
  rw [← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro i
  exact h _ (FixedSpanRenewalPayload.rawWord_length n T i)

private theorem wordSum_const_local (n T c : Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun _ => c) = c * n ^ T := by
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun _ => c)]
  simp only [FiniteUniformStoppingTree.ofFn_sum_const]
  exact Nat.mul_comm _ _

private theorem orphanPassive_aliveCount_full (T : Nat) :
    aliveCount Step3 Good3 orphanPassive T = 3 ^ T := by
  unfold aliveCount
  calc
    FixedSpanRenewalPayload.wordSum 3 T
        (aliveBit Step3 Good3 orphanPassive) =
        FixedSpanRenewalPayload.wordSum 3 T (fun _ => 1) := by
      apply wordSum_congr_length_local
      intro u _
      exact orphanPassive_aliveBit_one u
    _ = 1 * 3 ^ T := wordSum_const_local 3 T 1
    _ = 3 ^ T := Nat.one_mul _

private theorem no_uniform_recovery_mass
    (L Q : Nat) (hQ : 2 ≤ Q) :
    ¬ UniformEscapeMass Step3 Good3 L Q := by
  intro hmass
  have h := hmass orphanPassive orphanPassive_good
  rw [orphanPassive_aliveCount_full L] at h
  have hN : 0 < 3 ^ L := Nat.pow_pos (by decide)
  have hQlt : Q - 1 < Q := by omega
  have hlt : (Q - 1) * 3 ^ L < Q * 3 ^ L :=
    (Nat.mul_lt_mul_right hN).2 hQlt
  exact (Nat.not_le_of_gt hlt) h

/-- Decisive leaf failure for the smallest empty exit predicate. -/
theorem controllerRecoveryObligationV3_false :
    ¬ ControllerRecoveryObligationV3
      (κ := 3) (τ := 48) h3 h23 ring3 ExitFalse := by
  intro h
  rcases h with ⟨L, Q, _hL, hQ, hmass⟩
  exact no_uniform_recovery_mass L Q hQ hmass

end R2CoherenceV3Recovery
