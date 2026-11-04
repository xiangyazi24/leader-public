import Leader.Wu.Coherence.LabelPreservation


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31Entrance


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceBranches
open R2CoherenceV31 R2CoherenceV31Closure


variable {n ψ κ τ : Nat}


/-- The missing V31 initialization map: keep the complete R2 physical state
and initialize the new controller in the neutral open/token-free state. -/
def openInitV31 (D : R2.FC n ψ κ τ) : FC n ψ κ τ :=
  fun i => ⟨D i, ⟨.open, .none⟩⟩


/-- A genuine post-birth entrance has at least one physical leader. -/
def HasLeaderV31 (C : FC n ψ κ τ) : Prop :=
  ∃ i : Fin n, (raw (C i)).leader = true


/-- Exact neutral shape intended at the instant the V31 wrapper is entered. -/
def AllOpenV31 (C : FC n ψ κ τ) : Prop :=
  ∀ i : Fin n, (C i).ctl.mark = .open ∧ (C i).ctl.tok = .none


/-- Minimal non-circular post-birth entrance contract exposed by the census.
`CoherentPrefixesV3` is deliberately not included: proving or refuting it is
the entrance obligation under audit. -/
def EntranceConfigV31
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∃ D : R2.FC n ψ κ τ,
    C = openInitV31 D ∧
    HasLeaderV31 C ∧
    AdmittedPostBirthGeometryV3 hψ ring C




theorem openInitV31_allOpen (D : R2.FC n ψ κ τ) :
    AllOpenV31 (openInitV31 D) := by
  intro i
  exact ⟨rfl, rfl⟩




theorem entrance_allOpen
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : EntranceConfigV31 hψ ring C) :
    AllOpenV31 C := by
  rcases h with ⟨D, hC, _, _⟩
  rw [hC]
  exact openInitV31_allOpen D




theorem entrance_marks_open
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : EntranceConfigV31 hψ ring C) :
    ∀ i : Fin n, (C i).ctl.mark = .open := by
  intro i
  exact (entrance_allOpen hψ ring C h i).1




theorem entrance_tokens_none
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : EntranceConfigV31 hψ ring C) :
    ∀ i : Fin n, (C i).ctl.tok = .none := by
  intro i
  exact (entrance_allOpen hψ ring C h i).2




private theorem entrance_geometry
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : EntranceConfigV31 hψ ring C) :
    AdmittedPostBirthGeometryV3 hψ ring C := by
  rcases h with ⟨_, _, _, hGeom⟩
  exact hGeom




/-- Open/none controls satisfy every guarded clause of the current structural
controller invariant vacuously. -/
theorem allOpenV31_controllerShape
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : AllOpenV31 C) :
    ControllerShapeV3 ring C := by
  unfold ControllerShapeV3
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hs
    have hi := (h i).1
    rw [hi] at hs
    cases hs
  · intro i ht
    have hi := (h i).2
    rw [hi] at ht
    cases ht
  · intro i ht
    have hi := (h i).2
    rw [hi] at ht
    cases ht
  · intro i ht
    have hi := (h i).2
    rw [hi] at ht
    cases ht




theorem entrance_controllerShape
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : EntranceConfigV31 hψ ring C) :
    ControllerShapeV3 ring C := by
  exact allOpenV31_controllerShape ring C
    (entrance_allOpen hψ ring C h)




theorem entrance_electionGeometry
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : EntranceConfigV31 hψ ring C) :
    ElectionGeometryV31 ring C := by
  exact admitted_implies_electionGeometryV31
    hψ ring C (entrance_geometry hψ ring C h)




namespace Regression


private theorem h3 : 0 < 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩


/-- Closed physical literal, following the existing V31 regression-fixture
style. -/
private def literal (lab : Fin 3)
    (leader : Bool := false)
    (state : MainState := .none)
    (path : BoundedPathInfo 3 := .bot)
    (bit : Bool := false) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
      leader := leader
      shield := leader
      gen_ws := false
      label := lab
      state := state
      path := path
      bit := bit
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
      b_carry := false
  }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩


/-- Labels are the admitted 0,1,2 cycle with a real leader at label zero.
Cell 1 is already `.equal`, but its stored component claims label zero rather
than its current label one. -/
private def stalePhysical : R2.FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => literal 0 true .none (.some 0 0) false
  | 1 => literal 1 false .equal (.some 0 0) false
  | _ => literal 2 false .none .bot false


private def staleEqualEntrance : FC 3 3 3 48 :=
  openInitV31 stalePhysical


/-- The current post-birth interface accepts the stale-equal state: it has a
leader, admitted post-birth label geometry, and the intended open/none V31
initial controller. -/
theorem staleEqualEntrance_is_entrance :
    EntranceConfigV31 h3 ring3 staleEqualEntrance := by
  refine ⟨stalePhysical, rfl, ?_, ?_⟩
  · exact ⟨0, by decide +kernel⟩
  · decide +kernel


/-- Nevertheless CHECK/ID coherence is false. Because every controller is
open/none, there is no `PrefixDead` escape; the `.equal` cell at label one
therefore has to justify component one, but its stored path carries label zero. -/
theorem staleEqualEntrance_not_coherent :
    ¬ CoherentPrefixesV3 ring3 staleEqualEntrance := by
  decide +kernel


/-- Closed witness that the minimal intended entrance contract does not imply
CHECK/ID coherence. -/
theorem entranceConfigV31_not_coherent :
    ∃ C : FC 3 3 3 48,
      EntranceConfigV31 h3 ring3 C ∧
        ¬ CoherentPrefixesV3 ring3 C := by
  exact ⟨staleEqualEntrance,
    staleEqualEntrance_is_entrance,
    staleEqualEntrance_not_coherent⟩


end Regression


end R2CoherenceV31Entrance
