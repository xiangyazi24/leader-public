import Leader.Wu.Splice.ShapeClearInvariant
import Leader.Wu.Splice.PhysicalHoldProjectionLetter
import Leader.Wu.Birth.ShortDoneTerminalFirstHit

set_option autoImplicit false

/-! # The composed leaderless run is the B7 leaderless run on the physical sub-word

From a leaderless `SpliceSafeV7` `ShapeClear` configuration, every V10e service is either a
physical service (its base projection is exactly the B7 host step) or a projection stutter.
Let `physWord w C` be the sub-word of `w` consisting of the physical services along the V10e run.
Then the V10e run of `w` stays leaderless exactly when the B7 physical run of `physWord w C`
from the projected configuration stays leaderless, and the projections of the endpoints agree. -/

namespace B9SpliceComposedLeaderless

open PPLL PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceTableV10e B9SpliceV10eTransparency
  B9SpliceV10ePhysicalIsB7Step B9SpliceV10eWordProjection B9SpliceV10eProjectionLetter
  B9SpliceComposedEvents

variable {n psi width kappa tau : Nat}

/-- The physical services along the V10e run of a word. -/
noncomputable def physWord (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : List (Fin n) → R1ConfigV6 n psi kappa tau → List (Fin n)
  | [], _ => []
  | e :: w, C => by
      classical
      exact (if PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e
        then [e] else []) ++ physWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)

theorem leaderless_iff_proj (C : R1ConfigV6 n psi kappa tau) :
    B9SpliceV10eAssembly.Leaderless C ↔
      BirthShortDoneTerminalFirstHit.Leaderless (physicalProj C) := Iff.rfl

/-- The projection of one leaderless safe ShapeClear service: a B7 step if physical, else a
stutter. -/
theorem proj_step (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hlead : B9SpliceV10eAssembly.Leaderless C) (hS : SpliceSafeV7 hpsi ring C)
    (hSC : ShapeClear C) :
    (PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e →
      physicalProj (stepV10e hpsi hwidth hle ring C e) =
        BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring (physicalProj C) e) ∧
    (¬ PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e →
      physicalProj (stepV10e hpsi hwidth hle ring C e) = physicalProj C) := by
  have hne := rightNeighbor_ne_self ring hn e
  refine ⟨fun hp => ?_, fun hnp => ?_⟩
  · exact physicalService_is_hostStep hpsi hwidth hle ring C _ e hp
      (fun i hi hj => by rw [stepV10e_other hpsi hwidth hle ring C e i hi hj])
  · exact stutter_frame hpsi hwidth hle ring C e hne hlead hS hnp
      (noCommit_of_shapeClear ring C e hSC)

theorem leaderlessAlong_append_single (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (P : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (es : List (Fin n)) :
    BirthShortDoneTerminalFirstHit.LeaderlessAlong hpsi hwidth hle ring P ([e] ++ es) ↔
      BirthShortDoneTerminalFirstHit.Leaderless P ∧
        BirthShortDoneTerminalFirstHit.LeaderlessAlong hpsi hwidth hle ring
          (BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring P e) es := Iff.rfl

/-- Main equivalence: the composed run is leaderless iff the B7 run on the physical sub-word is. -/
theorem leaderlessAlong_iff_physWord (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (w : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau, SpliceSafeV7 hpsi ring C → ShapeClear C →
      (LeaderlessAlong hpsi hwidth hle ring w C ↔
        BirthShortDoneTerminalFirstHit.LeaderlessAlong hpsi hwidth hle ring (physicalProj C)
          (physWord hpsi hwidth hle ring w C)) := by
  induction w with
  | nil =>
    intro C _ _
    exact Iff.rfl
  | cons e w ih =>
    intro C hS hSC
    classical
    -- both sides start with leaderlessness of C (the right side through the projection)
    have key : B9SpliceV10eAssembly.Leaderless C →
        (LeaderlessAlong hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e) ↔
          BirthShortDoneTerminalFirstHit.LeaderlessAlong hpsi hwidth hle ring (physicalProj C)
            (physWord hpsi hwidth hle ring (e :: w) C)) := by
      intro hl
      have hS' := B9SpliceV10eAssembly.stepV10e_preserves_spliceSafeV7_leaderless_final
        hpsi hwidth hle ring C e hl hS
      have hSC' := B9SpliceShapeClear.stepV10e_preserves_shapeClear
        hpsi hwidth hle ring C e hl hS hSC
      have hih := ih (stepV10e hpsi hwidth hle ring C e) hS' hSC'
      obtain ⟨hphys, hstut⟩ := proj_step hpsi hwidth hle ring hn C e hl hS hSC
      show _ ↔ BirthShortDoneTerminalFirstHit.LeaderlessAlong hpsi hwidth hle ring (physicalProj C)
        ((if PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e
          then [e] else []) ++ physWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e))
      by_cases hp : PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e
      · rw [if_pos hp, leaderlessAlong_append_single, ← hphys hp]
        exact ⟨fun h => ⟨hl, hih.1 h⟩, fun h => hih.2 h.2⟩
      · rw [if_neg hp, List.nil_append, ← hstut hp]
        exact hih
    constructor
    · intro h
      exact (key h.1).1 h.2
    · intro h
      -- extract leaderlessness of C from the head of the physical run
      have hl : B9SpliceV10eAssembly.Leaderless C := by
        by_cases hp : PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e
        · have h' : BirthShortDoneTerminalFirstHit.LeaderlessAlong hpsi hwidth hle ring
              (physicalProj C) ([e] ++ physWord hpsi hwidth hle ring w
                (stepV10e hpsi hwidth hle ring C e)) := by
            have : physWord hpsi hwidth hle ring (e :: w) C =
                [e] ++ physWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e) := by
              show (if _ then [e] else []) ++ _ = _
              rw [if_pos hp]
            rw [← this]; exact h
          exact (leaderless_iff_proj C).2 h'.1
        · have h' : BirthShortDoneTerminalFirstHit.LeaderlessAlong hpsi hwidth hle ring
              (physicalProj C) (physWord hpsi hwidth hle ring w
                (stepV10e hpsi hwidth hle ring C e)) := by
            have : physWord hpsi hwidth hle ring (e :: w) C =
                physWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e) := by
              show (if _ then [e] else []) ++ _ = _
              rw [if_neg hp, List.nil_append]
            rw [← this]; exact h
          exact (leaderless_iff_proj C).2
            (BirthShortDoneTerminalFirstHit.LeaderlessAlong.head hpsi hwidth hle ring _ _ h')
      exact ⟨hl, (key hl).2 h⟩

/-- The physical sub-word is a sub-word: its length is at most the length of the word. -/
theorem physWord_length_le (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau, (physWord hpsi hwidth hle ring w C).length ≤ w.length := by
  induction w with
  | nil => intro C; exact Nat.le_refl 0
  | cons e w ih =>
    intro C
    classical
    show ((if _ then [e] else []) ++ _).length ≤ _
    rw [List.length_append]
    have := ih (stepV10e hpsi hwidth hle ring C e)
    split <;> simp <;> omega

end B9SpliceComposedLeaderless
