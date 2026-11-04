import Leader.Wu.Splice.PhysicalHoldProjection
import Leader.Wu.Splice.PhysicalHoldLeaderlessSafe

set_option autoImplicit false

/-! # Word-level projection of the leaderless V10e controller

Iterating the projection trichotomy: on the physical bases, any leaderless service word of the
V10e controller is a word over the two-letter alphabet {B7 host step at `e`, responder relabel
at `e`}, with controller-only services erased.  The relabel is the MOVE-COMMIT ruler repair:
the responder's label becomes the initiator's label plus one, its probe and phase bits are
cleared, and nothing else (in particular no leader bit) changes. -/

namespace B9SpliceV10eWordProjection

open PPLL PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceTableV10e B9SpliceV10ePhysicalIsB7Step
  B9SpliceV10eProjection

variable {n psi width kappa tau : Nat}

/-- The base-level ruler repair of a responder by its initiator. -/
def relabelResponder (hpsi : 0 < psi) (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau :=
  { r with
    core :=
      { r.core with
        core :=
          { r.core.core with
            label := ⟨(l.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
            probe := false
            phase := false } } }

/-- The relabel at edge `e` on a physical configuration. -/
def relabelAt (hpsi : 0 < psi) (ring : DirectedRing n)
    (P : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n) :
    Fin n → ExpiringAgentState psi kappa tau :=
  fun i => if i = ring.rightNeighbor e
    then relabelResponder hpsi (P e) (P (ring.rightNeighbor e)) else P i

/-- The MOVE-COMMIT projection is the base-level relabel of the projection. -/
theorem commitProj_eq_relabelAt (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    commitProj hpsi ring C e = relabelAt hpsi ring (physicalProj C) e := rfl

/-- The relabel keeps every leader bit. -/
theorem relabelAt_leader (hpsi : 0 < psi) (ring : DirectedRing n)
    (P : Fin n → ExpiringAgentState psi kappa tau) (e i : Fin n) :
    (relabelAt hpsi ring P e i).core.core.leader = (P i).core.core.leader := by
  unfold relabelAt
  by_cases hi : i = ring.rightNeighbor e
  · subst hi; simp [relabelResponder]
  · simp [hi]

/-- The relabel changes only the responder cell. -/
theorem relabelAt_other (hpsi : 0 < psi) (ring : DirectedRing n)
    (P : Fin n → ExpiringAgentState psi kappa tau) (e i : Fin n)
    (hi : i ≠ ring.rightNeighbor e) :
    relabelAt hpsi ring P e i = P i := by
  simp [relabelAt, hi]

/-- The relabel keeps the responder's stall budget and erase/path metadata. -/
theorem relabelAt_stall (hpsi : 0 < psi) (ring : DirectedRing n)
    (P : Fin n → ExpiringAgentState psi kappa tau) (e i : Fin n) :
    (relabelAt hpsi ring P e i).stall = (P i).stall := by
  unfold relabelAt
  by_cases hi : i = ring.rightNeighbor e
  · subst hi; simp [relabelResponder]
  · simp [hi]

/-- The projected alphabet: a B7 host step or a responder relabel, each at an edge. -/
inductive ExtLetter (n : Nat)
  | host (e : Fin n)
  | relabel (e : Fin n)

/-- Run an extended word on a physical configuration. -/
def extRun (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi) (ring : DirectedRing n) :
    List (ExtLetter n) → (Fin n → ExpiringAgentState psi kappa tau) →
      (Fin n → ExpiringAgentState psi kappa tau)
  | [], P => P
  | .host e :: w, P =>
      extRun hpsi hwidth hle ring w (BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring P e)
  | .relabel e :: w, P => extRun hpsi hwidth hle ring w (relabelAt hpsi ring P e)

/-- Serve a word of edges with the V10e controller. -/
def serveWord (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi) (ring : DirectedRing n) :
    List (Fin n) → R1ConfigV6 n psi kappa tau → R1ConfigV6 n psi kappa tau
  | [], C => C
  | e :: w, C => serveWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)

/-- `ProjWord w w'`: `w'` is obtained from the service word `w` by erasing some letters and
tagging each kept letter as a host step or a relabel at the same edge. -/
inductive ProjWord : List (Fin n) → List (ExtLetter n) → Prop
  | nil : ProjWord [] []
  | stutter (e : Fin n) (w : List (Fin n)) (w' : List (ExtLetter n)) :
      ProjWord w w' → ProjWord (e :: w) w'
  | host (e : Fin n) (w : List (Fin n)) (w' : List (ExtLetter n)) :
      ProjWord w w' → ProjWord (e :: w) (.host e :: w')
  | relabel (e : Fin n) (w : List (Fin n)) (w' : List (ExtLetter n)) :
      ProjWord w w' → ProjWord (e :: w) (.relabel e :: w')

theorem ProjWord.length_le {w : List (Fin n)} {w' : List (ExtLetter n)} (h : ProjWord w w') :
    w'.length ≤ w.length := by
  induction h with
  | nil => exact Nat.le_refl 0
  | stutter e w w' _ ih => simp; omega
  | host e w w' _ ih => simp; omega
  | relabel e w w' _ ih => simp; omega

/-- Every intermediate V10e configuration along the word is leaderless. -/
def LeaderlessAlong (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : List (Fin n) → R1ConfigV6 n psi kappa tau → Prop
  | [], C => B9SpliceV10eAssembly.Leaderless C
  | e :: w, C => B9SpliceV10eAssembly.Leaderless C ∧
      LeaderlessAlong hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)

/-- One leaderless safe service, on the bases, is one extended letter or nothing. -/
theorem step_projects (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hlead : B9SpliceV10eAssembly.Leaderless C) (hS : SpliceSafeV7 hpsi ring C) :
    physicalProj (stepV10e hpsi hwidth hle ring C e) = physicalProj C ∨
    physicalProj (stepV10e hpsi hwidth hle ring C e) =
      extRun hpsi hwidth hle ring [.host e] (physicalProj C) ∨
    physicalProj (stepV10e hpsi hwidth hle ring C e) =
      extRun hpsi hwidth hle ring [.relabel e] (physicalProj C) := by
  by_cases hne : ring.rightNeighbor e = e
  · left; rw [stepV10e_self hpsi hwidth hle ring C e hne]
  · rcases projection_trichotomy hpsi hwidth hle ring C e hne hlead hS with h | h | h
    · left; exact h
    · right; left; exact h
    · right; right; rw [h.2, commitProj_eq_relabelAt]; rfl

/-- The leaderless V10e trajectory, projected on the bases, is an extended word. -/
theorem word_projects (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ (C : R1ConfigV6 n psi kappa tau),
      SpliceSafeV7 hpsi ring C → LeaderlessAlong hpsi hwidth hle ring w C →
      ∃ w' : List (ExtLetter n), ProjWord w w' ∧
        physicalProj (serveWord hpsi hwidth hle ring w C) =
          extRun hpsi hwidth hle ring w' (physicalProj C) := by
  induction w with
  | nil =>
    intro C _ _
    exact ⟨[], ProjWord.nil, rfl⟩
  | cons e w ih =>
    intro C hS hl
    have hlead : B9SpliceV10eAssembly.Leaderless C := hl.1
    have hS' : SpliceSafeV7 hpsi ring (stepV10e hpsi hwidth hle ring C e) :=
      B9SpliceV10eAssembly.stepV10e_preserves_spliceSafeV7_leaderless_final
        hpsi hwidth hle ring C e hlead hS
    obtain ⟨w', hw', heq⟩ := ih (stepV10e hpsi hwidth hle ring C e) hS' hl.2
    rcases step_projects hpsi hwidth hle ring C e hlead hS with h | h | h
    · refine ⟨w', ProjWord.stutter e w w' hw', ?_⟩
      show physicalProj (serveWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)) = _
      rw [heq, h]
    · refine ⟨.host e :: w', ProjWord.host e w w' hw', ?_⟩
      show physicalProj (serveWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)) = _
      rw [heq, h]; rfl
    · refine ⟨.relabel e :: w', ProjWord.relabel e w w' hw', ?_⟩
      show physicalProj (serveWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)) = _
      rw [heq, h]; rfl

/-- Safety is kept along any leaderless word. -/
theorem serveWord_safe (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ (C : R1ConfigV6 n psi kappa tau),
      SpliceSafeV7 hpsi ring C → LeaderlessAlong hpsi hwidth hle ring w C →
      SpliceSafeV7 hpsi ring (serveWord hpsi hwidth hle ring w C) := by
  induction w with
  | nil => intro C hS _; exact hS
  | cons e w ih =>
    intro C hS hl
    exact ih _ (B9SpliceV10eAssembly.stepV10e_preserves_spliceSafeV7_leaderless_final
      hpsi hwidth hle ring C e hl.1 hS) hl.2

/-- Number of host letters in an extended word. -/
def hostCount : List (ExtLetter n) → Nat
  | [] => 0
  | .host _ :: w => hostCount w + 1
  | .relabel _ :: w => hostCount w

/-- Number of relabel letters in an extended word. -/
def relabelCount : List (ExtLetter n) → Nat
  | [] => 0
  | .host _ :: w => relabelCount w
  | .relabel _ :: w => relabelCount w + 1

end B9SpliceV10eWordProjection
