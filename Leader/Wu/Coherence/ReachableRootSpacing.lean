import Leader.Wu.Coherence.ReachablePsiWindowLinear
import Leader.Wu.Coherence.BirthQuarantine

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableRootSpacing

open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure2
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableFacts
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFreshSeek R2CoherenceV31ReachableFreshSeek2

variable {n ψ κ τ : Nat}

/-- The useful root-spacing formulation is exactly window linearity:
inside one computed ψ-window, offset d has label d. -/
abbrev RootSpacingV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  PsiWindowLinearV31 ring C

private theorem groupPos_eq_of_labels_rs
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hLab i]

private theorem rootSpacing_of_same_labels
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (h : RootSpacingV31 ring C) : RootSpacingV31 ring D := by
  unfold RootSpacingV31 PsiWindowLinearV31 at h ⊢
  intro j d
  rw [groupPos_eq_of_labels_rs ring hLab j d.val]
  rw [hLab]
  exact h j d

/-- Exact branch census: every service preserves the root predicate at every
cell.  In particular there is no label-changing arm to analyze separately. -/
theorem atRootB_stepV3_iff
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n) :
    atRootB (stepV3 hψ h2 ring C e p) = atRootB (C p) := by
  unfold atRootB
  rw [stepV3_labels_eq_or_held hψ h2 ring C e p]

/-- Consequently the full spacing/linearity invariant is preserved by every
branch, without inspecting `branchAtV3`. -/
theorem rootSpacing_stepV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : RootSpacingV31 ring C) :
    RootSpacingV31 ring (stepV3 hψ h2 ring C e) := by
  apply rootSpacing_of_same_labels ring
  · exact stepV3_labels_eq_or_held hψ h2 ring C e
  · exact h

/-- `quarantineInitV31` changes only the controller, so spacing at quarantine
is exactly spacing of the inherited physical birth configuration. -/
theorem rootSpacing_quarantineInit_iff
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    RootSpacingV31 ring (quarantineInitV31 C) ↔ RootSpacingV31 ring C := by
  constructor
  · intro h
    apply rootSpacing_of_same_labels ring (C := quarantineInitV31 C)
      (D := C)
    · intro p
      rfl
    · exact h
  · intro h
    apply rootSpacing_of_same_labels ring (C := C)
      (D := quarantineInitV31 C)
    · intro p
      rfl
    · exact h

/-- The actual missing base clause.  The current producer entrance guarantees
one ready 0..ψ-1 train, but not global absence of additional roots. -/
def BirthRootSpacingV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    BirthEntranceV1 hψ h2 ring C → RootSpacingV31 ring C


theorem psiWindowLinearReachable_of_birthRootSpacing
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hBirthSpacing : BirthRootSpacingV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    PsiWindowLinearReachableV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro C hReach _hGeom
  rcases hReach with ⟨C0, w, hBirth, rfl⟩
  have h0 : RootSpacingV31 ring C0 := hBirthSpacing C0 hBirth
  have carry :
      ∀ (v : List (Fin n)) (D : FC n ψ κ τ),
        RootSpacingV31 ring D →
          RootSpacingV31 ring
            (v.foldl (stepV3 hψ h2 ring) D) := by
    intro v
    induction v with
    | nil =>
        intro D hD
        simpa using hD
    | cons e v ih =>
        intro D hD
        simp only [List.foldl_cons]
        exact ih (stepV3 hψ h2 ring D e)
          (rootSpacing_stepV3 hψ h2 ring D e hD)
  exact carry w C0 h0

/-- Therefore the footprint containment follows from precisely the new
producer-side root-spacing entrance clause. -/
theorem pendingFootprintContainmentReachable_of_birthRootSpacing
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hBirthSpacing : BirthRootSpacingV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    PendingFootprintContainmentReachableV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  exact pendingFootprintContainmentReachable_of_psiWindowLinear
    hψ h2 ring
    (psiWindowLinearReachable_of_birthRootSpacing
      hψ h2 ring hBirthSpacing)

/-- A weaker producer target sufficient for FreshSeek can avoid global spacing:
only windows which contain a pending openR root need be anchored at that root.
This is the exact locality suggested if the global birth contract cannot be
strengthened. -/
def PendingOwnerWindowAnchoredV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (owner j : Fin n) (ko q : Fin ψ),
    PendingOpenROwnerV31 ring C owner →
    R2Coherence.groupPos ring (eraseCfgV3 C) j ko.val = owner →
      R2Coherence.groupStart ring (eraseCfgV3 C)
        (R2Coherence.groupPos ring (eraseCfgV3 C) j q.val) = owner

theorem pendingOwnerWindowAnchored_stepV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : PendingOwnerWindowAnchoredV31 ring C)
    (hPendingFrame : ∀ owner,
      PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner →
      PendingOpenROwnerV31 ring C owner) :
    PendingOwnerWindowAnchoredV31 ring (stepV3 hψ h2 ring C e) := by
  intro owner j ko q hp hHit
  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  have hko := groupPos_eq_of_labels_rs ring hLab j ko.val
  have hq := groupPos_eq_of_labels_rs ring hLab j q.val
  have hpC := hPendingFrame owner hp
  have hHitC :
      R2Coherence.groupPos ring (eraseCfgV3 C) j ko.val = owner := by
    exact hko.symm.trans hHit
  have hOld := h owner j ko q hpC hHitC
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hq' :
      R2Coherence.groupPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val = front := by
    simpa [front] using hq
  have hLabel :
      (R2Coherence.raw
        ((eraseCfgV3 (stepV3 hψ h2 ring C e)) front)).label =
      (R2Coherence.raw ((eraseCfgV3 C) front)).label := by
    change
      (raw (stepV3 hψ h2 ring C e front)).label =
        (raw (C front)).label
    exact hLab front
  unfold R2Coherence.groupStart at hOld ⊢
  rw [hq']
  rw [hLabel]
  simpa [front] using hOld

/-
STOP / decision.

There is no first failing transition arm: all V3.1 arms preserve labels exactly,
so `RootSpacingV31` is branch-invariant by `rootSpacing_stepV3`.

The first unclosed clause is the entrance proposition `BirthRootSpacingV31`.
`BirthEntranceV31` specifies labels 0..ψ-1 only on one ready train window and
leaves other cells unconstrained; `BirthEntranceV1` adds only
`ElectionGeometryV31`.  Therefore the current source does not imply global
`PsiWindowLinearV31` at quarantine.  If strengthening the birth contract is too
strong, the next target should be the local `PendingOwnerWindowAnchoredV31`
base/preservation package rather than global root spacing.
-/

end R2CoherenceV31ReachableRootSpacing
