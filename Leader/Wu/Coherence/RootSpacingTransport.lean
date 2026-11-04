import Leader.Wu.Coherence.ReachableSoundParametric
import Leader.Wu.Coherence.ReachableRootSpacing

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31RootSpacingTransport

open R2CoherenceV31
open R2CoherenceV31ReachableSoundParametric
open R2CoherenceV31ReachableRootSpacing

theorem rootSpacing_of_reachableFromV31
    {n ψ κ τ : Nat}
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) {ring : DirectedRing n}
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hbase : ∀ C0 : R2CoherenceV31.FC n ψ κ τ,
      Entrance C0 → RootSpacingV31 ring C0)
    (C : R2CoherenceV31.FC n ψ κ τ)
    (hReach : ReachableFromV31 Entrance hψ h2 ring C) :
    RootSpacingV31 ring C := by
  rcases hReach with ⟨C0, w, hEnt, rfl⟩
  have carry :
      ∀ (v : List (Fin n)) (D : R2CoherenceV31.FC n ψ κ τ),
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
  exact carry w C0 (hbase C0 hEnt)

end R2CoherenceV31RootSpacingTransport
