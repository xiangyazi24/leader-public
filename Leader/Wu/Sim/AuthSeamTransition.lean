import Leader.Wu.Sim.AuthHygieneTransition
import Leader.Wu.Authorization.SeamHygiene

/-!
# Bounded-carrier local transition for the `PPLLAuthSeam` variants

Same erase-run-reify wrapper as `PPLLAuthSimChamp.champTransitionCfg`, for
`PPLLAuthSeam.seamStepA` (the EpisodeCap counter rides in `Marks.episodes`, the arm latch in `Marks.armed`; it is
`seamStep` for every variant without `episodeCap`).  `localTransition` resolves the names of
`PPLLAuthSeam.variants` first, then defers to `PPLLAuthSimChamp.localTransition`
(`"authFchamp"`, `"authFplusmcc"`, ...).
-/

set_option autoImplicit false

namespace PPLLAuthSimSeam

open PPLLAuthSim PPLLAuthF PPLLAuthSeam

def seamTransitionCfg {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : SeamCfg) :
    AuthB ψ κ → AuthB ψ κ → Except String (AuthB ψ κ × AuthB ψ κ) :=
  fun a b => do
    let ((q, ep), ar) := seamStepA hψ κ c (toState a) (toState b) a.m.episodes b.m.episodes
      a.m.armed b.m.armed
    let a' ← (reifyCore (κ := κ) q.1.core).mapError fun e =>
      s!"seam({repr c}): left output out of domain ({e})"
    let b' ← (reifyCore (κ := κ) q.2.core).mapError fun e =>
      s!"seam({repr c}): right output out of domain ({e})"
    pure (⟨a', { marksOf q.1 with episodes := ep.1, armed := ar.1 }⟩,
          ⟨b', { marksOf q.2 with episodes := ep.2, armed := ar.2 }⟩)

def localTransition (variant : String) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    Except String (AuthB ψ κ → AuthB ψ κ → Except String (AuthB ψ κ × AuthB ψ κ)) :=
  match PPLLAuthSeam.variants.find? (fun t => t.1 == variant) with
  | some (_, c) => .ok (seamTransitionCfg hψ κ c)
  | none =>
    if variant = "authFchampNF" then .ok (PPLLAuthSimChamp.champTransitionCfg hψ κ PPLLAuthChamp.authFchampNF)
    else PPLLAuthSimChamp.localTransition variant hψ κ

end PPLLAuthSimSeam
