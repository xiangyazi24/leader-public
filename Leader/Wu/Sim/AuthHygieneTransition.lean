import Leader.Wu.Sim.AuthCarrier
import Leader.Wu.Authorization.DebrisHygiene

/-!
# Bounded-carrier local transition for `authFchamp`

`PPLLAuthSim.localTransition` looks variants up by name in `PPLLAuthF.variants`, which
`authFchamp` (a `PPLLAuthChamp.ChampCfg`, not a `PPLLAuthF.Cfg`) is not part of and cannot
be added to without editing `PPLLAuthF.lean`. This module supplies the same
erase-run-reify wrapper for `PPLLAuthChamp.champStep authFchamp` on `PPLLAuthSim.AuthB`, so
every census tool built on `AuthB`/`Marks` (`ZZStage3Global`-style exact closures,
`ZZSimClaimsAuth`-style random batteries) can compare `authFplusmcc` and `authFchamp` on
the same bounded carrier without reimplementing the codec.
-/

set_option autoImplicit false

namespace PPLLAuthSimChamp

open PPLLAuthSim PPLLAuthF PPLLAuthChamp

/-- The champion local transition on the bounded carrier, parametric in the `ChampCfg`:
erase to `AuthState`, run `champStep` under the given config, reify the two output cores
back into `BoundedAgentState`. Used both for `authFchamp` itself (via `champTransition`
below) and for the seed-83/152/309 regression ablation (each of the four flags
individually disabled), `run/verification/g62/champ/REGRESSION.md`. -/
def champTransitionCfg {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : ChampCfg) :
    AuthB ψ κ → AuthB ψ κ → Except String (AuthB ψ κ × AuthB ψ κ) :=
  fun a b => do
    let q := champStep hψ κ c (toState a) (toState b)
    let a' ← (reifyCore (κ := κ) q.1.core).mapError fun e =>
      s!"champ({repr c}): left output out of domain ({e})"
    let b' ← (reifyCore (κ := κ) q.2.core).mapError fun e =>
      s!"champ({repr c}): right output out of domain ({e})"
    pure (⟨a', marksOf q.1⟩, ⟨b', marksOf q.2⟩)

/-- The champion local transition on the bounded carrier under `authFchamp` itself. -/
def champTransition {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    AuthB ψ κ → AuthB ψ κ → Except String (AuthB ψ κ × AuthB ψ κ) :=
  champTransitionCfg hψ κ authFchamp

/-- Dispatch by name: `"authFchamp"` uses `champTransition`; every other name defers to
`PPLLAuthSim.localTransition` (so `"authFplusmcc"` and the rest of `PPLLAuthF.variants`
still work unchanged). -/
def localTransition (variant : String) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    Except String (AuthB ψ κ → AuthB ψ κ → Except String (AuthB ψ κ × AuthB ψ κ)) :=
  if variant = "authFchamp" then .ok (champTransition hψ κ)
  else PPLLAuthSim.localTransition variant hψ κ

end PPLLAuthSimChamp
