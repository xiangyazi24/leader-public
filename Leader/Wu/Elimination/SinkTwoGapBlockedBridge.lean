import Leader.Wu.Elimination.SinkTwoGapAbsorptionDrop


set_option autoImplicit false


open LDSinkGapCleanup LDTwoGapFrame
open LDSinkTwoGapNoResetKernel
open FiniteUniformStoppingTree


namespace LDSinkTwoGapEntrance


variable {n ψ : Nat}


/-- `UniqueLiveShot` is stronger than uniqueness among LIVE bullets: its final
clause says that every nonzero attack-sector bullet has the tagged index.
Consequently, once position `1` is known nonzero, every position `2..d` is
zero. -/
private theorem uniqueLiveShot_tail_zero
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hshot : UniqueLiveShot F C)
    (h1 : (C (F.attack.pos 1)).bullet = (2 : Fin 3)) :
    ∀ k, 2 ≤ k → k ≤ F.attack.d →
      (C (F.attack.pos k)).bullet = (0 : Fin 3) := by
  rcases hshot with ⟨t, ht0, htd, _htLive, huniq⟩
  have h1d : 1 ≤ F.attack.d := by omega
  have h1nz : (C (F.attack.pos 1)).bullet ≠ (0 : Fin 3) := by
    rw [h1]
    decide
  have h1t : 1 = t := huniq 1 (by omega) h1d h1nz
  intro k hk2 hkd
  by_cases hk0 : (C (F.attack.pos k)).bullet = (0 : Fin 3)
  · exact hk0
  · have hkt : k = t := huniq k (by omega) hkd hk0
    omega


/-- The invariant plus a failed attempt already supplies the first two
conjuncts of `GapBlocked`: the parked tag puts the unique nonzero attack bullet
at position `1`, and uniqueness clears the entire tail. -/
theorem blocked_bullet_shape_of_invariant_failure
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (hI : AInvariant hψ F x)
    (hf : attemptStepRaw hψ F x e = .failure) :
    (x.conf (F.attack.pos 1)).bullet = (2 : Fin 3) ∧
      (∀ k, 2 ≤ k → k ≤ F.attack.d →
        (x.conf (F.attack.pos k)).bullet = (0 : Fin 3)) := by
  have hfailure := (attemptStepRaw_failure_iff hψ F x e).1 hf
  have hparked : x.phase = .parked := hfailure.2.1
  have h1 : (x.conf (F.attack.pos 1)).bullet = (2 : Fin 3) :=
    hI.tag.parked_iff.mp hparked
  exact ⟨h1, uniqueLiveShot_tail_zero F x.conf hI.tag.shot h1⟩


/-- **Single remaining kernel-local seam.**


`NoResetAbsorbedAt` records protection in the post-state through `Loss`, whereas
`GapBlocked` asks for the victim's shield/signal in the pre-state.  The exposed
public absorption interface does not provide the converse theorem saying that
an observational `Loss` at the victim edge came from the post-FIRE
`ProtectedGuard`.  This one field is exactly that pre-state implication; no
bullet-tail or geometry fact is left in the residual. -/
structure BlockedProtectionResidual (hψ : ψ > 0)
    (F : TwoGapFrame n) : Prop where
  victim_preprotected :
    ∀ (x : AState n ψ) (e : Fin n),
      AInvariant hψ F x →
      attemptStepRaw hψ F x e = .failure →
      (x.conf (F.attack.pos 0)).shield = true ∨
        (x.conf (F.attack.pos 0)).signal_B = (1 : Fin 2)


/-- Final blocked bridge, conditional only on the one kernel-local protection
residual above.  The two bullet conjuncts are proved from `AInvariant` itself. -/
theorem blocked_of_invariant_failure
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : BlockedProtectionResidual hψ F)
    (x : AState n ψ) (e : Fin n)
    (hI : AInvariant hψ F x)
    (hf : attemptStepRaw hψ F x e = .failure) :
    GapBlocked F.attack x.conf := by
  have hb := blocked_bullet_shape_of_invariant_failure hψ F x e hI hf
  exact ⟨hb.1, hb.2, hR.victim_preprotected x e hI hf⟩


#print axioms LDSinkTwoGapEntrance.blocked_bullet_shape_of_invariant_failure
#print axioms LDSinkTwoGapEntrance.blocked_of_invariant_failure


end LDSinkTwoGapEntrance
