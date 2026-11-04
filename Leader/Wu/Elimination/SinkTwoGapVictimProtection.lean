import Leader.Wu.Elimination.SinkTwoGapBlockedBridge


set_option autoImplicit false


open PPLL PPLLRepair
open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDTwoGapFrame
open LDSinkTwoGapNoResetKernel
open FiniteUniformStoppingTree


namespace LDSinkTwoGapEntrance


variable {n ψ : Nat}


/-- FIRE can make the initiator shielded only by preserving an old shield or
by firing an old signal-1 leader. -/
theorem fire_shield_source (hψ : ψ > 0) (l r : AgentState ψ)
    (hshield :
      (eliminateLeadersNoCollisionFire hψ l r).1.shield = true) :
    l.shield = true ∨ l.signal_B = (1 : Fin 2) := by
  unfold eliminateLeadersNoCollisionFire at hshield
  dsimp only at hshield
  split at hshield
  · rename_i hfire
    exact Or.inr hfire.2
  · exact Or.inl hshield


private theorem victim_head_ne (G : GapFrame n) (e : Fin n) :
    G.ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  have he := e.isLt
  have hd := G.hd
  have hdn := G.hdn
  by_cases ha : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self] at hv
    omega


private theorem victim_sinkStepC_at_right
    (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ G C e (G.ring.rightNeighbor e) =
      (sinkKernelC hψ (C e) (C (G.ring.rightNeighbor e))).2 := by
  have hh := victim_head_ne G e
  simp [sinkStepC, updatePair, hh, Ne.symm hh]


/-- A failed tagged attempt can only be the protected K2 absorption row.
The protected guard is on FIRE's output; `fire_shield_source` transports its
shield fact back to the pre-interaction victim. -/
theorem victim_preprotected
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n)
    (hI : AInvariant hψ F x)
    (hf : attemptStepRaw hψ F x e = .failure) :
    (x.conf (F.attack.pos 0)).shield = true ∨
      (x.conf (F.attack.pos 0)).signal_B = (1 : Fin 2) := by
  have hfailure := (attemptStepRaw_failure_iff hψ F x e).1 hf
  rcases hfailure.2 with ⟨_hparked, he, habs⟩
  subst e
  have hb :
      (x.conf (F.attack.pos 1)).bullet = (2 : Fin 3) :=
    habs.1
  have hl :
      (x.conf (F.attack.pos 0)).leader = true :=
    habs.2.1
  have hr :
      (x.conf (F.attack.pos 1)).leader = false := by
    exact hI.attack.2.1 1 (by omega) (by
      have hd := F.attack.hd
      omega)
  have hpostRight :
      (sinkKernelC hψ
          (x.conf (F.attack.pos 0))
          (x.conf (F.attack.pos 1))).2.bullet =
        (0 : Fin 3) := by
    have hp := habs.2.2.1
    change
      (sinkStepC hψ F.attack x.conf (F.attack.pos 0)
          (F.attack.pos 1)).bullet = (0 : Fin 3) at hp
    have hright :=
      victim_sinkStepC_at_right hψ F.attack x.conf (F.attack.pos 0)
    rw [gap_rightNeighbor_pos] at hright
    rw [hright] at hp
    exact hp
  have hg :
      ProtectedGuard hψ
        (x.conf (F.attack.pos 0))
        (x.conf (F.attack.pos 1)) := by
    by_cases hg :
        ProtectedGuard hψ
          (x.conf (F.attack.pos 0))
          (x.conf (F.attack.pos 1))
    · exact hg
    · have heq :=
        kernelC_eq_of_not_protected hψ
          (x.conf (F.attack.pos 0))
          (x.conf (F.attack.pos 1)) hg
      have hlive :=
        sinkKernel_live_at_leader hψ
          (x.conf (F.attack.pos 0))
          (x.conf (F.attack.pos 1)) hl hr hb
      have hz := hpostRight
      rw [heq] at hz
      exact False.elim (hlive hz)
  exact fire_shield_source hψ
    (x.conf (F.attack.pos 0))
    (x.conf (F.attack.pos 1))
    hg.2.1


/-- The last field of `BlockedProtectionResidual` is now kernel-free outside
of the single K2/R7 guard split above. -/
theorem blockedProtectionResidual
    (hψ : ψ > 0) (F : TwoGapFrame n) :
    BlockedProtectionResidual hψ F :=
  ⟨victim_preprotected hψ F⟩


#print axioms LDSinkTwoGapEntrance.fire_shield_source
#print axioms LDSinkTwoGapEntrance.victim_preprotected
#print axioms LDSinkTwoGapEntrance.blockedProtectionResidual


end LDSinkTwoGapEntrance
