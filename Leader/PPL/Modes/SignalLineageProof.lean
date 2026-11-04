import Leader.PPL.Modes.SignalLineage

namespace PPL.Modes.SignalLineage

set_option autoImplicit false
set_option Elab.async false

/-!
Signal lineage preservation in the paper domain `2 ≤ psi`. The signal and
hit projection below records the exact three DetermineMode responder cases.
-/

def armedSignalVal {psi kappa : Nat}
    (l : PPL.State psi kappa) : Nat :=
  if l.leader = true then kappa else l.signalR.val

def bumpedHitsVal {psi kappa : Nat}
    (r : PPL.State psi kappa) : Nat :=
  Nat.min (r.hits.val + 1) psi

def DetermineModeResponderCases {psi kappa : Nat}
    (l r : PPL.State psi kappa) : Prop :=
  let q := PPL.determineMode l r
  Or
    (And (armedSignalVal l = 0)
      (And (r.signalR.val = 0)
        (And (q.2.signalR.val = 0)
          (q.2.hits.val =
            if bumpedHitsVal r = psi then 0 else bumpedHitsVal r))))
    (Or
      (And (0 < armedSignalVal l)
        (And (r.signalR.val <= armedSignalVal l)
          (And (q.2.signalR.val = armedSignalVal l)
            (q.2.hits.val = 0))))
      (And (armedSignalVal l < r.signalR.val)
        (And
          (q.2.signalR.val =
            if bumpedHitsVal r = psi then
              r.signalR.val - 1
            else
              r.signalR.val)
          (q.2.hits.val =
            if bumpedHitsVal r = psi then 0 else bumpedHitsVal r))))

private theorem determineMode_left_signalR_zero
    {psi kappa : Nat} (l r : PPL.State psi kappa) :
    (PPL.determineMode l r).1.signalR.val = 0 := by
  simp only [PPL.determineMode]
  repeat (first | rfl | split <;> try dsimp only)
  all_goals simp_all
  all_goals try (change (0 : Fin (kappa + 1)) = 0; rfl)
  all_goals repeat (first | rfl | split <;> simp_all)
  all_goals try (change (0 : Fin (kappa + 1)) = 0; rfl)
  all_goals
    by_cases hs : 0 < l.signalR.val ∨ 0 < r.signalR.val
    · simp [hs]
      split <;> change (0 : Fin (kappa + 1)) = 0 <;> rfl
    · have hzl : l.signalR.val = 0 := by
        omega
      have hzr : r.signalR.val = 0 := by
        omega
      have hz : l.signalR = 0 := Fin.ext (by simpa using hzl)
      have hrz : r.signalR = 0 := Fin.ext (by simpa using hzr)
      simp [hz, hrz]
      change (0 : Fin (kappa + 1)) = 0
      rfl

private theorem determineMode_left_hits_zero
    {psi kappa : Nat} (l r : PPL.State psi kappa) :
    (PPL.determineMode l r).1.hits.val = 0 := by
  simp only [PPL.determineMode]
  repeat (first | rfl | split <;> try dsimp only)
  all_goals simp_all
  all_goals change (0 : Fin (psi + 1)) = 0 <;> rfl

/-- The exact responder trichotomy remains an open pair-level obligation. -/
def DetermineModeSignalProjectionObligation : Prop :=
  ∀ {psi kappa : Nat}, 2 ≤ psi →
    ∀ l r : PPL.State psi kappa,
      let q := PPL.determineMode l r
      q.1.signalR.val = 0 ∧ q.1.hits.val = 0 ∧
        DetermineModeResponderCases l r

/-- PopulationProtocol.step changes no signalR/hits field away from the
initiator and responder sites. This part is protocol-generic. -/
theorem step_signal_hits_away
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Fin n -> PPL.State psi kappa)
    (e k : Fin n)
    (hke : k ≠ e)
    (hkr : k ≠ ring.rightNeighbor e) :
    And
      ((step ring C e k).signalR = (C k).signalR)
      ((step ring C e k).hits = (C k).hits) := by
  constructor
  · simp [step, PopulationProtocol.step, hke, hkr]
  · simp [step, PopulationProtocol.step, hke, hkr]

/-- The post-DetermineMode signal/hits fields are not written by the remaining
CreateLeader/MoveToken/EliminateLeaders suffix. This is the smallest physical
pair projection needed to lift determineMode_signal_projection to the full
PPL.protocol boundary. -/
def PostDetermineModeSignalStable : Prop :=
  forall {psi kappa : Nat},
    (hpsi : 2 ≤ psi) ->
    forall l r : PPL.State psi kappa,
      let d := PPL.determineMode l r
      let q := PPL.ppl hpsi l r
      And (q.1.signalR = d.1.signalR)
        (And (q.1.hits = d.1.hits)
          (And (q.2.signalR = d.2.signalR)
            (q.2.hits = d.2.hits)))

/-- Configuration-level endpoint projection from the named suffix-stability
obligation. -/
theorem step_signal_projection_of_stable
    (hstable : PostDetermineModeSignalStable)
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Fin n -> PPL.State psi kappa)
    (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) :
    let j := ring.rightNeighbor e
    let d := PPL.determineMode (C e) (C j)
    And ((step ring C e e).signalR = d.1.signalR)
      (And ((step ring C e e).hits = d.1.hits)
        (And ((step ring C e j).signalR = d.2.signalR)
          ((step ring C e j).hits = d.2.hits))) := by
  dsimp only
  have hs := hstable hpsi (C e) (C (ring.rightNeighbor e))
  rcases hs with ⟨hlr, hlh, hrr, hrh⟩
  constructor
  · simpa [step, PopulationProtocol.step, PPL.protocol,
      PPL.transition, hpsi] using hlr
  constructor
  · simpa [step, PopulationProtocol.step, PPL.protocol,
      PPL.transition, hpsi] using hlh
  constructor
  · simpa [step, PopulationProtocol.step, PPL.protocol,
      PPL.transition, hpsi, hself] using hrr
  · simpa [step, PopulationProtocol.step, PPL.protocol,
      PPL.transition, hpsi, hself] using hrh

/-! Ghost-only preservation helpers. -/

theorem ghostStep_owner_other
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e k : Fin n)
    (hke : k ≠ e)
    (hkr : k ≠ ring.rightNeighbor e) :
    (ghostStep ring g e).owner k = g.owner k := by
  unfold ghostStep
  dsimp only
  change
    (if k = e then none
      else if k = ring.rightNeighbor e then
        (if 0 <
            (step ring g.physical e
              (ring.rightNeighbor e)).signalR.val then
          winnerOwner g e (ring.rightNeighbor e)
        else
          none)
      else
        g.owner k) =
      g.owner k
  simp [hke, hkr]

theorem ghostStep_nextArm_other_of_arm
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e k : Fin n)
    (hlead : (g.physical e).leader = true)
    (hke : k ≠ e) :
    (ghostStep ring g e).nextArm k = g.nextArm k := by
  unfold ghostStep
  dsimp only
  rw [if_pos hlead]
  change
    (if k = e then g.nextArm k + 1 else g.nextArm k) =
      g.nextArm k
  simp [hke]

theorem ghostStep_nextArm_mono
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e k : Fin n) :
    g.nextArm k <= (ghostStep ring g e).nextArm k := by
  by_cases hlead : (g.physical e).leader = true
  · by_cases hke : k = e
    · subst k
      rw [ghostStep_nextArm_of_arm ring g e hlead]
      omega
    · rw [ghostStep_nextArm_other_of_arm ring g e k hlead hke]
      exact Nat.le_refl _
  · have hfalse : (g.physical e).leader = false := by
      cases h : (g.physical e).leader <;> simp_all
    rw [ghostStep_nextArm_of_no_arm ring g e hfalse]
    exact Nat.le_refl _

theorem winnerOwner_some_cases
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (e j : Fin n)
    (t : SignalTag n)
    (hwin : winnerOwner g e j = some t) :
    Or
      (And ((g.physical e).leader = true)
        (t = freshTag g e))
      (Or (g.owner e = some t)
        (g.owner j = some t)) := by
  by_cases hcmp :
      (g.physical j).signalR.val <= armedTTL g e
  · rw [winnerOwner, if_pos hcmp] at hwin
    by_cases hlead : (g.physical e).leader = true
    · have hs :
        some (freshTag g e) = some t := by
        simpa [armedOwner, hlead] using hwin
      have ht : freshTag g e = t :=
        Option.some.inj hs
      exact Or.inl ⟨hlead, ht.symm⟩
    · have he : g.owner e = some t := by
        simpa [armedOwner, hlead] using hwin
      exact Or.inr (Or.inl he)
  · rw [winnerOwner, if_neg hcmp] at hwin
    exact Or.inr (Or.inr hwin)

theorem responder_winner_of_some
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (t : SignalTag n)
    (howner :
      (ghostStep ring g e).owner (ring.rightNeighbor e) = some t) :
    winnerOwner g e (ring.rightNeighbor e) = some t := by
  rw [ghostStep_responder_owner ring g e hself] at howner
  by_cases hp :
      0 <
        (step ring g.physical e
          (ring.rightNeighbor e)).signalR.val
  · simpa [hp] using howner
  · simp [hp] at howner

theorem winnerOwner_not_owned_other
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (e j k : Fin n)
    (t : SignalTag n)
    (hwf : LineageWellFormed g)
    (hwin : winnerOwner g e j = some t)
    (hke : k ≠ e)
    (hkj : k ≠ j) :
    g.owner k ≠ some t := by
  intro hk
  rcases winnerOwner_some_cases g e j t hwin with hnew | hold
  · rcases hnew with ⟨hlead, ht⟩
    have hnot :=
      freshTag_not_preowned g e hwf.2.2 k
    apply hnot
    simpa [ht] using hk
  · rcases hold with he | hj
    · have hek := hwf.2.1 e k t he hk
      exact hke hek.symm
    · have hjk := hwf.2.1 j k t hj hk
      exact hkj hjk.symm

/-- Ghost ownership cannot clone a tag in one ghostStep. -/
theorem noCloningPreserved
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    NoCloningPreserved (psi := psi) (kappa := kappa) ring := by
  intro g e _ hself hwf
  intro i k t hi hk
  by_cases hie : i = e
  · subst i
    have hbad : False := by
      simpa [ghostStep_initiator_owner_none] using hi
    exact hbad.elim
  by_cases hke : k = e
  · subst k
    have hbad : False := by
      simpa [ghostStep_initiator_owner_none] using hk
    exact hbad.elim
  by_cases hir : i = ring.rightNeighbor e
  · subst i
    by_cases hkr : k = ring.rightNeighbor e
    · exact hkr.symm
    · have hwin :=
        responder_winner_of_some ring g e hself t hi
      have hkold : g.owner k = some t := by
        rw [← ghostStep_owner_other ring g e k hke hkr]
        exact hk
      have hnot :=
        winnerOwner_not_owned_other
          g e (ring.rightNeighbor e) k t
          hwf hwin hke hkr
      exact False.elim (hnot hkold)
  · by_cases hkr : k = ring.rightNeighbor e
    · subst k
      have hwin :=
        responder_winner_of_some ring g e hself t hk
      have hiold : g.owner i = some t := by
        rw [← ghostStep_owner_other ring g e i hie hir]
        exact hi
      have hnot :=
        winnerOwner_not_owned_other
          g e (ring.rightNeighbor e) i t
          hwf hwin hie hir
      exact False.elim (hnot hiold)
    · have hiold : g.owner i = some t := by
        rw [← ghostStep_owner_other ring g e i hie hir]
        exact hi
      have hkold : g.owner k = some t := by
        rw [← ghostStep_owner_other ring g e k hke hkr]
        exact hk
      exact hwf.2.1 i k t hiold hkold

/-- Every tag present after ghostStep is still below the next-arm counter of
its origin. Fresh line-35 tags use exactly the incremented counter. -/
theorem issuedPreserved
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    IssuedPreserved (psi := psi) (kappa := kappa) ring := by
  intro g e _ hself hwf
  intro k t hk
  by_cases hke : k = e
  · subst k
    have hbad : False := by
      simpa [ghostStep_initiator_owner_none] using hk
    exact hbad.elim
  by_cases hkr : k = ring.rightNeighbor e
  · subst k
    have hwin :=
      responder_winner_of_some ring g e hself t hk
    rcases winnerOwner_some_cases
        g e (ring.rightNeighbor e) t hwin with hnew | hold
    · rcases hnew with ⟨hlead, ht⟩
      subst t
      change
        g.nextArm e <
          (ghostStep ring g e).nextArm e
      rw [ghostStep_nextArm_of_arm ring g e hlead]
      omega
    · rcases hold with he | hr
      · have hlt := hwf.2.2 e t he
        have hmono :=
          ghostStep_nextArm_mono ring g e t.origin
        exact Nat.lt_of_lt_of_le hlt hmono
      · have hlt :=
          hwf.2.2 (ring.rightNeighbor e) t hr
        have hmono :=
          ghostStep_nextArm_mono ring g e t.origin
        exact Nat.lt_of_lt_of_le hlt hmono
  · have hold : g.owner k = some t := by
      rw [← ghostStep_owner_other ring g e k hke hkr]
      exact hk
    have hlt := hwf.2.2 k t hold
    have hmono :=
      ghostStep_nextArm_mono ring g e t.origin
    exact Nat.lt_of_lt_of_le hlt hmono

end PPL.Modes.SignalLineage

#print axioms PPL.Modes.SignalLineage.determineMode_left_signalR_zero
#print axioms PPL.Modes.SignalLineage.determineMode_left_hits_zero
#print axioms PPL.Modes.SignalLineage.step_signal_hits_away
#print axioms PPL.Modes.SignalLineage.step_signal_projection_of_stable
#print axioms PPL.Modes.SignalLineage.ghostStep_owner_other
#print axioms PPL.Modes.SignalLineage.ghostStep_nextArm_other_of_arm
#print axioms PPL.Modes.SignalLineage.ghostStep_nextArm_mono
#print axioms PPL.Modes.SignalLineage.winnerOwner_some_cases
#print axioms PPL.Modes.SignalLineage.responder_winner_of_some
#print axioms PPL.Modes.SignalLineage.winnerOwner_not_owned_other
#print axioms PPL.Modes.SignalLineage.noCloningPreserved
#print axioms PPL.Modes.SignalLineage.issuedPreserved

