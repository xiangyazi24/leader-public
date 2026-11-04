import Leader.Wu.Splice.HoldRepairChainLength
import Leader.Wu.Splice.HoldRepairLeaderlessTransfer
import Leader.Wu.Splice.ShapeClearInvariant
import Leader.Wu.Splice.LocalStepMass

set_option autoImplicit false
set_option Elab.async false

/-! # V10j: controller stutters only at hold shapes; leaderless runs have a linear physical rate

`row_stutter_shape`: if a V10j row is not physical and leaves the served pair unchanged, the pair is a stutter shape
(`StutterShapeJ`): a pending predecessor on the left, a pending victim facing a pending predecessor, or a deletion
candidate whose left cell is a reserved front facing a quiet cell.  The first two need a pending predecessor or a
victim role and the third needs a leader on the left, so on a leaderless `ShapeClear` configuration every non-physical
V10j service changes the configuration (`leaderless_no_stutter`).

`psiJ_step_le`: any single V10j service raises `PsiJ` by at most 18 (the two served cells and the three edge terms
touching them).  Hence along any word from a `SpliceSafeV7g`, `ShapeClear` configuration whose run stays leaderless,
`|w| ≤ PsiJ C + 19 * physCountG w C ≤ 7 n + 19 * physCountG w C` (`linear_rate`): at least `(|w| - 7 n) / 19` of the
services are physical, deterministically, for every scheduler word. -/

namespace B9SpliceV10jLinearRate

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
  B9SpliceV10jHoldRing B9SpliceV10eRowPotential B9SpliceV10eHandoffFollowUp B9SpliceV10ePhysicalHoldNoBirth
  B9SpliceV10jRowProgress B9SpliceV10jFirstRow B9SpliceV10hControllerRowsSafe B9SpliceV10eTransparency
  B9SpliceV10jAmortizedPotential B9SpliceV10jAmortizedChain B9SpliceV10jGlobalProgress B9SpliceLocalStepMass

variable {n psi width kappa tau : Nat}

/-! ## Stutter shapes -/

def StutterShapeJ (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    Prop :=
  (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true) ∨
  (role l.carrier = .victimArmed ∧ l.carrier.repairPending = true ∧
    role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true) ∨
  (LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice ∧ ReservedFrontHoldGuard l.carrier ∧
    ((role r.carrier = .none ∧ r.carrier.repairPending = false) ∨
     (role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = false)))

theorem role_eq_of_pair_eq {a b l r : R1AgentStateV6 psi kappa tau} (h : (a, b) = (l, r)) :
    role a.carrier = role l.carrier ∧ role b.carrier = role r.carrier ∧
      a.carrier.repairPending = l.carrier.repairPending ∧ b.carrier.repairPending = r.carrier.repairPending := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem row_stutter_shape (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hnp : ¬ PhysRow hpsi hwidth hle l r (rowV10j hpsi hwidth hle l r))
    (hw : rowV10j hpsi hwidth hle l r = (l, r)) :
    StutterShapeJ hpsi hwidth hle l r := by
  classical
  rw [rowV10j.eq_1] at hnp hw
  by_cases hd : LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice
  · rw [if_pos hd] at hnp hw
    by_cases hrf : ReservedFrontHoldGuard l.carrier
    · rw [if_pos hrf, holdRepairV10j.eq_1] at hw
      right; right
      refine ⟨hd, hrf, ?_⟩
      by_cases h1 : ReservedFrontHoldGuard r.carrier
      · rw [if_pos h1] at hw
        have h := (role_eq_of_pair_eq hw).2.1
        have h' : SpliceRole.none = role r.carrier := h
        rw [h1.1] at h'; cases h'
      rw [if_neg h1] at hw
      by_cases h2 : role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true
      · rw [if_pos h2] at hw
        have h := (role_eq_of_pair_eq hw).2.2.2
        have h' : false = r.carrier.repairPending := h
        rw [h2.2] at h'; cases h'
      rw [if_neg h2] at hw
      by_cases h3 : role r.carrier = .victimArmed ∧ r.carrier.repairPending = true
      · rw [if_pos h3] at hw
        have h := (role_eq_of_pair_eq hw).2.1
        have h' : SpliceRole.none = role r.carrier := h
        rw [h3.1] at h'; cases h'
      rw [if_neg h3] at hw
      by_cases h4 : VictimRightScrubGuardV6 r ∨ FrontRightScrubGuardV6 r ∨ MalformedRightPendingGuardV6 r
      · rw [if_pos h4] at hw
        have hr := (role_eq_of_pair_eq hw).2.1
        have hp := (role_eq_of_pair_eq hw).2.2.2
        have hr' : SpliceRole.none = role r.carrier := hr
        have hp' : false = r.carrier.repairPending := hp
        rcases h4 with hv | hf | hm
        · rw [hv.1] at hr'; cases hr'
        · rw [hf.1] at hr'; cases hr'
        · rw [hm.1] at hp'; cases hp'
      rw [if_neg h4] at hw
      cases hrole : role r.carrier with
      | none =>
          left; refine ⟨rfl, ?_⟩
          cases hp : r.carrier.repairPending
          · rfl
          · exact absurd (Or.inr (Or.inr ⟨hp, by rw [hrole]; decide, by rw [hrole]; decide, by rw [hrole]; decide⟩)) h4
      | predecessorArmed =>
          right; refine ⟨rfl, ?_⟩
          cases hp : r.carrier.repairPending
          · rfl
          · exact absurd ⟨hrole, hp⟩ h2
      | front =>
          exfalso
          cases hp : r.carrier.repairPending
          · exact h4 (Or.inr (Or.inl ⟨hrole, hp⟩))
          · exact h1 ⟨hrole, hp⟩
      | victimArmed =>
          exfalso
          cases hp : r.carrier.repairPending
          · exact h4 (Or.inl ⟨hrole, hp⟩)
          · exact h3 ⟨hrole, hp⟩
    · rw [if_neg hrf] at hnp
      exact absurd (phys_delete hpsi hwidth hle l r) hnp
  · rw [if_neg hd] at hnp hw
    by_cases hq : rowV10dg hpsi hwidth hle l r = (l, r)
    · have hg := rowV10g.eq_1 hpsi hwidth hle l r
      dsimp only at hg
      rw [if_pos hq] at hg
      rw [hg] at hnp hw
      by_cases h0 : role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true
      · exact Or.inl h0
      rw [if_neg h0] at hnp hw
      by_cases h1 : VictimRightScrubGuardV6 r
      · rw [if_pos h1] at hw
        have h' : SpliceRole.none = role r.carrier := (role_eq_of_pair_eq hw).2.1
        rw [h1.1] at h'; cases h'
      rw [if_neg h1] at hnp hw
      by_cases h2 : FrontRightScrubGuardV6 r
      · rw [if_pos h2] at hw
        have h' : SpliceRole.none = role r.carrier := (role_eq_of_pair_eq hw).2.1
        rw [h2.1] at h'; cases h'
      rw [if_neg h2] at hnp hw
      by_cases h3 : MalformedRightPendingGuardV6 r
      · rw [if_pos h3] at hw
        have h' : false = r.carrier.repairPending := (role_eq_of_pair_eq hw).2.2.2
        rw [h3.1] at h'; cases h'
      rw [if_neg h3] at hnp hw
      by_cases h4 : role r.carrier = .predecessorArmed
      · rw [if_pos h4] at hnp hw
        by_cases h5 : r.carrier.repairPending = true
        · rw [if_pos h5] at hnp hw
          by_cases h6 : ReservedFrontHoldGuard l.carrier
          · rw [if_pos h6] at hw
            have h' : false = r.carrier.repairPending := (role_eq_of_pair_eq hw).2.2.2
            rw [h5] at h'; cases h'
          rw [if_neg h6] at hw
          by_cases h7 : LeftScrubGuardV10e l
          · rw [if_pos h7] at hw
            have hr' : SpliceRole.none = role l.carrier := (role_eq_of_pair_eq hw).1
            have hp' : false = l.carrier.repairPending := (role_eq_of_pair_eq hw).2.2.1
            rcases h7 with hv | hf | hm
            · rw [hv.1] at hr'; cases hr'
            · rw [hf.1] at hr'; cases hr'
            · rw [hm.1] at hp'; cases hp'
          rw [if_neg h7] at hw
          right; left
          cases hrole : role l.carrier with
          | none =>
              exfalso
              have hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier := by
                intro h; have := h.1.1; rw [h4] at this; exact absurd this (by decide)
              have hD2 : ¬ OrphanVictimGuard l r := by intro h; have := h.1; rw [h4] at this; exact absurd this (by decide)
              have hD3 : ¬ OwnedPendingVictimGuard l r := by
                intro h; have := h.2.2.1; rw [h4] at this; exact absurd this (by decide)
              have hD4 : OwnerlessPendingPredGuard l r := ⟨hrole, h4, h5⟩
              have hrow : rowV10dg hpsi hwidth hle l r = (fenceV6 l, settleV6 r) := by
                rw [rowV10dg.eq_1, if_neg hD1, if_neg hD2, if_neg hD3, if_pos hD4]
              rw [hrow] at hq
              have hp := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau =>
                z.2.carrier.repairPending) hq
              have hs : (settleV6 r).carrier.repairPending = false := rfl
              simp only at hp
              rw [hs, h5] at hp
              exact absurd hp (by decide)
          | front =>
              exfalso
              cases hp : l.carrier.repairPending
              · exact h7 (Or.inr (Or.inl ⟨hrole, hp⟩))
              · exact h6 ⟨hrole, hp⟩
          | victimArmed =>
              cases hp : l.carrier.repairPending
              · exact absurd (Or.inl ⟨hrole, hp⟩) h7
              · exact ⟨rfl, rfl, h4, h5⟩
          | predecessorArmed =>
              exfalso
              cases hp : l.carrier.repairPending
              · have hn := rowV10dg_left_none_of_SP_PP hpsi hwidth hle l r hrole hp h4 h5
                rw [hq] at hn
                simp only at hn
                rw [hrole] at hn
                exact absurd hn (by decide)
              · exact h0 ⟨hrole, hp⟩
        · rw [if_neg h5] at hnp
          exact absurd (phys_fence hpsi hwidth hle l r) hnp
      · rw [if_neg h4] at hnp
        exact absurd (phys_hold hpsi hwidth hle l r) hnp
    · rw [rowV10g_of_change hpsi hwidth hle l r hq] at hw
      exact absurd hw hq

/-- On a leaderless `ShapeClear` configuration no pair is a stutter shape. -/
theorem not_stutterShape (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (C : R1ConfigV6 n psi kappa tau) (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hSC : B9SpliceComposedEvents.ShapeClear C) (e j : Fin n) :
    ¬ StutterShapeJ hpsi hwidth hle (C e) (C j) := by
  rintro (h | h | h)
  · have := hSC.2 e h.1; rw [h.2] at this; exact absurd this (by decide)
  · exact hSC.1 e h.1
  · have := h.1.1; rw [hlead e] at this; exact absurd this (by decide)

theorem leaderless_no_stutter (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (C : R1ConfigV6 n psi kappa tau)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hSC : B9SpliceComposedEvents.ShapeClear C) (e : Fin n)
    (hnp : ¬ PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e) :
    stepV10j hpsi hwidth hle ring C e ≠ C := by
  classical
  intro hsame
  have hself := rightNeighbor_ne_of_two_le ring hn e
  have hstep := stepV10j_eq_writeAt hpsi hwidth hle ring C e hself
  generalize hwdef : rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = w at hstep
  have h1 : w.1 = C e := by
    have := congrFun (hstep.symm.trans hsame) e
    rwa [writeAt_e] at this
  have h2 : w.2 = C (ring.rightNeighbor e) := by
    have := congrFun (hstep.symm.trans hsame) (ring.rightNeighbor e)
    rwa [writeAt_j ring C e w hself] at this
  have hweq : w = (C e, C (ring.rightNeighbor e)) := by
    cases w with
    | mk a b => simp only at h1 h2; rw [h1, h2]
  apply not_stutterShape hpsi hwidth hle C hlead hSC e (ring.rightNeighbor e)
  apply row_stutter_shape hpsi hwidth hle
  · intro hp
    apply hnp
    rw [hstep]
    have hw := physical_of_row hpsi hwidth hle ring C e hself (C e, C (ring.rightNeighbor e)) w (hwdef ▸ hp)
    rwa [B9SpliceV10hWholeStepSafe.writeAt_self] at hw
  · rw [hwdef]; exact hweq

/-! ## A service raises `PsiJ` by at most 18 -/

theorem ofFn_spike (a : Fin n) (c : Nat) : (List.ofFn (fun i : Fin n => if i = a then c else 0)).sum = c := by
  have h1 := B9SpliceTableV10d.ofFn_sum_split (fun _ : Fin n => 0) (fun i : Fin n => if i = a then c else 0) a
    (fun _ _ => Nat.zero_le _)
  have h2 := B9SpliceTableV10d.ofFn_sum_split (fun i : Fin n => if i = a then c else 0) (fun _ : Fin n => 0) a
    (fun i hi => by simp [hi])
  rw [FiniteUniformStoppingTree.ofFn_sum_const] at h1 h2
  simp only [if_pos] at h1 h2
  simp at h1 h2
  omega

theorem psiJ_step_le (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    PsiJ hpsi ring (stepV10j hpsi hwidth hle ring C e) ≤ PsiJ hpsi ring C + 18 := by
  classical
  have hself := rightNeighbor_ne_of_two_le ring (by omega) e
  rw [stepV10j_eq_writeAt hpsi hwidth hle ring C e hself]
  generalize rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = w
  let p := ring.leftNeighbor e
  have hpe : ring.rightNeighbor p = e := B9SpliceV10eGlobalProgress.rightNeighbor_leftNeighbor ring e
  have hpne : p ≠ e := fun h => by
    have := rightNeighbor_ne_of_two_le ring (by omega) p
    rw [hpe] at this; exact this h.symm
  have hpnj : p ≠ ring.rightNeighbor e := fun h => by
    have := rn_rn_ne ring hn p
    rw [hpe] at this
    exact this (by rw [← h])
  let d : Fin n → Nat := fun i =>
    (if i = p then 4 else 0) + ((if i = e then 7 else 0) + (if i = ring.rightNeighbor e then 7 else 0))
  have hd : (List.ofFn d).sum = 18 := by
    show (List.ofFn (fun i => (if i = p then 4 else 0) +
      ((if i = e then 7 else 0) + (if i = ring.rightNeighbor e then 7 else 0)))).sum = 18
    rw [FiniteUniformStoppingTree.ofFn_sum_add, FiniteUniformStoppingTree.ofFn_sum_add, ofFn_spike, ofFn_spike,
      ofFn_spike]
  have hpoint : ∀ i, edgeTermJ hpsi ring (writeAt ring C e w) i ≤ edgeTermJ hpsi ring C i + d i := by
    intro i
    unfold edgeTermJ
    have ht := cellWJ_le (writeAt ring C e w i)
    by_cases hie : i = e
    · have hdi : d i = 7 := by
        show (if i = p then 4 else 0) + ((if i = e then 7 else 0) + (if i = ring.rightNeighbor e then 7 else 0)) = 7
        rw [if_neg (by rw [hie]; exact hpne.symm), if_pos hie, if_neg (by rw [hie]; exact Ne.symm hself)]
      rw [hdi]
      omega
    by_cases hij : i = ring.rightNeighbor e
    · have hdi : d i = 7 := by
        show (if i = p then 4 else 0) + ((if i = e then 7 else 0) + (if i = ring.rightNeighbor e then 7 else 0)) = 7
        rw [if_neg (by rw [hij]; exact Ne.symm hpnj), if_neg hie, if_pos hij]
      rw [hdi]
      omega
    rw [writeAt_other ring C e w i hie hij]
    by_cases hip : i = p
    · have hdi : d i = 4 := by
        show (if i = p then 4 else 0) + ((if i = e then 7 else 0) + (if i = ring.rightNeighbor e then 7 else 0)) = 4
        rw [if_pos hip, if_neg hie, if_neg hij]
      rw [hdi]
      omega
    · have hdi : d i = 0 := by
        show (if i = p then 4 else 0) + ((if i = e then 7 else 0) + (if i = ring.rightNeighbor e then 7 else 0)) = 0
        rw [if_neg hip, if_neg hie, if_neg hij]
      have hi2 : ring.rightNeighbor i ≠ e := fun h => hip (rn_inj ring (h.trans hpe.symm))
      have hi3 : ring.rightNeighbor i ≠ ring.rightNeighbor e := fun h => hie (rn_inj ring h)
      rw [writeAt_other ring C e w _ hi2 hi3, hdi]
      omega
  have hsum := FiniteUniformStoppingTree.ofFn_sum_le _ _ hpoint
  rw [FiniteUniformStoppingTree.ofFn_sum_add, hd] at hsum
  exact hsum

/-! ## Linear rate before the first leader -/

/-- Every configuration before a service of the word is leaderless. -/
def LeaderlessBeforeJ (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau → List (Fin n) → Prop
  | _, [] => True
  | C, e :: es => (∀ i, (C i).carrier.splice.base.core.core.leader = false) ∧
      LeaderlessBeforeJ hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring C e) es

theorem linear_rate (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 3 ≤ n) (w : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau, SpliceSafeV7g hpsi ring C → B9SpliceComposedEvents.ShapeClear C →
      LeaderlessBeforeJ hpsi hwidth hle ring C w →
        w.length ≤ PsiJ hpsi ring C + 19 * physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) w C := by
  induction w with
  | nil => intro C _ _ _; exact Nat.zero_le _
  | cons e es ih =>
      intro C hS hSC hL
      classical
      have hS' := stepV10j_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS
      have hSC' : B9SpliceComposedEvents.ShapeClear (stepV10j hpsi hwidth hle ring C e) := by
        rw [B9SpliceV10jLeaderlessTransfer.stepV10j_eq_stepV10e_of_leaderless_shapeClear hpsi hwidth hle ring C
          hL.1 hSC e]
        exact B9SpliceShapeClear.stepV10e_preserves_shapeClear hpsi hwidth hle ring C e hL.1
          ((spliceSafeV7_iff_V7g_of_shapeClear hpsi ring C hSC).2 hS) hSC
      have hrest := ih _ hS' hSC' hL.2
      show es.length + 1 ≤ PsiJ hpsi ring C + 19 *
        ((if PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e then 1 else 0) +
          physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) es (stepV10j hpsi hwidth hle ring C e))
      by_cases hp : PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e
      · rw [if_pos hp]
        have hup := psiJ_step_le hpsi hwidth hle ring hn C e
        omega
      · rw [if_neg hp]
        have hch := leaderless_no_stutter hpsi hwidth hle ring (by omega) C hL.1 hSC e hp
        have hd := psiJ_drop hpsi hwidth hle ring hn C hS e hp hch
        omega

theorem linear_rate_seven (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 3 ≤ n) (w : List (Fin n)) (C : R1ConfigV6 n psi kappa tau)
    (hS : SpliceSafeV7g hpsi ring C) (hSC : B9SpliceComposedEvents.ShapeClear C)
    (hL : LeaderlessBeforeJ hpsi hwidth hle ring C w) :
    w.length ≤ 7 * n + 19 * physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) w C := by
  have h1 := linear_rate hpsi hwidth hle ring hn w C hS hSC hL
  have h2 := PsiJ_le hpsi ring C
  omega

end B9SpliceV10jLinearRate
