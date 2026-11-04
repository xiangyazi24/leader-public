import Leader.Wu.Splice.ControllerRecovery
import Leader.Wu.Birth.TwoStageEscape
import Leader.Core.ModArith

set_option autoImplicit false
set_option Elab.async false

/-!
# Global controller-recovery mass

The potential is

  3 * ticketFaults + 2 * backingFaults + holes,

bounded by `6*n`. A selected recovery-active edge strictly decreases the
stopped rank. No monotonicity is asserted for unrelated host edges.
-/

namespace B9ControllerRecovery

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7
open B9OrphanToFence B9SpliceTableV10g
open B9SpliceV10hControllerRowsSafe
open B9Host B9SpliceTableHost
open BirthTwoStageEscape

variable {n psi kappa tau : Nat}

/-! ## Finite fault scans -/

private theorem fold_add_sum :
    ∀ (xs : List Nat) (acc : Nat),
      xs.foldl (fun a b : Nat => a + b) acc = acc + xs.sum
  | [], acc => by simp
  | x :: xs, acc => by
      simp only [List.foldl_cons, List.sum_cons]
      rw [fold_add_sum xs (acc + x)]
      omega

noncomputable def faultScan (P : Fin n → Prop) : Nat :=
  (List.ofFn (fun i => ind (P i))).sum

private theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  classical
  by_cases h : P <;> simp [ind, h]

private theorem ind_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  classical
  by_cases hp : P
  · have hq : Q := h hp
    simp [ind, hp, hq]
  · simp [ind, hp]

private theorem ind_eq_one {P : Prop} (h : P) : ind P = 1 := by
  classical
  simp [ind, h]

private theorem ind_eq_zero {P : Prop} (h : ¬ P) : ind P = 0 := by
  classical
  simp [ind, h]

theorem faultCount_eq_faultScan (P : Fin n → Prop) :
    faultCount P = faultScan P := by
  classical
  unfold faultCount faultScan
  rw [fold_add_sum]
  simp [ind]

private theorem faultScan_le_n (P : Fin n → Prop) : faultScan P ≤ n := by
  unfold faultScan
  calc
    (List.ofFn (fun i : Fin n => ind (P i))).sum
        ≤ (List.ofFn (fun _ : Fin n => 1)).sum :=
      FiniteUniformStoppingTree.ofFn_sum_le _ _
        (fun i => ind_le_one (P i))
    _ = n := by
      rw [FiniteUniformStoppingTree.ofFn_sum_const]
      simp

private theorem faultScan_mono (P Q : Fin n → Prop)
    (h : ∀ i, P i → Q i) : faultScan P ≤ faultScan Q := by
  unfold faultScan
  exact FiniteUniformStoppingTree.ofFn_sum_le _ _
    (fun i => ind_mono (h i))

private theorem faultScan_strict (P Q : Fin n → Prop) (a : Fin n)
    (h : ∀ i, P i → Q i) (hQa : Q a) (hPa : ¬ P a) :
    faultScan P < faultScan Q := by
  have hs := B9SpliceTableV10d.ofFn_sum_split
    (fun i : Fin n => ind (P i)) (fun i : Fin n => ind (Q i)) a
    (fun i _ => ind_mono (h i))
  have hp := ind_eq_zero hPa
  have hq := ind_eq_one hQa
  unfold faultScan
  unfold faultScan at hs
  rw [hp, hq] at hs
  omega

private theorem faultScan_le_add_one_except
    (P Q : Fin n → Prop) (a : Fin n)
    (h : ∀ i, i ≠ a → P i → Q i) :
    faultScan P ≤ faultScan Q + 1 := by
  have hs := B9SpliceTableV10d.ofFn_sum_split
    (fun i : Fin n => ind (P i)) (fun i : Fin n => ind (Q i)) a
    (fun i hi => ind_mono (h i hi))
  have ha := ind_le_one (P a)
  unfold faultScan
  unfold faultScan at hs
  omega

private theorem faultScan_le_add_two_except
    (P Q : Fin n → Prop) (a b : Fin n)
    (h : ∀ i, i ≠ a → i ≠ b → P i → Q i) :
    faultScan P ≤ faultScan Q + 2 := by
  let R : Fin n → Prop := fun i => P i ∧ i ≠ b
  have h1 : faultScan P ≤ faultScan R + 1 :=
    faultScan_le_add_one_except P R b (fun i hi hPi => ⟨hPi, hi⟩)
  have h2 : faultScan R ≤ faultScan Q + 1 :=
    faultScan_le_add_one_except R Q a (fun i hia hRi =>
      h i hia hRi.2 hRi.1)
  omega

private theorem faultScan_pos_of (P : Fin n → Prop) (a : Fin n)
    (ha : P a) : 0 < faultScan P := by
  have hs := B9SpliceTableV10d.ofFn_sum_split
    (fun _ : Fin n => 0) (fun i : Fin n => ind (P i)) a
    (fun _ _ => Nat.zero_le _)
  have hi := ind_eq_one ha
  have hz : (List.ofFn (fun _ : Fin n => 0)).sum = 0 := by
    rw [FiniteUniformStoppingTree.ofFn_sum_const]
    simp
  unfold faultScan
  rw [hz, hi] at hs
  omega

theorem ticketFaults_eq_faultScan (C : Config n psi kappa tau) :
    ticketFaults C = faultScan (fun i => BadTicket (C i)) := by
  unfold ticketFaults
  exact faultCount_eq_faultScan _

theorem backingFaults_eq_faultScan (ring : DirectedRing n)
    (C : Config n psi kappa tau) :
    backingFaults ring C =
      faultScan (fun i => BadBacking (C i) (C (ring.rightNeighbor i))) := by
  unfold backingFaults
  exact faultCount_eq_faultScan _

theorem holes_eq_faultScan (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) :
    holes hpsi ring C =
      faultScan (fun i => Hole hpsi (C i) (C (ring.rightNeighbor i))) := by
  unfold holes
  exact faultCount_eq_faultScan _

theorem recoveryPotential_le_six_mul
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) :
    recoveryPotential hpsi ring C ≤ 6 * n := by
  have hT := faultScan_le_n (fun i : Fin n => BadTicket (C i))
  have hB := faultScan_le_n
    (fun i : Fin n => BadBacking (C i) (C (ring.rightNeighbor i)))
  have hU := faultScan_le_n
    (fun i : Fin n => Hole hpsi (C i) (C (ring.rightNeighbor i)))
  rw [← ticketFaults_eq_faultScan C] at hT
  rw [← backingFaults_eq_faultScan ring C] at hB
  rw [← holes_eq_faultScan hpsi ring C] at hU
  unfold recoveryPotential
  omega

private theorem localDanger_iff_at_mass (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n) :
    LocalDanger hpsi (C e) (C (ring.rightNeighbor e)) ↔
      PreparedDangerAt hpsi ring (projectV6 C) e := by
  rfl

private theorem pairCovered_iff_at_mass (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n) :
    PairCovered (C e) (C (ring.rightNeighbor e)) ↔
      ProtectedSpliceEdgeV7g ring C e := by
  rfl

private theorem safe_of_no_garbage
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau)
    (hN : ∀ e, ¬ Garbage hpsi (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7g hpsi ring C := by
  classical
  constructor
  · intro e hd
    have hld : LocalDanger hpsi (C e) (C (ring.rightNeighbor e)) :=
      (localDanger_iff_at_mass hpsi ring C e).mpr hd
    by_cases hc : PairCovered (C e) (C (ring.rightNeighbor e))
    · exact (pairCovered_iff_at_mass ring C e).mp hc
    · exact False.elim (hN e (Or.inr ⟨hld, hc⟩))
  · constructor
    · intro i ht
      by_cases hs :
          ReservedFrontHoldGuard (C i).carrier ∨ HostFenceShapeV7 (C i)
      · exact hs
      · exact False.elim (hN i (Or.inl (Or.inl ⟨ht, hs⟩)))
    · intro i hr hp
      by_cases hb :
          ReservedFrontHoldGuard (C (ring.rightNeighbor i)).carrier ∧
            (C (ring.rightNeighbor i)).acquireTicket = false
      · exact hb
      · exact False.elim
          (hN i (Or.inl (Or.inr (Or.inr ⟨⟨hr, hp⟩, hb⟩))))

private theorem garbage_exists_of_not_safe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau)
    (hS : ¬ SpliceSafeV7g hpsi ring C) :
    ∃ e, Garbage hpsi (C e) (C (ring.rightNeighbor e)) := by
  classical
  by_cases h : ∃ e, Garbage hpsi (C e) (C (ring.rightNeighbor e))
  · exact h
  · exact False.elim (hS (safe_of_no_garbage hpsi ring C
      (fun e hg => h ⟨e, hg⟩)))

/-! ## Ring incidence and one-cell clears -/

private theorem rn_injective (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega

private theorem rn_left (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

private theorem eq_left_of_rn_eq (ring : DirectedRing n) {i x : Fin n}
    (h : ring.rightNeighbor i = x) : i = ring.leftNeighbor x := by
  apply rn_injective ring
  calc
    ring.rightNeighbor i = x := h
    _ = ring.rightNeighbor (ring.leftNeighbor x) := (rn_left ring x).symm

def clearAt (C : Config n psi kappa tau) (x : Fin n) :
    Config n psi kappa tau :=
  fun i => if i = x then clearControlV6 (C x) else C i

@[simp] theorem clearAt_hit (C : Config n psi kappa tau) (x : Fin n) :
    clearAt C x x = clearControlV6 (C x) := by
  simp [clearAt]

theorem clearAt_miss (C : Config n psi kappa tau) (x i : Fin n)
    (h : i ≠ x) : clearAt C x i = C i := by
  simp [clearAt, h]

private theorem writeAt_clear_left_eq_clearAt
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) :
    writeAt ring C e (clearControlV6 (C e), C (ring.rightNeighbor e)) =
      clearAt C e := by
  funext i
  by_cases hi : i = e
  · subst i
    rw [writeAt_e]
    simp [clearAt]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      rw [writeAt_j ring C e _ hself]
      simp [clearAt, hself]
    · rw [writeAt_other ring C e _ i hi hj]
      simp [clearAt, hi]

private theorem writeAt_clear_right_eq_clearAt
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) :
    writeAt ring C e (C e, clearControlV6 (C (ring.rightNeighbor e))) =
      clearAt C (ring.rightNeighbor e) := by
  funext i
  by_cases hi : i = e
  · subst i
    rw [writeAt_e]
    simp [clearAt, Ne.symm hself]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      rw [writeAt_j ring C e _ hself]
      simp [clearAt]
    · rw [writeAt_other ring C e _ i hi hj]
      simp [clearAt, hj]

private theorem clear_not_pending_mass (u : Cell psi kappa tau) :
    ¬ Pending (clearControlV6 u) := by
  intro h
  have bad : SpliceRole.none = .predecessorArmed := h.1
  cases bad

private theorem clear_not_badTicket_mass (u : Cell psi kappa tau) :
    ¬ BadTicket (clearControlV6 u) := by
  intro h
  have bad : (false : Bool) = true := h.1
  cases bad

private theorem localDanger_clear_left_iff
    (hpsi : 0 < psi) (l r : Cell psi kappa tau) :
    LocalDanger hpsi (clearControlV6 l) r ↔ LocalDanger hpsi l r := by
  rfl

private theorem badTicket_clearAt_imp
    (C : Config n psi kappa tau) (x i : Fin n) :
    BadTicket (clearAt C x i) → BadTicket (C i) := by
  intro h
  by_cases hi : i = x
  · subst i
    rw [clearAt_hit C x] at h
    exact False.elim (clear_not_badTicket_mass (C x) h)
  · rw [clearAt_miss C x i hi] at h
    exact h

private theorem badBacking_clearAt_badTicket_imp
    (ring : DirectedRing n) (C : Config n psi kappa tau) (x : Fin n)
    (hx : BadTicket (C x)) (i : Fin n) :
    BadBacking (clearAt C x i) (clearAt C x (ring.rightNeighbor i)) →
      BadBacking (C i) (C (ring.rightNeighbor i)) := by
  intro h
  by_cases hi : i = x
  · subst i
    rw [clearAt_hit C x] at h
    exact False.elim (clear_not_pending_mass (C x) h.1)
  · by_cases hj : ring.rightNeighbor i = x
    · rw [clearAt_miss C x i hi, hj, clearAt_hit C x] at h
      rw [hj]
      refine ⟨h.1, ?_⟩
      rintro ⟨_, ht⟩
      have bad : true = false := hx.1.symm.trans ht
      cases bad
    · rw [clearAt_miss C x i hi,
          clearAt_miss C x (ring.rightNeighbor i) hj] at h
      exact h

private theorem badBacking_clearAt_pending_imp
    (ring : DirectedRing n) (C : Config n psi kappa tau) (x : Fin n)
    (hx : Pending (C x)) (i : Fin n) :
    BadBacking (clearAt C x i) (clearAt C x (ring.rightNeighbor i)) →
      BadBacking (C i) (C (ring.rightNeighbor i)) := by
  intro h
  by_cases hi : i = x
  · subst i
    rw [clearAt_hit C x] at h
    exact False.elim (clear_not_pending_mass (C x) h.1)
  · by_cases hj : ring.rightNeighbor i = x
    · rw [clearAt_miss C x i hi, hj, clearAt_hit C x] at h
      rw [hj]
      refine ⟨h.1, ?_⟩
      rintro ⟨hfront, _⟩
      have bad : SpliceRole.predecessorArmed = .front :=
        hx.1.symm.trans hfront.1
      cases bad
    · rw [clearAt_miss C x i hi,
          clearAt_miss C x (ring.rightNeighbor i) hj] at h
      exact h

private theorem hole_clearAt_outside
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (x i : Fin n)
    (hi : i ≠ x) (hp : i ≠ ring.leftNeighbor x) :
    Hole hpsi (clearAt C x i) (clearAt C x (ring.rightNeighbor i)) →
      Hole hpsi (C i) (C (ring.rightNeighbor i)) := by
  intro h
  have hj : ring.rightNeighbor i ≠ x := by
    intro hj
    exact hp (eq_left_of_rn_eq ring hj)
  rw [clearAt_miss C x i hi,
      clearAt_miss C x (ring.rightNeighbor i) hj] at h
  exact h

private theorem hole_clear_pending_outgoing
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hB : BadBacking l r) :
    Hole hpsi (clearControlV6 l) r → Hole hpsi l r := by
  intro hD
  refine ⟨(localDanger_clear_left_iff hpsi l r).mp hD.1, ?_⟩
  intro hC
  apply hD.2
  rcases hC with hOuter | hOwner
  · rcases hOuter with hMain | hFence
    · rcases hMain with hRF | hRest
      · have bad : SpliceRole.predecessorArmed = .front :=
          hB.1.1.symm.trans hRF.1
        cases bad
      · rcases hRest with hPR | hSettled
        · exact Or.inl (Or.inl (Or.inr (Or.inl hPR)))
        · have bad : true = false := hB.1.2.symm.trans hSettled.2.1
          cases bad
    · have bad : SpliceRole.predecessorArmed = .none :=
        hB.1.1.symm.trans hFence.1
      cases bad
  · exact (hB.2 ⟨hOwner.2.2.1, hOwner.2.2.2.2⟩).elim

/-- Weight 3 pays for a ticket clear plus both incident hole slots. -/
theorem recoveryPotential_clear_badTicket_lt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (x : Fin n)
    (hx : BadTicket (C x)) :
    recoveryPotential hpsi ring (clearAt C x) <
      recoveryPotential hpsi ring C := by
  have hT : ticketFaults (clearAt C x) < ticketFaults C := by
    rw [ticketFaults_eq_faultScan, ticketFaults_eq_faultScan]
    exact faultScan_strict _ _ x
      (badTicket_clearAt_imp C x) hx (by
        intro h
        rw [clearAt_hit C x] at h
        exact clear_not_badTicket_mass (C x) h)
  have hB : backingFaults ring (clearAt C x) ≤ backingFaults ring C := by
    rw [backingFaults_eq_faultScan, backingFaults_eq_faultScan]
    exact faultScan_mono _ _
      (badBacking_clearAt_badTicket_imp ring C x hx)
  have hU : holes hpsi ring (clearAt C x) ≤ holes hpsi ring C + 2 := by
    rw [holes_eq_faultScan, holes_eq_faultScan]
    exact faultScan_le_add_two_except _ _ x (ring.leftNeighbor x)
      (fun i hi hp => hole_clearAt_outside hpsi ring C x i hi hp)
  unfold recoveryPotential
  omega

/-- Weight 2 pays for clearing an unsupported pending predecessor and for the
single incoming hole that this can expose. -/
theorem recoveryPotential_clear_badBacking_lt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (x : Fin n)
    (hx : BadBacking (C x) (C (ring.rightNeighbor x))) :
    recoveryPotential hpsi ring (clearAt C x) <
      recoveryPotential hpsi ring C := by
  have hT : ticketFaults (clearAt C x) ≤ ticketFaults C := by
    rw [ticketFaults_eq_faultScan, ticketFaults_eq_faultScan]
    exact faultScan_mono _ _ (badTicket_clearAt_imp C x)
  have hB : backingFaults ring (clearAt C x) < backingFaults ring C := by
    rw [backingFaults_eq_faultScan, backingFaults_eq_faultScan]
    exact faultScan_strict _ _ x
      (badBacking_clearAt_pending_imp ring C x hx.1)
      hx (by
        intro h
        rw [clearAt_hit C x] at h
        exact clear_not_pending_mass (C x) h.1)
  have hU : holes hpsi ring (clearAt C x) ≤ holes hpsi ring C + 1 := by
    rw [holes_eq_faultScan, holes_eq_faultScan]
    exact faultScan_le_add_one_except _ _ (ring.leftNeighbor x)
      (fun i hp hHole => by
        by_cases hi : i = x
        · subst i
          have hne : ring.rightNeighbor x ≠ x := by
            intro hs
            exact hp (eq_left_of_rn_eq ring hs)
          rw [clearAt_hit C x,
              clearAt_miss C x (ring.rightNeighbor x) hne] at hHole
          exact hole_clear_pending_outgoing hpsi (C x)
            (C (ring.rightNeighbor x)) hx hHole
        · exact hole_clearAt_outside hpsi ring C x i hi hp hHole)
  unfold recoveryPotential
  omega

/-! ## Two-cell cover write -/

def coverAt (ring : DirectedRing n) (C : Config n psi kappa tau)
    (e : Fin n) : Config n psi kappa tau :=
  writeAt ring C e (coverWrite (C e) (C (ring.rightNeighbor e)))

@[simp] theorem coverAt_left (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n) :
    coverAt ring C e e = (coverWrite (C e) (C (ring.rightNeighbor e))).1 := by
  exact writeAt_e _ _ _ _

theorem coverAt_right (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) :
    coverAt ring C e (ring.rightNeighbor e) =
      (coverWrite (C e) (C (ring.rightNeighbor e))).2 := by
  exact writeAt_j ring C e _ hself

private theorem coverAt_other (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e i : Fin n)
    (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) :
    coverAt ring C e i = C i := by
  exact writeAt_other ring C e _ i h1 h2

private theorem cover_left_not_badTicket
    (l r : Cell psi kappa tau) : ¬ BadTicket (coverWrite l r).1 := by
  intro h
  have bad : (false : Bool) = true := h.1
  cases bad

private theorem cover_right_not_badTicket
    (l r : Cell psi kappa tau) : ¬ BadTicket (coverWrite l r).2 := by
  intro h
  have bad : (false : Bool) = true := h.1
  cases bad

private theorem cover_pairCovered_mass (l r : Cell psi kappa tau) :
    PairCovered (coverWrite l r).1 (coverWrite l r).2 := by
  right
  exact ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩

private theorem not_reserved_left_of_hole
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hH : Hole hpsi l r) : ¬ ReservedFrontHoldGuard l.carrier := by
  intro hRF
  exact hH.2 (Or.inl (Or.inl (Or.inl hRF)))

private theorem badTicket_coverAt_imp
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) (i : Fin n) :
    BadTicket (coverAt ring C e i) → BadTicket (C i) := by
  intro h
  by_cases hi : i = e
  · subst i
    rw [coverAt_left] at h
    exact False.elim (cover_left_not_badTicket _ _ h)
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      rw [coverAt_right ring C e hself] at h
      exact False.elim (cover_right_not_badTicket _ _ h)
    · rw [coverAt_other ring C e i hi hj] at h
      exact h

private theorem badBacking_coverAt_imp
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (hH : Hole hpsi (C e) (C (ring.rightNeighbor e)))
    (i : Fin n) :
    BadBacking (coverAt ring C e i)
        (coverAt ring C e (ring.rightNeighbor i)) →
      BadBacking (C i) (C (ring.rightNeighbor i)) := by
  intro h
  have hnotRF := not_reserved_left_of_hole hpsi
    (C e) (C (ring.rightNeighbor e)) hH
  by_cases hi : i = e
  · subst i
    rw [coverAt_left, coverAt_right ring C e hself] at h
    exact False.elim (h.2 ⟨(coverWrite_fields _ _).2.1,
      (coverWrite_fields _ _).2.2.2⟩)
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      rw [coverAt_right ring C e hself] at h
      have hp := h.1.1
      have hf := (coverWrite_fields (C e)
        (C (ring.rightNeighbor e))).2.1.1
      have bad : SpliceRole.front = .predecessorArmed := hf.symm.trans hp
      cases bad
    · by_cases hje : ring.rightNeighbor i = e
      · rw [coverAt_other ring C e i hi hir, hje, coverAt_left] at h
        rw [hje]
        refine ⟨h.1, ?_⟩
        rintro ⟨hRF, _⟩
        exact hnotRF hRF
      · by_cases hjr : ring.rightNeighbor i = ring.rightNeighbor e
        · have hie : i = e := rn_injective ring hjr
          exact (hi hie).elim
        · rw [coverAt_other ring C e i hi hir,
            coverAt_other ring C e (ring.rightNeighbor i) hje hjr] at h
          exact h

private theorem hole_coverAt_imp
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) (i : Fin n) :
    Hole hpsi (coverAt ring C e i)
        (coverAt ring C e (ring.rightNeighbor i)) →
      Hole hpsi (C i) (C (ring.rightNeighbor i)) := by
  intro h
  by_cases hi : i = e
  · subst i
    rw [coverAt_left, coverAt_right ring C e hself] at h
    exact (h.2 (cover_pairCovered_mass _ _)).elim
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      rw [coverAt_right ring C e hself] at h
      have hRF := (coverWrite_fields (C e)
        (C (ring.rightNeighbor e))).2.1
      exact (h.2 (Or.inl (Or.inl (Or.inl hRF)))).elim
    · by_cases hje : ring.rightNeighbor i = e
      · rw [coverAt_other ring C e i hi hir, hje, coverAt_left] at h
        have hp := (coverWrite_fields (C e)
          (C (ring.rightNeighbor e))).1
        exact (h.2 (Or.inl (Or.inl (Or.inr (Or.inl hp))))).elim
      · by_cases hjr : ring.rightNeighbor i = ring.rightNeighbor e
        · have hie : i = e := rn_injective ring hjr
          exact (hi hie).elim
        · rw [coverAt_other ring C e i hi hir,
            coverAt_other ring C e (ring.rightNeighbor i) hje hjr] at h
          exact h

/-- A coverage write creates no ticket/backing fault and removes its served
hole. -/
theorem recoveryPotential_cover_hole_lt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (hH : Hole hpsi (C e) (C (ring.rightNeighbor e))) :
    recoveryPotential hpsi ring (coverAt ring C e) <
      recoveryPotential hpsi ring C := by
  have hT : ticketFaults (coverAt ring C e) ≤ ticketFaults C := by
    rw [ticketFaults_eq_faultScan, ticketFaults_eq_faultScan]
    exact faultScan_mono _ _ (badTicket_coverAt_imp ring C e hself)
  have hB : backingFaults ring (coverAt ring C e) ≤ backingFaults ring C := by
    rw [backingFaults_eq_faultScan, backingFaults_eq_faultScan]
    exact faultScan_mono _ _
      (badBacking_coverAt_imp hpsi ring C e hself hH)
  have hU : holes hpsi ring (coverAt ring C e) < holes hpsi ring C := by
    rw [holes_eq_faultScan, holes_eq_faultScan]
    exact faultScan_strict _ _ e
      (hole_coverAt_imp hpsi ring C e hself)
      hH (by
        intro h
        rw [coverAt_left, coverAt_right ring C e hself] at h
        exact h.2 (cover_pairCovered_mass _ _))
  unfold recoveryPotential
  omega

/-- Every genuinely recovery-active non-self edge strictly lowers the raw
`3*T+2*B+U` potential. -/
theorem recoveryPotential_drop_active_nonself
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (hg : Garbage hpsi (C e) (C (ring.rightNeighbor e))) :
    recoveryPotential hpsi ring (stepRecover host hpsi ring C e) <
      recoveryPotential hpsi ring C := by
  classical
  unfold stepRecover
  rw [if_neg hself]
  by_cases hL : BadTicket (C e)
  · rw [show rowRecoverH host hpsi (C e) (C (ring.rightNeighbor e)) =
        (clearControlV6 (C e), C (ring.rightNeighbor e)) by
      simp only [rowRecoverH, if_pos hL]]
    rw [writeAt_clear_left_eq_clearAt ring C e hself]
    exact recoveryPotential_clear_badTicket_lt hpsi ring C e hL
  · by_cases hR : BadTicket (C (ring.rightNeighbor e))
    · rw [show rowRecoverH host hpsi (C e) (C (ring.rightNeighbor e)) =
          (C e, clearControlV6 (C (ring.rightNeighbor e))) by
        simp only [rowRecoverH, if_neg hL, if_pos hR]]
      rw [writeAt_clear_right_eq_clearAt ring C e hself]
      exact recoveryPotential_clear_badTicket_lt hpsi ring C
        (ring.rightNeighbor e) hR
    · by_cases hB : BadBacking (C e) (C (ring.rightNeighbor e))
      · rw [show rowRecoverH host hpsi (C e) (C (ring.rightNeighbor e)) =
            (clearControlV6 (C e), C (ring.rightNeighbor e)) by
          simp only [rowRecoverH, if_neg hL, if_neg hR, if_pos hB]]
        rw [writeAt_clear_left_eq_clearAt ring C e hself]
        exact recoveryPotential_clear_badBacking_lt hpsi ring C e hB
      · have hH : Hole hpsi (C e) (C (ring.rightNeighbor e)) := by
          rcases hg with (a | a | a) | a
          · exact (hL a).elim
          · exact (hR a).elim
          · exact (hB a).elim
          · exact a
        rw [show rowRecoverH host hpsi (C e) (C (ring.rightNeighbor e)) =
            coverWrite (C e) (C (ring.rightNeighbor e)) by
          simp only [rowRecoverH, if_neg hL, if_neg hR, if_neg hB, if_pos hH]]
        change recoveryPotential hpsi ring (coverAt ring C e) < _
        exact recoveryPotential_cover_hole_lt hpsi ring C e hself hH

/-! ## Stopped rank, including the singleton alias -/

noncomputable def recoveryRank (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Nat := by
  classical
  exact if RecoveryTarget hpsi ring C then 0
    else recoveryPotential hpsi ring C

theorem recoveryRank_le_six_mul
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) :
    recoveryRank hpsi ring C ≤ 6 * n := by
  classical
  unfold recoveryRank
  by_cases hT : RecoveryTarget hpsi ring C
  · rw [if_pos hT]
    omega
  · rw [if_neg hT]
    exact recoveryPotential_le_six_mul hpsi ring C

private theorem size_one_of_self (ring : DirectedRing n) (e : Fin n)
    (hs : ring.rightNeighbor e = e) : n = 1 := by
  by_cases h1 : n = 1
  · exact h1
  · have hnpos : 0 < n := ring.hn
    have hn2 : 2 ≤ n := by omega
    have hv := congrArg Fin.val hs
    have heLt := e.isLt
    unfold DirectedRing.rightNeighbor at hv
    dsimp only at hv
    by_cases he : e.val + 1 < n
    · rw [Nat.mod_eq_of_lt he] at hv
      omega
    · have heq : e.val + 1 = n := by omega
      rw [heq, Nat.mod_self] at hv
      omega

private theorem all_eq_of_self (ring : DirectedRing n) (e i : Fin n)
    (hs : ring.rightNeighbor e = e) : i = e := by
  have hn1 := size_one_of_self ring e hs
  apply Fin.ext
  have hi := i.isLt
  have he := e.isLt
  omega

private theorem stepRecover_target_of_self_garbage
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n)
    (hs : ring.rightNeighbor e = e)
    (hg : Garbage hpsi (C e) (C e)) :
    RecoveryTarget hpsi ring (stepRecover host hpsi ring C e) := by
  right
  intro i
  have hi := all_eq_of_self ring e i hs
  subst i
  unfold stepRecover
  rw [if_pos hs, if_pos hg, writeAt_e]
  exact clearControl_neutral _

private theorem recoveryPotential_pos_of_self_garbage
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n)
    (hs : ring.rightNeighbor e = e)
    (hg : Garbage hpsi (C e) (C e)) :
    0 < recoveryPotential hpsi ring C := by
  rcases hg with (hL | hR | hB) | hH
  · have hT : 0 < ticketFaults C := by
      rw [ticketFaults_eq_faultScan]
      exact faultScan_pos_of _ e hL
    unfold recoveryPotential
    omega
  · have hT : 0 < ticketFaults C := by
      rw [ticketFaults_eq_faultScan]
      exact faultScan_pos_of _ e hR
    unfold recoveryPotential
    omega
  · have hB' : BadBacking (C e) (C (ring.rightNeighbor e)) := by
      simpa [hs] using hB
    have hp : 0 < backingFaults ring C := by
      rw [backingFaults_eq_faultScan]
      exact faultScan_pos_of _ e hB'
    unfold recoveryPotential
    omega
  · have hH' : Hole hpsi (C e) (C (ring.rightNeighbor e)) := by
      simpa [hs] using hH
    have hp : 0 < holes hpsi ring C := by
      rw [holes_eq_faultScan]
      exact faultScan_pos_of _ e hH'
    unfold recoveryPotential
    omega

/-- Every recovery-active selected edge strictly lowers the stopped rank. -/
theorem recoveryRank_drop_active
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n)
    (hnot : ¬ RecoveryTarget hpsi ring C)
    (hg : Garbage hpsi (C e) (C (ring.rightNeighbor e))) :
    recoveryRank hpsi ring (stepRecover host hpsi ring C e) <
      recoveryRank hpsi ring C := by
  classical
  by_cases hs : ring.rightNeighbor e = e
  · have hg' : Garbage hpsi (C e) (C e) := by simpa [hs] using hg
    have ht := stepRecover_target_of_self_garbage host hpsi ring C e hs hg'
    have hp := recoveryPotential_pos_of_self_garbage hpsi ring C e hs hg'
    unfold recoveryRank
    rw [if_neg hnot, if_pos ht]
    exact hp
  · have hd := recoveryPotential_drop_active_nonself
      host hpsi ring C e hs hg
    by_cases ht : RecoveryTarget hpsi ring (stepRecover host hpsi ring C e)
    · unfold recoveryRank
      rw [if_neg hnot, if_pos ht]
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) hd
    · unfold recoveryRank
      rw [if_neg hnot, if_neg ht]
      exact hd

/-- Outside the target, some scheduler edge strictly decreases the stopped
rank. -/
theorem recovery_descent
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau)
    (hnot : ¬ RecoveryTarget hpsi ring C) :
    ∃ e : Fin n,
      recoveryRank hpsi ring (stepRecover host hpsi ring C e) <
        recoveryRank hpsi ring C := by
  have hns : ¬ SpliceSafeV7g hpsi ring C := fun hS => hnot (Or.inl hS)
  obtain ⟨e, hg⟩ := garbage_exists_of_not_safe hpsi ring C hns
  exact ⟨e, recoveryRank_drop_active host hpsi ring C e hnot hg⟩

/-! ## First-hit counting from bounded existential descent -/

section FirstHit

variable {S : Type}

private theorem avoidCount_le_pow_any
    (step : S → Fin n → S) (Good R : S → Prop) (x : S) (T : Nat) :
    BirthTwoStageEscape.avoidCount step Good R x T ≤ n ^ T := by
  unfold BirthTwoStageEscape.avoidCount
  apply BirthTwoStageEscape.wordSum_le_pow
  intro u
  classical
  unfold BirthTwoStageEscape.avoidBit
  split <;> omega

/-- If every non-target state has one rank-decreasing scheduler edge, then by
horizon `B` at least one word has hit the target whenever `rank x ≤ B`. -/
theorem avoidCount_lt_pow_of_rank_descent
    (step : S → Fin n → S) (R : S → Prop) (rank : S → Nat)
    (hn : 0 < n)
    (hdesc : ∀ x, ¬ R x → ∃ e, rank (step x e) < rank x) :
    ∀ (B : Nat) (x : S), rank x ≤ B → ¬ R x →
      BirthTwoStageEscape.avoidCount step (fun _ => True) R x B < n ^ B
  | 0, x, hr, hR => by
      obtain ⟨e, he⟩ := hdesc x hR
      omega
  | B + 1, x, hr, hR => by
      classical
      rw [BirthTwoStageEscape.avoidCount_succ step (fun _ => True) R x
        ⟨True.intro, hR⟩ B]
      obtain ⟨e, he⟩ := hdesc x hR
      have hsel :
          BirthTwoStageEscape.avoidCount step (fun _ => True) R
              (step x e) B < n ^ B := by
        by_cases ht : R (step x e)
        · have hz := BirthTwoStageEscape.avoidCount_zero_of
            step (fun _ => True) R (step x e)
            (fun h => h.2 ht) B
          rw [hz]
          exact Nat.pow_pos hn
        · apply avoidCount_lt_pow_of_rank_descent step R rank hn hdesc
            B (step x e)
          · omega
          · exact ht
      have hs := B9SpliceTableV10d.ofFn_sum_split
        (fun j : Fin n =>
          BirthTwoStageEscape.avoidCount step (fun _ => True) R (step x j) B)
        (fun _ : Fin n => n ^ B) e
        (fun j _ => avoidCount_le_pow_any step (fun _ => True) R (step x j) B)
      calc
        (List.ofFn (fun j : Fin n =>
          BirthTwoStageEscape.avoidCount step (fun _ => True) R
            (step x j) B)).sum
            < (List.ofFn (fun _ : Fin n => n ^ B)).sum := by omega
        _ = n ^ (B + 1) := by
          rw [FiniteUniformStoppingTree.ofFn_sum_const, Nat.pow_succ,
            Nat.mul_comm]

end FirstHit

def RecoveryB (n : Nat) : Nat := 6 * n

def RecoveryQ (n : Nat) : Nat := n ^ RecoveryB n

/-- First-hit mass into `SpliceSafeV7g ∨ all-neutral`, with
`B = 6*n` and `Q = n^(6*n)`. -/
theorem recovery_first_hit_mass
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) :
    RecoveryQ n * BirthTwoStageEscape.avoidCount
      (stepRecover host hpsi ring)
      (fun _ : Config n psi kappa tau => True)
      (RecoveryTarget hpsi ring) C (RecoveryB n) ≤
      (RecoveryQ n - 1) * n ^ RecoveryB n := by
  classical
  let B := RecoveryB n
  have hRank : recoveryRank hpsi ring C ≤ B := by
    dsimp [B, RecoveryB]
    exact recoveryRank_le_six_mul hpsi ring C
  by_cases hT : RecoveryTarget hpsi ring C
  · have hz := BirthTwoStageEscape.avoidCount_zero_of
      (stepRecover host hpsi ring)
      (fun _ : Config n psi kappa tau => True)
      (RecoveryTarget hpsi ring) C (fun h => h.2 hT) B
    unfold RecoveryQ
    change n ^ B * BirthTwoStageEscape.avoidCount
      (stepRecover host hpsi ring)
      (fun _ : Config n psi kappa tau => True)
      (RecoveryTarget hpsi ring) C B ≤ (n ^ B - 1) * n ^ B
    rw [hz]
    simp
  · have hlt := avoidCount_lt_pow_of_rank_descent
      (stepRecover host hpsi ring)
      (RecoveryTarget hpsi ring)
      (recoveryRank hpsi ring) ring.hn
      (fun X hX => recovery_descent host hpsi ring X hX)
      B C hRank hT
    have hle : BirthTwoStageEscape.avoidCount
        (stepRecover host hpsi ring)
        (fun _ : Config n psi kappa tau => True)
        (RecoveryTarget hpsi ring) C B ≤ n ^ B - 1 := by
      omega
    unfold RecoveryQ
    change n ^ B * BirthTwoStageEscape.avoidCount
      (stepRecover host hpsi ring)
      (fun _ : Config n psi kappa tau => True)
      (RecoveryTarget hpsi ring) C B ≤ (n ^ B - 1) * n ^ B
    calc
      n ^ B * BirthTwoStageEscape.avoidCount
          (stepRecover host hpsi ring)
          (fun _ : Config n psi kappa tau => True)
          (RecoveryTarget hpsi ring) C B
          ≤ n ^ B * (n ^ B - 1) := Nat.mul_le_mul_left _ hle
      _ = (n ^ B - 1) * n ^ B := Nat.mul_comm _ _

/-!
No theorem claims that an unrelated non-recovery host edge is potential
non-increasing. The mass proof needs only the selected recovery edge, whose
recovery branch precedes `rowB9` and therefore does not evaluate the host.
-/

end B9ControllerRecovery
