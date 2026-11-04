import Leader.Wu.Splice.NeutralGuardsFalse


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace ZZNeutralRow


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost B9FullCarrierRows
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g
  B9SpliceTableHost
open ZZNeutralGuardsFalse


variable {psi kappa tau : Nat} {P : Type}


/-! ## Controller-neutrality transport -/


private theorem toOld_neutral
    (laws : PhysCarrierLaws P psi kappa tau)
    (u : CellP P) (h : NeutralP u) :
    B9SpliceHostQuiescence.Neutral (toOld laws u) := by
  rcases h with ⟨hr, hp, ht⟩
  refine ⟨?_, ?_, ?_⟩
  · change u.spliceRole = .none
    exact hr
  · change u.repairPending = false
    exact hp
  · change u.acquireTicket = false
    exact ht


private theorem ofOldWith_neutral
    (u : OldCell psi kappa tau) (p : P)
    (h : B9SpliceHostQuiescence.Neutral u) :
    NeutralP (ofOldWith u p) := by
  rcases h with ⟨hr, hp, ht⟩
  refine ⟨?_, ?_, ?_⟩
  · change role u.carrier = .none
    exact hr
  · change u.carrier.repairPending = false
    exact hp
  · change u.acquireTicket = false
    exact ht


private theorem ofOldWith_toOld_eq_neutral
    (laws : PhysCarrierLaws P psi kappa tau)
    (u : CellP P) (h : NeutralP u) (p : P) :
    ofOldWith (toOld laws u) p =
      { phys := p
        spliceRole := .none
        repairPending := false
        acquireTicket := false } := by
  rcases u with ⟨up, ur, ub, ut⟩
  change ur = .none ∧ ub = false ∧ ut = false at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl


private theorem cell_eq_of_neutral_phys
    (u v : CellP P)
    (hu : NeutralP u) (hv : NeutralP v)
    (hp : u.phys = v.phys) : u = v := by
  rcases u with ⟨up, ur, ub, ut⟩
  rcases v with ⟨vp, vr, vb, vt⟩
  change ur = .none ∧ ub = false ∧ ut = false at hu
  change vr = .none ∧ vb = false ∧ vt = false at hv
  rcases hu with ⟨rfl, rfl, rfl⟩
  rcases hv with ⟨rfl, rfl, rfl⟩
  change up = vp at hp
  cases hp
  rfl


private theorem transportPair_allNeutral
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (q : OldPair psi kappa tau)
    (a : PhysicalAction)
    (hqL : B9SpliceHostQuiescence.Neutral q.1)
    (hqR : B9SpliceHostQuiescence.Neutral q.2) :
    AllNeutral
      (transportPair laws host hpsi l r q a).1
      (transportPair laws host hpsi l r q a).2 := by
  cases a with
  | keep =>
      simp only [transportPair]
      exact ⟨ofOldWith_neutral q.1 _ hqL,
        ofOldWith_neutral q.2 _ hqR⟩
  | host =>
      simp only [transportPair]
      exact ⟨ofOldWith_neutral q.1 _ hqL,
        ofOldWith_neutral q.2 _ hqR⟩
  | relabel =>
      simp only [transportPair]
      exact ⟨ofOldWith_neutral q.1 _ hqL,
        ofOldWith_neutral q.2 _ hqR⟩


private theorem runPlan_allNeutral
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (p : RowPlan psi kappa tau)
    (hOut :
      B9SpliceHostQuiescence.Neutral p.out.1 ∧
      B9SpliceHostQuiescence.Neutral p.out.2) :
    AllNeutral
      (runPlan laws host hpsi l r p).1
      (runPlan laws host hpsi l r p).2 := by
  unfold runPlan
  exact transportPair_allNeutral laws host hpsi l r p.out p.action
    hOut.1 hOut.2


private theorem runPlan_planFromRow_allNeutral
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (a : PhysicalAction)
    (w : CellP P × CellP P)
    (hw : AllNeutral w.1 w.2) :
    AllNeutral
      (runPlan laws host hpsi l r (planFromRow laws a w)).1
      (runPlan laws host hpsi l r (planFromRow laws a w)).2 := by
  apply runPlan_allNeutral laws host hpsi l r
  constructor
  · change B9SpliceHostQuiescence.Neutral (toOld laws w.1)
    exact toOld_neutral laws w.1 hw.1
  · change B9SpliceHostQuiescence.Neutral (toOld laws w.2)
    exact toOld_neutral laws w.2 hw.2


private theorem quietWrite_allNeutral
    (oh : HostRow (OldPhys psi kappa tau))
    (l r : OldCell psi kappa tau)
    (hl : B9SpliceHostQuiescence.Neutral l)
    (hr : B9SpliceHostQuiescence.Neutral r) :
    B9SpliceHostQuiescence.Neutral
        (B9SpliceHostQuiescence.quietWrite oh l r).1 ∧
      B9SpliceHostQuiescence.Neutral
        (B9SpliceHostQuiescence.quietWrite oh l r).2 := by
  rcases hl with ⟨hlr, hlp, _⟩
  rcases hr with ⟨hrr, hrp, _⟩
  unfold B9SpliceHostQuiescence.quietWrite
    B9SpliceTableHost.ordinaryRowH
  dsimp only
  constructor
  · refine ⟨?_, ?_, rfl⟩
    · simpa [B9SpliceControllerR1Table.role,
        B9SpliceControllerR1Table.setPhysical] using hlr
    · simpa [B9SpliceControllerR1Table.setPhysical] using hlp
  · refine ⟨?_, ?_, rfl⟩
    · simpa [B9SpliceControllerR1Table.role,
        B9SpliceControllerR1Table.setPhysical] using hrr
    · simpa [B9SpliceControllerR1Table.setPhysical] using hrp


private theorem row7P_allNeutral_of_quiet
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (hN : AllNeutral l r)
    (hNo : ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier)
    (hrel : rightFollowerRelabelledV7
      (toOld laws r).carrier
      (ordinaryRowH
        (shadowHostAt laws host l.phys r.phys)
        (toOld laws l).carrier (toOld laws r).carrier).2 = false) :
    AllNeutral
      (B9FullCarrierHost.row7P laws host hpsi l r).1
      (B9FullCarrierHost.row7P laws host hpsi l r).2 := by
  have hOldL := toOld_neutral laws l hN.1
  have hOldR := toOld_neutral laws r hN.2
  have hquiet := B9SpliceHostQuiescence.row7H_quiet
    (shadowHostAt laws host l.phys r.phys) hpsi
    (toOld laws l) (toOld laws r) hOldL hOldR hNo hrel
  have hqN := quietWrite_allNeutral
    (shadowHostAt laws host l.phys r.phys)
    (toOld laws l) (toOld laws r) hOldL hOldR
  unfold B9FullCarrierHost.row7P
  dsimp only
  rw [hquiet]
  cases ha : B9FullCarrierHost.row7ActionP laws host hpsi l r with
  | keep =>
      simp only [ha]
      exact ⟨ofOldWith_neutral _ _ hqN.1,
        ofOldWith_neutral _ _ hqN.2⟩
  | host =>
      simp only [ha]
      exact ⟨ofOldWith_neutral _ _ hqN.1,
        ofOldWith_neutral _ _ hqN.2⟩
  | relabel =>
      simp only [ha]
      exact ⟨ofOldWith_neutral _ _ hqN.1,
        ofOldWith_neutral _ _ hqN.2⟩


/-!
The complete plan remains controller-neutral under exactly the two payload
conditions needed to make the row-7/physical-hold host writes quiet.


Notice that V10c does not need to be ruled out.  Its true arm explicitly uses
`(toOld l,toOld r)`, which is neutral, and its false arm inherits row10b.
-/
private theorem fullRowP_allNeutral_of_quiet
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (hN : AllNeutral l r)
    (hNo : ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier)
    (hrel : rightFollowerRelabelledV7
      (toOld laws r).carrier
      (ordinaryRowH
        (shadowHostAt laws host l.phys r.phys)
        (toOld laws l).carrier (toOld laws r).carrier).2 = false) :
    AllNeutral
      (fullRowP laws host hpsi l r).1
      (fullRowP laws host hpsi l r).2 := by
  have hOldL := toOld_neutral laws l hN.1
  have hOldR := toOld_neutral laws r hN.2
  have h7N := row7P_allNeutral_of_quiet
    laws host hpsi l r hN hNo hrel


  have hSP8 := ZZNeutralGuardsFalse.rightStalePredecessorHoldGuardV8_false
    laws l r hN
  have h8N : AllNeutral
      (row8P laws host hpsi l r).1
      (row8P laws host hpsi l r).2 := by
    unfold row8P
    rw [B9FullCarrierRows.row8PlanP.eq_1]
    try dsimp only
    rw [if_neg hSP8]
    exact runPlan_planFromRow_allNeutral laws host hpsi l r
      (B9FullCarrierHost.row7ActionP laws host hpsi l r)
      (B9FullCarrierHost.row7P laws host hpsi l r) h7N


  have hBF := ZZNeutralGuardsFalse.hostFenceBusyFrontGuardV9_false
    laws hpsi l r hN
  have h9N : AllNeutral
      (row9P laws host hpsi l r).1
      (row9P laws host hpsi l r).2 := by
    unfold row9P
    rw [B9FullCarrierRows.row9PlanP.eq_1]
    try dsimp only
    rw [if_neg hBF]
    exact runPlan_planFromRow_allNeutral laws host hpsi l r
      (row8ActionP laws host hpsi l r)
      (row8P laws host hpsi l r) h8N


  have hHO := ZZNeutralGuardsFalse.hostFenceAdvanceGuardV10b_false
    laws hpsi l r hN
  have hbN : AllNeutral
      (row10bP laws host hpsi l r).1
      (row10bP laws host hpsi l r).2 := by
    unfold row10bP
    rw [B9FullCarrierRows.row10bPlanP.eq_1]
    try dsimp only
    rw [if_neg hHO]
    exact runPlan_planFromRow_allNeutral laws host hpsi l r
      (row9ActionP laws host hpsi l r)
      (row9P laws host hpsi l r) h9N


  have hcN : AllNeutral
      (row10cP laws host hpsi l r).1
      (row10cP laws host hpsi l r).2 := by
    unfold row10cP
    rw [B9FullCarrierRows.row10cPlanP.eq_1]
    try dsimp only
    by_cases hz : ZeroRefreshOnlyGuardP laws host hpsi l r
    · rw [if_pos hz]
      apply runPlan_allNeutral laws host hpsi l r
      exact ⟨toOld_neutral laws l hN.1,
        toOld_neutral laws r hN.2⟩
    · rw [if_neg hz]
      exact runPlan_planFromRow_allNeutral laws host hpsi l r
        (row10bActionP laws host hpsi l r)
        (row10bP laws host hpsi l r) hbN


  have hD1 := ZZNeutralGuardsFalse.orphanReservedFrontGuardV3_false
    laws l r hN
  have hD2 := ZZNeutralGuardsFalse.orphanVictimGuard_false laws l r hN
  have hD3 := ZZNeutralGuardsFalse.ownedPendingVictimGuard_false laws l r hN
  have hD4 := ZZNeutralGuardsFalse.ownerlessPendingPredGuard_false laws l r hN
  have hdgN : AllNeutral
      (row10dgP laws host hpsi l r).1
      (row10dgP laws host hpsi l r).2 := by
    unfold row10dgP
    rw [B9FullCarrierRows.row10dgPlanP.eq_1]
    try dsimp only
    rw [if_neg hD1, if_neg hD2, if_neg hD3, if_neg hD4]
    exact runPlan_planFromRow_allNeutral laws host hpsi l r
      (row10cActionP laws host hpsi l r)
      (row10cP laws host hpsi l r) hcN


  have hLP := ZZNeutralGuardsFalse.row10g_left_pending_predecessor_false
    laws l r hN
  have hVR := ZZNeutralGuardsFalse.victimRightScrubGuardV6_false laws l r hN
  have hFR := ZZNeutralGuardsFalse.frontRightScrubGuardV6_false laws l r hN
  have hMR := ZZNeutralGuardsFalse.malformedRightPendingGuardV6_false laws l r hN
  have hRP := ZZNeutralGuardsFalse.row10g_right_predecessor_false laws l r hN
  have hquietOld := quietWrite_allNeutral
    (shadowHostAt laws host l.phys r.phys)
    (toOld laws l) (toOld laws r) hOldL hOldR
  have hgN : AllNeutral
      (row10gP laws host hpsi l r).1
      (row10gP laws host hpsi l r).2 := by
    unfold row10gP
    rw [B9FullCarrierRows.row10gPlanP.eq_1]
    try dsimp only
    by_cases hq : row10dgP laws host hpsi l r = (l, r)
    · rw [if_pos hq]
      rw [if_neg hLP, if_neg hVR, if_neg hFR, if_neg hMR, if_neg hRP]
      have hhold := B9SpliceHostQuiescence.physicalHold_quiet
        (shadowHostAt laws host l.phys r.phys)
        (toOld laws l) (toOld laws r) hOldL hOldR hrel
      apply runPlan_allNeutral laws host hpsi l r
      rw [hhold]
      exact hquietOld
    · rw [if_neg hq]
      exact runPlan_planFromRow_allNeutral laws host hpsi l r
        (row10dgActionP laws host hpsi l r)
        (row10dgP laws host hpsi l r) hdgN


  unfold fullRowP
  rw [B9FullCarrierRows.fullPlanP.eq_1]
  try dsimp only
  rw [if_neg hNo]
  exact runPlan_planFromRow_allNeutral laws host hpsi l r
    (row10gActionP laws host hpsi l r)
    (row10gP laws host hpsi l r) hgN


/-! ## What AllNeutral alone really proves -/


/--
Unconditional exact dispatch form.  This is the literal `.host` consequence of
the already-compiled action theorem.  It intentionally retains `fullPlanP.out`:
that old pair is the controller payload installed by `transportPair`.
-/
theorem fullRowP_host_dispatch_of_allNeutral
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (hN : AllNeutral l r) :
    fullRowP laws host hpsi l r =
      transportPair laws host hpsi l r
        (fullPlanP laws host hpsi l r).out .host := by
  have ha' : (fullPlanP laws host hpsi l r).action = .host := by
    simpa [fullActionP] using
      (ZZNeutralGuardsFalse.fullActionP_host_of_allNeutral
        laws host hpsi l r hN)
  unfold fullRowP runPlan
  rw [ha']


/-- Same theorem with the `.host` arm of `transportPair` exposed literally. -/
theorem fullRowP_host_dispatch_exact_of_allNeutral
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (hN : AllNeutral l r) :
    fullRowP laws host hpsi l r =
      let hp := host.row l.phys r.phys
      let q := (fullPlanP laws host hpsi l r).out
      (ofOldWith q.1 hp.1, ofOldWith q.2 hp.2) := by
  rw [fullRowP_host_dispatch_of_allNeutral laws host hpsi l r hN]
  rfl


/-! ## Corrected neutral-rewrap theorem -/


/--
This is the requested row theorem in its true form.  The extra two hypotheses
are exactly the payload gates that can write non-neutral outer coordinates on
an otherwise neutral pair.
-/
theorem fullRowP_host_of_allNeutral
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (hN : AllNeutral l r)
    (hNo : ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier)
    (hrel : rightFollowerRelabelledV7
      (toOld laws r).carrier
      (ordinaryRowH
        (shadowHostAt laws host l.phys r.phys)
        (toOld laws l).carrier (toOld laws r).carrier).2 = false) :
    fullRowP laws host hpsi l r =
      (ofOldWith (toOld laws l) (host.row l.phys r.phys).1,
        ofOldWith (toOld laws r) (host.row l.phys r.phys).2) := by
  have hOutN := fullRowP_allNeutral_of_quiet
    laws host hpsi l r hN hNo hrel
  have ha := ZZNeutralGuardsFalse.fullActionP_host_of_allNeutral
    laws host hpsi l r hN
  have hphys := fullRowP_action_spec laws host hpsi l r
  unfold ActionSpecP at hphys
  simp only [ha] at hphys
  apply Prod.ext
  · apply cell_eq_of_neutral_phys
    · exact hOutN.1
    · exact ofOldWith_neutral _ _ (toOld_neutral laws l hN.1)
    · simpa only [B9FullCarrierHost.phys_ofOldWith] using hphys.1
  · apply cell_eq_of_neutral_phys
    · exact hOutN.2
    · exact ofOldWith_neutral _ _ (toOld_neutral laws r hN.2)
    · simpa only [B9FullCarrierHost.phys_ofOldWith] using hphys.2


/-- A follower on the left cannot trigger the top-level deletion detector. -/
theorem not_ldc_of_left_follower
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P)
    (l r : CellP P)
    (hL : laws.leader l.phys = false) :
    ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier := by
  intro h
  unfold B9SpliceTableHost.ldc B9Host.LeftDeletionCandidate at h
  have ht := h.1
  change (laws.erase l.phys).core.core.leader = true at ht
  rw [← laws.leader_eq l.phys] at ht
  rw [hL] at ht
  cases ht


theorem fullRowP_host_of_allNeutral_of_left_follower
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (hN : AllNeutral l r)
    (hL : laws.leader l.phys = false)
    (hrel : rightFollowerRelabelledV7
      (toOld laws r).carrier
      (ordinaryRowH
        (shadowHostAt laws host l.phys r.phys)
        (toOld laws l).carrier (toOld laws r).carrier).2 = false) :
    fullRowP laws host hpsi l r =
      (ofOldWith (toOld laws l) (host.row l.phys r.phys).1,
        ofOldWith (toOld laws r) (host.row l.phys r.phys).2) := by
  apply fullRowP_host_of_allNeutral laws host hpsi l r hN
  · exact not_ldc_of_left_follower laws host l r hL
  · exact hrel


/-! ## The six `liftC` pairs -/


private theorem h3 : 0 < 3 := ZZOrbitLiftClean.h3
private theorem h23 : 2 ≤ 3 := by omega


private abbrev OrbitP := ZZFinalCarrierV3.P 3 3 48
private abbrev OrbitCell := ZZFinalCarrierV3.Cell 3 3 48
private abbrev OrbitCfg := ZZFinalCarrierV3.Config 6 3 3 48


private def orbitLaws : PhysCarrierLaws OrbitP 3 3 48 :=
  ZZFinalCarrierV3.carrierLawsV3


private def orbitHost : HostRow OrbitP :=
  ZZFinalCarrierV3.hostR2CV3 (κ := 3) (τ := 48) h3 h23


private theorem fin6_cases (i : Fin 6) :
    i = (0 : Fin 6) ∨ i = 1 ∨ i = 2 ∨
      i = 3 ∨ i = 4 ∨ i = 5 := by
  have hi : i.val < 6 := i.isLt
  have hv :
      i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
        i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
    omega
  rcases hv with h | h | h | h | h | h
  · left; apply Fin.ext; omega
  · right; left; apply Fin.ext; omega
  · right; right; left; apply Fin.ext; omega
  · right; right; right; left; apply Fin.ext; omega
  · right; right; right; right; left; apply Fin.ext; omega
  · right; right; right; right; right; apply Fin.ext; omega


theorem liftC_left_follower (e : Fin 6) :
    orbitLaws.leader (ZZOrbitLiftClean.liftC e).phys = false := by
  rfl


/-- The only remaining HOST-ticket payload gate is false on all six edges. -/
theorem liftC_rightFollowerRelabelled_false (e : Fin 6) :
    rightFollowerRelabelledV7
      (toOld orbitLaws
        (ZZOrbitLiftClean.liftC
          (ZZOrbitLiftClean.ring6.rightNeighbor e))).carrier
      (ordinaryRowH
        (shadowHostAt orbitLaws orbitHost
          (ZZOrbitLiftClean.liftC e).phys
          (ZZOrbitLiftClean.liftC
            (ZZOrbitLiftClean.ring6.rightNeighbor e)).phys)
        (toOld orbitLaws (ZZOrbitLiftClean.liftC e)).carrier
        (toOld orbitLaws
          (ZZOrbitLiftClean.liftC
            (ZZOrbitLiftClean.ring6.rightNeighbor e))).carrier).2 = false := by
  rcases fin6_cases e with h | h | h | h | h | h
  all_goals subst e
  all_goals rfl


/-- Public neutral wrapper for the inner V3.1 carrier. -/
def neutralLiftCell (u : OrbitP) : OrbitCell :=
  { phys := u
    spliceRole := .none
    repairPending := false
    acquireTicket := false }


/-- Pointwise neutral outer-B9 lift of an inner V3.1 configuration. -/
def neutralLift (C : R2CoherenceV31.FC 6 3 3 48) : OrbitCfg :=
  fun i => neutralLiftCell (C i)


/-- Public re-extraction of the private inner orbit stored inside `liftC`. -/
def innerC : R2CoherenceV31.FC 6 3 3 48 :=
  fun i => (ZZOrbitLiftClean.liftC i).phys


theorem liftC_eq_neutralLift :
    ZZOrbitLiftClean.liftC = neutralLift innerC := by
  funext i
  rfl


/-- Neutral rewrap of the physical host pair at one orbit edge. -/
def neutralHostPair (e : Fin 6) : OrbitCell × OrbitCell :=
  let q := orbitHost.row
    (ZZOrbitLiftClean.liftC e).phys
    (ZZOrbitLiftClean.liftC
      (ZZOrbitLiftClean.ring6.rightNeighbor e)).phys
  (neutralLiftCell q.1, neutralLiftCell q.2)


/-- The actual `concretePortV3.row` is exactly the neutral host rewrap. -/
theorem liftC_port_row_host (e : Fin 6) :
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).row
      (ZZOrbitLiftClean.liftC e)
      (ZZOrbitLiftClean.liftC
        (ZZOrbitLiftClean.ring6.rightNeighbor e)) =
      neutralHostPair e := by
  have hN := ZZNeutralGuardsFalse.liftC_allNeutral e
  change fullRowP orbitLaws orbitHost h3
      (ZZOrbitLiftClean.liftC e)
      (ZZOrbitLiftClean.liftC
        (ZZOrbitLiftClean.ring6.rightNeighbor e)) =
    neutralHostPair e
  have hrow := fullRowP_host_of_allNeutral_of_left_follower
    orbitLaws orbitHost h3
    (ZZOrbitLiftClean.liftC e)
    (ZZOrbitLiftClean.liftC
      (ZZOrbitLiftClean.ring6.rightNeighbor e))
    hN (liftC_left_follower e) (liftC_rightFollowerRelabelled_false e)
  rw [hrow]
  unfold neutralHostPair
  dsimp only
  apply Prod.ext
  · simpa only [neutralLiftCell] using
      (ofOldWith_toOld_eq_neutral orbitLaws
        (ZZOrbitLiftClean.liftC e) hN.1
        (orbitHost.row
          (ZZOrbitLiftClean.liftC e).phys
          (ZZOrbitLiftClean.liftC
            (ZZOrbitLiftClean.ring6.rightNeighbor e)).phys).1)
  · simpa only [neutralLiftCell] using
      (ofOldWith_toOld_eq_neutral orbitLaws
        (ZZOrbitLiftClean.liftC
          (ZZOrbitLiftClean.ring6.rightNeighbor e)) hN.2
        (orbitHost.row
          (ZZOrbitLiftClean.liftC e).phys
          (ZZOrbitLiftClean.liftC
            (ZZOrbitLiftClean.ring6.rightNeighbor e)).phys).2)


/-- Explicit six-edge form, including the wrap edge `5 -> 0`. -/
theorem liftC_six_port_rows_host :
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).row
        (ZZOrbitLiftClean.liftC 0) (ZZOrbitLiftClean.liftC 1) =
        neutralHostPair 0 ∧
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).row
        (ZZOrbitLiftClean.liftC 1) (ZZOrbitLiftClean.liftC 2) =
        neutralHostPair 1 ∧
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).row
        (ZZOrbitLiftClean.liftC 2) (ZZOrbitLiftClean.liftC 3) =
        neutralHostPair 2 ∧
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).row
        (ZZOrbitLiftClean.liftC 3) (ZZOrbitLiftClean.liftC 4) =
        neutralHostPair 3 ∧
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).row
        (ZZOrbitLiftClean.liftC 4) (ZZOrbitLiftClean.liftC 5) =
        neutralHostPair 4 ∧
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).row
        (ZZOrbitLiftClean.liftC 5) (ZZOrbitLiftClean.liftC 0) =
        neutralHostPair 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (liftC_port_row_host (0 : Fin 6))
  · simpa using (liftC_port_row_host (1 : Fin 6))
  · simpa using (liftC_port_row_host (2 : Fin 6))
  · simpa using (liftC_port_row_host (3 : Fin 6))
  · simpa using (liftC_port_row_host (4 : Fin 6))
  · simpa using (liftC_port_row_host (5 : Fin 6))


/-! ## Final wrapper and configuration step -/


/-- `hostR2CV3.row` is definitionally the inner `rowV3`. -/
theorem hostR2CV3_row_eq_rowV3 (l r : OrbitP) :
    orbitHost.row l r =
      R2CoherenceV31.rowV3 h3 (by decide : 0 < 2) h23 l r := by
  rfl


/-- Recovery is already known off and the final action is already compiled HOST. -/
theorem liftC_final_row_host (e : Fin 6) :
    ZZFinalCarrierV3.rowFinalV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      (ZZOrbitLiftClean.liftC e)
      (ZZOrbitLiftClean.liftC
        (ZZOrbitLiftClean.ring6.rightNeighbor e)) =
      neutralHostPair e := by
  unfold ZZFinalCarrierV3.rowFinalV3
  rw [ZZNeutralGuardsFalse.liftC_finalAction_host e]
  exact liftC_port_row_host e


private theorem ring6_nonself (e : Fin 6) :
    ZZOrbitLiftClean.ring6.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % 6 = e.val at hv
  have he := e.isLt
  by_cases hlt : e.val + 1 < 6
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = 6 := by omega
    rw [heq, Nat.mod_self] at hv
    omega


/--
Writing the neutral host pair into the neutral outer configuration is exactly
neutral lifting the inner `stepV3` service.
-/
private theorem write_neutralHost_eq_innerStep (e : Fin 6) :
    B9FullCarrierHost.writeAtP ZZOrbitLiftClean.ring6
      (neutralLift innerC) e (neutralHostPair e) =
    neutralLift
      (R2CoherenceV31.stepV3 h3 h23
        ZZOrbitLiftClean.ring6 innerC e) := by
  funext i
  by_cases hi : i = e
  · subst i
    simp [B9FullCarrierHost.writeAtP,
      neutralLift, neutralLiftCell, neutralHostPair, innerC,
      orbitHost, ZZFinalCarrierV3.hostR2CV3,
      R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
      PopulationProtocol.step]
  · by_cases hj : i = ZZOrbitLiftClean.ring6.rightNeighbor e
    · have hne := ring6_nonself e
      simp [B9FullCarrierHost.writeAtP, hi, hj, hne,
        neutralLift, neutralLiftCell, neutralHostPair, innerC,
        orbitHost, ZZFinalCarrierV3.hostR2CV3,
        R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
        PopulationProtocol.step]
    · simp [B9FullCarrierHost.writeAtP, hi, hj,
        neutralLift, neutralLiftCell, neutralHostPair, innerC,
        orbitHost, ZZFinalCarrierV3.hostR2CV3,
        R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
        PopulationProtocol.step]


/--
Final carrier lift theorem for every edge.  This is the configuration-level
form of “the port installs `hostR2CV3.row = rowV3` and leaves the outer B9
controller neutral”.
-/
theorem stepConcreteV3_liftC (e : Fin 6) :
    ZZFinalCarrierV3.stepConcreteV3 h3 h23
      ZZOrbitLiftClean.ring6 ZZOrbitLiftClean.liftC e =
    neutralLift
      (R2CoherenceV31.stepV3 h3 h23
        ZZOrbitLiftClean.ring6 innerC e) := by
  unfold ZZFinalCarrierV3.stepConcreteV3 ZZFinalCarrierV3.stepFinalV3
  rw [if_neg (ring6_nonself e), liftC_final_row_host e]
  rw [liftC_eq_neutralLift]
  exact write_neutralHost_eq_innerStep e


#print axioms ZZNeutralRow.fullRowP_host_dispatch_of_allNeutral
#print axioms ZZNeutralRow.fullRowP_host_of_allNeutral
#print axioms ZZNeutralRow.liftC_port_row_host
#print axioms ZZNeutralRow.stepConcreteV3_liftC


end ZZNeutralRow
