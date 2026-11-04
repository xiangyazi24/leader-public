import Leader.Wu.Coherence.PositiveTimerNotFixed

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2PositiveTimerUniversalMove

variable {n psi kappa tau width : Nat}

/-- Every raw R2 pair moves at positive timer.  No label, leader, path,
producer, or controller hypothesis is needed. -/
theorem raw_row_not_fixed_of_positive_timer
    (hpsi : 0 < psi) (hw : 0 < width) (hle : width <= psi)
    (htau : 0 < tau) (l r : R2.Cell psi kappa tau) :
    R2.row hpsi hw hle l r ≠ (l, r) :=
  R2CoherenceOpenPositiveTimerNotFixed.raw_row_not_fixed_of_positive_timer_any
    hpsi hw hle htau l r

/-- On two open/token-free wrapper cells, universal raw motion survives the
coherence arbitration: a hazardous proposal changes a controller, while a
harmless proposal installs the moving raw pair. -/
theorem open_row_not_fixed_of_positive_timer
    (hpsi : 0 < psi) (hw : 0 < width) (hle : width <= psi)
    (htau : 0 < tau)
    (l r : R2Coherence.Cell psi kappa tau)
    (hl : R2Coherence.OpenControl l)
    (hr : R2Coherence.OpenControl r) :
    R2Coherence.row hpsi hw hle l r ≠ (l, r) := by
  have hraw :
      R2.row hpsi hw hle l.phys r.phys ≠ (l.phys, r.phys) :=
    raw_row_not_fixed_of_positive_timer hpsi hw hle htau l.phys r.phys
  rcases hl with ⟨hlm, hlt⟩
  rcases hr with ⟨hrm, hrt⟩
  have hdispatch :
      R2Coherence.row hpsi hw hle l r =
        R2Coherence.openStage hpsi hw hle l r := by
    simp [R2Coherence.row, R2Coherence.ordinaryStage,
      hlm, hrm, hlt, hrt]
  rw [hdispatch]
  unfold R2Coherence.openStage
  dsimp only
  split
  · split
    · intro heq
      have hc := congrArg
        (fun q : R2Coherence.Cell psi kappa tau ×
            R2Coherence.Cell psi kappa tau => q.2.ctl.mark) heq
      change R2Coherence.Mark.closing = r.ctl.mark at hc
      rw [hrm] at hc
      cases hc
    · intro heq
      have hc := congrArg
        (fun q : R2Coherence.Cell psi kappa tau ×
            R2Coherence.Cell psi kappa tau => q.1.ctl.mark) heq
      change R2Coherence.Mark.closing = l.ctl.mark at hc
      rw [hlm] at hc
      cases hc
  · intro heq
    have hpL := congrArg
      (fun q : R2Coherence.Cell psi kappa tau ×
          R2Coherence.Cell psi kappa tau => q.1.phys) heq
    have hpR := congrArg
      (fun q : R2Coherence.Cell psi kappa tau ×
          R2Coherence.Cell psi kappa tau => q.2.phys) heq
    have hpL' :
        (R2.row hpsi hw hle l.phys r.phys).1 = l.phys := by
      simpa [R2Coherence.install, R2Coherence.proposal] using hpL
    have hpR' :
        (R2.row hpsi hw hle l.phys r.phys).2 = r.phys := by
      simpa [R2Coherence.install, R2Coherence.proposal] using hpR
    exact hraw (Prod.ext hpL' hpR')

/-- The exact global consequence needs no label geometry and no leaderless
hypothesis.  What it does need is an actual two-endpoint interaction edge,
because `PopulationProtocol.step` discards the responder output on a self-edge. -/
theorem allOpen_not_whole_fixed_of_positive_timer_of_nonself_edge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (htau : 0 < tau)
    (ring : DirectedRing n)
    (C : R2Coherence.FC n psi kappa tau)
    (hOpen : R2Coherence.AllOpen C)
    (hEdge : ∃ e : Fin n, ring.rightNeighbor e ≠ e) :
    (∀ e : Fin n, R2Coherence.step hpsi h2 ring C e = C) → False := by
  rcases hEdge with ⟨e, hne⟩
  have hpair :
      R2Coherence.row hpsi (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e)) ≠
        (C e, C (ring.rightNeighbor e)) :=
    open_row_not_fixed_of_positive_timer
      hpsi (by decide : 0 < 2) h2 htau
      (C e) (C (ring.rightNeighbor e))
      (hOpen e) (hOpen (ring.rightNeighbor e))
  intro hFixed
  have hcfg := hFixed e
  have hleft :
      (R2Coherence.row hpsi (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).1 = C e := by
    have h := congrFun hcfg e
    simpa only [R2Coherence.step, R2Coherence.protocol,
      PopulationProtocol.step, if_true] using h
  have hright :
      (R2Coherence.row hpsi (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).2 =
          C (ring.rightNeighbor e) := by
    have h := congrFun hcfg (ring.rightNeighbor e)
    simpa only [R2Coherence.step, R2Coherence.protocol,
      PopulationProtocol.step, if_neg hne, if_true] using h
  exact hpair (Prod.ext hleft hright)

/-- A ring of size at least two supplies the required non-self edge. -/
theorem allOpen_not_whole_fixed_of_positive_timer
    (hpsi : 0 < psi) (h2 : 2 <= psi) (htau : 0 < tau)
    (hn : 2 <= n) (ring : DirectedRing n)
    (C : R2Coherence.FC n psi kappa tau)
    (hOpen : R2Coherence.AllOpen C) :
    (∀ e : Fin n, R2Coherence.step hpsi h2 ring C e = C) → False := by
  let e : Fin n := ⟨0, by omega⟩
  have hne : ring.rightNeighbor e ≠ e := by
    intro heq
    have hv := congrArg Fin.val heq
    change (e.val + 1) % n = e.val at hv
    have h1n : 1 < n := by omega
    have hv' : 1 = 0 := by
      simpa [e, Nat.mod_eq_of_lt h1n] using hv
    omega
  exact allOpen_not_whole_fixed_of_positive_timer_of_nonself_edge
    hpsi h2 htau ring C hOpen ⟨e, hne⟩

/-- The C-final timeout `16 * psi` is positive as soon as `psi` is. -/
theorem campaign_tau_positive (hpsi : 0 < psi) : 0 < 16 * psi := by
  omega

end R2PositiveTimerUniversalMove

#print axioms R2PositiveTimerUniversalMove.raw_row_not_fixed_of_positive_timer
#print axioms R2PositiveTimerUniversalMove.open_row_not_fixed_of_positive_timer
#print axioms R2PositiveTimerUniversalMove.allOpen_not_whole_fixed_of_positive_timer_of_nonself_edge
#print axioms R2PositiveTimerUniversalMove.allOpen_not_whole_fixed_of_positive_timer
