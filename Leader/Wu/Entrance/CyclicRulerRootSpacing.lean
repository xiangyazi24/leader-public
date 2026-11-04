import Leader.Wu.Entrance.AdmissionCyclicRuler
import Leader.Wu.Coherence.CarrierSimulationComponents

set_option autoImplicit false
set_option Elab.async false

namespace CFinalJ2Ruler

open CFinalJ2Edge CFinalJ2Edge2
open CFinalJ2Landing
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open R2CoherenceV31 R2CoherenceV31Closure
open R2CoherenceV31FinalSimulation R2CoherenceV31FinalSimulation5
open R2CoherenceV31ReachableRootSpacing

variable {n psi : Nat}

def CyclicRulerV31
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n psi psi (16 * psi)) : Prop :=
  ∀ a : Fin n,
    (R2CoherenceV31.raw (C (ring.rightNeighbor a))).label =
      ⟨((R2CoherenceV31.raw (C a)).label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

private theorem mod_left (a b m : Nat) :
    (a % m + b) % m = (a + b) % m := by
  rw [Nat.add_mod (a % m) b m, Nat.mod_mod]
  exact (Nat.add_mod a b m).symm

private theorem mod_right (a b m : Nat) :
    (a + b % m) % m = (a + b) % m := by
  rw [Nat.add_mod a (b % m) m, Nat.mod_mod]
  exact (Nat.add_mod a b m).symm

private theorem groupPos_self
    (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n psi psi (16 * psi)) (i : Fin n) :
    R2Coherence.groupPos ring (eraseCfgV3 C) i
      (R2CoherenceV31.raw (C i)).label.val = i := by
  let L := (R2CoherenceV31.raw (C i)).label.val
  apply Fin.ext
  unfold R2Coherence.groupPos R2Coherence.groupStart
    R2Coherence.fwd R2Coherence.back
  dsimp only
  change (((i.val + n - (L % n)) % n + L) % n) = i.val
  have hs : L % n ≤ i.val + n := by
    have hm := Nat.mod_lt L ring.hn
    omega
  calc
    (((i.val + n - (L % n)) % n + L) % n) =
        (i.val + n - (L % n) + L) % n := mod_left _ _ _
    _ = (i.val + n - (L % n) + (L % n)) % n :=
      (mod_right (i.val + n - (L % n)) L n).symm
    _ = (i.val + n) % n := by rw [Nat.sub_add_cancel hs]
    _ = i.val := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
        Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

private theorem groupPos_succ
    (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n psi psi (16 * psi))
    (i : Fin n) (k : Nat) :
    ring.rightNeighbor (R2Coherence.groupPos ring (eraseCfgV3 C) i k) =
      R2Coherence.groupPos ring (eraseCfgV3 C) i (k + 1) := by
  apply Fin.ext
  unfold DirectedRing.rightNeighbor R2Coherence.groupPos R2Coherence.fwd
  dsimp only
  rw [mod_left]
  congr 1

theorem cyclicRulerV31_of_rootSpacing
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n psi psi (16 * psi))
    (hGeom : ElectionGeometryV31 ring C)
    (hRoot : RootSpacingV31 ring C) :
    CyclicRulerV31 hpsi ring C := by
  intro a
  let b := ring.rightNeighbor a
  let L := (R2CoherenceV31.raw (C a)).label.val
  by_cases hz : (R2CoherenceV31.raw (C b)).label.val = 0
  · have hLlt : L < psi := (R2CoherenceV31.raw (C a)).label.isLt
    have hterm : L + 1 = psi := by
      by_cases heq : L + 1 = psi
      · exact heq
      · have hlt : L + 1 < psi := by omega
        let d : Fin psi := ⟨L + 1, hlt⟩
        have hp : R2Coherence.groupPos ring (eraseCfgV3 C) a d.val = b := by
          change R2Coherence.groupPos ring (eraseCfgV3 C) a (L + 1) = b
          calc
            _ = ring.rightNeighbor
                  (R2Coherence.groupPos ring (eraseCfgV3 C) a L) :=
                (groupPos_succ ring C a L).symm
            _ = ring.rightNeighbor a := congrArg ring.rightNeighbor
                (groupPos_self ring C a)
            _ = b := rfl
        have hl :
            (R2CoherenceV31.raw
              (C (R2Coherence.groupPos ring (eraseCfgV3 C) a (L + 1)))).label.val =
              L + 1 := by
          simpa [d] using (hRoot a d)
        rw [hp, hz] at hl
        omega
    apply Fin.ext
    change (R2CoherenceV31.raw (C b)).label.val = (L + 1) % psi
    rw [hz, hterm, Nat.mod_self]
  · have hr : R2CoherenceV31.atRootB (C b) = false := by
      simp [R2CoherenceV31.atRootB, b, hz]
    have hs : R2CoherenceV31.successorB (C a) (C b) = true := by
      simpa [ElectionGeometryV31, R2CoherenceV31.passiveEdgeOKV3, hr, b]
        using hGeom a
    have hv : (R2CoherenceV31.raw (C b)).label.val = L + 1 := by
      simpa [R2CoherenceV31.successorB, L, b] using hs
    have hlt : L + 1 < psi := by
      rw [← hv]
      exact (R2CoherenceV31.raw (C b)).label.isLt
    apply Fin.ext
    change (R2CoherenceV31.raw (C b)).label.val = (L + 1) % psi
    rw [hv, Nat.mod_eq_of_lt hlt]

theorem finalCyclicRuler_iff_view
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi psi (16 * psi)) :
    FinalCyclicRuler hpsi ring C ↔
      CyclicRulerV31 hpsi ring (liftFinalV31 C) := by
  rfl

def ConcreteB7PassiveCyclicRulerEntranceObligation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi psi (16 * psi),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C → FinalCyclicRuler hpsi ring C

theorem cyclicRulerEntrance_of_admittedLabelProfile
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hGeom : C1FinalV31AdmittedElectionGeometryResidual
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hProfile : C1FinalV31AdmittedLabelProfileResidual
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring) :
    ConcreteB7PassiveCyclicRulerEntranceObligation hpsi h2 ring := by
  intro C hA hL
  have hOpen : FinalAllOpen C := hA.2.2.1
  apply (finalCyclicRuler_iff_view hpsi ring C).2
  exact cyclicRulerV31_of_rootSpacing hpsi ring (liftFinalV31 C)
    (hGeom C hA hL hOpen) (hProfile C hA hL hOpen)

private theorem proposalNoWrite_labels
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : R2Coherence.Cell psi psi (16 * psi))
    (hNo : R2Coherence.ProposalNoWrite hpsi (by decide : 0 < 2) h2 l r) :
    let q := R2Coherence.proposal hpsi (by decide : 0 < 2) h2 l r
    q.1.base.core.core.label = l.phys.base.core.core.label ∧
      q.2.base.core.core.label = r.phys.base.core.core.label := by
  dsimp only
  change
    R2Coherence.pairWrites l.phys r.phys
      (R2Coherence.proposal hpsi (by decide : 0 < 2) h2 l r).1
      (R2Coherence.proposal hpsi (by decide : 0 < 2) h2 l r).2 = false ∧
    R2Coherence.pairRelabels l.phys r.phys
      (R2Coherence.proposal hpsi (by decide : 0 < 2) h2 l r).1
      (R2Coherence.proposal hpsi (by decide : 0 < 2) h2 l r).2 = false at hNo
  have h :
      l.phys.base.core.core.label =
          (R2Coherence.proposal hpsi (by decide : 0 < 2) h2 l r).1.base.core.core.label ∧
      r.phys.base.core.core.label =
          (R2Coherence.proposal hpsi (by decide : 0 < 2) h2 l r).2.base.core.core.label := by
    simpa [R2Coherence.pairRelabels, R2Coherence.labelChanged] using hNo.2
  exact ⟨h.1.symm, h.2.symm⟩

private theorem hostR2C_labels_of_open_noWrite
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : R2Coherence.Cell psi psi (16 * psi))
    (hl : R2Coherence.OpenControl l) (hr : R2Coherence.OpenControl r)
    (hNo : R2Coherence.ProposalNoWrite hpsi (by decide : 0 < 2) h2 l r) :
    let q := (hostR2C (κ := psi) (τ := 16 * psi) hpsi h2).row l r
    q.1.phys.base.core.core.label = l.phys.base.core.core.label ∧
      q.2.phys.base.core.core.label = r.phys.base.core.core.label := by
  rcases hl with ⟨hlm, hlt⟩
  rcases hr with ⟨hrm, hrt⟩
  have he := R2Coherence.row_eq_r2_of_open_no_write
    hpsi (by decide : 0 < 2) h2 l r hlm hrm hlt hrt hNo
  have hp := proposalNoWrite_labels hpsi h2 l r hNo
  dsimp only [hostR2C]
  rw [he]
  simpa [R2Coherence.install] using hp

private theorem concretePort_row_labels
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi psi (16 * psi)) (e : Fin n)
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C) :
    let q := (concretePort (κ := psi) (τ := 16 * psi) hpsi h2).row
      (C e) (C (ring.rightNeighbor e))
    q.1.phys.phys.base.core.core.label = (C e).phys.phys.base.core.core.label ∧
      q.2.phys.phys.base.core.core.label =
        (C (ring.rightNeighbor e)).phys.phys.base.core.core.label := by
  have ha : (concretePort (κ := psi) (τ := 16 * psi) hpsi h2).action
      (C e) (C (ring.rightNeighbor e)) = .host := by
    simpa only [concretePort, concretePortLocal] using (hA.2.2.2 e).2.1
  have hs := (concretePort (κ := psi) (τ := 16 * psi) hpsi h2).physical_spec
    (C e) (C (ring.rightNeighbor e))
  simp only [ha] at hs
  have hh := hostR2C_labels_of_open_noWrite hpsi h2
    (C e).phys (C (ring.rightNeighbor e)).phys
    (hA.2.2.1 e) (hA.2.2.1 (ring.rightNeighbor e)) (hA.2.2.2 e).2.2
  dsimp only
  exact ⟨
    (congrArg (fun u : R2Coherence.Cell psi psi (16 * psi) =>
      u.phys.base.core.core.label) hs.1).trans hh.1,
    (congrArg (fun u : R2Coherence.Cell psi psi (16 * psi) =>
      u.phys.base.core.core.label) hs.2).trans hh.2⟩

theorem stepConcrete_labels_eq_of_passive_admitted
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi psi (16 * psi)) (e i : Fin n)
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C) :
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e i).phys.phys.base.core.core.label =
      (C i).phys.phys.base.core.core.label := by
  classical
  have hg := (hA.2.2.2 e).1
  have hp := concretePort_row_labels hpsi h2 ring C e hA
  dsimp only at hp
  by_cases hs : ring.rightNeighbor e = e
  · have hgs : ¬ FinalGarbage hpsi (C e) (C e) := by simpa only [hs] using hg
    change (stepFinal hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring C e i).phys.phys.base.core.core.label = _
    unfold stepFinal
    rw [if_pos hs, if_neg hgs]
  · have ha : (concretePort (κ := psi) (τ := 16 * psi) hpsi h2).action
        (C e) (C (ring.rightNeighbor e)) = .host := by
      simpa only [concretePort, concretePortLocal] using (hA.2.2.2 e).2.1
    have hrow : rowFinal hpsi h2
        (concretePort (κ := psi) (τ := 16 * psi) hpsi h2)
        (C e) (C (ring.rightNeighbor e)) =
        (concretePort (κ := psi) (τ := 16 * psi) hpsi h2).row
          (C e) (C (ring.rightNeighbor e)) := by
      unfold rowFinal finalAction
      rw [if_neg hg, ha]
    change (stepFinal hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring C e i).phys.phys.base.core.core.label = _
    unfold stepFinal
    rw [if_neg hs, hrow]
    by_cases hi : i = e
    · subst i
      simp only [B9FullCarrierHost.writeAtP, if_pos rfl]
      exact hp.1
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simp only [B9FullCarrierHost.writeAtP, if_neg hs, if_pos rfl]
        exact hp.2
      · simp only [B9FullCarrierHost.writeAtP, if_neg hi, if_neg hj]

theorem finalCyclicRuler_stepConcrete
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi psi (16 * psi)) (e : Fin n)
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C)
    (hR : FinalCyclicRuler hpsi ring C) :
    FinalCyclicRuler hpsi ring
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e) := by
  intro a
  have hr := hR a
  change (C (ring.rightNeighbor a)).phys.phys.base.core.core.label =
    ⟨((C a).phys.phys.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ at hr
  change (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e
      (ring.rightNeighbor a)).phys.phys.base.core.core.label =
    ⟨((stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e a).phys.phys.base.core.core.label.val + 1) % psi,
      Nat.mod_lt _ hpsi⟩
  rw [stepConcrete_labels_eq_of_passive_admitted hpsi h2 ring C e _ hA,
    stepConcrete_labels_eq_of_passive_admitted hpsi h2 ring C e a hA]
  exact hr

theorem cyclicRulerPost_of_entrance
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hEnt : ConcreteB7PassiveCyclicRulerEntranceObligation hpsi h2 ring) :
    ConcreteB7PassiveCyclicRulerPostObligation hpsi h2 ring := by
  intro C e hA hL
  dsimp only
  intro _hDL
  exact finalCyclicRuler_stepConcrete hpsi h2 ring C e hA (hEnt C hA hL)

theorem j2Hole_of_cyclicRulerEntrance
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hEnt : ConcreteB7PassiveCyclicRulerEntranceObligation hpsi h2 ring) :
    J2C1AdmissionHoleResidual hpsi h2 ring :=
  j2C1AdmissionHoleResidual_of_cyclicRulerPost hpsi h2 ring
    (cyclicRulerPost_of_entrance hpsi h2 ring hEnt)

theorem j2Edge_of_cyclicRulerEntrance
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hEnt : ConcreteB7PassiveCyclicRulerEntranceObligation hpsi h2 ring)
    (hNoWrite : ConcreteB7PassiveProposalNoWritePostObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring) :
    J2C1AdmissionEdgeResidual hpsi h2 ring :=
  CFinalJ2Edge.j2C1AdmissionEdgeResidual_of_residuals hpsi h2 ring
    (j2Hole_of_cyclicRulerEntrance hpsi h2 ring hEnt)
    (j2C1AdmissionHostActionResidual_closed hpsi h2 ring) hNoWrite

end CFinalJ2Ruler
