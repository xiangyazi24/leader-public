import Leader.Wu.Elimination.SinkTwoGapWiredInstance
import Leader.Wu.Elimination.SinkTwoGapRankBoundaryDischarged

set_option autoImplicit false

open FiniteUniformStoppingTree PredictableRenewalOverlap
open PPLLRepair LDSinkGapCleanup LDTwoGapFrame
open LDSinkTwoGapEpochKernel LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance LDSinkTwoGapDeletion LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant LDSinkTwoGapRestartClosure
open CleanBoundaryDecision
open LDSinkTwoGapWiredInstance

namespace LDSinkTwoGapPhysPortSpecInstance

noncomputable section

variable {n psi : Nat}

/-! ## Two concrete fallback ports -/

theorem frame_one_lt_n (F : TwoGapFrame n) : 1 < n := by
  have hr := F.recovery.hd
  have ha := F.attack.hd
  have hl := F.length_lt
  omega

def port0 (F : TwoGapFrame n) : Fin n :=
  ⟨0, by
    have h := frame_one_lt_n F
    omega⟩

def port1 (F : TwoGapFrame n) : Fin n :=
  ⟨1, frame_one_lt_n F⟩

theorem port0_ne_port1 (F : TwoGapFrame n) : port0 F ≠ port1 F := by
  intro h
  have hv := congrArg Fin.val h
  change 0 = 1 at hv
  omega

def otherPort (F : TwoGapFrame n) (p : Fin n) : Fin n :=
  if p = port0 F then port1 F else port0 F

theorem port_ne_otherPort (F : TwoGapFrame n) (p : Fin n) :
    p ≠ otherPort F p := by
  unfold otherPort
  by_cases h0 : p = port0 F
  · rw [if_pos h0]
    intro h1
    exact port0_ne_port1 F (h0.symm.trans h1)
  · rw [if_neg h0]
    exact h0

/-! ## Configuration-only physical step -/

theorem attemptStepConf_conf_only
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (x s : AState n psi) (e : Fin n)
    (h : x.conf = s.conf) :
    attemptStepConf hpsi F x e = attemptStepConf hpsi F s e := by
  rw [attemptStepConf_eq_sinkStepC hpsi F x e,
    attemptStepConf_eq_sinkStepC hpsi F s e, h]

theorem postState_conf_only
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (x s : AState n psi) (e : Fin n)
    (h : x.conf = s.conf) :
    (postState hpsi F x e).conf = (postState hpsi F s e).conf := by
  change attemptStepConf hpsi F x e = attemptStepConf hpsi F s e
  exact attemptStepConf_conf_only hpsi F x s e h

/-! ## Weak equality relation and unconditional one-step GapPair closure -/

def pairRel
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (x s : AState n psi) : Prop :=
  GapPair hpsi F x ∧ GapPair hpsi F s ∧ x.conf = s.conf

theorem gapPair_postState
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AState n psi) (e : Fin n)
    (hi : GapPair hpsi F x)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F x e)) :
    GapPair hpsi F (postState hpsi F x e) := by
  have hy :
      physicalBlockStep hpsi F x e = .active (postState hpsi F x e) := by
    rw [physicalBlockStep_normal_form, if_neg hn]
  exact LDSinkTwoGapRestartClosure.gapPair_physical_step
    hpsi F
    (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F)
    x e (postState hpsi F x e) hi hy

theorem pairRel_postState
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (x s : AState n psi) (e : Fin n)
    (hrel : pairRel hpsi F x s)
    (hnS : ¬ NoResetSuccess F (attemptStepConf hpsi F s e)) :
    pairRel hpsi F
      (postState hpsi F x e) (postState hpsi F s e) := by
  rcases hrel with ⟨hx, hs, hconf⟩
  have hnX : ¬ NoResetSuccess F (attemptStepConf hpsi F x e) := by
    intro hxSuccess
    apply hnS
    have heq := attemptStepConf_conf_only hpsi F x s e hconf
    rw [← heq]
    exact hxSuccess
  exact ⟨
    gapPair_postState hpsi F x e hx hnX,
    gapPair_postState hpsi F s e hs hnS,
    postState_conf_only hpsi F x s e hconf⟩

/-! ## Exact serial-stage-2 support -/

inductive SecondSupport
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (firstGood : AState n psi → Fin n) : AState n psi → Prop where
  | enter (a : AState n psi)
      (hpair : GapPair hpsi F a)
      (hn : ¬ NoResetSuccess F
        (attemptStepConf hpsi F a (firstGood a))) :
      SecondSupport hpsi F firstGood
        (postState hpsi F a (firstGood a))
  | step (b : AState n psi) (e : Fin n)
      (hsupport : SecondSupport hpsi F firstGood b)
      (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F b e)) :
      SecondSupport hpsi F firstGood (postState hpsi F b e)

/-- The one physical race fact left after all equality/closure bookkeeping is
removed. The selector functions are data; `success` is the sole semantic field. -/
structure RacePortResidual
    (hpsi : psi > 0) (F : TwoGapFrame n) where
  firstGood : AState n psi → Fin n
  secondGood : AState n psi → Fin n
  success : ∀ b : AState n psi,
    SecondSupport hpsi F firstGood b →
      NoResetSuccess F (attemptStepConf hpsi F b (secondGood b))

def firstBad
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : RacePortResidual hpsi F) (a : AState n psi) : Fin n :=
  otherPort F (H.firstGood a)

def secondBad
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : RacePortResidual hpsi F) (b : AState n psi) : Fin n :=
  otherPort F (H.secondGood b)

def secondRel
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : RacePortResidual hpsi F)
    (b s : AState n psi) : Prop :=
  SecondSupport hpsi F H.firstGood b ∧ pairRel hpsi F b s

theorem firstTotalGood_eq
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : RacePortResidual hpsi F) (a : AState n psi) :
    totalGood (port0 F) H.firstGood (firstBad hpsi F H) a =
      H.firstGood a := by
  unfold totalGood firstBad
  rw [if_neg (port_ne_otherPort F (H.firstGood a))]

theorem secondTotalGood_eq
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : RacePortResidual hpsi F) (b : AState n psi) :
    totalGood (port0 F) H.secondGood (secondBad hpsi F H) b =
      H.secondGood b := by
  unfold totalGood secondBad
  rw [if_neg (port_ne_otherPort F (H.secondGood b))]

/-! ## All seven PhysPortSpec fields -/

noncomputable def physPortSpec
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : RacePortResidual hpsi F) : PhysPortSpec hpsi F where
  fallbackGood := port0 F
  fallbackBad := port1 F
  fallback_ne := port0_ne_port1 F

  firstGoodRaw := H.firstGood
  firstBadRaw := firstBad hpsi F H
  secondGoodRaw := H.secondGood
  secondBadRaw := secondBad hpsi F H

  firstRel := pairRel hpsi F
  secondRel := secondRel hpsi F H

  init_success := by
    intro x s e hrel hxSuccess
    change pairRel hpsi F x s at hrel
    have heq := attemptStepConf_conf_only hpsi F x s e hrel.2.2
    rw [← heq]
    exact hxSuccess

  init_continue := by
    intro x s e hrel _hEntrance hnS
    change pairRel hpsi F x s at hrel
    change pairRel hpsi F
      (postState hpsi F x e) (postState hpsi F s e)
    exact pairRel_postState hpsi F x s e hrel hnS

  init_handoff := by
    intro x s e hrel _hEntrance _hnX hnS
    change pairRel hpsi F x s at hrel
    change pairRel hpsi F
      (postState hpsi F x e) (postState hpsi F s e)
    exact pairRel_postState hpsi F x s e hrel hnS

  first_good := by
    intro a s hrel hnS
    change pairRel hpsi F a s at hrel
    have hgood := firstTotalGood_eq hpsi F H a
    rw [hgood] at hnS ⊢
    have hnA :
        ¬ NoResetSuccess F
          (attemptStepConf hpsi F a (H.firstGood a)) := by
      intro haSuccess
      apply hnS
      have heq := attemptStepConf_conf_only
        hpsi F a s (H.firstGood a) hrel.2.2
      rw [← heq]
      exact haSuccess
    have hpair := pairRel_postState
      hpsi F a s (H.firstGood a) hrel hnS
    change secondRel hpsi F H
      (postState hpsi F a (H.firstGood a))
      (postState hpsi F s (H.firstGood a))
    exact ⟨
      SecondSupport.enter
        (hpsi := hpsi) (F := F) (firstGood := H.firstGood)
        a hrel.1 hnA,
      hpair⟩

  first_continue := by
    intro a s e hrel _hgood _hbad hnS
    change pairRel hpsi F a s at hrel
    change pairRel hpsi F
      (postState hpsi F a e) (postState hpsi F s e)
    exact pairRel_postState hpsi F a s e hrel hnS

  second_good := by
    intro b s hrel
    change secondRel hpsi F H b s at hrel
    rcases hrel with ⟨hsupport, hb, hs, hconf⟩
    have hgood := secondTotalGood_eq hpsi F H b
    rw [hgood]
    have hbSuccess := H.success b hsupport
    have heq := attemptStepConf_conf_only
      hpsi F b s (H.secondGood b) hconf
    rw [← heq]
    exact hbSuccess

  second_continue := by
    intro b s e hrel _hgood _hbad hnS
    change secondRel hpsi F H b s at hrel
    rcases hrel with ⟨hsupport, hb, hs, hconf⟩
    have hnB : ¬ NoResetSuccess F (attemptStepConf hpsi F b e) := by
      intro hbSuccess
      apply hnS
      have heq := attemptStepConf_conf_only hpsi F b s e hconf
      rw [← heq]
      exact hbSuccess
    have hpair : pairRel hpsi F
        (postState hpsi F b e) (postState hpsi F s e) :=
      pairRel_postState hpsi F b s e ⟨hb, hs, hconf⟩ hnS
    change secondRel hpsi F H
      (postState hpsi F b e) (postState hpsi F s e)
    exact ⟨
      SecondSupport.step
        (hpsi := hpsi) (F := F) (firstGood := H.firstGood)
        b e hsupport hnB,
      hpair⟩

/-- Conditional capstone: all generic wiring is now proved; only the one
physical race-port residual remains. -/
theorem wired_gapPair_of_racePort
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : RacePortResidual hpsi F) :
    WiredResidualGapPair hpsi F
      (physD hpsi F (physPortSpec hpsi F H))
      (ready hpsi F)
      (Rel hpsi F (physPortSpec hpsi F H)) := by
  exact wired_gapPair hpsi F (physPortSpec hpsi F H)

end

end LDSinkTwoGapPhysPortSpecInstance

#print axioms LDSinkTwoGapPhysPortSpecInstance.frame_one_lt_n
#print axioms LDSinkTwoGapPhysPortSpecInstance.port0_ne_port1
#print axioms LDSinkTwoGapPhysPortSpecInstance.port_ne_otherPort
#print axioms LDSinkTwoGapPhysPortSpecInstance.attemptStepConf_conf_only
#print axioms LDSinkTwoGapPhysPortSpecInstance.postState_conf_only
#print axioms LDSinkTwoGapPhysPortSpecInstance.gapPair_postState
#print axioms LDSinkTwoGapPhysPortSpecInstance.pairRel_postState
#print axioms LDSinkTwoGapPhysPortSpecInstance.firstTotalGood_eq
#print axioms LDSinkTwoGapPhysPortSpecInstance.secondTotalGood_eq
#print axioms LDSinkTwoGapPhysPortSpecInstance.wired_gapPair_of_racePort
