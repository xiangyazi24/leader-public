import Leader.Wu.Birth.IncreaseOrCapNoBoundarySurvival

namespace BirthPhaseB3PhysicalFireIdentification

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait BirthShortWaitProjection
  BirthShortWaitTerminalEntryRepair
open BirthWaitClockMass
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation
open BirthShortWaitDomainWitness

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

private theorem key_label (u v : AgentState 2)
    (h : WaitKey.ofState u = WaitKey.ofState v) : u.label = v.label := by
  apply Fin.ext
  simpa [WaitKey.ofState] using congrArg WaitKey.label h

private theorem key_h (u v : AgentState 2)
    (h : WaitKey.ofState u = WaitKey.ofState v) : u.h_field = v.h_field := by
  simpa [WaitKey.ofState] using congrArg WaitKey.h_field h

private theorem key_carry (u v : AgentState 2)
    (h : WaitKey.ofState u = WaitKey.ofState v) : u.carry = v.carry := by
  simpa [WaitKey.ofState] using congrArg WaitKey.carry h

private theorem key_reset (u v : AgentState 2)
    (h : WaitKey.ofState u = WaitKey.ofState v) : u.reset = v.reset := by
  simpa [WaitKey.ofState] using congrArg WaitKey.reset h

private theorem key_count (u v : AgentState 2)
    (h : WaitKey.ofState u = WaitKey.ofState v) : u.count = v.count := by
  simpa [WaitKey.ofState] using congrArg WaitKey.count h

private theorem waitSaturated_key_congr (cap : Nat)
    (a b c d : AgentState 2)
    (ha : WaitKey.ofState a = WaitKey.ofState c)
    (hb : WaitKey.ofState b = WaitKey.ofState d) :
    waitKeyPair (waitSaturated (by decide : 0 < 2) cap a b) =
      waitKeyPair (waitSaturated (by decide : 0 < 2) cap c d) := by
  have hal := key_label a c ha
  have hbl := key_label b d hb
  have hah := key_h a c ha
  have hac := key_carry a c ha
  have haz := key_reset a c ha
  have han := key_count a c ha
  have hbh := key_h b d hb
  have hbc := key_carry b d hb
  have hbz := key_reset b d hb
  have hbn := key_count b d hb
  simp [waitKeyPair, WaitKey.ofState, waitSaturated,
    waitSaturatedPrepare, waitSaturatedCarry, waitSaturatedReset,
    waitSaturatedFinish, hal, hbl, hah, hac, haz, han,
    hbh, hbc, hbz, hbn]

/-- The already-proved physical no-stop induction, exported at the exact B3
prefix seam. -/
theorem noStopPrefixCountNondecrease
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : BirthPhaseWait2Transfer.FC n psi kappa tau)
    (hC : BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C)
    (pre : List (Fin n))
    (hrun : BirthPhaseWait2Transfer.LocalWait2RunSource
      hpsi h2 hn kappa tau ring anchor C pre) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseGenericRenewal.rawEndpoint
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C pre) := by
  exact BirthPhaseB3NoBoundarySurvival.noBoundaryNoCap_suffix_count_nondec
    hpsi h2 hn kappa tau ring anchor C hC.1 pre hrun

/-- Exact local identification needed at the first strict raw service fire.
Only the two width-two WAIT keys are synchronized; unrelated state is absent. -/
theorem strictAnchorOfRawFire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : BirthPhaseWait2Transfer.FC n psi kappa tau)
    (S : Fin n -> AgentState 2)
    (hl : (raw (C anchor)).label.val < 2)
    (hr : (raw (C (ring.rightNeighbor anchor))).label.val < 2)
    (hproj : RowProjection2 hpsi h2 kappa tau ring C anchor)
    (hk0 : WaitKey.ofState
        (waitPrefixProject (raw (C anchor)) hl) =
      WaitKey.ofState (S (p0 hn)))
    (hk1 : WaitKey.ofState
        (waitPrefixProject (raw (C (ring.rightNeighbor anchor))) hr) =
      WaitKey.ofState (S (p1 hn)))
    (hraw : (S (p1 hn)).count <
      (BirthWaitClockMass.RawRing.rawStep
        (w := 2) (n := n) (by omega : 2 < n)
        (by decide : 2 <= 2) kappa S (p0 hn) (p1 hn)).count) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C anchor) := by
  let l := raw (C anchor)
  let r := raw (C (ring.rightNeighbor anchor))
  let lp := waitPrefixProject l hl
  let rp := waitPrefixProject r hr
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r
  let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2
    (C anchor) (C (ring.rightNeighbor anchor))
  have hp := hproj
  unfold RowProjection2 at hp
  change clock (raw q.1) = clock w.1 /\ clock (raw q.2) = clock w.2 at hp
  have hq : (raw q.2).count = w.2.count :=
    congrArg (fun z : Clock psi => z.count) hp.2
  have hentry :
      w = BirthShortWait.waitWidth hpsi (by decide : 0 < 2) h2 kappa l r := by
    dsimp [w]
    exact waitWidthEntry_eq_old_of_active_labels
      hpsi (by decide : 0 < 2) h2 kappa l r hl hr
  have hregs : waitRegsPair w =
      waitRegsPair (waitSaturated (by decide : 0 < 2) kappa lp rp) := by
    rw [hentry]
    simpa only [lp, rp] using
      (waitWidth_regs_eq_waitSaturated_prefix
        (kappa := kappa) hpsi (by decide : 0 < 2) h2 l r hl hr)
  have hwc : w.2.count =
      (waitSaturated (by decide : 0 < 2) kappa lp rp).2.count := by
    simpa [waitRegsPair, WaitRegs.ofState] using
      congrArg (fun z : WaitRegs × WaitRegs => z.2.count) hregs
  have hkc := waitSaturated_key_congr kappa lp rp
    (S (p0 hn)) (S (p1 hn)) (by simpa [lp, l] using hk0)
      (by simpa [rp, r] using hk1)
  have hsc :
      (waitSaturated (by decide : 0 < 2) kappa lp rp).2.count =
        (waitSaturated (by decide : 0 < 2) kappa
          (S (p0 hn)) (S (p1 hn))).2.count := by
    simpa [waitKeyPair, WaitKey.ofState] using
      congrArg (fun z : WaitKey × WaitKey => z.2.count) hkc
  let hfit : 2 < n := by omega
  have hp0root : p0 hn ≠ BirthWaitClockMass.RawRing.rootIncoming hfit := by
    intro h
    have hv := congrArg Fin.val h
    simp [p0, BirthWaitClockMass.RawRing.rootIncoming] at hv
    omega
  have hresp := BirthWaitClockMass.RawRing.rawStep_responder
    hfit (by decide : 2 <= 2) kappa S (p0 hn) hp0root
  rw [right_p0 hn (BirthWaitClockMass.RawRing.ring hfit)] at hresp
  have hrc :
      (BirthWaitClockMass.RawRing.rawStep hfit
        (by decide : 2 <= 2) kappa S (p0 hn) (p1 hn)).count =
        (waitSaturated (by decide : 0 < 2) kappa
          (S (p0 hn)) (S (p1 hn))).2.count := by
    simpa only using congrArg (fun z : AgentState 2 => z.count) hresp
  have hne := rightNeighbor_ne_self_of_one_lt ring (by omega : 1 < n) anchor
  have hs : BirthPhaseWait2Transfer.hostStep hpsi h2 ring C anchor
      (ring.rightNeighbor anchor) = q.2 :=
    BirthShortDoneTerminalPassiveR4.hostStep_right hpsi h2 ring C anchor hne
  have hs' : BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C anchor
      (ring.rightNeighbor anchor) = q.2 := by
    rw [<- BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2
      hpsi h2 ring C anchor]
    exact hs
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  rw [hs']
  change r.count < (raw q.2).count
  calc
    r.count = (S (p1 hn)).count := key_count rp (S (p1 hn))
      (by simpa [rp, r, WaitKey_of_waitPrefixProject] using hk1)
    _ < (BirthWaitClockMass.RawRing.rawStep hfit
          (by decide : 2 <= 2) kappa S (p0 hn) (p1 hn)).count := by
      simpa [hfit] using hraw
    _ = (waitSaturated (by decide : 0 < 2) kappa
          (S (p0 hn)) (S (p1 hn))).2.count := hrc
    _ = (waitSaturated (by decide : 0 < 2) kappa lp rp).2.count := hsc.symm
    _ = w.2.count := hwc.symm
    _ = (raw q.2).count := hq.symm

#print axioms BirthPhaseB3PhysicalFireIdentification.noStopPrefixCountNondecrease
#print axioms BirthPhaseB3PhysicalFireIdentification.strictAnchorOfRawFire

end BirthPhaseB3PhysicalFireIdentification
