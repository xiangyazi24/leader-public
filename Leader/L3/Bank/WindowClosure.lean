import Leader.L3.Bank.WindowTraversal

/-!
BANK-PHASE: closure of the state contract J (BankWindowExact) and
births only in complete windows.

Proved here: a real pending-RL birth creates a genuine zero-headed
controller at its root and keeps the root's PACK 0 and the first
digit's PACK 1.  The earlier PROTO clause allowed a
second token in front of the waiting root's pending RR; PROTO now
requires that pending RR to be the leftmost token (BankWindowExact,
PROGRESS 2026-11-01).
-/
namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The real OLD RWAIT/RL birth promotes the consumed pending
receipt to a genuine, zero-headed controller at its source.
Consumer: the proto-run root branch of BANK-PHASE. The fact
does not require a complete PACK window. -/
theorem bankWindowClosureBirthCreatesGenuineRoot
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (e : Fin n) (o : RenewalBankOrigin n)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    ∃ p : RenewalBankPayload n,
      ((renewalBankNext ring r e).2.sites e).controller =
        .active p ∧
      p.origin = some o ∧ p.heads = 0 := by
  obtain ⟨hx, hg, hy, hm, ht, rho, hw, hroot,
    hservice, hreceipt⟩ :=
    bankWindowBirthOldReceipt ring r.1 r.2 e o hbirth
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpair := rbZeroAcceptMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    rho hb hx hy hg hm ht hw
  have hsource := (rbReferenceSelectedPairFrame ring hn r e).2.2.1
  change ((renewalBankNext ring r e).2.sites e) =
    (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      r.2 e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1 at hsource
  have hcontroller := congrArg
    (fun z : RenewalBankSite n => z.controller) hsource
  rw [hpair] at hcontroller
  have hidentity :
      ({ service := r.2.service, root := e, receipt := rho }
        : RenewalBankOrigin n) = o := by
    cases o with
    | mk service root receipt =>
        dsimp at hroot hservice hreceipt
        cases hservice
        cases hroot
        cases hreceipt
        rfl
  refine ⟨
    { atoms := renewalBankWaitingAtoms (r.2.sites e).controller
      origin := some
        { service := r.2.service, root := e, receipt := rho }
      heads := 0 }, ?_, ?_, rfl⟩
  · exact hcontroller
  · exact congrArg some hidentity

/-- A real birth does not repair PACK at either endpoint: its
OLD 0→1 edge is already aligned, so the source stays role zero
and the responder stays role one. Consumer: identifying the
unchanged proto-run root after a pending-RL acceptance. -/
theorem bankWindowClosureBirthKeepsPackPrefix
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (e : Fin n) (o : RenewalBankOrigin n)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    ((renewalBankNext ring r e).1 e).pack.val = 0 ∧
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 1 := by
  obtain ⟨hx, _, hy, _, _, _⟩ :=
    bankWindowBirthOldReceipt ring r.1 r.2 e o hbirth
  have hp := rbBankReferencePairPack ring hn r e
  have hsource :
      ((renewalBankNext ring r e).1 e).pack.val =
        (r.1 e).pack.val := by
    change ((rbRun ring r [e]).1 e).pack.val =
      (r.1 e).pack.val
    exact hp.1
  have htarget :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val =
          packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b := by
    change ((rbRun ring r [e]).1
      (ring.rightNeighbor e)).pack.val =
        packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b
    exact hp.2
  rw [hx] at hsource
  rw [hx, hy] at htarget
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hnext :
      packNext 0 1 (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  rw [hnext] at htarget
  exact ⟨hsource, htarget⟩

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Appendix C: a genuine OLD RWAIT/RL pending birth excludes
every first PACK mismatch in the root's current proto-run.
Used by bankWindowClosureBirthComplete. -/
private theorem bankWindowClosureReturnRejectsProto
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (e : Fin n) (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring r)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o)
    (limit : Nat)
    (hproto : BankWindowProtoRun ring r e limit) : False := by
  obtain ⟨hroot, _, hfirst, hmode, htok,
    rho, hworker, _, _, _⟩ :=
    bankWindowBirthOldReceipt ring r.1 r.2 e o hbirth
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hlimit : 1 ≤ limit := by
    by_cases hzero : limit = 0
    · have hbad := hproto.2.2
      rw [hzero] at hbad
      change (r.1 (ring.rightNeighbor e)).pack.val ≠ 1 at hbad
      exact False.elim (hbad hfirst)
    · omega
  have hshape :
      ∃ atoms : List (RenewalBankAtom n),
        (r.2.sites e).controller = .waiting atoms := by
    have hframe := (hJ.frame e).1
    simpa [bankInFlightControllerShape, hroot, hmode] using hframe
  obtain ⟨atoms, hcontroller⟩ := hshape
  cases atoms with
  | nil =>
      obtain ⟨j, _, rhoFront, _, hrr, _, hleft⟩ :=
        (hJ.proto e limit hproto).2.2.1 ⟨hmode, hcontroller⟩
      by_cases hjzero : j.val = 0
      · rw [hjzero] at hrr
        change (r.1 (ring.rightNeighbor e)).tok = .RR at hrr
        rw [htok] at hrr
        cases hrr
      · have he :=
          hleft (⟨0, hb⟩ :
            Fin (compileAdvice (ceilLogTwo n)).b)
            (show 0 < j.val by omega)
        change (r.1 (ring.rightNeighbor e)).tok = .E at he
        rw [htok] at he
        cases he
  | cons a tail =>
      have hinherited : BankWindowInheritedController r e :=
        Or.inl ⟨a :: tail, hcontroller, by simp⟩
      have hnot := (hJ.proto e limit hproto).2.1 hinherited
        (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
        (show 1 ≤ limit by omega)
      apply hnot
      change BankWindowTainted r (ring.rightNeighbor e)
      exact Or.inl ⟨rho, hworker⟩

/-- Appendix C: every actual pending-RL BANK birth under the
OLD exact state invariant J has a complete physical PACK
window through digit b. No historical RR path is assumed. -/
theorem bankWindowClosureBirthComplete
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (e : Fin n) (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring r)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    Counter.Complete ring r.1 e := by
  have hroot :=
    (bankWindowBirthOldReceipt ring r.1 r.2 e o hbirth).1
  have hprefix :
      ∀ j : Nat, j ≤ (compileAdvice (ceilLogTwo n)).b →
        ∀ k : Nat, k ≤ j →
          (r.1 (Counter.site ring e k)).pack.val = k := by
    intro j
    induction j with
    | zero =>
        intro _ k hk
        have hkzero : k = 0 := by omega
        subst k
        change (r.1 e).pack.val = 0
        exact hroot
    | succ j ih =>
        intro hj k hk
        by_cases hbefore : k ≤ j
        · exact ih (by omega) k hbefore
        · have hknext : k = j + 1 := by omega
          subst k
          by_cases haligned :
              (r.1 (Counter.site ring e (j + 1))).pack.val =
                j + 1
          · exact haligned
          · have hproto : BankWindowProtoRun ring r e j :=
              ⟨(by omega), ih (by omega), haligned⟩
            exact False.elim
              (bankWindowClosureReturnRejectsProto ring r e o
                hJ hbirth j hproto)
  intro j hj
  exact hprefix (compileAdvice (ceilLogTwo n)).b
    (Nat.le_refl _) j hj

/-- Appendix C reset-return preparation: J excludes independent
inherited atoms, leaves the returning RL as the only nonempty
digit token, and fixes every digit bit to zero before birth.
Consumer: the post-birth ARMED/zero-head J row. -/
theorem bankWindowClosureBirthClearedWindow
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (e : Fin n) (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring r)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    (r.2.sites e).controller = .waiting [] ∧
    bankWindowOnlyToken ring r e (ring.rightNeighbor e) ∧
    bankWindowZeroPrefix ring r e
      (compileAdvice (ceilLogTwo n)).b := by
  obtain ⟨hroot, hgrant, _, hmode, htok,
    rho, hworker, _, _, _⟩ :=
    bankWindowBirthOldReceipt ring r.1 r.2 e o hbirth
  have hscope : BankWindowScope ring r e :=
    ⟨bankWindowClosureBirthComplete ring r e o hJ hbirth, hgrant⟩
  have hshape :
      ∃ atoms : List (RenewalBankAtom n),
        (r.2.sites e).controller = .waiting atoms := by
    have hframe := (hJ.frame e).1
    simpa [bankInFlightControllerShape, hroot, hmode] using hframe
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  obtain ⟨atoms, hctl⟩ := hshape
  have hempty : (r.2.sites e).controller = .waiting [] := by
    cases atoms with
    | nil =>
        exact hctl
    | cons a rest =>
        have hinherited : BankWindowInheritedController r e :=
          Or.inl ⟨a :: rest, hctl, by simp⟩
        have hnot := hJ.inheritedClean e hscope hinherited
          (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
        apply False.elim
        apply hnot
        change BankWindowTainted r (ring.rightNeighbor e)
        exact Or.inl ⟨rho, hworker⟩
  obtain ⟨j, rhoFront, hfrontWorker, _, _, hleft, hreturn⟩ :=
    hJ.resetWait e hscope hmode hempty
  have hjzero : j.val = 0 := by
    by_cases hz : j.val = 0
    · exact hz
    · have he := hleft
        (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
        (show 0 < j.val by omega)
      change (r.1 (ring.rightNeighbor e)).tok = .E at he
      rw [htok] at he
      cases he
  have hRL : (r.1 (Counter.site ring e (j.val + 1))).tok =
      .RL := by
    rw [hjzero]
    change (r.1 (ring.rightNeighbor e)).tok = .RL
    exact htok
  have htail := hreturn hRL
  have hsite :
      Counter.site ring e (j.val + 1) =
        ring.rightNeighbor e := by
    rw [hjzero]
    rfl
  rw [hsite] at htail
  exact ⟨hempty, htail.1, htail.2⟩

/-- Appendix C: at a genuine OLD reset-return the real masked
physical source leaves RWAIT and becomes ARMED. Consumer:
the post-birth local J transition. -/
theorem bankWindowClosureBirthPostArmed
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    ((renewalBankNext ring r e).1 e).mode = .ARMED := by
  obtain ⟨hx, hg, hy, hm, ht, _, _, _, _, _⟩ :=
    bankWindowBirthOldReceipt ring r.1 r.2 e o hbirth
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpack :
      packNext 0 1 (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  have howner :
      (Counter.resetBankOld (r.1 e)
        (r.1 (ring.rightNeighbor e))).1.mode = .ARMED := by
    have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hg, hy, hm, ht, hb0, hpack, isRetTok]
  have hf := (rbReferenceSelectedPairFrame ring hn r e).1
  have hforget := (renewalMaskedPairFrames
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))).1
  have htrip := (Counter.resetTransitionBankTrip
    (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e)) hbank).1
  have hsource :=
    congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode) hf
  have hmask :=
    congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
      hforget
  have hbankrow := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((renewalBankNext ring r e).1 e).mode =
    (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode at hsource
  change (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode at hmask
  change (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.mode at hbankrow
  exact hsource.trans (hmask.trans (hbankrow.trans howner))

/-- PACK-change sanitation excludes any surviving genuine
controller at the repaired responder. This is the controller
component needed by PROTO/ORPH repair rows of J. -/
theorem bankWindowClosureChangedResponderNoOrigin
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val) :
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).mode = .RESET ∧
    ¬ BankWindowInheritedController
      (renewalBankNext ring r e) (ring.rightNeighbor e) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((renewalBankNext ring r e).2.sites
        (ring.rightNeighbor e)).controller = .active p →
      p.origin = some o → False) := by
  obtain ⟨hm, _, _, _, hc⟩ :=
    bankWindowBirthChangedResponderStep ring hn hbank r e hchanged
  refine ⟨hm, ?_, ?_⟩
  · intro hinherited
    rcases hinherited with ⟨atoms, hw, _⟩ | ⟨p, hw, _⟩
    · rw [hc] at hw
      cases hw
    · rw [hc] at hw
      cases hw
  · intro p o hw _
    rw [hc] at hw
    cases hw

/-- Real RESET launch at a normalized 0→1 edge overwrites
*any* OLD responder worker, including an orphan receipt, by
the new root's pending RR. No stale worker is copied. -/
theorem bankWindowClosureResetLaunchGhost
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RESET) :
    ((renewalBankNext ring r e).2.sites e).controller =
      .waiting [] ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker =
        .pending { service := r.2.service, root := e } := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpair := rbResetLaunchMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    hb hx hy hg hm
  have hframe := (rbReferenceSelectedPairFrame ring hn r e).2.2
  have hsource : ((renewalBankNext ring r e).2.sites e) =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1 := by
    change ((rbRun ring r [e]).2.sites e) = _
    exact hframe.1
  have htarget :
      ((renewalBankNext ring r e).2.sites
        (ring.rightNeighbor e)) =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2 := by
    change ((rbRun ring r [e]).2.sites
      (ring.rightNeighbor e)) = _
    exact hframe.2
  rw [hpair] at hsource htarget
  exact ⟨congrArg (fun z : RenewalBankSite n => z.controller) hsource,
    congrArg (fun z : RenewalBankSite n => z.worker) htarget⟩

/-- Orphaned reset RR forward service leaves a nonincident
root's physical BANK state and its ghost controller intact,
while the matched pending receipt moves to the next digit. -/
theorem bankWindowClosureOrphanForwardFrame
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (root e : Fin n) (rho : RenewalBankReceipt n)
    (hrootSource : root ≠ e)
    (hrootTarget : root ≠ ring.rightNeighbor e)
    (hfirst : 1 ≤ (r.1 e).pack.val)
    (hinside : (r.1 e).pack.val <
      (compileAdvice (ceilLogTwo n)).b)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val =
      (r.1 e).pack.val + 1)
    (hrr : (r.1 e).tok = .RR)
    (hpending : (r.2.sites e).worker = .pending rho) :
    (renewalBankNext ring r e).1 root = r.1 root ∧
    ((renewalBankNext ring r e).2.sites root) =
      (r.2.sites root) ∧
    ((renewalBankNext ring r e).2.sites e).worker = .empty ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker = .pending rho := by
  have hf := bankWindowExactOffPairFrame ring r e root
    hrootSource hrootTarget
  have hw := bankWindowBirthPendingForwardStep ring hn r e
    rho hfirst hinside hy hrr hpending
  exact ⟨hf.1, hf.2, hw.1, hw.2⟩

/-- At the actual top-turn, the OLD pending RR transfers
backward without consulting its originating root. A separate
nonincident root is framed both physically and in the ghost. -/
theorem bankWindowClosureOrphanTopTurnFrame
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (root e : Fin n) (rho : RenewalBankReceipt n)
    (hne : ring.rightNeighbor e ≠ e)
    (hrootSource : root ≠ e)
    (hrootTarget : root ≠ ring.rightNeighbor e)
    (hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val + 1 =
      (compileAdvice (ceilLogTwo n)).b)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val =
      (compileAdvice (ceilLogTwo n)).b)
    (hsource : (r.1 e).tok = .E)
    (htop : (r.1 (ring.rightNeighbor e)).tok = .RR)
    (hpending : (r.2.sites (ring.rightNeighbor e)).worker =
      .pending rho) :
    (renewalBankNext ring r e).1 root = r.1 root ∧
    ((renewalBankNext ring r e).2.sites root) =
      (r.2.sites root) ∧
    ((renewalBankNext ring r e).2.sites e).worker =
      .pending rho ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker = .empty := by
  have hf := bankWindowExactOffPairFrame ring r e root
    hrootSource hrootTarget
  have hw := bankWindowBirthTopTurnTransfersPendingStep ring r
    e rho hne hb hx hy hsource htop hpending
  exact ⟨hf.1, hf.2, hw.1, hw.2⟩

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankHeadThreshold
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ### (A) Exact transport of the fields read in an off-window root -/

/-- The complete physical PACK prefix is unchanged on a real
off-window edge. Consumers: Scope, PROTO and ORPH transport. -/
theorem bankWindowClosureOffWindowAlignedPrefix
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e)
    (last : Nat)
    (hlast : last ≤ (compileAdvice (ceilLogTwo n)).b) :
    (∀ j : Nat, j ≤ last →
      ((renewalBankNext ring r e).1
        (Counter.site ring root j)).pack.val = j) ↔
    (∀ j : Nat, j ≤ last →
      (r.1 (Counter.site ring root j)).pack.val = j) := by
  constructor
  · intro hp j hj
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
      ((bankWindowExactOffWindowFrame ring r root e houtside
        j (by omega)).1)
    exact hf.symm.trans (hp j hj)
  · intro hp j hj
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
      ((bankWindowExactOffWindowFrame ring r root e houtside
        j (by omega)).1)
    exact hf.trans (hp j hj)

/-- The complete-and-grant-free scope is transported in both
directions. Consumer: all root-local complete-window J fields. -/
theorem bankWindowClosureOffWindowScope
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e) :
    BankWindowScope ring (renewalBankNext ring r e) root ↔
      BankWindowScope ring r root := by
  have hp :
      Counter.Complete ring (renewalBankNext ring r e).1 root ↔
        Counter.Complete ring r.1 root :=
    bankWindowClosureOffWindowAlignedPrefix
      ring r root e houtside
      (compileAdvice (ceilLogTwo n)).b (Nat.le_refl _)
  have hr :
      (renewalBankNext ring r e).1 root = r.1 root := by
    change (renewalBankNext ring r e).1
      (Counter.site ring root 0) =
        r.1 (Counter.site ring root 0)
    exact (bankWindowExactOffWindowFrame ring r root e
      houtside 0 (by omega)).1
  have hg := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.grant) hr
  unfold BankWindowScope
  constructor
  · intro hs
    exact ⟨hp.mp hs.1, hg.symm.trans hs.2⟩
  · intro hs
    exact ⟨hp.mpr hs.1, hg.trans hs.2⟩

/-- All digit bits read by the reset and increment clauses
are preserved outside the window. -/
theorem bankWindowClosureOffWindowZeroPrefix
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e)
    (last : Nat) :
    bankWindowZeroPrefix ring (renewalBankNext ring r e)
      root last ↔
    bankWindowZeroPrefix ring r root last := by
  constructor
  · intro hz j hj
    have hbound : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hjlt := j.isLt
      omega
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      ((bankWindowExactOffWindowFrame ring r root e houtside
        (j.val + 1) hbound).1)
    exact hf.symm.trans (hz j hj)
  · intro hz j hj
    have hbound : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hjlt := j.isLt
      omega
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      ((bankWindowExactOffWindowFrame ring r root e houtside
        (j.val + 1) hbound).1)
    exact hf.trans (hz j hj)

/-- The unique nonempty digit-token location, if any, is
unchanged outside the whole window. -/
theorem bankWindowClosureOffWindowOnlyToken
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e i : Fin n)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e) :
    bankWindowOnlyToken ring (renewalBankNext ring r e)
      root i ↔
    bankWindowOnlyToken ring r root i := by
  constructor
  · intro ho j hne
    have hbound : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hjlt := j.isLt
      omega
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((bankWindowExactOffWindowFrame ring r root e houtside
        (j.val + 1) hbound).1)
    have hpost : ((renewalBankNext ring r e).1
        (Counter.site ring root (j.val + 1))).tok ≠ .E := by
      intro he
      exact hne (hf.symm.trans he)
    exact ho j hpost
  · intro ho j hne
    have hbound : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hjlt := j.isLt
      omega
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((bankWindowExactOffWindowFrame ring r root e houtside
        (j.val + 1) hbound).1)
    have hold : (r.1
        (Counter.site ring root (j.val + 1))).tok ≠ .E := by
      intro he
      exact hne (hf.trans he)
    exact ho j hold

/-- PROTO/ORPH's tainted-site predicate is literally unchanged
at every digit of an untouched window. -/
theorem bankWindowClosureOffWindowTainted
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e)
    (j : Fin (compileAdvice (ceilLogTwo n)).b) :
    BankWindowTainted (renewalBankNext ring r e)
      (Counter.site ring root (j.val + 1)) ↔
    BankWindowTainted r
      (Counter.site ring root (j.val + 1)) := by
  have hbound : j.val + 1 ≤
      (compileAdvice (ceilLogTwo n)).b := by
    have hjlt := j.isLt
    omega
  have hf := (bankWindowExactOffWindowFrame
    ring r root e houtside (j.val + 1) hbound).2
  unfold BankWindowTainted
  rw [hf]

/-- The inherited controller at an untouched root is the same
ghost object, including its original nonempty-atom distinction. -/
theorem bankWindowClosureOffWindowInherited
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e) :
    BankWindowInheritedController (renewalBankNext ring r e) root ↔
      BankWindowInheritedController r root := by
  have hf :
      ((renewalBankNext ring r e).2.sites root) =
        (r.2.sites root) := by
    change ((renewalBankNext ring r e).2.sites
      (Counter.site ring root 0)) =
        (r.2.sites (Counter.site ring root 0))
    exact (bankWindowExactOffWindowFrame ring r root e
      houtside 0 (by omega)).2
  unfold BankWindowInheritedController
  rw [hf]

/-- The first incorrect PACK position is unchanged by a real
off-window edge. Consumer: preservation of the PROTO exclusions. -/
theorem bankWindowClosureOffWindowProto
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e)
    (limit : Nat) :
    BankWindowProtoRun ring (renewalBankNext ring r e)
      root limit ↔
    BankWindowProtoRun ring r root limit := by
  unfold BankWindowProtoRun
  constructor
  · rintro ⟨hlt, hp, hbad⟩
    refine ⟨hlt,
      (bankWindowClosureOffWindowAlignedPrefix
        ring r root e houtside limit (by omega)).mp hp, ?_⟩
    intro hcorrect
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
      ((bankWindowExactOffWindowFrame ring r root e houtside
        (limit + 1) (by omega)).1)
    exact hbad (hf.trans hcorrect)
  · rintro ⟨hlt, hp, hbad⟩
    refine ⟨hlt,
      (bankWindowClosureOffWindowAlignedPrefix
        ring r root e houtside limit (by omega)).mpr hp, ?_⟩
    intro hcorrect
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
      ((bankWindowExactOffWindowFrame ring r root e houtside
        (limit + 1) (by omega)).1)
    exact hbad (hf.symm.trans hcorrect)

/-- A tainted orphan's physical owner test is unchanged outside
the complete read window, including its negated prefix. -/
theorem bankWindowClosureOffWindowOrphan
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e)
    (j : Fin (compileAdvice (ceilLogTwo n)).b) :
    BankWindowOrphanOwner ring (renewalBankNext ring r e) root j ↔
      BankWindowOrphanOwner ring r root j := by
  have hzero := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
    ((bankWindowExactOffWindowFrame ring r root e
      houtside 0 (by omega)).1)
  have hbound : j.val + 1 ≤
      (compileAdvice (ceilLogTwo n)).b := by
    have hjlt := j.isLt
    omega
  have hdigit := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
    ((bankWindowExactOffWindowFrame ring r root e
      houtside (j.val + 1) hbound).1)
  have hprefix := bankWindowClosureOffWindowAlignedPrefix
    ring r root e houtside (j.val + 1) hbound
  change ((renewalBankNext ring r e).1 root).pack.val =
    (r.1 root).pack.val at hzero
  unfold BankWindowOrphanOwner
  rw [hzero, hdigit, hprefix]

/-- Both payload-shape fields of J transfer at each actual
site in an untouched window, without assumptions on the
contents of the ghost payload. -/
theorem bankWindowClosureOffWindowPayloadFields
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (hJ : BankWindowExact ring r)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e) :
    ∀ j : Nat, j ≤ (compileAdvice (ceilLogTwo n)).b →
      (∀ p, p ∈ rbSiteLivePayloads
          ((renewalBankNext ring r e).2.sites
            (Counter.site ring root j)) →
          p.origin = none → p.atoms ≠ [] ∧ p.heads = 0) ∧
      (∀ p o, p ∈ rbSiteLivePayloads
          ((renewalBankNext ring r e).2.sites
            (Counter.site ring root j)) →
          p.origin = some o → p.atoms = []) := by
  intro j hj
  have hf := (bankWindowExactOffWindowFrame
    ring r root e houtside j hj).2
  constructor
  · intro p hp ho
    rw [hf] at hp
    exact hJ.payloadShape (Counter.site ring root j) p hp ho
  · intro p o hp ho
    rw [hf] at hp
    exact hJ.genuinePayloadEmpty (Counter.site ring root j) p o hp ho

/-- The inheritedClean field of J is fully transported for
this root on every off-window edge. -/
theorem bankWindowClosureOffWindowInheritedClean
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (hJ : BankWindowExact ring r)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e)
    (hscope : BankWindowScope ring
      (renewalBankNext ring r e) root)
    (hinherited : BankWindowInheritedController
      (renewalBankNext ring r e) root) :
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted (renewalBankNext ring r e)
        (Counter.site ring root (j.val + 1)) := by
  intro j htainted
  have hs := (bankWindowClosureOffWindowScope
    ring r root e houtside).mp hscope
  have hi := (bankWindowClosureOffWindowInherited
    ring r root e houtside).mp hinherited
  have ht := (bankWindowClosureOffWindowTainted
    ring r root e houtside j).mp htainted
  exact hJ.inheritedClean root hs hi j ht

/-- The genuinely-originated-controller exclusion in PROTO
is transported at an untouched proto-run root. -/
theorem bankWindowClosureOffWindowProtoNoGenuine
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (hJ : BankWindowExact ring r)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e)
    (limit : Nat)
    (hproto : BankWindowProtoRun ring
      (renewalBankNext ring r e) root limit) :
    ∀ p o,
      ((renewalBankNext ring r e).2.sites root).controller =
        .active p → p.origin = some o → False := by
  have hpre := (bankWindowClosureOffWindowProto
    ring r root e houtside limit).mp hproto
  have hno := (hJ.proto root limit hpre).1
  have hf :
      ((renewalBankNext ring r e).2.sites root) =
        (r.2.sites root) := by
    change ((renewalBankNext ring r e).2.sites
      (Counter.site ring root 0)) =
        (r.2.sites (Counter.site ring root 0))
    exact (bankWindowExactOffWindowFrame ring r root e
      houtside 0 (by omega)).2
  intro p o hc ho
  rw [hf] at hc
  exact hno p o hc ho

/-- The origin's full binary value is identical outside the
window in which that origin's bits are read. Consumer: exact
ARMED and CSTART head equalities, not just capped bounds. -/
theorem bankWindowClosureOffWindowBinaryValue
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring o.root e) :
    bankOriginBinaryValue ring (renewalBankNext ring r e).1 o =
      bankOriginBinaryValue ring r.1 o := by
  have hbits :
      (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
        if ((renewalBankNext ring r e).1
          (Counter.site ring o.root (j.val + 1))).bit
        then 2 ^ j.val else 0) =
      (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
        if (r.1 (Counter.site ring o.root (j.val + 1))).bit
        then 2 ^ j.val else 0) := by
    funext j
    have hjlt := j.isLt
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      ((bankWindowExactOffWindowFrame ring r o.root e
        houtside (j.val + 1) (by omega)).1)
    rw [hf]
  exact congrArg
    (fun f : Fin (compileAdvice (ceilLogTwo n)).b → Nat =>
      (List.ofFn f).sum) hbits

/-- The entire uncapped ARMED/CSTART clause is transported
whenever the step is outside both the controller root's
window and the origin's own bit window. -/
theorem bankWindowClosureOffWindowArmedExact
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (hJ : BankWindowExact ring r)
    (hrootOutside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e)
    (horiginOutside : Counter.OutsideSites
      (q := ceilLogTwo n) ring o.root e)
    (hscope : BankWindowScope ring
      (renewalBankNext ring r e) root)
    (hphase :
      ((renewalBankNext ring r e).1 root).mode = .ARMED ∨
      ((renewalBankNext ring r e).1 root).mode = .CSTART)
    (hcontroller :
      ((renewalBankNext ring r e).2.sites root).controller =
        .active p)
    (horigin : p.origin = some o) :
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((renewalBankNext ring r e).1
        (Counter.site ring root (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring
      (renewalBankNext ring r e).1 o ∧
    (((renewalBankNext ring r e).1 root).mode = .ARMED →
      bankOriginBinaryValue ring (renewalBankNext ring r e).1 o <
        (compileAdvice (ceilLogTwo n)).K) ∧
    (((renewalBankNext ring r e).1 root).mode = .CSTART →
      bankOriginBinaryValue ring (renewalBankNext ring r e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K) := by
  have hframe := bankWindowExactOffWindowFrame
    ring r root e hrootOutside
  have hphysical :
      (renewalBankNext ring r e).1 root = r.1 root := by
    change (renewalBankNext ring r e).1
      (Counter.site ring root 0) =
        r.1 (Counter.site ring root 0)
    exact (hframe 0 (by omega)).1
  have hghost :
      ((renewalBankNext ring r e).2.sites root) =
        (r.2.sites root) := by
    change ((renewalBankNext ring r e).2.sites
      (Counter.site ring root 0)) =
        (r.2.sites (Counter.site ring root 0))
    exact (hframe 0 (by omega)).2
  have hmode := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hphysical
  have hphaseOld :
      (r.1 root).mode = .ARMED ∨
      (r.1 root).mode = .CSTART := by
    rcases hphase with ha | hc
    · exact Or.inl (hmode.symm.trans ha)
    · exact Or.inr (hmode.symm.trans hc)
  have hcOld :
      (r.2.sites root).controller = .active p := by
    rw [hghost] at hcontroller
    exact hcontroller
  obtain ⟨hclean, hheads, harmed, hcstart⟩ :=
    hJ.armedExact root o p
      ((bankWindowClosureOffWindowScope
        ring r root e hrootOutside).mp hscope)
      hphaseOld hcOld horigin
  have hvalue := bankWindowClosureOffWindowBinaryValue
    ring r e o horiginOutside
  refine ⟨?_, hheads.trans hvalue.symm, ?_, ?_⟩
  · intro j
    have hjlt := j.isLt
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((hframe (j.val + 1) (by omega)).1)
    exact hf.trans (hclean j)
  · intro hm
    rw [hvalue]
    exact harmed (hmode.symm.trans hm)
  · intro hm
    rw [hvalue]
    exact hcstart (hmode.symm.trans hm)

/-! ### (B) Every internal edge preserves all PACK roles;
    representative literal ghost rows of the same edges. -/

/-- The entire complete PACK window survives *every* edge
from digit j to digit j+1, including launch, return, birth,
ARMED, CSTART, IWAIT and CWAIT physical rows. -/
theorem bankWindowClosureCompleteInternalPack
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (k : Nat) (hk : k < (compileAdvice (ceilLogTwo n)).b) :
    Counter.Complete ring
      (renewalBankNext ring r (Counter.site ring root k)).1
      root := by
  intro j hj
  by_cases hsource :
      Counter.site ring root j = Counter.site ring root k
  · have hv := congrArg
      (fun i : Fin n => (r.1 i).pack.val) hsource
    rw [hcomplete j hj, hcomplete k (by omega)] at hv
    have hsame : j = k := hv
    subst j
    have hpack :=
      (rbBankReferencePairPack ring
        (by omega : 2 ≤ n) r (Counter.site ring root k)).1
    change
      ((renewalBankNext ring r
        (Counter.site ring root k)).1
        (Counter.site ring root k)).pack.val =
      (r.1 (Counter.site ring root k)).pack.val at hpack
    exact hpack.trans (hcomplete k (by omega))
  · by_cases htarget :
      Counter.site ring root j =
        ring.rightNeighbor (Counter.site ring root k)
    · have hv := congrArg
        (fun i : Fin n => (r.1 i).pack.val) htarget
      change (r.1 (Counter.site ring root j)).pack.val =
        (r.1 (Counter.site ring root (k + 1))).pack.val at hv
      rw [hcomplete j hj, hcomplete (k + 1) (by omega)] at hv
      have hnext : j = k + 1 := hv
      subst j
      exact bankWindowExactCompleteDigitPackFixed
        ring r root hcomplete k hk
    · have hf := (bankWindowExactOffPairFrame ring r
        (Counter.site ring root k)
        (Counter.site ring root j) hsource htarget).1
      have hpack := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val) hf
      exact hpack.trans (hcomplete j hj)

/-- RESET launch inside a complete window keeps it complete,
with a waiting empty root and the exact pending receipt at d1. -/
theorem bankWindowClosureCompleteResetLaunch
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (hgrant : (r.1 root).grant = false)
    (hreset : (r.1 root).mode = .RESET) :
    Counter.Complete ring (renewalBankNext ring r root).1 root ∧
    ((renewalBankNext ring r root).2.sites root).controller =
      .waiting [] ∧
    ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker =
        .pending { service := r.2.service, root := root } := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx : (r.1 root).pack.val = 0 := by
    change (r.1 (Counter.site ring root 0)).pack.val = 0
    exact hcomplete 0 (by omega)
  have hy : (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
    change (r.1 (Counter.site ring root 1)).pack.val = 1
    exact hcomplete 1 (by omega)
  have hc := bankWindowClosureCompleteInternalPack
    ring hn r root hcomplete 0 hb
  change Counter.Complete ring
    (renewalBankNext ring r root).1 root at hc
  have hg := bankWindowClosureResetLaunchGhost
    ring (by omega : 2 ≤ n) r root hx hy hgrant hreset
  exact ⟨hc, hg.1, hg.2⟩

/-- The real pending-RR forward row transfers the receipt
without losing completeness of the current full window. -/
theorem bankWindowClosureCompletePendingForward
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (j : Nat) (hjlow : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (rho : RenewalBankReceipt n)
    (hrr : (r.1 (Counter.site ring root j)).tok = .RR)
    (hpending :
      (r.2.sites (Counter.site ring root j)).worker =
        .pending rho) :
    Counter.Complete ring
      (renewalBankNext ring r
        (Counter.site ring root j)).1 root ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).2.sites
      (Counter.site ring root j)).worker = .empty ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).2.sites
      (ring.rightNeighbor (Counter.site ring root j))).worker =
        .pending rho := by
  have hx := hcomplete j (by omega)
  have hy :
      (r.1 (ring.rightNeighbor
        (Counter.site ring root j))).pack.val =
      (r.1 (Counter.site ring root j)).pack.val + 1 := by
    change
      (r.1 (Counter.site ring root (j + 1))).pack.val =
      (r.1 (Counter.site ring root j)).pack.val + 1
    rw [hcomplete (j + 1) (by omega), hx]
  have hfirst :
      1 ≤ (r.1 (Counter.site ring root j)).pack.val := by
    rw [hx]
    exact hjlow
  have hinside :
      (r.1 (Counter.site ring root j)).pack.val <
        (compileAdvice (ceilLogTwo n)).b := by
    rw [hx]
    exact hjtop
  have hworker := bankWindowBirthPendingForwardStep
    ring (by omega : 2 ≤ n) r
    (Counter.site ring root j) rho
    hfirst hinside hy hrr hpending
  exact ⟨bankWindowClosureCompleteInternalPack
    ring hn r root hcomplete j hjtop,
    hworker.1, hworker.2⟩

/-- The real top turn preserves completeness and moves the
pending receipt backward without consulting its old root. -/
theorem bankWindowClosureCompleteTopTurn
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (j : Nat) (hjlow : 1 ≤ j)
    (hjtop : j + 1 = (compileAdvice (ceilLogTwo n)).b)
    (rho : RenewalBankReceipt n)
    (hempty : (r.1 (Counter.site ring root j)).tok = .E)
    (hrr : (r.1 (ring.rightNeighbor
      (Counter.site ring root j))).tok = .RR)
    (hpending : (r.2.sites (ring.rightNeighbor
      (Counter.site ring root j))).worker = .pending rho) :
    Counter.Complete ring
      (renewalBankNext ring r
        (Counter.site ring root j)).1 root ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).2.sites
      (Counter.site ring root j)).worker = .pending rho ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).2.sites
      (ring.rightNeighbor (Counter.site ring root j))).worker =
        .empty := by
  have hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b := by omega
  have hj : j < (compileAdvice (ceilLogTwo n)).b := by omega
  have hx :
      (r.1 (Counter.site ring root j)).pack.val + 1 =
        (compileAdvice (ceilLogTwo n)).b := by
    rw [hcomplete j (by omega)]
    exact hjtop
  have hy :
      (r.1 (ring.rightNeighbor
        (Counter.site ring root j))).pack.val =
          (compileAdvice (ceilLogTwo n)).b := by
    change (r.1 (Counter.site ring root (j + 1))).pack.val =
      (compileAdvice (ceilLogTwo n)).b
    rw [hcomplete (j + 1) (by omega)]
    exact hjtop
  have hne : ring.rightNeighbor (Counter.site ring root j) ≠
      Counter.site ring root j := by
    intro he
    have hv := congrArg
      (fun i : Fin n => (r.1 i).pack.val) he
    change (r.1 (Counter.site ring root (j + 1))).pack.val =
      (r.1 (Counter.site ring root j)).pack.val at hv
    rw [hcomplete (j + 1) (by omega),
      hcomplete j (by omega)] at hv
    omega
  have hw := bankWindowBirthTopTurnTransfersPendingStep
    ring r (Counter.site ring root j) rho
    hne hb hx hy hempty hrr hpending
  exact ⟨bankWindowClosureCompleteInternalPack
    ring hn r root hcomplete j hj, hw.1, hw.2⟩

/-- A real OLD RL birth from J gives a complete POST window,
an ARMED source, and its genuine zero-headed controller.
Consumer: the bankWindowExactStep birth branch. -/
theorem bankWindowClosureBirthCompletePost
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring r)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    Counter.Complete ring (renewalBankNext ring r e).1 e ∧
    ((renewalBankNext ring r e).1 e).mode = .ARMED ∧
    ∃ p : RenewalBankPayload n,
      ((renewalBankNext ring r e).2.sites e).controller =
        .active p ∧ p.origin = some o ∧ p.heads = 0 := by
  have hc := bankWindowClosureBirthComplete ring r e o hJ hbirth
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpost := bankWindowClosureCompleteInternalPack
    ring hn r e hc 0 hb
  change Counter.Complete ring
    (renewalBankNext ring r e).1 e at hpost
  exact ⟨hpost,
    bankWindowClosureBirthPostArmed
      ring (by omega) hbank r e o hbirth,
    bankWindowClosureBirthCreatesGenuineRoot
      ring (by omega : 2 ≤ n) r e o hbirth⟩

/-! ### (C) PACK-changing responder sanitation -/

/-- Any PACK-changing real responder is RESET, bit-zero,
token-empty, ghost-worker-empty and ghost-controller-empty.
The last two facts discharge the local PROTO/ORPH taint tests. -/
theorem bankWindowClosureChangedDigitClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val) :
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).mode = .RESET ∧
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).bit = false ∧
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).tok = .E ∧
    ¬ BankWindowTainted (renewalBankNext ring r e)
      (ring.rightNeighbor e) ∧
    ¬ BankWindowInheritedController (renewalBankNext ring r e)
      (ring.rightNeighbor e) := by
  obtain ⟨hm, hb, ht, hw, hc⟩ :=
    bankWindowBirthChangedResponderStep ring
      (by omega : 2 ≤ n) hbank r e hchanged
  refine ⟨hm, hb, ht, ?_, ?_⟩
  · intro htaint
    rcases htaint with ⟨rho, hp⟩ | ⟨p, o, hp, ho⟩
    · rw [hw] at hp
      cases hp
    · rw [hw] at hp
      cases hp
  · intro hinherited
    rcases hinherited with ⟨atoms, hp, _⟩ | ⟨p, hp, _⟩
    · rw [hc] at hp
      cases hp
    · rw [hc] at hp
      cases hp

/-- When a responder formerly carrying PACK zero is assigned
a nonzero role, the old root is reset and has neither a
tainted worker nor an inherited controller afterward. -/
theorem bankWindowClosureBrokenRootSanitized
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hroot : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hnew :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val ≠ 0) :
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).mode = .RESET ∧
    ¬ BankWindowTainted (renewalBankNext ring r e)
      (ring.rightNeighbor e) ∧
    ¬ BankWindowInheritedController (renewalBankNext ring r e)
      (ring.rightNeighbor e) := by
  have hp := bankWindowExactResponderPack ring r e
    (clockNeighborDifferent ring
      (by omega : 2 ≤ n) e)
  have hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val := by
    intro he
    apply hnew
    exact (hp.trans he).trans hroot
  have hs := bankWindowClosureChangedDigitClean
    ring hn hbank r e hchanged
  exact ⟨hs.1, hs.2.2.2.1, hs.2.2.2.2⟩

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankHeadThreshold
open Classical

/-! ## Incident BANK-window edges: RESET, pending traversal, repair -/

/-- The real masked physical RESET launch is RWAIT/RR with a
zero first-digit bit.  Consumer: the resetWait launch row of J.
This is the selected physical pair, not an abstract bankPair. -/
theorem bankWindowClosureResetLaunchPhysicalPair
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root : Fin n)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .RESET) :
    ((renewalBankNext ring r root).1 root).mode = .RWAIT ∧
    ((renewalBankNext ring r root).1
      (ring.rightNeighbor root)).bit = false ∧
    ((renewalBankNext ring r root).1
      (ring.rightNeighbor root)).tok = .RR := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpost :
      packNext (r.1 root).pack.val
        (r.1 (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hraw :
      (Counter.resetBankOld (r.1 root)
        (r.1 (ring.rightNeighbor root))).1.mode = .RWAIT ∧
      (Counter.resetBankOld (r.1 root)
        (r.1 (ring.rightNeighbor root))).2.bit = false ∧
      (Counter.resetBankOld (r.1 root)
        (r.1 (ring.rightNeighbor root))).2.tok = .RR := by
    have hpack01 : packNext 0 1 (compileAdvice (ceilLogTwo n)).b = 1 := by
      simp [packNext, hb]
    have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, hb0, hpack01, isRetTok,
      Id.run_pure, Id.run_bind]
  have hf := rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r root
  have hmask := renewalMaskedPairFrames
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 root)
    (r.1 root) (r.1 (ring.rightNeighbor root))
  have htrip := Counter.resetTransitionBankTrip
    (compileAdvice (ceilLogTwo n))
    (r.1 root) (r.1 (ring.rightNeighbor root)) hbank
  have hsource := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hf.1
  have hsourceMask := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hmask.1
  have hsourceTrip := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip.1
  change ((renewalBankNext ring r root).1 root).mode =
    (renewalMaskedPair
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).1.mode
    at hsource
  change (renewalMaskedPair
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).1.mode =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 root) (r.1 (ring.rightNeighbor root))).1.mode
    at hsourceMask
  change (transition (compileAdvice (ceilLogTwo n))
      (r.1 root) (r.1 (ring.rightNeighbor root))).1.mode =
    (Counter.resetBankOld
      (r.1 root) (r.1 (ring.rightNeighbor root))).1.mode
    at hsourceTrip
  have hdestBit := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
    hf.2.1
  have hdestBitMask := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
    hmask.2
  have hdestBitTrip := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.2
  change ((renewalBankNext ring r root).1
      (ring.rightNeighbor root)).bit =
    (renewalMaskedPair
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.bit
    at hdestBit
  change (renewalMaskedPair
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.bit =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.bit
    at hdestBitMask
  change (transition (compileAdvice (ceilLogTwo n))
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.bit =
    (Counter.resetBankOld
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.bit
    at hdestBitTrip
  have hdestTok := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
    hf.2.1
  have hdestTokMask := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
    hmask.2
  have hdestTokTrip := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.2
  change ((renewalBankNext ring r root).1
      (ring.rightNeighbor root)).tok =
    (renewalMaskedPair
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.tok
    at hdestTok
  change (renewalMaskedPair
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.tok =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.tok
    at hdestTokMask
  change (transition (compileAdvice (ceilLogTwo n))
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.tok =
    (Counter.resetBankOld
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.tok
    at hdestTokTrip
  exact ⟨hsource.trans
      (hsourceMask.trans (hsourceTrip.trans hraw.1)),
    hdestBit.trans
      (hdestBitMask.trans (hdestBitTrip.trans hraw.2.1)),
    hdestTok.trans
      (hdestTokMask.trans (hdestTokTrip.trans hraw.2.2))⟩

/-- A complete OLD RESET window starts a literal RWAIT front
at its first digit, with the new pending receipt, RR, bit zero,
and the full resetWait witness (including its RL implication).
Consumer: J.resetWait on the RESET-launch edge. -/
theorem bankWindowClosureResetLaunchWaitWitness
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .RESET) :
    Counter.Complete ring (renewalBankNext ring r root).1 root ∧
    ((renewalBankNext ring r root).1 root).mode = .RWAIT ∧
    ((renewalBankNext ring r root).2.sites root).controller =
      .waiting [] ∧
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n),
      ((renewalBankNext ring r root).2.sites
        (Counter.site ring root (j.val + 1))).worker =
        .pending rho ∧
      (((renewalBankNext ring r root).1
          (Counter.site ring root (j.val + 1))).tok = .RR ∨
       ((renewalBankNext ring r root).1
          (Counter.site ring root (j.val + 1))).tok = .RL) ∧
      bankWindowZeroPrefix ring (renewalBankNext ring r root)
        root (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        k.val < j.val →
        ((renewalBankNext ring r root).1
          (Counter.site ring root (k.val + 1))).tok = .E) ∧
      (((renewalBankNext ring r root).1
          (Counter.site ring root (j.val + 1))).tok = .RL →
        bankWindowOnlyToken ring (renewalBankNext ring r root)
          root (Counter.site ring root (j.val + 1)) ∧
        bankWindowZeroPrefix ring (renewalBankNext ring r root)
          root (compileAdvice (ceilLogTwo n)).b) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx : (r.1 root).pack.val = 0 := by
    change (r.1 (Counter.site ring root 0)).pack.val = 0
    exact hcomplete 0 (by omega)
  have hy : (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
    change (r.1 (Counter.site ring root 1)).pack.val = 1
    exact hcomplete 1 (by omega)
  obtain ⟨hc, hctl, hworker⟩ :=
    bankWindowClosureCompleteResetLaunch
      ring hn r root hcomplete hg hm
  obtain ⟨hmode, hbit, htok⟩ :=
    bankWindowClosureResetLaunchPhysicalPair
      ring hn hbank r root hx hy hg hm
  refine ⟨hc, hmode, hctl,
    (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b),
    { service := r.2.service, root := root },
    ?_, ?_, ?_, ?_, ?_⟩
  · change ((renewalBankNext ring r root).2.sites
        (ring.rightNeighbor root)).worker =
        .pending { service := r.2.service, root := root }
    exact hworker
  · apply Or.inl
    change ((renewalBankNext ring r root).1
      (ring.rightNeighbor root)).tok = .RR
    exact htok
  · intro k hk
    have hkzero : k.val = 0 := by
      have h' := hk
      try simp only [Fin.le_def, Fin.lt_def, Fin.val_mk] at h'
      omega
    have hsite : Counter.site ring root (k.val + 1) =
        ring.rightNeighbor root := by
      rw [hkzero]
      rfl
    rw [hsite]
    exact hbit
  · intro k hk
    have hbad : k.val < 0 := hk
    have hkzero : 0 ≤ k.val := Nat.zero_le _
    omega
  · intro hrl
    change ((renewalBankNext ring r root).1
      (ring.rightNeighbor root)).tok = .RL at hrl
    rw [htok] at hrl
    cases hrl

/-- An untouched root of an internal non-root digit service
keeps its RWAIT mode and empty waiting controller.
Consumer: resetWait forward and top-turn case splits. -/
theorem bankWindowClosureInteriorRootWaitFrame
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (j : Nat) (hjlow : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hm : (r.1 root).mode = .RWAIT)
    (hctl : (r.2.sites root).controller = .waiting []) :
    ((renewalBankNext ring r
      (Counter.site ring root j)).1 root).mode = .RWAIT ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).2.sites root).controller =
        .waiting [] := by
  have hsource : root ≠ Counter.site ring root j := by
    intro he
    have hv := congrArg
      (fun i : Fin n => (r.1 i).pack.val) he
    change (r.1 (Counter.site ring root 0)).pack.val =
      (r.1 (Counter.site ring root j)).pack.val at hv
    rw [hcomplete 0 (by omega), hcomplete j (by omega)] at hv
    omega
  have htarget :
      root ≠ ring.rightNeighbor (Counter.site ring root j) := by
    intro he
    have hv := congrArg
      (fun i : Fin n => (r.1 i).pack.val) he
    change (r.1 (Counter.site ring root 0)).pack.val =
      (r.1 (Counter.site ring root (j + 1))).pack.val at hv
    rw [hcomplete 0 (by omega),
      hcomplete (j + 1) (by omega)] at hv
    omega
  have hf := bankWindowExactOffPairFrame ring r
    (Counter.site ring root j) root hsource htarget
  have hmode := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode) hf.1
  have hghost := congrArg
    (fun s : RenewalBankSite n => s.controller) hf.2
  exact ⟨hmode.trans hm, hghost.trans hctl⟩

/-- A real pending-RR forward step retains the old RWAIT root
and its single pending carrier moves one digit outward.
Consumer: resetWait forward case before token/bit transport. -/
theorem bankWindowClosurePendingForwardWaitCarrier
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (j : Nat) (hjlow : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (rho : RenewalBankReceipt n)
    (hm : (r.1 root).mode = .RWAIT)
    (hctl : (r.2.sites root).controller = .waiting [])
    (hrr : (r.1 (Counter.site ring root j)).tok = .RR)
    (hpending :
      (r.2.sites (Counter.site ring root j)).worker =
        .pending rho) :
    Counter.Complete ring
      (renewalBankNext ring r
        (Counter.site ring root j)).1 root ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).1 root).mode = .RWAIT ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).2.sites root).controller =
        .waiting [] ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).2.sites
      (ring.rightNeighbor (Counter.site ring root j))).worker =
        .pending rho := by
  have hmove := bankWindowClosureCompletePendingForward
    ring hn r root hcomplete j hjlow hjtop rho hrr hpending
  have hframe := bankWindowClosureInteriorRootWaitFrame
    ring hn r root hcomplete j hjlow hjtop hm hctl
  exact ⟨hmove.1, hframe.1, hframe.2, hmove.2.2⟩

/-- At the actual top turn the RWAIT root is framed and
the same pending receipt moves back one digit.
Consumer: the top-turn resetWait case. -/
theorem bankWindowClosureTopTurnWaitCarrier
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (j : Nat) (hjlow : 1 ≤ j)
    (hjtop : j + 1 = (compileAdvice (ceilLogTwo n)).b)
    (rho : RenewalBankReceipt n)
    (hm : (r.1 root).mode = .RWAIT)
    (hctl : (r.2.sites root).controller = .waiting [])
    (hempty : (r.1 (Counter.site ring root j)).tok = .E)
    (hrr : (r.1 (ring.rightNeighbor
      (Counter.site ring root j))).tok = .RR)
    (hpending :
      (r.2.sites (ring.rightNeighbor
        (Counter.site ring root j))).worker =
          .pending rho) :
    Counter.Complete ring
      (renewalBankNext ring r
        (Counter.site ring root j)).1 root ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).1 root).mode = .RWAIT ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).2.sites root).controller =
        .waiting [] ∧
    ((renewalBankNext ring r
      (Counter.site ring root j)).2.sites
        (Counter.site ring root j)).worker =
          .pending rho := by
  have ht := bankWindowClosureCompleteTopTurn
    ring hn r root hcomplete j hjlow hjtop rho
    hempty hrr hpending
  have hf := bankWindowClosureInteriorRootWaitFrame
    ring hn r root hcomplete j hjlow (by omega) hm hctl
  exact ⟨ht.1, hf.1, hf.2, ht.2.1⟩

/-- A complete OLD window cannot acquire PROTO or ORPH for
that same root on an internal real edge (all BANK modes).
Consumer: proto/orphan incident-window branches of J. -/
theorem bankWindowClosureInternalNoProtoOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (j : Nat) (hj : j < (compileAdvice (ceilLogTwo n)).b) :
    (∀ limit : Nat,
      ¬ BankWindowProtoRun ring
        (renewalBankNext ring r
          (Counter.site ring root j)) root limit) ∧
    (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowOrphanOwner ring
        (renewalBankNext ring r
          (Counter.site ring root j)) root k) := by
  have hc := bankWindowClosureCompleteInternalPack
    ring hn r root hcomplete j hj
  constructor
  · intro limit hp
    exact hp.2.2 (hc (limit + 1) (by have := hp.1; omega))
  · intro k hk
    exact hk.2.2 (fun t ht =>
      hc t (by have hl := k.isLt; omega))

/-- A genuine pending-RL birth cannot create a proto-run or
an orphan at its own completed window.
Consumer: post-birth PROTO/ORPH fields. -/
theorem bankWindowClosureBirthNoProtoOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root : Fin n)
    (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring r)
    (hbirth : renewalBankBirth ring r.1 r.2 root = some o) :
    (∀ limit : Nat,
      ¬ BankWindowProtoRun ring
        (renewalBankNext ring r root) root limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowOrphanOwner ring
        (renewalBankNext ring r root) root j) := by
  have hc :=
    (bankWindowClosureBirthCompletePost
      ring hn hbank r root o hJ hbirth).1
  constructor
  · intro limit hp
    exact hp.2.2 (hc (limit + 1) (by have := hp.1; omega))
  · intro j hj
    exact hj.2.2 (fun k hk =>
      hc k (by have hl := j.isLt; omega))

/-- A repaired former PACK-zero responder is now RESET and
cannot be the root of any proto-run or orphan-owner claim.
Consumer: the broken-root PROTO/ORPH branch of J. -/
theorem bankWindowClosureBrokenRootNoProtoOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hzero : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hnew : ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val ≠ 0) :
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).mode = .RESET ∧
    (∀ limit : Nat, ¬ BankWindowProtoRun ring
      (renewalBankNext ring r e)
      (ring.rightNeighbor e) limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowOrphanOwner ring
        (renewalBankNext ring r e)
        (ring.rightNeighbor e) j) := by
  have hs := bankWindowClosureBrokenRootSanitized
    ring hn hbank r e hzero hnew
  refine ⟨hs.1, ?_, ?_⟩
  · intro limit hp
    have hpack := hp.2.1 0 (by omega)
    change ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 0 at hpack
    exact hnew hpack
  · intro j hj
    exact hnew hj.1

/-- The responder repaired into digit j+1 is an empty,
bit-zero, token-empty non-tainted digit even if the old worker
carried a pending RR or a completed origin.
Consumer: local PROTO/ORPH repair sanitation. -/
theorem bankWindowClosureRepairDigitNoTaint
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hbefore :
      (r.1 (ring.rightNeighbor e)).pack.val ≠ j.val + 1)
    (hafter :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val = j.val + 1) :
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).bit = false ∧
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).tok = .E ∧
    ¬ BankWindowTainted (renewalBankNext ring r e)
      (ring.rightNeighbor e) := by
  obtain ⟨hb, ht, hw, _⟩ :=
    bankWindowBirthRepairedDigitClear
      ring (by omega : 2 ≤ n) hbank r e j hbefore hafter
  refine ⟨hb, ht, ?_⟩
  intro htainted
  rcases htainted with ⟨rho, hp⟩ | ⟨p, o, hp, ho⟩
  · rw [hw] at hp
    cases hp
  · rw [hw] at hp
    cases hp

/-! ## Genuine ARMED, IWAIT and CSTART incident rows -/

/-- When an OLD genuine ARMED head sees a set first bit, the
actual ghost issues a new origin-preserving worker and enters
empty waiting control. The issued worker's head number equals
the OLD exact binary value plus one.
Consumer: the IWAIT issue branch of J.incrementExact. -/
theorem bankWindowClosureArmedIssueGenuine
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hscope : BankWindowScope ring r root)
    (hm : (r.1 root).mode = .ARMED)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive : (r.2.sites root).controller = .active p)
    (ho : p.origin = some o)
    (hbit : (r.1 (ring.rightNeighbor root)).bit = true) :
    Counter.Complete ring (renewalBankNext ring r root).1 root ∧
    ((renewalBankNext ring r root).2.sites root).controller =
      .waiting [] ∧
    ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker =
        .payload (renewalBankHead p) ∧
    (renewalBankHead p).origin = some o ∧
    (renewalBankHead p).heads =
      bankOriginBinaryValue ring r.1 o + 1 := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx : (r.1 root).pack.val = 0 := by
    change (r.1 (Counter.site ring root 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy : (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
    change (r.1 (Counter.site ring root 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  obtain ⟨hclean, hheads, _, _⟩ :=
    hJ.armedExact root o p hscope (Or.inl hm) hactive ho
  have ht : (r.1 (ring.rightNeighbor root)).tok = .E := by
    have hfirst := hclean
      (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
    change (r.1 (ring.rightNeighbor root)).tok = .E at hfirst
    exact hfirst
  have hrow := rbArmedWorkMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2 root
    (ring.rightNeighbor root)
    (r.1 root) (r.1 (ring.rightNeighbor root))
    hb hx hy hscope.2 hm ht hbit
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r root).2.2
  have hctl := congrArg
    (fun s : RenewalBankSite n => s.controller) hf.1
  have hworker := congrArg
    (fun s : RenewalBankSite n => s.worker) hf.2
  rw [hrow] at hctl hworker
  change ((renewalBankNext ring r root).2.sites root).controller =
    .waiting [] at hctl
  change ((renewalBankNext ring r root).2.sites
    (ring.rightNeighbor root)).worker =
      .payload (renewalBankHead
        (renewalBankActivePayload (r.2.sites root).controller root))
    at hworker
  rw [hactive] at hworker
  change ((renewalBankNext ring r root).2.sites
    (ring.rightNeighbor root)).worker =
      .payload (renewalBankHead p) at hworker
  have hnew := rbHeadIncrementsOrigin p o ho
  rw [hheads] at hnew
  exact ⟨bankWindowClosureCompleteInternalPack
      ring hn r root hscope.1 0 hb,
    hctl, hworker, hnew.1, hnew.2⟩

/-- When the first bit is zero, a genuine ARMED head stays in
the real root controller and increments its uncapped count.
Consumer: the CSTART/ARMED exact-head step. -/
theorem bankWindowClosureArmedSetGenuine
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hscope : BankWindowScope ring r root)
    (hm : (r.1 root).mode = .ARMED)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive : (r.2.sites root).controller = .active p)
    (ho : p.origin = some o)
    (hbit : (r.1 (ring.rightNeighbor root)).bit = false) :
    Counter.Complete ring (renewalBankNext ring r root).1 root ∧
    ((renewalBankNext ring r root).2.sites root).controller =
      .active (renewalBankHead p) ∧
    (renewalBankHead p).origin = some o ∧
    (renewalBankHead p).heads =
      bankOriginBinaryValue ring r.1 o + 1 := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx : (r.1 root).pack.val = 0 := by
    change (r.1 (Counter.site ring root 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy : (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
    change (r.1 (Counter.site ring root 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  obtain ⟨hclean, hheads, _, _⟩ :=
    hJ.armedExact root o p hscope (Or.inl hm) hactive ho
  have ht : (r.1 (ring.rightNeighbor root)).tok = .E := by
    have hfirst := hclean
      (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
    change (r.1 (ring.rightNeighbor root)).tok = .E at hfirst
    exact hfirst
  have hrow := rbArmedIdleMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2 root
    (ring.rightNeighbor root)
    (r.1 root) (r.1 (ring.rightNeighbor root))
    hb hx hy hscope.2 hm ht hbit
  have hframe := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r root).2.2.1
  have hctl := congrArg
    (fun s : RenewalBankSite n => s.controller) hframe
  rw [hrow] at hctl
  change ((renewalBankNext ring r root).2.sites root).controller =
    .active (renewalBankHead
      (renewalBankActivePayload (r.2.sites root).controller root))
    at hctl
  rw [hactive] at hctl
  change ((renewalBankNext ring r root).2.sites root).controller =
    .active (renewalBankHead p) at hctl
  have hnew := rbHeadIncrementsOrigin p o ho
  rw [hheads] at hnew
  exact ⟨bankWindowClosureCompleteInternalPack
      ring hn r root hscope.1 0 hb,
    hctl, hnew.1, hnew.2⟩

/-- Every matching AL/IWAIT or CL0/CWAIT return consumes the
first-digit worker, places its same origin and head count into
the root controller, and preserves the complete window.
Consumer: the exact IWAIT/CWAIT return branches. -/
theorem bankWindowClosureMatchedReturnGenuine
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (hg : (r.1 root).grant = false)
    (hmatch :
      ((r.1 root).mode = .IWAIT ∧
        (r.1 (ring.rightNeighbor root)).tok = .AL) ∨
      ((r.1 root).mode = .CWAIT ∧
        (r.1 (ring.rightNeighbor root)).tok = .CL0))
    (hwait : (r.2.sites root).controller = .waiting [])
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : (r.2.sites (ring.rightNeighbor root)).worker =
      .payload p)
    (ho : p.origin = some o) :
    Counter.Complete ring (renewalBankNext ring r root).1 root ∧
    ∃ q : RenewalBankPayload n,
      ((renewalBankNext ring r root).2.sites root).controller =
        .active q ∧
      ((renewalBankNext ring r root).2.sites
        (ring.rightNeighbor root)).worker = .empty ∧
      q.origin = some o ∧ q.heads = p.heads ∧
      q.atoms = p.atoms := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx : (r.1 root).pack.val = 0 := by
    change (r.1 (Counter.site ring root 0)).pack.val = 0
    exact hcomplete 0 (by omega)
  have hy : (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
    change (r.1 (Counter.site ring root 1)).pack.val = 1
    exact hcomplete 1 (by omega)
  have hpair := rbMatchedReturnMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2 root
    (ring.rightNeighbor root)
    (r.1 root) (r.1 (ring.rightNeighbor root))
    hb hx hy hg hmatch
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r root).2.2
  have hctl := congrArg
    (fun s : RenewalBankSite n => s.controller) hf.1
  have hclear := congrArg
    (fun s : RenewalBankSite n => s.worker) hf.2
  rw [hpair] at hctl hclear
  change ((renewalBankNext ring r root).2.sites root).controller =
    .active (renewalBankReturned
      (r.2.sites root).controller
      (r.2.sites (ring.rightNeighbor root)).worker
      (ring.rightNeighbor root)) at hctl
  rw [hwait, hw] at hctl
  change ((renewalBankNext ring r root).2.sites
    (ring.rightNeighbor root)).worker = .empty at hclear
  have hr := rbReturnRetainsOriginHeads
    p (.waiting []) (ring.rightNeighbor root)
  refine ⟨bankWindowClosureCompleteInternalPack
      ring hn r root hcomplete 0 hb,
    renewalBankReturned (.waiting []) (.payload p)
      (ring.rightNeighbor root),
    hctl, hclear, hr.1.trans ho, hr.2.1, ?_⟩
  simpa [renewalBankWaitingAtoms] using hr.2.2

/-- In the genuine AL/IWAIT return, the reactivated controller
has no inherited atoms and retains the OLD exact binary value.
Consumer: the AL-return part of J.armedExact. -/
theorem bankWindowClosureIncrementReturnExactGhost
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hscope : BankWindowScope ring r root)
    (hm : (r.1 root).mode = .IWAIT)
    (hwait : (r.2.sites root).controller = .waiting [])
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : (r.2.sites (ring.rightNeighbor root)).worker =
      .payload p)
    (ho : p.origin = some o) (hroot : o.root = root)
    (ht : (r.1 (ring.rightNeighbor root)).tok = .AL) :
    Counter.Complete ring (renewalBankNext ring r root).1 root ∧
    ∃ q : RenewalBankPayload n,
      ((renewalBankNext ring r root).2.sites root).controller =
        .active q ∧
      ((renewalBankNext ring r root).2.sites
        (ring.rightNeighbor root)).worker = .empty ∧
      q.origin = some o ∧
      q.heads = bankOriginBinaryValue ring r.1 o ∧
      q.atoms = [] := by
  have hinc := hJ.incrementExact root o
    (ring.rightNeighbor root) p hscope hm hwait hw ho hroot
  have hheads : p.heads = bankOriginBinaryValue ring r.1 o := by
    rcases hinc.2 with hforward | hreturn
    · have hbad : BTok.IR = BTok.AL := hforward.1.symm.trans ht
      cases hbad
    · exact hreturn.2.1
  have hlive :
      p ∈ rbSiteLivePayloads
        (r.2.sites (ring.rightNeighbor root)) := by
    simp [rbSiteLivePayloads, hw]
  have hatoms := hJ.genuinePayloadEmpty
    (ring.rightNeighbor root) p o hlive ho
  obtain ⟨hc, q, hctl, hclear, hqorigin, hqheads, hqatoms⟩ :=
    bankWindowClosureMatchedReturnGenuine
      ring hn r root hscope.1 hscope.2
      (Or.inl ⟨hm, ht⟩) hwait p o hw ho
  exact ⟨hc, q, hctl, hclear, hqorigin,
    hqheads.trans hheads, hqatoms.trans hatoms⟩

/-! ## Genuine CSTART and CWAIT comparison rows -/

/-- CSTART physically paired with an empty first-digit token
issues the genuine controller as an unchanged comparison worker.
The old J fixes both its uncapped heads and empty atoms.
Consumer: compareExact and cwaitTaintedUnique issue branches. -/
theorem bankWindowClosureCstartIssueGenuine
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hscope : BankWindowScope ring r root)
    (hm : (r.1 root).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive : (r.2.sites root).controller = .active p)
    (ho : p.origin = some o) :
    Counter.Complete ring (renewalBankNext ring r root).1 root ∧
    ((renewalBankNext ring r root).2.sites root).controller =
      .waiting [] ∧
    ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker = .payload p ∧
    p.origin = some o ∧
    p.heads = bankOriginBinaryValue ring r.1 o ∧
    p.atoms = [] := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx : (r.1 root).pack.val = 0 := by
    change (r.1 (Counter.site ring root 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy : (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
    change (r.1 (Counter.site ring root 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  obtain ⟨hclean, hheads, _, _⟩ :=
    hJ.armedExact root o p hscope (Or.inr hm) hactive ho
  have ht : (r.1 (ring.rightNeighbor root)).tok = .E := by
    have hfirst := hclean
      (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
    change (r.1 (ring.rightNeighbor root)).tok = .E at hfirst
    exact hfirst
  have hpair := rbRootCstartMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2 root
    (ring.rightNeighbor root)
    (r.1 root) (r.1 (ring.rightNeighbor root))
    hb hx hy hscope.2 hm ht
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r root).2.2
  have hctl := congrArg
    (fun s : RenewalBankSite n => s.controller) hf.1
  have hworker := congrArg
    (fun s : RenewalBankSite n => s.worker) hf.2
  rw [hpair] at hctl hworker
  change ((renewalBankNext ring r root).2.sites root).controller =
    .waiting [] at hctl
  change ((renewalBankNext ring r root).2.sites
    (ring.rightNeighbor root)).worker =
      .payload (renewalBankActivePayload
        (r.2.sites root).controller root) at hworker
  rw [hactive] at hworker
  change ((renewalBankNext ring r root).2.sites
    (ring.rightNeighbor root)).worker = .payload p at hworker
  have hlive : p ∈ rbSiteLivePayloads (r.2.sites root) := by
    simp [rbSiteLivePayloads, hactive]
  have hatoms := hJ.genuinePayloadEmpty root p o hlive ho
  exact ⟨bankWindowClosureCompleteInternalPack
      ring hn r root hscope.1 0 hb,
    hctl, hworker, ho, hheads, hatoms⟩

/-- CL0/CWAIT returns precisely the already-accounted genuine
worker to the root without losing its exact binary head value
or introducing inherited atoms.
Consumer: J.armedExact reactivation after failed comparison. -/
theorem bankWindowClosureCompareReturnExactGhost
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hscope : BankWindowScope ring r root)
    (hm : (r.1 root).mode = .CWAIT)
    (hwait : (r.2.sites root).controller = .waiting [])
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : (r.2.sites (ring.rightNeighbor root)).worker =
      .payload p)
    (ho : p.origin = some o)
    (hroot : o.root = root)
    (ht : (r.1 (ring.rightNeighbor root)).tok = .CL0) :
    Counter.Complete ring (renewalBankNext ring r root).1 root ∧
    ∃ q : RenewalBankPayload n,
      ((renewalBankNext ring r root).2.sites root).controller =
        .active q ∧
      ((renewalBankNext ring r root).2.sites
        (ring.rightNeighbor root)).worker = .empty ∧
      q.origin = some o ∧
      q.heads = bankOriginBinaryValue ring r.1 o ∧
      q.atoms = [] := by
  have hcmp := hJ.compareExact o
    (ring.rightNeighbor root) p hw ho
    (by rw [hroot]; exact hm) (by rw [hroot]; exact hwait)
  have hheads : p.heads = bankOriginBinaryValue ring r.1 o :=
    hcmp.2.2.1
  have hlive :
      p ∈ rbSiteLivePayloads
        (r.2.sites (ring.rightNeighbor root)) := by
    simp [rbSiteLivePayloads, hw]
  have hatoms := hJ.genuinePayloadEmpty
    (ring.rightNeighbor root) p o hlive ho
  obtain ⟨hc, q, hctl, hclear, hqorigin, hqheads, hqatoms⟩ :=
    bankWindowClosureMatchedReturnGenuine
      ring hn r root hscope.1 hscope.2
      (Or.inr ⟨hm, ht⟩) hwait p o hw ho
  exact ⟨hc, q, hctl, hclear, hqorigin,
    hqheads.trans hheads, hqatoms.trans hatoms⟩

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankHeadThreshold
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ## Selected real BANK field bridge -/

/-- Both physical selected endpoints have the exact OLD BANK
mode/bit/token triple even under renewal masking.
Consumer: RWAIT timeout, IR/CR service and CL1 return below. -/
theorem bankWindowClosureSelectedBankTrip
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n) :
    Counter.resetAgentBankTrip ((renewalBankNext ring r e).1 e) =
      Counter.resetCellBankTrip
        (Counter.resetBankOld (r.1 e)
          (r.1 (ring.rightNeighbor e))).1 ∧
    Counter.resetAgentBankTrip
        ((renewalBankNext ring r e).1
          (ring.rightNeighbor e)) =
      Counter.resetCellBankTrip
        (Counter.resetBankOld (r.1 e)
          (r.1 (ring.rightNeighbor e))).2 := by
  have hf := rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r e
  have hs := congrArg Counter.resetAgentBankTrip hf.1
  have hd := congrArg Counter.resetAgentBankTrip hf.2.1
  change
    Counter.resetAgentBankTrip ((renewalBankNext ring r e).1 e) =
      Counter.resetAgentBankTrip
        (renewalMaskedPair
          (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 at hs
  change
    Counter.resetAgentBankTrip
      ((renewalBankNext ring r e).1 (ring.rightNeighbor e)) =
      Counter.resetAgentBankTrip
        (renewalMaskedPair
          (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 at hd
  exact ⟨hs.trans
      (rbBankMaskedSourceTrip
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank),
    hd.trans
      (rbBankMaskedResponderTrip
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank)⟩

/-! ## (1) RWAIT expiry and newly repaired windows -/

/-- On an actual 0→1 service with no return token, an expired
RWAIT lease exits to RESET; the corresponding real ghost root
controller is cleared. The post PACK window is still complete,
so resetWait is vacuous for this root after the timeout.
Consumer: J.resetWait, J.proto and J.orphan timeout rows. -/
theorem bankWindowClosureRootWaitTimeout
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (hgrant : (r.1 root).grant = false)
    (hmode : (r.1 root).mode = .RWAIT)
    (htok : (r.1 (ring.rightNeighbor root)).tok = .E)
    (hlease : (r.1 root).lease.val ≤ 1) :
    Counter.Complete ring (renewalBankNext ring r root).1 root ∧
    ((renewalBankNext ring r root).1 root).mode = .RESET ∧
    ((renewalBankNext ring r root).2.sites root).controller =
      .empty := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hzero : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hroot : (r.1 root).pack.val = 0 := by
    change (r.1 (Counter.site ring root 0)).pack.val = 0
    exact hcomplete 0 (by omega)
  have hdigit : (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
    change (r.1 (Counter.site ring root 1)).pack.val = 1
    exact hcomplete 1 (by omega)
  have hp : packNext 0 1
      (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  have hnot : ¬ 1 < (r.1 root).lease.val := by omega
  have hraw :
      (Counter.resetBankOld (r.1 root)
        (r.1 (ring.rightNeighbor root))).1.mode = .RESET := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hroot, hdigit, hgrant, hmode, htok, hp, hzero,
      hnot, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
  have hrawGhost :
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 root
        (ring.rightNeighbor root)
        (r.1 root) (r.1 (ring.rightNeighbor root))).1.controller =
        .empty := by
    simp [renewalBankPairMemory, renewalBankWaitSlot,
      bankCell, hroot, hdigit, hgrant, hmode, htok,
      hp, hzero, hnot, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]
  have htriple := (bankWindowClosureSelectedBankTrip
    ring hn hbank r root).1
  have hm := congrArg
    (fun t : Mode × Bool × BTok => t.1) htriple
  change ((renewalBankNext ring r root).1 root).mode =
    (Counter.resetBankOld (r.1 root)
      (r.1 (ring.rightNeighbor root))).1.mode at hm
  have hframe := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r root).2.2.1
  have hctl := congrArg
    (fun s : RenewalBankSite n => s.controller) hframe
  change ((renewalBankNext ring r root).2.sites root).controller =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2 root
      (ring.rightNeighbor root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).1.controller
      at hctl
  exact ⟨bankWindowClosureCompleteInternalPack
      ring hn r root hcomplete 0 hb,
    hm.trans hraw, hctl.trans hrawGhost⟩

theorem bankWindowClosureInteriorIrCrWorkerForward
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hjlow : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hkind : (r.1 e).tok = .IR ∨
      (r.1 e).tok = .CR0 ∨ (r.1 e).tok = .CR1)
    (hempty : (r.1 (ring.rightNeighbor e)).tok = .E) :
    ((renewalBankNext ring r e).2.sites e).worker = .empty ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker =
        (r.2.sites e).worker := by
  have hle : j ≤ (compileAdvice (ceilLogTwo n)).b := by omega
  have hnz : j ≠ 0 := by omega
  have htopne : j ≠ (compileAdvice (ceilLogTwo n)).b := by omega
  have hnextle : j + 1 ≤ (compileAdvice (ceilLogTwo n)).b := by omega
  have hnextpos : 1 ≤ j + 1 := by omega
  have hnextnz : j + 1 ≠ 0 := by omega
  have hpost : packNext j (j + 1)
      (compileAdvice (ceilLogTwo n)).b = j + 1 := by
    simp [packNext, hjtop]
  have hpair :
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker = .empty ∧
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker =
        (r.2.sites e).worker := by
    rcases hkind with hir | hcr
    · simp [renewalBankPairMemory, bankCell, hx, hy,
        hjlow, hjtop, hle, hnz, htopne, hnextle,
        hnextpos, hnextnz, hpost, hir, hempty,
        Id.run_pure, Id.run_bind]
    · rcases hcr with hcrzero | hcrone
      · simp [renewalBankPairMemory, bankCell, hx, hy,
          hjlow, hjtop, hle, hnz, htopne, hnextle,
          hnextpos, hnextnz, hpost, hcrzero, hempty,
          Id.run_pure, Id.run_bind]
      · simp [renewalBankPairMemory, bankCell, hx, hy,
          hjlow, hjtop, hle, hnz, htopne, hnextle,
          hnextpos, hnextnz, hpost, hcrone, hempty,
          Id.run_pure, Id.run_bind]
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r e).2.2
  have hs := congrArg
    (fun s : RenewalBankSite n => s.worker) hf.1
  have hd := congrArg
    (fun s : RenewalBankSite n => s.worker) hf.2
  change ((renewalBankNext ring r e).2.sites e).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2 e
      (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker at hs
  change ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2 e
      (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker at hd
  exact ⟨hs.trans hpair.1, hd.trans hpair.2⟩

theorem bankWindowClosureClOneReturnClears
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .CWAIT)
    (ht : (r.1 (ring.rightNeighbor root)).tok = .CL1) :
    Counter.Complete ring (renewalBankNext ring r root).1 root ∧
    ((renewalBankNext ring r root).1 root).mode = .RESET ∧
    ((renewalBankNext ring r root).2.sites root).controller =
      .empty ∧
    ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker = .empty := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hz : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hx : (r.1 root).pack.val = 0 := by
    change (r.1 (Counter.site ring root 0)).pack.val = 0
    exact hcomplete 0 (by omega)
  have hy : (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
    change (r.1 (Counter.site ring root 1)).pack.val = 1
    exact hcomplete 1 (by omega)
  have hpost : packNext 0 1
      (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  have hraw :
      (Counter.resetBankOld (r.1 root)
        (r.1 (ring.rightNeighbor root))).1.mode = .RESET := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, hb, hz, hpost, isRetTok,
      Id.run_pure, Id.run_bind]
  have hrawMemory :
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 root
        (ring.rightNeighbor root)
        (r.1 root) (r.1 (ring.rightNeighbor root))).1.controller =
          .empty ∧
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 root
        (ring.rightNeighbor root)
        (r.1 root) (r.1 (ring.rightNeighbor root))).2.worker =
          .empty := by
    simp [renewalBankPairMemory, bankCell,
      hx, hy, hg, hm, ht, hb, hz, hpost, isRetTok,
      Id.run_pure, Id.run_bind]
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank r root).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((renewalBankNext ring r root).1 root).mode =
    (Counter.resetBankOld (r.1 root)
      (r.1 (ring.rightNeighbor root))).1.mode at hmode
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r root).2.2
  have hc := congrArg
    (fun s : RenewalBankSite n => s.controller) hf.1
  have hw := congrArg
    (fun s : RenewalBankSite n => s.worker) hf.2
  change ((renewalBankNext ring r root).2.sites root).controller =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2 root
      (ring.rightNeighbor root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).1.controller
      at hc
  change ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2 root
      (ring.rightNeighbor root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.worker
      at hw
  exact ⟨bankWindowClosureCompleteInternalPack
      ring hn r root hcomplete 0 hb,
    hmode.trans hraw, hc.trans hrawMemory.1,
    hw.trans hrawMemory.2⟩


end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ### Geometry: newly complete windows -/

/-- A real step preserves PACK at every site other than its
responder, including at the selected source. Consumer: the
XR/XD repair-first-mismatch argument. -/
theorem bankWindowClosureRepairNonresponderPackFixed
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e i : Fin n)
    (hi : i ≠ ring.rightNeighbor e) :
    ((renewalBankNext ring r e).1 i).pack.val =
      (r.1 i).pack.val := by
  by_cases he : i = e
  · subst i
    change ((rbRun ring r [e]).1 e).pack.val =
      (r.1 e).pack.val
    exact (rbBankReferencePairPack ring hn r e).1
  · exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
      (bankWindowExactOffPairFrame ring r e i he hi).1

/-- Every new-complete/old-incomplete window has an OLD
wrong PACK at the selected responder, and all other OLD
PACK entries were correct. Consumer: root-vs-digit split
of bankWindowExactRepairActivationStep. -/
theorem bankWindowClosureRepairFirstMismatchAtResponder
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hpost : Counter.Complete ring
      (renewalBankNext ring r e).1 root)
    (hnot : ¬ Counter.Complete ring r.1 root) :
    ∃ t : Nat,
      t ≤ (compileAdvice (ceilLogTwo n)).b ∧
      Counter.site ring root t = ring.rightNeighbor e ∧
      (r.1 (Counter.site ring root t)).pack.val ≠ t ∧
      (∀ k : Nat, k ≤ (compileAdvice (ceilLogTwo n)).b →
        Counter.site ring root k ≠ ring.rightNeighbor e →
        (r.1 (Counter.site ring root k)).pack.val = k) := by
  have hbad :
      ∃ t : Nat, t ≤ (compileAdvice (ceilLogTwo n)).b ∧
        (r.1 (Counter.site ring root t)).pack.val ≠ t := by
    by_cases hx :
        ∃ t : Nat, t ≤ (compileAdvice (ceilLogTwo n)).b ∧
          (r.1 (Counter.site ring root t)).pack.val ≠ t
    · exact hx
    · exfalso
      apply hnot
      intro t ht
      by_cases heq :
          (r.1 (Counter.site ring root t)).pack.val = t
      · exact heq
      · exact False.elim (hx ⟨t, ht, heq⟩)
  obtain ⟨t, ht, hwrong⟩ := hbad
  have htarget :
      Counter.site ring root t = ring.rightNeighbor e := by
    by_cases heq :
        Counter.site ring root t = ring.rightNeighbor e
    · exact heq
    · have hf := bankWindowClosureRepairNonresponderPackFixed
        ring hn r e (Counter.site ring root t) heq
      have hold : (r.1 (Counter.site ring root t)).pack.val = t :=
        hf.symm.trans (hpost t ht)
      exact False.elim (hwrong hold)
  refine ⟨t, ht, htarget, hwrong, ?_⟩
  intro k hk hne
  have hf := bankWindowClosureRepairNonresponderPackFixed
    ring hn r e (Counter.site ring root k) hne
  exact hf.symm.trans (hpost k hk)

/-- A PACK-changing responder becoming digit j+1 of a complete
POST window was exactly the first OLD proto-run mismatch.
Consumer: OLD J.proto in XD activation. -/
theorem bankWindowClosureRepairOldProtoAtDigit
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (htarget :
      ring.rightNeighbor e =
        Counter.site ring root (j.val + 1))
    (hpost : Counter.Complete ring
      (renewalBankNext ring r e).1 root) :
    BankWindowProtoRun ring r root j.val := by
  have hpostTarget :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val = j.val + 1 := by
    rw [htarget]
    exact hpost (j.val + 1) (by have hj := j.isLt; omega)
  have hnext :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = j.val + 1 :=
    (bankWindowExactResponderPack ring r e
      (clockNeighborDifferent ring
        (by omega : 2 ≤ n) e)).symm.trans hpostTarget
  have hwrong :
      (r.1 (Counter.site ring root (j.val + 1))).pack.val ≠
        j.val + 1 := by
    intro he
    have hold :
        (r.1 (ring.rightNeighbor e)).pack.val =
          j.val + 1 := by
      rw [htarget]
      exact he
    exact hchanged (hnext.trans hold.symm)
  refine ⟨j.isLt, ?_, hwrong⟩
  intro k hk
  have hne :
      Counter.site ring root k ≠ ring.rightNeighbor e := by
    intro he
    have heq :
        Counter.site ring root k =
          Counter.site ring root (j.val + 1) :=
      he.trans htarget
    have hv := congrArg
      (fun i : Fin n =>
        ((renewalBankNext ring r e).1 i).pack.val) heq
    rw [hpost k (by omega),
      hpost (j.val + 1) (by have hj := j.isLt; omega)] at hv
    omega
  have hf := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n) r e
    (Counter.site ring root k) hne
  exact hf.symm.trans (hpost k (by omega))

/-- If an aligned OLD suffix digit beyond the repaired mismatch
is tainted, OLD J.orphan forces its root to be RESET or
empty-controller RWAIT, at the same OLD time as J.proto.
Consumer: inheritedClean and phase activation. -/
theorem bankWindowClosureRepairOldSuffixTaintModes
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hJ : BankWindowExact ring r)
    (j k : Fin (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (htarget :
      ring.rightNeighbor e =
        Counter.site ring root (j.val + 1))
    (hpost : Counter.Complete ring
      (renewalBankNext ring r e).1 root)
    (horder : j.val < k.val)
    (htainted : BankWindowTainted r
      (Counter.site ring root (k.val + 1))) :
    (r.1 root).mode = .RESET ∨
      ((r.1 root).mode = .RWAIT ∧
        (r.2.sites root).controller = .waiting []) := by
  have hp := bankWindowClosureRepairOldProtoAtDigit
    ring hn r e root j hchanged htarget hpost
  have hne :
      Counter.site ring root (k.val + 1) ≠
        ring.rightNeighbor e := by
    intro he
    have heq :
        Counter.site ring root (k.val + 1) =
          Counter.site ring root (j.val + 1) :=
      he.trans htarget
    have hv := congrArg
      (fun i : Fin n =>
        ((renewalBankNext ring r e).1 i).pack.val) heq
    rw [hpost (k.val + 1) (by have hk := k.isLt; omega),
      hpost (j.val + 1) (by have hj := j.isLt; omega)] at hv
    omega
  have hfixed := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n) r e
    (Counter.site ring root (k.val + 1)) hne
  have haligned :
      (r.1 (Counter.site ring root (k.val + 1))).pack.val =
        k.val + 1 :=
    hfixed.symm.trans
      (hpost (k.val + 1) (by have hk := k.isLt; omega))
  have horphan : BankWindowOrphanOwner ring r root k := by
    refine ⟨hp.2.1 0 (by omega), haligned, ?_⟩
    intro hprefix
    exact hp.2.2 (hprefix (j.val + 1) (by omega))
  exact hJ.orphan root k horphan htainted

/-! ### Changed-PACK worker provenance -/

theorem bankWindowClosureIncompleteCwaitNoOwnWorker
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hnot : ¬ Counter.Complete ring r.1 root)
    (hm : (r.1 root).mode = .CWAIT)
    (hc : (r.2.sites root).controller = .waiting []) :
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      o.root = root →
      (r.2.sites i).worker = .payload p →
      p.origin = some o → False := by
  intro i p o hroot hw ho
  have hmode : (r.1 o.root).mode = .CWAIT := by
    rw [hroot]
    exact hm
  have hwait :
      (r.2.sites o.root).controller = .waiting [] := by
    rw [hroot]
    exact hc
  have hcmp := hJ.compareExact o i p hw ho hmode hwait
  have hcomp : BankComparatorOriginWorker ring r o i p :=
    ⟨hw, ho, hcmp.2.1⟩
  have hcomplete := hJ.phaseComplete o i p hcomp hmode
  rw [hroot] at hcomplete
  exact hnot hcomplete

theorem bankWindowClosureRepairProtoReadSetFrame
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (limit : Nat)
    (havoid : ∀ k : Nat, k ≤ limit + 1 →
      Counter.site ring root k ≠ ring.rightNeighbor e) :
    BankWindowProtoRun ring (renewalBankNext ring r e) root limit ↔
      BankWindowProtoRun ring r root limit := by
  unfold BankWindowProtoRun
  constructor
  · rintro ⟨hl, hp, hbad⟩
    refine ⟨hl, ?_, ?_⟩
    · intro k hk
      have hf := bankWindowClosureRepairNonresponderPackFixed
        ring hn r e (Counter.site ring root k)
        (havoid k (by omega))
      exact hf.symm.trans (hp k hk)
    · intro hcorrect
      have hf := bankWindowClosureRepairNonresponderPackFixed
        ring hn r e (Counter.site ring root (limit + 1))
        (havoid (limit + 1) (by omega))
      exact hbad (hf.trans hcorrect)
  · rintro ⟨hl, hp, hbad⟩
    refine ⟨hl, ?_, ?_⟩
    · intro k hk
      have hf := bankWindowClosureRepairNonresponderPackFixed
        ring hn r e (Counter.site ring root k)
        (havoid k (by omega))
      exact hf.trans (hp k hk)
    · intro hcorrect
      have hf := bankWindowClosureRepairNonresponderPackFixed
        ring hn r e (Counter.site ring root (limit + 1))
        (havoid (limit + 1) (by omega))
      exact hbad (hf.symm.trans hcorrect)

/-- An orphan owner predicate is unchanged when the complete
prefix through its named digit avoids the repaired responder,
even if its source is selected. Consumer: moving-ORPH XD row. -/
theorem bankWindowClosureRepairOrphanReadSetFrame
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (havoid : ∀ k : Nat, k ≤ j.val + 1 →
      Counter.site ring root k ≠ ring.rightNeighbor e) :
    BankWindowOrphanOwner ring (renewalBankNext ring r e)
      root j ↔ BankWindowOrphanOwner ring r root j := by
  have hzero : ((renewalBankNext ring r e).1 root).pack.val =
    (r.1 root).pack.val := by
    change ((renewalBankNext ring r e).1
      (Counter.site ring root 0)).pack.val =
      (r.1 (Counter.site ring root 0)).pack.val
    exact bankWindowClosureRepairNonresponderPackFixed
      ring hn r e _ (havoid 0 (by omega))
  have hdigit := bankWindowClosureRepairNonresponderPackFixed
    ring hn r e (Counter.site ring root (j.val + 1))
    (havoid (j.val + 1) (by omega))
  have hprefix :
      (∀ k : Nat, k ≤ j.val + 1 →
        ((renewalBankNext ring r e).1
          (Counter.site ring root k)).pack.val = k) ↔
      (∀ k : Nat, k ≤ j.val + 1 →
        (r.1 (Counter.site ring root k)).pack.val = k) := by
    constructor
    · intro hp k hk
      have hf := bankWindowClosureRepairNonresponderPackFixed
        ring hn r e (Counter.site ring root k) (havoid k hk)
      exact hf.symm.trans (hp k hk)
    · intro hp k hk
      have hf := bankWindowClosureRepairNonresponderPackFixed
        ring hn r e (Counter.site ring root k) (havoid k hk)
      exact hf.trans (hp k hk)
  unfold BankWindowOrphanOwner
  rw [hzero, hdigit, hprefix]

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ### (A) Repaired changed-role worker sourcing and dependent XD rows -/

/-- In the changed-role branch the selected source worker
is either its OLD worker or empty. Consumer: global
PACK-repair taint noncreation; no incoming worker is copied. -/
private theorem bankWindowClosureChangedPairSourceWorkerChoice
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hchanged :
      packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    (renewalBankPairMemory c m e dest x y).1.worker =
        (m.sites e).worker ∨
    (renewalBankPairMemory c m e dest x y).1.worker = .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  by_cases hx : x.pack.val = 0
  · have hpostZero : packNext 0 y.pack.val c.b = 1 := by
      simp [packNext, hb]
    have hpost :
        packNext x.pack.val y.pack.val c.b = 1 := by
      rw [hx]
      exact hpostZero
    have hneq : y.pack.val ≠ 1 := by
      intro he
      apply hchanged
      exact hpost.trans he.symm
    have hchangedZero :
        packNext 0 y.pack.val c.b ≠ y.pack.val := by
      rw [hpostZero]
      exact Ne.symm hneq
    have hne1 : ¬ (1 = y.pack.val) := fun h => hneq h.symm
    have hbz : c.b ≠ 0 := by omega
    have hw :
        (renewalBankPairMemory c m e dest x y).1.worker =
          .empty := by
      simp [renewalBankPairMemory, bankCell, hx,
        hpostZero, hpost, hneq, hchangedZero, hne1, hbz,
        renewalBankWaitSlot, isWaitMode, Id.run_pure,
        Id.run_bind] <;>
        (repeat' split) <;> rfl
    exact Or.inr hw
  · cases ht : x.tok <;>
      simp [renewalBankPairMemory, bankCell,
        hchanged, hx, ht] <;>
      (repeat' split) <;>
      (first | exact Or.inl rfl | exact Or.inr rfl)

/-- Every real changed-PACK worker is unchanged at its own OLD site or empty; consumer: XD inheritedClean. -/
theorem bankWindowClosureChangedWorkerChoice
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val) :
    ∀ i : Fin n,
      ((renewalBankNext ring r e).2.sites i).worker =
        (r.2.sites i).worker ∨
      ((renewalBankNext ring r e).2.sites i).worker = .empty := by
  intro i
  by_cases hsource : i = e
  · subst i
    have hs := bankWindowClosureChangedPairSourceWorkerChoice
      (compileAdvice (ceilLogTwo n)) r.2 e
      (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) hchanged
    have hf := congrArg
      (fun s : RenewalBankSite n => s.worker)
      (rbReferenceSelectedPairFrame
        ring (by omega : 2 ≤ n) r e).2.2.1
    change ((renewalBankNext ring r e).2.sites e).worker =
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker at hf
    rcases hs with hw | hw
    · exact Or.inl (hf.trans hw)
    · exact Or.inr (hf.trans hw)
  · by_cases htarget : i = ring.rightNeighbor e
    · subst i
      exact Or.inr
        (bankWindowBirthChangedResponderStep ring
          (by omega : 2 ≤ n) hbank r e hchanged).2.2.2.1
    · have hf := (bankWindowExactOffPairFrame
        ring r e i hsource htarget).2
      exact Or.inl
        (congrArg (fun s : RenewalBankSite n => s.worker) hf)

/-- The actual changed-role transition cannot create post taint at a new site; consumer: PROTO/ORPH activation. -/
theorem bankWindowClosureChangedTaintOld
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val) :
    ∀ i : Fin n,
      BankWindowTainted (renewalBankNext ring r e) i →
        BankWindowTainted r i := by
  intro i ht
  rcases bankWindowClosureChangedWorkerChoice
      ring hn hbank r e hchanged i with hw | hw
  · unfold BankWindowTainted at ht ⊢
    rw [hw] at ht
    exact ht
  · unfold BankWindowTainted at ht
    rcases ht with ⟨rho, hp⟩ | ⟨p, o, hp, ho⟩
    · rw [hw] at hp
      cases hp
    · rw [hw] at hp
      cases hp

/-- OLD proto and orphan jointly clear every POST digit for a non-RESET/non-RWAIT root; consumer: XD uniqueness fields. -/
theorem bankWindowClosureRepairNonresetPhaseDigitsClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n)
    (hJ : BankWindowExact ring r)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (htarget :
      ring.rightNeighbor e =
        Counter.site ring root (j.val + 1))
    (hpost : Counter.Complete ring
      (renewalBankNext ring r e).1 root)
    (hnotReset : (r.1 root).mode ≠ .RESET)
    (hnotWait : (r.1 root).mode ≠ .RWAIT) :
    ∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted (renewalBankNext ring r e)
        (Counter.site ring root (k.val + 1)) := by
  have hproto := bankWindowClosureRepairOldProtoAtDigit
    ring hn r e root j hchanged htarget hpost
  have hclean := (bankWindowClosureChangedDigitClean
    ring hn hbank r e hchanged).2.2.2.1
  intro k ht
  by_cases heq : k.val = j.val
  · have hsite :
        Counter.site ring root (k.val + 1) =
          ring.rightNeighbor e := by
      rw [heq]
      exact htarget.symm
    rw [hsite] at ht
    exact hclean ht
  · have hold := bankWindowClosureChangedTaintOld
      ring hn hbank r e hchanged
      (Counter.site ring root (k.val + 1)) ht
    by_cases hbefore : k.val < j.val
    · have hno := (hJ.proto root j.val hproto).2.2.2
        hnotReset hnotWait k (by omega)
      exact hno hold
    · have horder : j.val < k.val := by omega
      rcases bankWindowClosureRepairOldSuffixTaintModes
          ring hn r e root hJ j k
          hchanged htarget hpost horder hold with hm | ⟨hm, _⟩
      · exact hnotReset hm
      · exact hnotWait hm

/-- An OLD incomplete CWAIT/empty-wait root owns no genuine POST worker after PACK repair; consumer: comparison phase activation. -/
theorem bankWindowClosureRepairCwaitNoOwnWorker
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n)
    (hJ : BankWindowExact ring r)
    (hnot : ¬ Counter.Complete ring r.1 root)
    (hm : (r.1 root).mode = .CWAIT)
    (hc : (r.2.sites root).controller = .waiting [])
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val) :
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      o.root = root →
      ((renewalBankNext ring r e).2.sites i).worker = .payload p →
      p.origin = some o → False := by
  intro i p o hroot hw ho
  rcases bankWindowClosureChangedWorkerChoice
      ring hn hbank r e hchanged i with hsame | hempty
  · rw [hsame] at hw
    exact bankWindowClosureIncompleteCwaitNoOwnWorker
      ring r root hJ hnot hm hc i p o hroot hw ho
  · rw [hempty] at hw
    cases hw

/-! ### Activation of inherited roots and nonincident genuine controllers -/

/-- Even if the OLD repaired-window root has an inherited controller
with nonempty atoms, no POST digit is tainted. The OLD proto
prefix excludes inherited taint; an OLD suffix taint would force
RESET or empty-controller RWAIT by orphan, contradicting the
OLD inherited root. Consumer: inheritedClean in the XD case,
including OLD RWAIT with independent waiting atoms. -/
theorem bankWindowClosureRepairInheritedDigitsClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n)
    (hJ : BankWindowExact ring r)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (htarget :
      ring.rightNeighbor e =
        Counter.site ring root (j.val + 1))
    (hpost : Counter.Complete ring
      (renewalBankNext ring r e).1 root)
    (hinherited : BankWindowInheritedController r root) :
    ∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted (renewalBankNext ring r e)
        (Counter.site ring root (k.val + 1)) := by
  have hproto := bankWindowClosureRepairOldProtoAtDigit
    ring hn r e root j hchanged htarget hpost
  have hrootZero : (r.1 root).pack.val = 0 := by
    change (r.1 (Counter.site ring root 0)).pack.val = 0
    exact hproto.2.1 0 (by omega)
  have hnotReset : (r.1 root).mode ≠ .RESET := by
    intro hreset
    have hshape := (hJ.frame root).1
    have hempty : (r.2.sites root).controller = .empty := by
      simpa [bankInFlightControllerShape, hrootZero, hreset]
        using hshape
    rcases hinherited with ⟨atoms, hc, _⟩ | ⟨p, hc, _⟩
    · rw [hempty] at hc
      cases hc
    · rw [hempty] at hc
      cases hc
  have hnotEmpty :
      (r.2.sites root).controller ≠ .waiting [] := by
    intro hempty
    rcases hinherited with ⟨atoms, hc, hne⟩ | ⟨p, hc, _⟩
    · rw [hempty] at hc
      have hz : atoms = [] := by
        cases hc
        rfl
      exact hne hz
    · rw [hempty] at hc
      cases hc
  have hclean := (bankWindowClosureChangedDigitClean
    ring hn hbank r e hchanged).2.2.2.1
  intro k ht
  by_cases heq : k.val = j.val
  · have hsite :
        Counter.site ring root (k.val + 1) =
          ring.rightNeighbor e := by
      rw [heq]
      exact htarget.symm
    rw [hsite] at ht
    exact hclean ht
  · have hold := bankWindowClosureChangedTaintOld
      ring hn hbank r e hchanged
      (Counter.site ring root (k.val + 1)) ht
    by_cases hbefore : k.val < j.val
    · exact (hJ.proto root j.val hproto).2.1
        hinherited k (by omega) hold
    · have hafter : j.val < k.val := by omega
      rcases bankWindowClosureRepairOldSuffixTaintModes
          ring hn r e root hJ j k
          hchanged htarget hpost hafter hold with
        hreset | ⟨_, hempty⟩
      · exact hnotReset hreset
      · exact hnotEmpty hempty

/-- All three POST scoped taint-consequents are vacuous when
the OLD root mode is neither RESET nor RWAIT: no POST digit
can be tainted. Consumer: inheritedClean, iwaitTaintedUnique
and cwaitTaintedUnique for a newly completed repaired window. -/
theorem bankWindowClosureRepairNonresetScopedClauses
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n)
    (hJ : BankWindowExact ring r)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (htarget :
      ring.rightNeighbor e =
        Counter.site ring root (j.val + 1))
    (hpost : Counter.Complete ring
      (renewalBankNext ring r e).1 root)
    (hnotReset : (r.1 root).mode ≠ .RESET)
    (hnotWait : (r.1 root).mode ≠ .RWAIT) :
    (BankWindowInheritedController (renewalBankNext ring r e) root →
      ∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        ¬ BankWindowTainted (renewalBankNext ring r e)
          (Counter.site ring root (k.val + 1))) ∧
    (((renewalBankNext ring r e).1 root).mode = .IWAIT →
      ((renewalBankNext ring r e).2.sites root).controller =
        .waiting [] →
      ∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        BankWindowTainted (renewalBankNext ring r e)
          (Counter.site ring root (k.val + 1)) →
        ∃ o p,
          ((renewalBankNext ring r e).2.sites
            (Counter.site ring root (k.val + 1))).worker = .payload p ∧
          p.origin = some o ∧ o.root = root ∧
          bankWindowOnlyToken ring (renewalBankNext ring r e)
            root (Counter.site ring root (k.val + 1))) ∧
    (((renewalBankNext ring r e).1 root).mode = .CWAIT →
      ((renewalBankNext ring r e).2.sites root).controller =
        .waiting [] →
      ∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        BankWindowTainted (renewalBankNext ring r e)
          (Counter.site ring root (k.val + 1)) →
        ∃ o p,
          ((renewalBankNext ring r e).2.sites
            (Counter.site ring root (k.val + 1))).worker = .payload p ∧
          p.origin = some o ∧ o.root = root ∧
          BankTrialLiveComparisonToken
            ((renewalBankNext ring r e).1
              (Counter.site ring root (k.val + 1))).tok ∧
          bankWindowOnlyToken ring (renewalBankNext ring r e)
            root (Counter.site ring root (k.val + 1))) := by
  have hclear := bankWindowClosureRepairNonresetPhaseDigitsClean
    ring hn hbank r e root hJ j hchanged htarget
    hpost hnotReset hnotWait
  refine ⟨?_, ?_, ?_⟩
  · intro _ k
    exact hclear k
  · intro _ _ k ht
    exact False.elim (hclear k ht)
  · intro _ _ k ht
    exact False.elim (hclear k ht)

/-- At an OLD proto-root untouched by the selected pair,
a newly completed window cannot acquire a genuine active
controller; OLD J.proto already excluded its existence.
Consumer: newly activated ARMED/CSTART numeric branch. -/
theorem bankWindowClosureRepairNonincidentGenuineController
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hJ : BankWindowExact ring r)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (htarget :
      ring.rightNeighbor e =
        Counter.site ring root (j.val + 1))
    (hpost : Counter.Complete ring
      (renewalBankNext ring r e).1 root)
    (hsource : root ≠ e)
    (hresponder : root ≠ ring.rightNeighbor e) :
    ∀ p : RenewalBankPayload n, ∀ o : RenewalBankOrigin n,
      ((renewalBankNext ring r e).2.sites root).controller =
        .active p →
      p.origin = some o → False := by
  have hproto := bankWindowClosureRepairOldProtoAtDigit
    ring hn r e root j hchanged htarget hpost
  have hf := (bankWindowExactOffPairFrame
    ring r e root hsource hresponder).2
  intro p o hc ho
  rw [hf] at hc
  exact (hJ.proto root j.val hproto).1 p o hc ho

/-- An OLD RESET root that initiates a genuine PACK-changing
edge cannot launch RWAIT at that service: the selected real
BANK source remains RESET. Consumer: the NEW RWAIT/root-source
repair classification and its non-activation case. -/
theorem bankWindowClosureRepairResetSourceNoLaunch
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hroot : (r.1 e).pack.val = 0)
    (hreset : (r.1 e).mode = .RESET)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val) :
    ((renewalBankNext ring r e).1 e).mode = .RESET := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpostZero :
      packNext 0 (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  have hpost :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hroot]
    exact hpostZero
  have hneq :
      (r.1 (ring.rightNeighbor e)).pack.val ≠ 1 := by
    intro he
    apply hchanged
    exact hpost.trans he.symm
  have hraw :
      (Counter.resetBankOld (r.1 e)
        (r.1 (ring.rightNeighbor e))).1.mode = .RESET := by
    have hne1 : ¬ (1 = (r.1 (ring.rightNeighbor e)).pack.val) :=
      fun h => hneq h.symm
    have hbz : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
    cases hg : (r.1 e).grant <;>
      simp [Counter.resetBankOld, bankPair, bankCell,
        hroot, hreset, hpostZero, hpost, hneq, hchanged, hne1, hbz,
        hg, renewalBankWaitSlot, isWaitMode, Id.run_pure,
        Id.run_bind]
  have hselected := (bankWindowClosureSelectedBankTrip
    ring hn hbank r e).1
  have hm := congrArg
    (fun t : Mode × Bool × BTok => t.1) hselected
  change ((renewalBankNext ring r e).1 e).mode =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.mode at hm
  exact hm.trans hraw

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ### Payload fields, independent of numerical head credit -/

/-- The two exact J payload fields, packaged at a single live
payload. Consumer: bankWindowExactSelectedPayloadStep. -/
private def bankWindowSelectedPayloadSound {n : Nat}
    (p : RenewalBankPayload n) : Prop :=
  (p.origin = none → p.atoms ≠ [] ∧ p.heads = 0) ∧
  (∀ o : RenewalBankOrigin n, p.origin = some o → p.atoms = [])

/-- The OLD J fields apply to any OLD site payload. Consumer:
the selected-pair first-match payload dispatcher. -/
private theorem bankWindowSelectedOldPayloadSound
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (hJ : BankWindowExact ring r)
    (i : Fin n) (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads (r.2.sites i)) :
    bankWindowSelectedPayloadSound p := by
  exact ⟨hJ.payloadShape i p hp,
    fun o ho => hJ.genuinePayloadEmpty i p o hp ho⟩

/-- Worker and active-controller membership are real
rbSiteLivePayloads membership, not extra ghost assumptions.
Consumer: the root/nonroot payload source cases. -/
private theorem bankWindowSelectedWorkerLive
    {n : Nat} (s : RenewalBankSite n)
    (p : RenewalBankPayload n)
    (hw : s.worker = .payload p) :
    p ∈ rbSiteLivePayloads s := by
  simp [rbSiteLivePayloads, hw]

private theorem bankWindowSelectedActiveLive
    {n : Nat} (s : RenewalBankSite n)
    (p : RenewalBankPayload n)
    (hc : s.controller = .active p) :
    p ∈ rbSiteLivePayloads s := by
  simp [rbSiteLivePayloads, hc]

/-- Every live site payload comes from either one worker or
one controller, no additional constructor. Consumer: all
seven real root cases and the six nonroot wirings. -/
private theorem bankWindowSelectedLiveChoice
    {n : Nat} (s : RenewalBankSite n)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads s) :
    s.worker = .payload p ∨ s.controller = .active p := by
  unfold rbSiteLivePayloads at hp
  rcases List.mem_append.mp hp with hw | hc
  · cases hworker : s.worker with
    | empty => simp [hworker] at hw
    | pending rho => simp [hworker] at hw
    | payload q =>
        have hq : p = q := by simpa [hworker] using hw
        subst p
        exact Or.inl rfl
  · cases hcontroller : s.controller with
    | empty => simp [hcontroller] at hc
    | waiting atoms => simp [hcontroller] at hc
    | active q =>
        have hq : p = q := by simpa [hcontroller] using hc
        subst p
        exact Or.inr rfl

/-- An arbitrary inherited entrance fallback is nonempty
and has zero heads. Consumer: ARMED/CSTART fallback and
ordinary-return empty-worker fallback. -/
private theorem bankWindowSelectedEntranceSound
    {n : Nat} (i : Fin n) (controller : Bool) :
    bankWindowSelectedPayloadSound
      (renewalBankEntrancePayload i controller) := by
  constructor
  · intro _
    constructor
    · simp [renewalBankEntrancePayload]
    · rfl
  · intro o h
    simp [renewalBankEntrancePayload] at h

/-- A head service preserves both J payload-shape clauses;
for an inherited payload its head count remains zero.
Consumer: ARMED set and ARMED issue. -/
private theorem bankWindowSelectedHeadSound
    {n : Nat} (p : RenewalBankPayload n)
    (hp : bankWindowSelectedPayloadSound p) :
    bankWindowSelectedPayloadSound (renewalBankHead p) := by
  constructor
  · intro hnone
    have hold : p.origin = none := by
      simpa [renewalBankHead] using hnone
    have hshape := hp.1 hold
    constructor
    · exact hshape.1
    · simp [renewalBankHead, hold]
  · intro o hsome
    have hold : p.origin = some o := by
      simpa [renewalBankHead] using hsome
    exact hp.2 o hold

/-- An active controller contributes its OLD payload, while
empty or waiting controllers contribute only the inherited
entrance fallback. Consumer: ARMED/CSTART source cases. -/
private theorem bankWindowSelectedActivePayloadSound
    {n : Nat} (i : Fin n) (c : RenewalBankController n)
    (hc : ∀ p : RenewalBankPayload n,
      c = .active p → bankWindowSelectedPayloadSound p) :
    bankWindowSelectedPayloadSound
      (renewalBankActivePayload c i) := by
  cases c with
  | empty =>
      exact bankWindowSelectedEntranceSound i true
  | waiting atoms =>
      exact bankWindowSelectedEntranceSound i true
  | active p =>
      exact hc p rfl

/-- An ordinary return may merge inherited atoms with an OLD
worker. It preserves the two payload clauses if every OLD
genuine worker is forbidden to meet nonempty waiting atoms.
Consumer: the real root returned outcome. -/
private theorem bankWindowSelectedReturnedSound
    {n : Nat} (i : Fin n)
    (c : RenewalBankController n)
    (w : RenewalBankWorker n)
    (hold : ∀ p : RenewalBankPayload n,
      w = .payload p → bankWindowSelectedPayloadSound p)
    (hnomix : ∀ (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      w = .payload p → p.origin = some o →
      renewalBankWaitingAtoms c = []) :
    bankWindowSelectedPayloadSound
      (renewalBankReturned c w i) := by
  cases w with
  | empty =>
      constructor
      · intro _
        constructor
        · simp [renewalBankReturned,
            renewalBankWorkerPayload,
            renewalBankEntrancePayload]
        · rfl
      · intro o h
        simp [renewalBankReturned, renewalBankWorkerPayload,
          renewalBankEntrancePayload] at h
  | pending rho =>
      constructor
      · intro _
        constructor
        · simp [renewalBankReturned,
            renewalBankWorkerPayload,
            renewalBankEntrancePayload]
        · rfl
      · intro o h
        simp [renewalBankReturned, renewalBankWorkerPayload,
          renewalBankEntrancePayload] at h
  | payload p =>
      have hs := hold p rfl
      constructor
      · intro hn
        have ho : p.origin = none := by
          simpa [renewalBankReturned,
            renewalBankWorkerPayload] using hn
        have hp := hs.1 ho
        constructor
        · intro hnil
          have hleft : p.atoms = [] := by
            cases hatoms : p.atoms with
            | nil => rfl
            | cons a tail =>
                simp [renewalBankReturned,
                  renewalBankWorkerPayload, hatoms] at hnil
          exact hp.1 hleft
        · exact hp.2
      · intro o hn
        have ho : p.origin = some o := by
          simpa [renewalBankReturned,
            renewalBankWorkerPayload] using hn
        have hclean := hnomix p o rfl ho
        have hp := hs.2 o ho
        simp [renewalBankReturned, renewalBankWorkerPayload,
          hclean, hp]

/-! ### OLD inherited first-digit barrier (J.inheritedClean / J.proto) -/

/-- If an OLD 0→1 root is grant-free and has an independent
inherited controller, J forbids a tainted first digit even
when the OLD window is not complete. At the first mismatch
the PROTO prefix clause applies; without a mismatch
inheritedClean applies. Consumer: both real return and
pending-RL birth payload-shape branches. -/
private theorem bankWindowSelectedInheritedFirstDigitClean
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hroot : (r.1 root).pack.val = 0)
    (hfirst : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hgrant : (r.1 root).grant = false)
    (hinherited : BankWindowInheritedController r root) :
    ¬ BankWindowTainted r (ring.rightNeighbor root) := by
  intro htainted
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have htaint :
      BankWindowTainted r (Counter.site ring root 1) := by
    change BankWindowTainted r (ring.rightNeighbor root)
    exact htainted
  have hprefix :
      ∀ j : Nat, j ≤ (compileAdvice (ceilLogTwo n)).b →
        ∀ k : Nat, k ≤ j →
          (r.1 (Counter.site ring root k)).pack.val = k := by
    intro j
    induction j with
    | zero =>
        intro _ k hk
        have hz : k = 0 := by omega
        subst k
        change (r.1 root).pack.val = 0
        exact hroot
    | succ j ih =>
        intro hbound k hk
        by_cases hbefore : k ≤ j
        · exact ih (by omega) k hbefore
        · have hknext : k = j + 1 := by omega
          subst k
          by_cases haligned :
              (r.1 (Counter.site ring root (j + 1))).pack.val =
                j + 1
          · exact haligned
          · have hproto : BankWindowProtoRun ring r root j :=
              ⟨(by omega), ih (by omega), haligned⟩
            have hpositive : 1 ≤ j := by
              by_cases hz : j = 0
              · rw [hz] at haligned
                change (r.1 (ring.rightNeighbor root)).pack.val ≠
                  1 at haligned
                exact False.elim (haligned hfirst)
              · omega
            have hno := (hJ.proto root j hproto).2.1
              hinherited
              (⟨0, hb⟩ :
                Fin (compileAdvice (ceilLogTwo n)).b)
              hpositive
            exact False.elim (hno htaint)
  have hcomplete : Counter.Complete ring r.1 root := by
    intro j hj
    exact hprefix (compileAdvice (ceilLogTwo n)).b
      (Nat.le_refl _) j hj
  exact (hJ.inheritedClean root
    ⟨hcomplete, hgrant⟩ hinherited
      (⟨0, hb⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b)) htaint

/-- A returned OLD genuine first-digit worker cannot be merged
with a nonempty waiting controller on the actual root-source
ghost edge. Return-to-active requires OLD 0→1 geometry and no
grant; J then excludes the inherited/tainted combination.
Consumer: bankWindowSelectedReturnedSound. -/
private theorem bankWindowSelectedReturnCannotMix
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 root).pack.val = 0)
    (hpair :
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 root (ring.rightNeighbor root)
        (r.1 root) (r.1 (ring.rightNeighbor root)) =
      rbRootReturnedPair r.2 root (ring.rightNeighbor root))
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : (r.2.sites (ring.rightNeighbor root)).worker =
      .payload p) (ho : p.origin = some o) :
    renewalBankWaitingAtoms (r.2.sites root).controller = [] := by
  cases hc : (r.2.sites root).controller with
  | empty => rfl
  | active q => rfl
  | waiting atoms =>
      cases atoms with
      | nil => rfl
      | cons a tail =>
          have hwait :
              (r.2.sites root).controller =
                .waiting (a :: tail) := hc
          have hActive :
              (renewalBankPairMemory
                (compileAdvice (ceilLogTwo n)) r.2 root
                (ring.rightNeighbor root)
                (r.1 root) (r.1 (ring.rightNeighbor root))).1.controller =
                  .active
                    (renewalBankReturned
                      (r.2.sites root).controller
                      (r.2.sites (ring.rightNeighbor root)).worker
                      (ring.rightNeighbor root)) := by
            rw [hpair]
            rfl
          have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
            change 0 < (compileAdvice (ceilLogTwo n)).s + 11
            omega
          have hfirst :
              (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
            by_cases hy :
                (r.1 (ring.rightNeighbor root)).pack.val = 1
            · exact hy
            · have hpost :
                packNext (r.1 root).pack.val
                  (r.1 (ring.rightNeighbor root)).pack.val
                  (compileAdvice (ceilLogTwo n)).b = 1 := by
                rw [hx]
                simp [packNext, hb]
              have hchanged :
                  packNext (r.1 root).pack.val
                    (r.1 (ring.rightNeighbor root)).pack.val
                    (compileAdvice (ceilLogTwo n)).b ≠
                  (r.1 (ring.rightNeighbor root)).pack.val := by
                rw [hpost]
                exact Ne.symm hy
              have hne1 : ¬ (1 = (r.1 (ring.rightNeighbor root)).pack.val) :=
                fun h => hy h.symm
              have hbz : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
              have hpostZero :
                  packNext 0 (r.1 (ring.rightNeighbor root)).pack.val
                    (compileAdvice (ceilLogTwo n)).b = 1 := by
                simp [packNext, hb]
              have hchZ :
                  packNext 0 (r.1 (ring.rightNeighbor root)).pack.val
                    (compileAdvice (ceilLogTwo n)).b ≠
                  (r.1 (ring.rightNeighbor root)).pack.val := by
                rw [hpostZero]
                exact Ne.symm hy
              cases hg : (r.1 root).grant <;>
                cases hm : (r.1 root).mode <;>
                simp [renewalBankPairMemory, bankCell, hx,
                  hpostZero, hchZ, hwait, hg, hm, hne1, hbz,
                  renewalBankWaitSlot, isWaitMode,
                  Id.run_pure, Id.run_bind] at hActive <;>
                (split at hActive <;> cases hActive)
          have hgrant : (r.1 root).grant = false := by
            cases hg : (r.1 root).grant with
            | false => rfl
            | true =>
                have hpost :
                    packNext (r.1 root).pack.val
                      (r.1 (ring.rightNeighbor root)).pack.val
                      (compileAdvice (ceilLogTwo n)).b = 1 := by
                  rw [hx]
                  simp [packNext, hb]
                have hbz : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
                have hpostZero :
                    packNext 0 (r.1 (ring.rightNeighbor root)).pack.val
                      (compileAdvice (ceilLogTwo n)).b = 1 := by
                  simp [packNext, hb]
                have hp01 :
                    packNext 0 1 (compileAdvice (ceilLogTwo n)).b = 1 := by
                  simp [packNext, hb]
                simp [renewalBankPairMemory, bankCell, hx,
                  hfirst, hpostZero, hp01, hg, hbz, Id.run_pure,
                  Id.run_bind] at hActive
          have hinherited : BankWindowInheritedController r root :=
            Or.inl ⟨a :: tail, hwait, by simp⟩
          have htainted :
              BankWindowTainted r (ring.rightNeighbor root) :=
            Or.inr ⟨p, o, hw, ho⟩
          exact False.elim
            ((bankWindowSelectedInheritedFirstDigitClean
              ring r root hJ hx hfirst hgrant hinherited)
              htainted)

/-- The real OLD pending-RL acceptance row has no inherited
waiting atoms under J, even if its 0→1 PACK window had an
unseen mismatch elsewhere. Consumer: zero-origin birth in
the root selected-pair payload dispatcher. -/
private theorem bankWindowSelectedBirthNoWaitingAtoms
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .RWAIT)
    (rho : RenewalBankReceipt n)
    (hw : (r.2.sites (ring.rightNeighbor root)).worker =
      .pending rho) :
    renewalBankWaitingAtoms (r.2.sites root).controller = [] := by
  have hshape := (hJ.frame root).1
  have hwaiting :
      ∃ atoms : List (RenewalBankAtom n),
        (r.2.sites root).controller = .waiting atoms := by
    simpa [bankInFlightControllerShape, hx, hm] using hshape
  obtain ⟨atoms, hc⟩ := hwaiting
  cases atoms with
  | nil =>
      rw [hc]
      rfl
  | cons a tail =>
      have hinherited : BankWindowInheritedController r root :=
        Or.inl ⟨a :: tail, hc, by simp⟩
      have htainted :
          BankWindowTainted r (ring.rightNeighbor root) :=
        Or.inl ⟨rho, hw⟩
      exact False.elim
        ((bankWindowSelectedInheritedFirstDigitClean
          ring r root hJ hx hy hg hinherited) htainted)

/-! ### Nonroot selected worker/controller routing -/

/-- All selected nonroot payloads are OLD workers or a retained
OLD target controller, using the actual six-wiring theorem,
PACK-change and top/spacer branches. Consumer: the payload
root-group bankWindowExactSelectedPayloadStep. -/
private theorem bankWindowSelectedNonrootPairSound
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (p : RenewalBankPayload n)
    (hp :
      p ∈ rbSiteLivePayloads
        ((renewalBankNext ring r e).2.sites e) ∨
      p ∈ rbSiteLivePayloads
        ((renewalBankNext ring r e).2.sites
          (ring.rightNeighbor e))) :
    bankWindowSelectedPayloadSound p := by
  have hframe := (rbReferenceSelectedPairFrame ring hn r e).2.2
  have hctrl := rbBankNonrootControllerPair
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e) (r.1 e)
    (r.1 (ring.rightNeighbor e)) hnonroot
  have hworker :
      ∀ q : RenewalBankPayload n,
        ((renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker =
            .payload q ∨
         (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker =
            .payload q) →
        bankWindowSelectedPayloadSound q := by
    intro q hselected
    rcases rbBankNonrootSelectedWorkersInherited
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      hnonroot q hselected with hs | hd
    · exact bankWindowSelectedOldPayloadSound ring r hJ e q
        (bankWindowSelectedWorkerLive (r.2.sites e) q hs)
    · exact bankWindowSelectedOldPayloadSound ring r hJ
        (ring.rightNeighbor e) q
        (bankWindowSelectedWorkerLive
          (r.2.sites (ring.rightNeighbor e)) q hd)
  rcases hp with hs | hd
  · change p ∈ rbSiteLivePayloads ((rbRun ring r [e]).snd.sites e) at hs
    rw [hframe.1] at hs
    rcases bankWindowSelectedLiveChoice _ p hs with hw | hc
    · exact hworker p (Or.inl hw)
    · rw [hctrl.1] at hc
      cases hc
  · change p ∈ rbSiteLivePayloads ((rbRun ring r [e]).snd.sites (ring.rightNeighbor e)) at hd
    rw [hframe.2] at hd
    rcases bankWindowSelectedLiveChoice _ p hd with hw | hc
    · exact hworker p (Or.inr hw)
    · rcases hctrl.2 with hempty | hwait
      · rw [hempty] at hc
        cases hc
      · rw [hwait] at hc
        have hold := rbWaitKeepsOrErasesController
          (r.1 (ring.rightNeighbor e)).mode
          (r.1 (ring.rightNeighbor e)).lease.val
          (r.2.sites (ring.rightNeighbor e)).controller p hc
        exact bankWindowSelectedOldPayloadSound ring r hJ
          (ring.rightNeighbor e) p
          (bankWindowSelectedActiveLive
            (r.2.sites (ring.rightNeighbor e)) p hold)

/-! ### Seven first-match root outcomes -/

/-- The source role-zero selected pair preserves BOTH payload
fields, by the real guarded RBRootPayloadCase classification.
The only new genuine origin is the pending-RL acceptance, and
the only possible inherited/genuine merge is the ordinary
return, both ruled clean by OLD J's first-digit barrier.
Consumer: bankWindowExactSelectedPayloadStep. -/
private theorem bankWindowSelectedRootPairSound
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 e).pack.val = 0)
    (p : RenewalBankPayload n)
    (hp :
      p ∈ rbSiteLivePayloads
        ((renewalBankNext ring r e).2.sites e) ∨
      p ∈ rbSiteLivePayloads
        ((renewalBankNext ring r e).2.sites
          (ring.rightNeighbor e))) :
    bankWindowSelectedPayloadSound p := by
  have hframe := (rbReferenceSelectedPairFrame ring hn r e).2.2
  have hcase := rbRootPayloadCaseClassification
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hx
  have hlocal :
      p ∈ rbSiteLivePayloads
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 ∨
      p ∈ rbSiteLivePayloads
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 := by
    rcases hp with hs | hd
    · change p ∈ rbSiteLivePayloads ((rbRun ring r [e]).snd.sites e) at hs
      rw [hframe.1] at hs
      exact Or.inl hs
    · change p ∈ rbSiteLivePayloads ((rbRun ring r [e]).snd.sites (ring.rightNeighbor e)) at hd
      rw [hframe.2] at hd
      exact Or.inr hd
  cases hcase with
  | passive hpass =>
      obtain ⟨controller, worker, hpair, hc, hw⟩ := hpass
      rw [hpair] at hlocal
      rcases hlocal with hs | hd
      · rcases bankWindowSelectedLiveChoice _ p hs with hworker | ha
        · cases hworker
        · change controller = .active p at ha
          rcases hc with hzero | hwait
          · rw [hzero] at ha
            cases ha
          · have hold :
                (r.2.sites e).controller = .active p := by
              apply rbWaitKeepsOrErasesController
                (r.1 e).mode (r.1 e).lease.val
              rw [← hwait]
              exact ha
            exact bankWindowSelectedOldPayloadSound ring r hJ
              e p (bankWindowSelectedActiveLive
                (r.2.sites e) p hold)
      · rcases bankWindowSelectedLiveChoice _ p hd with hworker | ha
        · change worker = .payload p at hworker
          rcases hw with hzero | hkeep
          · rw [hzero] at hworker
            cases hworker
          · have hold :
                (r.2.sites (ring.rightNeighbor e)).worker =
                  .payload p := by
              rw [← hkeep]
              exact hworker
            exact bankWindowSelectedOldPayloadSound ring r hJ
              (ring.rightNeighbor e) p
              (bankWindowSelectedWorkerLive
                (r.2.sites (ring.rightNeighbor e)) p hold)
        · cases ha
  | launch hpair =>
      rw [hpair] at hlocal
      rcases hlocal with hs | hd
      · rcases bankWindowSelectedLiveChoice _ p hs with hw | hc
        · cases hw
        · cases hc
      · rcases bankWindowSelectedLiveChoice _ p hd with hw | hc
        · cases hw
        · cases hc
  | returned hpair =>
      rw [hpair] at hlocal
      rcases hlocal with hs | hd
      · rcases bankWindowSelectedLiveChoice _ p hs with hw | ha
        · cases hw
        · have heq :
              p = renewalBankReturned
                (r.2.sites e).controller
                (r.2.sites (ring.rightNeighbor e)).worker
                (ring.rightNeighbor e) := by
            change RenewalBankController.active
              (renewalBankReturned
                (r.2.sites e).controller
                (r.2.sites (ring.rightNeighbor e)).worker
                (ring.rightNeighbor e)) = .active p at ha
            exact (RenewalBankController.active.inj ha).symm
          rw [heq]
          apply bankWindowSelectedReturnedSound
          · intro q hold
            exact bankWindowSelectedOldPayloadSound ring r hJ
              (ring.rightNeighbor e) q
              (bankWindowSelectedWorkerLive
                (r.2.sites (ring.rightNeighbor e)) q hold)
          · intro q o hold ho
            exact bankWindowSelectedReturnCannotMix
              ring r e hJ hx hpair q o hold ho
      · rcases bankWindowSelectedLiveChoice _ p hd with hw | ha
        · cases hw
        · cases ha
  | accepted rho hy hg hm ht hw hpair =>
      rw [hpair] at hlocal
      rcases hlocal with hs | hd
      · rcases bankWindowSelectedLiveChoice _ p hs with hworker | ha
        · cases hworker
        · have heq :
              p = { atoms := renewalBankWaitingAtoms
                      (r.2.sites e).controller
                    origin := some
                      { service := r.2.service, root := e,
                        receipt := rho }
                    heads := 0 } := by
            change RenewalBankController.active
              { atoms := renewalBankWaitingAtoms
                  (r.2.sites e).controller
                origin := some
                  { service := r.2.service, root := e,
                    receipt := rho }
                heads := 0 } = .active p at ha
            exact (RenewalBankController.active.inj ha).symm
          rw [heq]
          have hclear := bankWindowSelectedBirthNoWaitingAtoms
            ring r e hJ hx hy hg hm rho hw
          constructor
          · intro h
            cases h
          · intro o _
            exact hclear
      · rcases bankWindowSelectedLiveChoice _ p hd with hw | ha
        · cases hw
        · cases ha
  | armedSet hy hg hm ht hpair =>
      rw [hpair] at hlocal
      rcases hlocal with hs | hd
      · rcases bankWindowSelectedLiveChoice _ p hs with hw | ha
        · cases hw
        · have heq : p = renewalBankHead
              (renewalBankActivePayload
                (r.2.sites e).controller e) := by
            change RenewalBankController.active
              (renewalBankHead
                (renewalBankActivePayload
                  (r.2.sites e).controller e)) = .active p at ha
            exact (RenewalBankController.active.inj ha).symm
          rw [heq]
          apply bankWindowSelectedHeadSound
          apply bankWindowSelectedActivePayloadSound
          intro q hold
          exact bankWindowSelectedOldPayloadSound ring r hJ e q
            (bankWindowSelectedActiveLive
              (r.2.sites e) q hold)
      · rcases bankWindowSelectedLiveChoice _ p hd with hw | ha
        · have hold :
              (r.2.sites (ring.rightNeighbor e)).worker =
                .payload p := by
            change (r.2.sites (ring.rightNeighbor e)).worker =
              .payload p at hw
            exact hw
          exact bankWindowSelectedOldPayloadSound ring r hJ
            (ring.rightNeighbor e) p
            (bankWindowSelectedWorkerLive
              (r.2.sites (ring.rightNeighbor e)) p hold)
        · cases ha
  | armedIssue hy hg hm ht hpair =>
      rw [hpair] at hlocal
      rcases hlocal with hs | hd
      · rcases bankWindowSelectedLiveChoice _ p hs with hw | ha
        · cases hw
        · cases ha
      · rcases bankWindowSelectedLiveChoice _ p hd with hw | ha
        · have heq : p = renewalBankHead
              (renewalBankActivePayload
                (r.2.sites e).controller e) := by
            change RenewalBankWorker.payload
              (renewalBankHead
                (renewalBankActivePayload
                  (r.2.sites e).controller e)) = .payload p at hw
            exact (RenewalBankWorker.payload.inj hw).symm
          rw [heq]
          apply bankWindowSelectedHeadSound
          apply bankWindowSelectedActivePayloadSound
          intro q hold
          exact bankWindowSelectedOldPayloadSound ring r hJ e q
            (bankWindowSelectedActiveLive
              (r.2.sites e) q hold)
        · cases ha
  | cstart hm hpair =>
      rw [hpair] at hlocal
      rcases hlocal with hs | hd
      · rcases bankWindowSelectedLiveChoice _ p hs with hw | ha
        · cases hw
        · cases ha
      · rcases bankWindowSelectedLiveChoice _ p hd with hw | ha
        · have heq :
              p = renewalBankActivePayload
                (r.2.sites e).controller e := by
            change RenewalBankWorker.payload
              (renewalBankActivePayload
                (r.2.sites e).controller e) = .payload p at hw
            exact (RenewalBankWorker.payload.inj hw).symm
          rw [heq]
          apply bankWindowSelectedActivePayloadSound
          intro q hold
          exact bankWindowSelectedOldPayloadSound ring r hJ e q
            (bankWindowSelectedActiveLive
              (r.2.sites e) q hold)
        · cases ha

/-- All actual selected sites (root or nonroot) and every
off-pair site satisfy the two J payload fields in one step.
This is the ledger's first row-group, not a claim about the
remaining fourteen fields of J. The scheduler prefix is the
real rbRun from the genuine renewalBankStart. -/
theorem bankWindowExactSelectedPayloadStep
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre)) :
    (∀ i p, p ∈ rbSiteLivePayloads
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i) →
      p.origin = none → p.atoms ≠ [] ∧ p.heads = 0) ∧
    (∀ i p o, p ∈ rbSiteLivePayloads
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i) →
      p.origin = some o → p.atoms = []) := by
  have hselected :
      ∀ (p : RenewalBankPayload n),
        (p ∈ rbSiteLivePayloads
          ((renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e) ∨
         p ∈ rbSiteLivePayloads
          ((renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
              (ring.rightNeighbor e))) →
        bankWindowSelectedPayloadSound p := by
    intro p hp
    by_cases hroot :
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0
    · exact bankWindowSelectedRootPairSound ring
        (by omega : 2 ≤ n)
        (rbRun ring (renewalBankStart ring seed) pre)
        e hJ hroot p hp
    · exact bankWindowSelectedNonrootPairSound ring
        (by omega : 2 ≤ n)
        (rbRun ring (renewalBankStart ring seed) pre)
        e hJ hroot p hp
  have hall :
      ∀ (i : Fin n) (p : RenewalBankPayload n),
        p ∈ rbSiteLivePayloads
          ((renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i) →
        bankWindowSelectedPayloadSound p := by
    intro i p hp
    by_cases hs : i = e
    · subst i
      exact hselected p (Or.inl hp)
    · by_cases hd : i = ring.rightNeighbor e
      · subst i
        exact hselected p (Or.inr hp)
      · have hf := (bankWindowExactOffPairFrame ring
          (rbRun ring (renewalBankStart ring seed) pre)
          e i hs hd).2
        rw [hf] at hp
        exact bankWindowSelectedOldPayloadSound ring
          (rbRun ring (renewalBankStart ring seed) pre)
          hJ i p hp
  constructor
  · intro i p hp ho
    exact (hall i p hp).1 ho
  · intro i p o hp ho
    exact (hall i p hp).2 o ho

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ### Incoming PACK-zero responder: selected-mode and controller rows -/

/-- If the actual incoming edge leaves its OLD role-zero
responder at role zero, the OLD source cannot itself have
role zero. Consumer: bankWindowIncomingRootRwaitExact. -/
private theorem bankWindowIncomingStableSourceNonzero
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hpost :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val = 0) :
    (r.1 e).pack.val ≠ 0 := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpack := bankWindowExactResponderPack ring r e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hnext :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 0 :=
    hpack.symm.trans hpost
  intro hx
  have hzero :
      packNext 0 0 (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  rw [hx, hy, hzero] at hnext
  omega

/-- The actual masked incoming-root RWAIT mode is the OLD
bankPair waiting-mode result, even with a changing private
grant at a different owner. Consumer: incoming-root lease
survival and expiration, not an independent BANK model. -/
private theorem bankWindowIncomingRwaitPhysicalMode
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hpost :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val = 0)
    (hg : (r.1 (ring.rightNeighbor e)).grant = false)
    (hm : (r.1 (ring.rightNeighbor e)).mode = .RWAIT) :
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).mode =
      Counter.resetClockWaitMode
        (r.1 (ring.rightNeighbor e)).lease.val := by
  have hx := bankWindowIncomingStableSourceNonzero
    ring hn r e hy hpost
  have hp := bankWindowExactResponderPack ring r e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hnext :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 0 :=
    hp.symm.trans hpost
  have hsymbol := Counter.resetClockIncomingWaitSymbolic
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    (by change (r.1 e).pack.val ≠ 0; exact hx)
    (by change (r.1 (ring.rightNeighbor e)).pack.val = 0; exact hy)
    (by change (r.1 (ring.rightNeighbor e)).grant = false; exact hg)
    (by change (r.1 (ring.rightNeighbor e)).mode = .RWAIT; exact hm)
  have hraw :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode =
      Counter.resetClockWaitMode
        (r.1 (ring.rightNeighbor e)).lease.val := by
    unfold Counter.resetBankOld
    rw [hnext]
    exact hsymbol.1
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank r e).2
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((renewalBankNext ring r e).1
    (ring.rightNeighbor e)).mode =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode at hmode
  exact hmode.trans hraw

/-- Incoming nonroot-source RWAIT either survives with
the identical OLD ghost waiting controller (lease > 1)
or expires into RESET with empty ghost (lease ≤ 1).
This uses the whole-reference frame theorem to
reject an impossible empty controller in a surviving
RWAIT mode, and rbBankNonrootControllerPair for ghost
ownership. Consumer: J.resetWait and IWAIT/CWAIT mode
classification in the incoming-root row group. -/
private theorem bankWindowIncomingRwaitExact
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hy : ((rbRun ring
      (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hg : ((rbRun ring
      (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).grant = false)
    (hm : ((rbRun ring
      (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).mode = .RWAIT) :
    (1 < ((rbRun ring
        (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).lease.val →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
          (ring.rightNeighbor e)).mode = .RWAIT ∧
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller =
      ((rbRun ring
        (renewalBankStart ring seed) pre).2.sites
          (ring.rightNeighbor e)).controller) ∧
    (((rbRun ring
        (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).lease.val ≤ 1 →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
          (ring.rightNeighbor e)).mode = .RESET ∧
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller = .empty) := by
  have hsource := bankWindowIncomingStableSourceNonzero
    ring hn (rbRun ring (renewalBankStart ring seed) pre)
    e hy hpost
  have hmode := bankWindowIncomingRwaitPhysicalMode
    ring hn hbank
    (rbRun ring (renewalBankStart ring seed) pre)
    e hy hpost hg hm
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  have hselected := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n)
    (rbRun ring (renewalBankStart ring seed) pre) e).2.2.2
  have hctrl := (rbBankNonrootControllerPair
    (compileAdvice (ceilLogTwo n))
    (rbRun ring (renewalBankStart ring seed) pre).2
    e (ring.rightNeighbor e)
    ((rbRun ring (renewalBankStart ring seed) pre).1 e)
    ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)) hsource).2
  constructor
  · intro hlease
    have hnewmode :
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
          (ring.rightNeighbor e)).mode = .RWAIT := by
      rw [hmode]
      simp [Counter.resetClockWaitMode, hlease]
    have hwshape := (hframe (ring.rightNeighbor e)).1
    have hwaiting :
        ∃ atoms : List (RenewalBankAtom n),
          ((renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
            (ring.rightNeighbor e)).controller = .waiting atoms := by
      simpa [bankInFlightControllerShape, hpost, hnewmode] using
        hwshape
    have hnotEmpty :
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller ≠ .empty := by
      intro hempty
      obtain ⟨atoms, hw⟩ := hwaiting
      rw [hempty] at hw
      cases hw
    have hselect := congrArg
      (fun s : RenewalBankSite n => s.controller) hselected
    change ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
      (ring.rightNeighbor e)).controller =
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n))
        (rbRun ring (renewalBankStart ring seed) pre).2
        e (ring.rightNeighbor e)
        ((rbRun ring (renewalBankStart ring seed) pre).1 e)
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e))).2.controller at hselect
    have hctrlExact :
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
            (ring.rightNeighbor e)).controller =
        ((rbRun ring
          (renewalBankStart ring seed) pre).2.sites
            (ring.rightNeighbor e)).controller := by
      rcases hctrl with hzero | hwait
      · have he := hselect.trans hzero
        exact False.elim (hnotEmpty he)
      · have hleaseWait :
            renewalBankWaitSlot
              ((rbRun ring (renewalBankStart ring seed) pre).1
                (ring.rightNeighbor e)).mode
              ((rbRun ring (renewalBankStart ring seed) pre).1
                (ring.rightNeighbor e)).lease.val
              ((rbRun ring (renewalBankStart ring seed) pre).2.sites
                (ring.rightNeighbor e)).controller =
            ((rbRun ring (renewalBankStart ring seed) pre).2.sites
              (ring.rightNeighbor e)).controller := by
          simp [renewalBankWaitSlot, hm, hlease, isWaitMode]
        exact hselect.trans (hwait.trans hleaseWait)
    exact ⟨hnewmode, hctrlExact⟩
  · intro hlease
    have hshort :
        ¬ 1 < ((rbRun ring
          (renewalBankStart ring seed) pre).1
            (ring.rightNeighbor e)).lease.val := by omega
    have hnewmode :
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
          (ring.rightNeighbor e)).mode = .RESET := by
      rw [hmode]
      simp [Counter.resetClockWaitMode, hshort]
    have hrootshape := (hframe (ring.rightNeighbor e)).1
    have hnewcontroller :
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller = .empty := by
      simpa [bankInFlightControllerShape, hpost, hnewmode]
        using hrootshape
    exact ⟨hnewmode, hnewcontroller⟩

/-! ### Incoming responder cannot create a genuine controller -/

/-- A role-zero OLD responder receives no new active payload:
any POST active controller is exactly its OLD active controller.
For a role-zero source the responder is necessarily PACK
changed and sanitized; for a nonzero source this is the
proved nonroot controller pair and renewalBankWaitSlot.
Consumer: global phaseExcludes and genuine root ownership. -/
private theorem bankWindowIncomingActiveFromOld
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 0) :
    ∀ p : RenewalBankPayload n,
      ((renewalBankNext ring r e).2.sites
        (ring.rightNeighbor e)).controller = .active p →
      (r.2.sites (ring.rightNeighbor e)).controller = .active p := by
  intro p ha
  by_cases hx : (r.1 e).pack.val = 0
  · have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
      change 0 < (compileAdvice (ceilLogTwo n)).s + 11
      omega
    have hchanged :
        packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b ≠
        (r.1 (ring.rightNeighbor e)).pack.val := by
      rw [hx, hy]
      simp [packNext, hb]
    have hclear := (bankWindowBirthChangedResponderStep
      ring (by omega : 2 ≤ n) hbank r e hchanged).2.2.2.2
    rw [hclear] at ha
    cases ha
  · have hpair := (rbBankNonrootControllerPair
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) hx).2
    have hf := (rbReferenceSelectedPairFrame
      ring (by omega : 2 ≤ n) r e).2.2.2
    have hactive := congrArg
      (fun s : RenewalBankSite n => s.controller) hf
    change ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).controller =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.controller
        at hactive
    have hp :
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.controller =
            .active p := by
      rw [← hactive]
      exact ha
    rcases hpair with hzero | hwait
    · rw [hzero] at hp
      cases hp
    · rw [hwait] at hp
      exact rbWaitKeepsOrErasesController
        (r.1 (ring.rightNeighbor e)).mode
        (r.1 (ring.rightNeighbor e)).lease.val
        (r.2.sites (ring.rightNeighbor e)).controller p hp

/-! ### Changed incoming root: the entire old-root scope exits -/

/-- When the OLD incoming PACK-zero responder acquires a
nonzero PACK, the full root-local J package is discharged:
its scope, proto-run, orphan-owner, inherited-controller and
all active modes vanish. Its mode is the real RESET output,
not an assumed abstract cleanup.
Consumer: IN/XR/B0 changed-responder root case. -/
private theorem bankWindowIncomingChangedRootExit
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hnew :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val ≠ 0) :
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).mode = .RESET ∧
    ¬ BankWindowScope ring
      (renewalBankNext ring r e) (ring.rightNeighbor e) ∧
    ¬ BankWindowInheritedController
      (renewalBankNext ring r e) (ring.rightNeighbor e) ∧
    (∀ limit : Nat,
      ¬ BankWindowProtoRun ring (renewalBankNext ring r e)
        (ring.rightNeighbor e) limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowOrphanOwner ring (renewalBankNext ring r e)
        (ring.rightNeighbor e) j) ∧
    (∀ o : RenewalBankOrigin n,
      o.root = ring.rightNeighbor e →
      ((renewalBankNext ring r e).1 o.root).mode ≠ .ARMED ∧
      ((renewalBankNext ring r e).1 o.root).mode ≠ .CSTART ∧
      ((renewalBankNext ring r e).1 o.root).mode ≠ .IWAIT ∧
      ((renewalBankNext ring r e).1 o.root).mode ≠ .CWAIT) := by
  have hsan := bankWindowClosureBrokenRootSanitized
    ring hn hbank r e hy hnew
  have hno := bankWindowClosureBrokenRootNoProtoOrphan
    ring hn hbank r e hy hnew
  have hnoscope :
      ¬ BankWindowScope ring (renewalBankNext ring r e)
        (ring.rightNeighbor e) := by
    intro hc
    have hz := hc.1 0 (by omega)
    change ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 0 at hz
    exact hnew hz
  refine ⟨hsan.1, hnoscope, hsan.2.2,
    hno.2.1, hno.2.2, ?_⟩
  intro o ho
  rw [ho]
  rw [hsan.1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hh
    cases hh
  · intro hh
    cases hh
  · intro hh
    cases hh
  · intro hh
    cases hh

/-! ### One incoming-root row-group statement: structural core -/

/-- Incoming PACK-zero responder, on the actual rbRun BANK
reference, classified by a genuine role-change exit and by
the literal RWAIT lease-survival / expiration branches.
The global frame/payload fields come from the already closed
J row groups; every possible active controller at this
responder has the OLD identity.

Consumer: the row-group theorem bankWindowExactIncomingRootStep
(ledger item 2), not yet proved. This is its structural core.
The other responder-root J clauses (continuing IWAIT/CWAIT
comparison flags, resetWait front, proto and orphan when
PACK is unchanged, and two-window overlap) are NOT claimed
by this theorem and remain part of the ledger item. -/
theorem bankWindowIncomingRootCoreStep
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hy :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val = 0) :
    BankInFlightAligned ring
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e) ∧
    (∀ i p, p ∈ rbSiteLivePayloads
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i) →
      p.origin = none → p.atoms ≠ [] ∧ p.heads = 0) ∧
    (∀ i p o, p ∈ rbSiteLivePayloads
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i) →
      p.origin = some o → p.atoms = []) ∧
    (∀ p : RenewalBankPayload n,
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller = .active p →
      ((rbRun ring
        (renewalBankStart ring seed) pre).2.sites
          (ring.rightNeighbor e)).controller = .active p) ∧
    (((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).pack.val ≠ 0 →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
          (ring.rightNeighbor e)).mode = .RESET ∧
      ¬ BankWindowScope ring
        (renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e)
          (ring.rightNeighbor e) ∧
      ¬ BankWindowInheritedController
        (renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e)
          (ring.rightNeighbor e) ∧
      (∀ limit : Nat,
        ¬ BankWindowProtoRun ring
          (renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e)
            (ring.rightNeighbor e) limit) ∧
      (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ¬ BankWindowOrphanOwner ring
          (renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e)
            (ring.rightNeighbor e) j) ∧
      (∀ o : RenewalBankOrigin n,
        o.root = ring.rightNeighbor e →
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
            o.root).mode ≠ .ARMED ∧
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
            o.root).mode ≠ .CSTART ∧
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
            o.root).mode ≠ .IWAIT ∧
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
            o.root).mode ≠ .CWAIT)) ∧
    (((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).pack.val = 0 →
      ((rbRun ring
        (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).grant = false →
      ((rbRun ring
        (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).mode = .RWAIT →
      (1 < ((rbRun ring
        (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).lease.val →
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
            (ring.rightNeighbor e)).mode = .RWAIT ∧
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
            (ring.rightNeighbor e)).controller =
        ((rbRun ring
          (renewalBankStart ring seed) pre).2.sites
            (ring.rightNeighbor e)).controller) ∧
      (((rbRun ring
        (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).lease.val ≤ 1 →
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
            (ring.rightNeighbor e)).mode = .RESET ∧
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
            (ring.rightNeighbor e)).controller = .empty)) := by
  have hf := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  have hp := bankWindowExactSelectedPayloadStep
    ring hn hbank seed pre e hJ
  have ha := bankWindowIncomingActiveFromOld
    ring hn hbank
    (rbRun ring (renewalBankStart ring seed) pre) e hy
  refine ⟨hf, hp.1, hp.2, ha, ?_, ?_⟩
  · intro hnew
    exact bankWindowIncomingChangedRootExit
      ring hn hbank
      (rbRun ring (renewalBankStart ring seed) pre)
      e hy hnew
  · intro hpost hg hm
    exact bankWindowIncomingRwaitExact
      ring hn hbank seed pre e hJ
      hy hpost hg hm

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankHeadThreshold
open L3.BankCounterRows
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Physical clockwise site arithmetic. Consumer:
bankWindowIncomingPredecessorOutsideDigits. -/
private theorem bankWindowIncomingSiteValue
    {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (j : Nat) :
    (Counter.site ring root j).val = (root.val + j) % n := by
  induction j with
  | zero =>
      change root.val = (root.val + 0) % n
      simp [Nat.mod_eq_of_lt root.isLt]
  | succ j ih =>
      change ((Counter.site ring root j).val + 1) % n =
        (root.val + (j + 1)) % n
      rw [ih, Nat.mod_add_mod]
      congr 1

/-- No positive clockwise displacement shorter than the
ring length returns to its starting vertex. Consumer:
bankWindowIncomingPredecessorOutsideDigits and digit framing. -/
private theorem bankWindowIncomingSiteNoShortReturn
    {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (j : Nat)
    (hj : 1 ≤ j) (hshort : j < n) :
    Counter.site ring root j ≠ root := by
  intro he
  have hv := congrArg Fin.val he
  rw [bankWindowIncomingSiteValue ring root j] at hv
  have hroot := root.isLt
  by_cases hlow : root.val + j < n
  · rw [Nat.mod_eq_of_lt hlow] at hv
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : n ≤ root.val + j)] at hv
    rw [Nat.mod_eq_of_lt (by omega : root.val + j - n < n)] at hv
    omega

/-- The predecessor of the PACK-zero responder is outside
ALL its nonroot digits, whether or not its old window is
complete. Consumer: J row IN/B0, resetWait, comparison
flags, proto and orphan transports. -/
theorem bankWindowIncomingPredecessorOutsideDigits
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root e : Fin n)
    (hy : ring.rightNeighbor e = root) :
    ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice (ceilLogTwo n)).b →
      e ≠ Counter.site ring root j := by
  intro j hj hb he
  have hsize := Counter.resetColdLargeAtSpatialCutoff n hbank
  change 2 * (13 * ((compileAdvice (ceilLogTwo n)).b + 2)) ≤ n
    at hsize
  have hjn : j + 1 < n := by omega
  have hreturn : Counter.site ring root (j + 1) = root := by
    have hright := hy
    rw [he] at hright
    change Counter.site ring root (j + 1) = root at hright
    exact hright
  exact (bankWindowIncomingSiteNoShortReturn
    ring root (j + 1) (by omega) hjn) hreturn

/-- Every physical digit agent and its entire ghost site
are framed on an edge entering its own root. Neither endpoint
is a digit: source exclusion is geometric, target is the root.
Consumer: all unchanged-PACK root-local J read sets. -/
theorem bankWindowIncomingDigitReadSetFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (j : Nat) (hj : 1 ≤ j)
    (hb : j ≤ (compileAdvice (ceilLogTwo n)).b) :
    (renewalBankNext ring r e).1
        (Counter.site ring root j) =
      r.1 (Counter.site ring root j) ∧
    ((renewalBankNext ring r e).2.sites
        (Counter.site ring root j)) =
      (r.2.sites (Counter.site ring root j)) := by
  have hsize := Counter.resetColdLargeAtSpatialCutoff n hbank
  change 2 * (13 * ((compileAdvice (ceilLogTwo n)).b + 2)) ≤ n
    at hsize
  have hjn : j < n := by omega
  have hleft : Counter.site ring root j ≠ e :=
    Ne.symm (bankWindowIncomingPredecessorOutsideDigits
      ring hbank root e hy j hj hb)
  have hright :
      Counter.site ring root j ≠ ring.rightNeighbor e := by
    rw [hy]
    exact bankWindowIncomingSiteNoShortReturn
      ring root j hj hjn
  exact bankWindowExactOffPairFrame ring r e
    (Counter.site ring root j) hleft hright

/-- In the unchanged-PACK-zero incoming branch, every role
read by this root's complete/proto/orphan tests is unchanged.
Consumer: J.inheritedClean, resetWait, proto and orphan. -/
theorem bankWindowIncomingPackReadSetFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (hyPack : (r.1 root).pack.val = 0)
    (hpostPack :
      ((renewalBankNext ring r e).1 root).pack.val = 0) :
    ∀ j : Nat, j ≤ (compileAdvice (ceilLogTwo n)).b →
      ((renewalBankNext ring r e).1
        (Counter.site ring root j)).pack.val =
      (r.1 (Counter.site ring root j)).pack.val := by
  intro j hj
  cases j with
  | zero =>
      change ((renewalBankNext ring r e).1 root).pack.val =
        (r.1 root).pack.val
      exact hpostPack.trans hyPack.symm
  | succ k =>
      exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
        ((bankWindowIncomingDigitReadSetFrame
          ring hbank r root e hy (k + 1)
          (by omega) (by omega)).1)

/-- Exact zero-prefix equivalence, including the full b-prefix
needed by the RL-only-token clause of J.resetWait. -/
theorem bankWindowIncomingZeroPrefixReadSetFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root e : Fin n)
    (hy : ring.rightNeighbor e = root) (last : Nat) :
    bankWindowZeroPrefix ring (renewalBankNext ring r e) root last ↔
      bankWindowZeroPrefix ring r root last := by
  unfold bankWindowZeroPrefix
  constructor
  · intro hz j hj
    have hbit := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank r root e hy (j.val + 1)
        (by omega) (by omega)).1)
    rw [← hbit]
    exact hz j hj
  · intro hz j hj
    have hbit := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank r root e hy (j.val + 1)
        (by omega) (by omega)).1)
    rw [hbit]
    exact hz j hj

/-- Exact only-token equivalence for any carrier i, not
merely the source of the incoming interaction. Consumer:
J.resetWait, incrementExact, compareExact and uniqueness. -/
theorem bankWindowIncomingOnlyTokenReadSetFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root e i : Fin n)
    (hy : ring.rightNeighbor e = root) :
    bankWindowOnlyToken ring (renewalBankNext ring r e) root i ↔
      bankWindowOnlyToken ring r root i := by
  unfold bankWindowOnlyToken
  constructor
  · intro honly j ht
    have htok := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank r root e hy (j.val + 1)
        (by omega) (by omega)).1)
    have hnew :
        ((renewalBankNext ring r e).1
          (Counter.site ring root (j.val + 1))).tok ≠ .E := by
      rw [htok]
      exact ht
    exact honly j hnew
  · intro honly j ht
    have htok := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank r root e hy (j.val + 1)
        (by omega) (by omega)).1)
    have hold :
        (r.1 (Counter.site ring root (j.val + 1))).tok ≠ .E := by
      rw [← htok]
      exact ht
    exact honly j hold

/-- A digit is tainted after an incoming-root edge exactly
when it was tainted before it. Consumer: inheritedClean,
IWAIT/CWAIT uniqueness, proto and orphan. -/
theorem bankWindowIncomingTaintedReadSetFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (j : Fin (compileAdvice (ceilLogTwo n)).b) :
    BankWindowTainted (renewalBankNext ring r e)
      (Counter.site ring root (j.val + 1)) ↔
    BankWindowTainted r
      (Counter.site ring root (j.val + 1)) := by
  have hghost := (bankWindowIncomingDigitReadSetFrame
    ring hbank r root e hy (j.val + 1)
    (by omega) (by omega)).2
  unfold BankWindowTainted
  rw [hghost]

/-- The exact uncapped binary value of an origin at the
incoming root is unchanged: only the root itself can change.
Consumer: J.compareExact and phaseFlags credit. -/
theorem bankWindowIncomingBinaryValueReadSetFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hy : ring.rightNeighbor e = o.root) :
    bankOriginBinaryValue ring (renewalBankNext ring r e).1 o =
      bankOriginBinaryValue ring r.1 o := by
  have hbits :
      (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
        if ((renewalBankNext ring r e).1
          (Counter.site ring o.root (j.val + 1))).bit
        then 2 ^ j.val else 0) =
      (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
        if (r.1 (Counter.site ring o.root (j.val + 1))).bit
        then 2 ^ j.val else 0) := by
    funext j
    have hbit := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank r o.root e hy (j.val + 1)
        (by omega) (by omega)).1)
    rw [hbit]
  exact congrArg
    (fun f : Fin (compileAdvice (ceilLogTwo n)).b → Nat =>
      (List.ofFn f).sum) hbits

/-- The comparator's exact bit-prefix predicate is invariant
at the incoming root. Consumer: CR0/CR1 and CL0/CL1 flags. -/
theorem bankWindowIncomingComparatorPrefixReadSetFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hy : ring.rightNeighbor e = o.root) (last : Nat) :
    bankComparatorPrefixMatched ring
      (renewalBankNext ring r e) o last ↔
    bankComparatorPrefixMatched ring r o last := by
  unfold bankComparatorPrefixMatched
  constructor
  · intro hm j hj
    have hbit := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank r o.root e hy (j.val + 1)
        (by omega) (by omega)).1)
    rw [← hbit]
    exact hm j hj
  · intro hm j hj
    have hbit := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank r o.root e hy (j.val + 1)
        (by omega) (by omega)).1)
    rw [hbit]
    exact hm j hj

/-- The proto antecedent, including its first bad PACK role,
is unchanged in an incoming PACK-zero responder branch.
Consumer: J.proto at this root. -/
theorem bankWindowIncomingProtoReadSetFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (hyPack : (r.1 root).pack.val = 0)
    (hpostPack :
      ((renewalBankNext ring r e).1 root).pack.val = 0)
    (limit : Nat) :
    BankWindowProtoRun ring (renewalBankNext ring r e)
      root limit ↔ BankWindowProtoRun ring r root limit := by
  unfold BankWindowProtoRun
  constructor
  · rintro ⟨hl, hp, hbad⟩
    refine ⟨hl, ?_, ?_⟩
    · intro j hj
      have heq := bankWindowIncomingPackReadSetFrame
        ring hbank r root e hy hyPack hpostPack j (by omega)
      rw [← heq]
      exact hp j hj
    · have heq := bankWindowIncomingPackReadSetFrame
        ring hbank r root e hy hyPack hpostPack
        (limit + 1) (by omega)
      rw [heq] at hbad
      exact hbad
  · rintro ⟨hl, hp, hbad⟩
    refine ⟨hl, ?_, ?_⟩
    · intro j hj
      have heq := bankWindowIncomingPackReadSetFrame
        ring hbank r root e hy hyPack hpostPack j (by omega)
      rw [heq]
      exact hp j hj
    · have heq := bankWindowIncomingPackReadSetFrame
        ring hbank r root e hy hyPack hpostPack
        (limit + 1) (by omega)
      rw [heq]
      exact hbad

/-- An orphan owner at an unchanged incoming PACK-zero root
is exactly an old orphan owner. Consumer: J.orphan. -/
theorem bankWindowIncomingOrphanReadSetFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (hyPack : (r.1 root).pack.val = 0)
    (hpostPack :
      ((renewalBankNext ring r e).1 root).pack.val = 0)
    (j : Fin (compileAdvice (ceilLogTwo n)).b) :
    BankWindowOrphanOwner ring (renewalBankNext ring r e)
      root j ↔ BankWindowOrphanOwner ring r root j := by
  unfold BankWindowOrphanOwner
  constructor
  · rintro ⟨_, hrole, hbad⟩
    refine ⟨hyPack, ?_, ?_⟩
    · have heq := bankWindowIncomingPackReadSetFrame
        ring hbank r root e hy hyPack hpostPack
        (j.val + 1) (by omega)
      rw [heq] at hrole
      exact hrole
    · intro hp
      apply hbad
      intro k hk
      have heq := bankWindowIncomingPackReadSetFrame
        ring hbank r root e hy hyPack hpostPack k (by omega)
      rw [heq]
      exact hp k hk
  · rintro ⟨_, hrole, hbad⟩
    refine ⟨hpostPack, ?_, ?_⟩
    · have heq := bankWindowIncomingPackReadSetFrame
        ring hbank r root e hy hyPack hpostPack
        (j.val + 1) (by omega)
      rw [heq]
      exact hrole
    · intro hp
      apply hbad
      intro k hk
      have heq := bankWindowIncomingPackReadSetFrame
        ring hbank r root e hy hyPack hpostPack k (by omega)
      rw [← heq]
      exact hp k hk

/-- A new scoped window at the stable root was already PACK
complete, provided the old root was grant-free. This supplies
the OLD J premise for all survivor-field transports. -/
theorem bankWindowIncomingScopeBackward
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (hyPack : (r.1 root).pack.val = 0)
    (hpostPack :
      ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hgrantOld : (r.1 root).grant = false)
    (hscope : BankWindowScope ring (renewalBankNext ring r e) root) :
    BankWindowScope ring r root := by
  constructor
  · intro j hj
    have hpack := hscope.1 j hj
    have heq := bankWindowIncomingPackReadSetFrame
      ring hbank r root e hy hyPack hpostPack j hj
    rw [heq] at hpack
    exact hpack
  · exact hgrantOld

/-- Actual RWAIT incoming-edge continuation transports the
ENTIRE leftmost pending-front witness, including the strong RL
only-token and full-zero clauses. Consumer: J.resetWait, IN/B0.
This uses the merged bankWindowIncomingRootCoreStep for the
real physical and controller survival rather than assuming it. -/
theorem bankWindowIncomingResetWaitSurvivor
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpostPack : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hgrantOld : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).grant = false)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).mode = .RWAIT)
    (hlease : 1 < ((rbRun ring
      (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).lease.val) :
    ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
      (ring.rightNeighbor e)).mode = .RWAIT ∧
    (BankWindowScope ring
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e)
      (ring.rightNeighbor e) →
    ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
      (ring.rightNeighbor e)).controller = .waiting [] →
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n),
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1))).worker =
        .pending rho ∧
      (((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1))).tok = .RR ∨
       ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1))).tok = .RL) ∧
      bankWindowZeroPrefix ring
        (renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e)
        (ring.rightNeighbor e) (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        k.val < j.val →
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
          (Counter.site ring (ring.rightNeighbor e) (k.val + 1))).tok = .E) ∧
      (((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1))).tok = .RL →
        bankWindowOnlyToken ring
          (renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e)
          (ring.rightNeighbor e)
          (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) ∧
        bankWindowZeroPrefix ring
          (renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e)
          (ring.rightNeighbor e)
          (compileAdvice (ceilLogTwo n)).b)) := by
  have hcore := bankWindowIncomingRootCoreStep
    ring hn hbank seed pre e hJ hy
  have hkeep :=
    ((hcore.2.2.2.2.2 hpostPack hgrantOld hmodeOld).1 hlease)
  refine ⟨hkeep.1, ?_⟩
  intro hscope hcontroller
  have hscopeOld := bankWindowIncomingScopeBackward
    ring hbank (rbRun ring (renewalBankStart ring seed) pre)
    (ring.rightNeighbor e) e rfl hy hpostPack hgrantOld hscope
  have hcontrollerOld :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites
        (ring.rightNeighbor e)).controller = .waiting [] := by
    rw [hkeep.2] at hcontroller
    exact hcontroller
  obtain ⟨j, rho, hw, ht, hz, hearlier, hrl⟩ :=
    hJ.resetWait (ring.rightNeighbor e)
      hscopeOld hmodeOld hcontrollerOld
  refine ⟨j, rho, ?_, ?_, ?_, ?_, ?_⟩
  · have hf := (bankWindowIncomingDigitReadSetFrame
      ring hbank (rbRun ring (renewalBankStart ring seed) pre)
      (ring.rightNeighbor e) e rfl (j.val + 1)
      (by omega) (by omega)).2
    rw [hf]
    exact hw
  · have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank (rbRun ring (renewalBankStart ring seed) pre)
        (ring.rightNeighbor e) e rfl (j.val + 1)
        (by omega) (by omega)).1)
    rw [hf]
    exact ht
  · exact (bankWindowIncomingZeroPrefixReadSetFrame
      ring hbank (rbRun ring (renewalBankStart ring seed) pre)
      (ring.rightNeighbor e) e rfl (j.val + 1)).2 hz
  · intro k hk
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank (rbRun ring (renewalBankStart ring seed) pre)
        (ring.rightNeighbor e) e rfl (k.val + 1)
        (by omega) (by omega)).1)
    rw [hf]
    exact hearlier k hk
  · intro hrlPost
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank (rbRun ring (renewalBankStart ring seed) pre)
        (ring.rightNeighbor e) e rfl (j.val + 1)
        (by omega) (by omega)).1)
    have hrlOld :
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (Counter.site ring (ring.rightNeighbor e)
            (j.val + 1))).tok = .RL := by
      rw [hf] at hrlPost
      exact hrlPost
    obtain ⟨honly, hzero⟩ := hrl hrlOld
    exact ⟨
      (bankWindowIncomingOnlyTokenReadSetFrame
        ring hbank (rbRun ring (renewalBankStart ring seed) pre)
        (ring.rightNeighbor e) e
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1))
        rfl).2 honly,
      (bankWindowIncomingZeroPrefixReadSetFrame
        ring hbank (rbRun ring (renewalBankStart ring seed) pre)
        (ring.rightNeighbor e) e rfl
        (compileAdvice (ceilLogTwo n)).b).2 hzero⟩

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankHeadThreshold
open L3.BankCounterRows
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! Incoming nonroot source, stable PACK-zero responder: IWAIT/CWAIT. -/

/-- The literal BANK pair, not an abstract timeout model:
a nonroot source cannot service a returning token at its
PACK-zero responder. Consumer: J incoming IWAIT/CWAIT modes,
ledger IN/B0. -/
private theorem bankWindowIncomingOtherWaitSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0)
    (hg : y.grant = false)
    (hm : y.mode = .IWAIT ∨ y.mode = .CWAIT) :
    (bankPair x y 0 b theta).2.mode =
      (if 1 < y.lease then y.mode else .RESET) := by
  rcases hm with hi | hc
  · by_cases hl : 1 < y.lease
    · simp [bankPair, hx, hy, hg, hi, hl, isWaitMode] <;>
        repeat (first | rfl | split)
    · simp [bankPair, hx, hy, hg, hi, hl, isWaitMode] <;>
        repeat (first | rfl | split)
  · by_cases hl : 1 < y.lease
    · simp [bankPair, hx, hy, hg, hc, hl, isWaitMode] <;>
        repeat (first | rfl | split)
    · simp [bankPair, hx, hy, hg, hc, hl, isWaitMode] <;>
        repeat (first | rfl | split)

/-- Physical projection of the actual masked reference step,
obtained from the selected BANK triple and the symbolic pair.
Consumer: incoming IWAIT/CWAIT continuation/expiration. -/
private theorem bankWindowIncomingOtherWaitPhysicalMode
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hpost :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val = 0)
    (hg : (r.1 (ring.rightNeighbor e)).grant = false)
    (hm : (r.1 (ring.rightNeighbor e)).mode = .IWAIT ∨
      (r.1 (ring.rightNeighbor e)).mode = .CWAIT) :
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).mode =
      (if 1 < (r.1 (ring.rightNeighbor e)).lease.val
       then (r.1 (ring.rightNeighbor e)).mode
       else .RESET) := by
  have hx := bankWindowIncomingStableSourceNonzero
    ring hn r e hy hpost
  have hp := bankWindowExactResponderPack ring r e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hnext :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 0 :=
    hp.symm.trans hpost
  have hsymbol := bankWindowIncomingOtherWaitSymbolic
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    (by change (r.1 e).pack.val ≠ 0; exact hx)
    (by change (r.1 (ring.rightNeighbor e)).pack.val = 0; exact hy)
    (by change (r.1 (ring.rightNeighbor e)).grant = false; exact hg)
    (by change
      (r.1 (ring.rightNeighbor e)).mode = .IWAIT ∨
      (r.1 (ring.rightNeighbor e)).mode = .CWAIT; exact hm)
  have hraw :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode =
      (if 1 < (r.1 (ring.rightNeighbor e)).lease.val
       then (r.1 (ring.rightNeighbor e)).mode
       else .RESET) := by
    unfold Counter.resetBankOld
    rw [hnext]
    exact hsymbol
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank r e).2
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((renewalBankNext ring r e).1
    (ring.rightNeighbor e)).mode =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode at hmode
  exact hmode.trans hraw

/-- On a real rbRun prefix, an incoming IWAIT or CWAIT
with old grant false either retains exactly its OLD ghost
controller and physical mode, or expires to RESET/empty.
This uses J.frame after the real step to exclude the
spurious empty-controller branch of rbBankNonrootControllerPair.
Consumer: J.compareExact, phaseFlags, tainted uniqueness,
inheritedClean, proto and orphan on IN/B0. -/
private theorem bankWindowIncomingOtherWaitExact
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hy : ((rbRun ring
      (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hg : ((rbRun ring
      (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).grant = false)
    (hm : ((rbRun ring
      (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).mode = .IWAIT ∨
      ((rbRun ring
      (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).mode = .CWAIT) :
    (1 < ((rbRun ring
        (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).lease.val →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
          (ring.rightNeighbor e)).mode =
        ((rbRun ring
          (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).mode ∧
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller =
        ((rbRun ring
          (renewalBankStart ring seed) pre).2.sites
          (ring.rightNeighbor e)).controller) ∧
    (((rbRun ring
        (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).lease.val ≤ 1 →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
          (ring.rightNeighbor e)).mode = .RESET ∧
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller = .empty) := by
  have hsource := bankWindowIncomingStableSourceNonzero
    ring hn (rbRun ring (renewalBankStart ring seed) pre)
    e hy hpost
  have hmode := bankWindowIncomingOtherWaitPhysicalMode
    ring hn hbank
    (rbRun ring (renewalBankStart ring seed) pre)
    e hy hpost hg hm
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  have hselected := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n)
    (rbRun ring (renewalBankStart ring seed) pre) e).2.2.2
  have hctrl := (rbBankNonrootControllerPair
    (compileAdvice (ceilLogTwo n))
    (rbRun ring (renewalBankStart ring seed) pre).2
    e (ring.rightNeighbor e)
    ((rbRun ring (renewalBankStart ring seed) pre).1 e)
    ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)) hsource).2
  constructor
  · intro hlease
    have hnewmode :
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
          (ring.rightNeighbor e)).mode =
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).mode := by
      rw [hmode]
      simp [hlease]
    have hwshape := (hframe (ring.rightNeighbor e)).1
    have hwaiting :
        ∃ atoms : List (RenewalBankAtom n),
          ((renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
              (ring.rightNeighbor e)).controller = .waiting atoms := by
      rcases hm with hi | hc
      · simpa [bankInFlightControllerShape, hpost, hnewmode, hi]
          using hwshape
      · simpa [bankInFlightControllerShape, hpost, hnewmode, hc]
          using hwshape
    have hnotEmpty :
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller ≠ .empty := by
      intro hempty
      obtain ⟨atoms, hw⟩ := hwaiting
      rw [hempty] at hw
      cases hw
    have hselect := congrArg
      (fun s : RenewalBankSite n => s.controller) hselected
    change ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
      (ring.rightNeighbor e)).controller =
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n))
        (rbRun ring (renewalBankStart ring seed) pre).2
        e (ring.rightNeighbor e)
        ((rbRun ring (renewalBankStart ring seed) pre).1 e)
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e))).2.controller at hselect
    have hctrlExact :
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller =
        ((rbRun ring
          (renewalBankStart ring seed) pre).2.sites
          (ring.rightNeighbor e)).controller := by
      rcases hctrl with hzero | hwait
      · have he := hselect.trans hzero
        exact False.elim (hnotEmpty he)
      · have hleaseWait :
            renewalBankWaitSlot
              ((rbRun ring (renewalBankStart ring seed) pre).1
                (ring.rightNeighbor e)).mode
              ((rbRun ring (renewalBankStart ring seed) pre).1
                (ring.rightNeighbor e)).lease.val
              ((rbRun ring (renewalBankStart ring seed) pre).2.sites
                (ring.rightNeighbor e)).controller =
            ((rbRun ring (renewalBankStart ring seed) pre).2.sites
              (ring.rightNeighbor e)).controller := by
          rcases hm with hi | hc
          · simp [renewalBankWaitSlot, hi, hlease, isWaitMode]
          · simp [renewalBankWaitSlot, hc, hlease, isWaitMode]
        exact hselect.trans (hwait.trans hleaseWait)
    exact ⟨hnewmode, hctrlExact⟩
  · intro hlease
    have hshort :
        ¬ 1 < ((rbRun ring
          (renewalBankStart ring seed) pre).1
            (ring.rightNeighbor e)).lease.val := by omega
    have hnewmode :
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1
          (ring.rightNeighbor e)).mode = .RESET := by
      rw [hmode]
      simp [hshort]
    have hrootshape := (hframe (ring.rightNeighbor e)).1
    have hnewcontroller :
        ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller = .empty := by
      simpa [bankInFlightControllerShape, hpost, hnewmode]
        using hrootshape
    exact ⟨hnewmode, hnewcontroller⟩

/-- The exact incoming IWAIT survivor/expiry dichotomy.
Consumer: IN/B0 and J.incrementExact/iwaitTaintedUnique. -/
theorem bankWindowIncomingIwaitExact
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).mode = .IWAIT) :
    (1 < ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).lease.val →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).mode = .IWAIT ∧
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        (ring.rightNeighbor e)).controller =
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites
        (ring.rightNeighbor e)).controller) ∧
    (((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).lease.val ≤ 1 →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).mode = .RESET ∧
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        (ring.rightNeighbor e)).controller = .empty) := by
  have h := bankWindowIncomingOtherWaitExact ring hn hbank
    seed pre e hJ hy hpost hg (Or.inl hm)
  constructor
  · intro hl
    obtain ⟨hmode, hc⟩ := h.1 hl
    exact ⟨hmode.trans hm, hc⟩
  · exact h.2

/-- The exact incoming CWAIT survivor/expiry dichotomy.
Consumer: IN/B0 and J.phaseFlags/compareExact/cwaitTaintedUnique. -/
theorem bankWindowIncomingCwaitExact
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).mode = .CWAIT) :
    (1 < ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).lease.val →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).mode = .CWAIT ∧
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        (ring.rightNeighbor e)).controller =
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites
        (ring.rightNeighbor e)).controller) ∧
    (((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).lease.val ≤ 1 →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).mode = .RESET ∧
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        (ring.rightNeighbor e)).controller = .empty) := by
  have h := bankWindowIncomingOtherWaitExact ring hn hbank
    seed pre e hJ hy hpost hg (Or.inr hm)
  constructor
  · intro hl
    obtain ⟨hmode, hc⟩ := h.1 hl
    exact ⟨hmode.trans hm, hc⟩
  · exact h.2

/-! Read-set transport for origin workers and scoped uniqueness. -/

/-- Actual post-step receipt provenance anchors any genuine
worker with an in-band PACK role at its origin's digit site.
Consumer: the inside/outside split in phaseUnique,
phaseFlags and compareExact. This does not silently assert
that every worker automatically has an in-band role. -/
theorem bankWindowIncomingPostWorkerAnchor
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e i : Fin n) (o : RenewalBankOrigin n)
    (p : RenewalBankPayload n)
    (hw :
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker =
      .payload p)
    (ho : p.origin = some o)
    (hlo : 1 ≤ ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val)
    (hhi : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val ≤
      (compileAdvice (ceilLogTwo n)).b) :
    i = Counter.site ring o.root
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val := by
  have hreceipt := rbReceiptInvBankWordOfInv
    ring (by omega : 2 ≤ n) seed hbank (pre ++ [e])
  have hword :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e := by
    rw [rbRunAppend]
    rfl
  rw [hword] at hreceipt
  exact hreceipt.workerSite i p o hw ho hlo hhi

/-- A surviving genuine comparison worker at an origin-root
digit inherits the old physical comparison-token uniqueness
and all four exact comparison flags. In particular an
out-of-window worker is NOT covered by this statement.
Consumer: J.phaseUnique and J.phaseFlags, IN/B0. -/
theorem bankWindowIncomingComparatorDigitSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (e : Fin n) (o : RenewalBankOrigin n)
    (p : RenewalBankPayload n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hy : ring.rightNeighbor e = o.root)
    (hmode : (r.1 o.root).mode = .CWAIT)
    (hcomp :
      BankComparatorOriginWorker ring
        (renewalBankNext ring r e) o
        (Counter.site ring o.root (j.val + 1)) p) :
    (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((renewalBankNext ring r e).1
          (Counter.site ring o.root (k.val + 1))).tok →
      Counter.site ring o.root (k.val + 1) =
        Counter.site ring o.root (j.val + 1)) ∧
    (((renewalBankNext ring r e).1
      (Counter.site ring o.root (j.val + 1))).tok = .CR1 →
        bankComparatorPrefixMatched ring
          (renewalBankNext ring r e) o
          ((renewalBankNext ring r e).1
            (Counter.site ring o.root (j.val + 1))).pack.val) ∧
    (((renewalBankNext ring r e).1
      (Counter.site ring o.root (j.val + 1))).tok = .CR0 →
        ¬ bankComparatorPrefixMatched ring
          (renewalBankNext ring r e) o
          ((renewalBankNext ring r e).1
            (Counter.site ring o.root (j.val + 1))).pack.val) ∧
    (((renewalBankNext ring r e).1
      (Counter.site ring o.root (j.val + 1))).tok = .CL1 →
        bankComparatorPrefixMatched ring
          (renewalBankNext ring r e) o
          (compileAdvice (ceilLogTwo n)).b) ∧
    (((renewalBankNext ring r e).1
      (Counter.site ring o.root (j.val + 1))).tok = .CL0 →
        ¬ bankComparatorPrefixMatched ring
          (renewalBankNext ring r e) o
          (compileAdvice (ceilLogTwo n)).b) := by
  have hframe := bankWindowIncomingDigitReadSetFrame
    ring hbank r o.root e hy (j.val + 1)
    (by omega) (by omega)
  have hghost := hframe.2
  have htok := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
    hframe.1
  have hpack := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
    hframe.1
  have hcompOld :
      BankComparatorOriginWorker ring r o
        (Counter.site ring o.root (j.val + 1)) p := by
    unfold BankComparatorOriginWorker at hcomp ⊢
    rcases hcomp with ⟨hw, ho, hc⟩
    refine ⟨?_, ho, ?_⟩
    · rw [← hghost]
      exact hw
    · rw [← htok]
      exact hc
  have hunique := hJ.phaseUnique o
    (Counter.site ring o.root (j.val + 1)) p hcompOld hmode
  have hflags := hJ.phaseFlags o
    (Counter.site ring o.root (j.val + 1)) p hcompOld hmode
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hnew
    have hk := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank r o.root e hy (k.val + 1)
        (by omega) (by omega)).1)
    rw [hk] at hnew
    exact hunique k hnew
  · intro ht
    have hold : (r.1
        (Counter.site ring o.root (j.val + 1))).tok = .CR1 := by
      rw [← htok]
      exact ht
    rw [hpack]
    exact (bankWindowIncomingComparatorPrefixReadSetFrame
      ring hbank r e o hy
      (r.1 (Counter.site ring o.root (j.val + 1))).pack.val).2
      (hflags.1 hold)
  · intro ht hmatch
    have hold : (r.1
        (Counter.site ring o.root (j.val + 1))).tok = .CR0 := by
      rw [← htok]
      exact ht
    rw [hpack] at hmatch
    exact (hflags.2.1 hold)
      ((bankWindowIncomingComparatorPrefixReadSetFrame
        ring hbank r e o hy
        (r.1 (Counter.site ring o.root (j.val + 1))).pack.val).1
        hmatch)
  · intro ht
    have hold : (r.1
        (Counter.site ring o.root (j.val + 1))).tok = .CL1 := by
      rw [← htok]
      exact ht
    exact (bankWindowIncomingComparatorPrefixReadSetFrame
      ring hbank r e o hy
      (compileAdvice (ceilLogTwo n)).b).2 (hflags.2.2.1 hold)
  · intro ht hmatch
    have hold : (r.1
        (Counter.site ring o.root (j.val + 1))).tok = .CL0 := by
      rw [← htok]
      exact ht
    exact (hflags.2.2.2 hold)
      ((bankWindowIncomingComparatorPrefixReadSetFrame
        ring hbank r e o hy
        (compileAdvice (ceilLogTwo n)).b).1 hmatch)

/-- When the comparator's carrier is a framed digit of its
origin root, the exact comparison payload/credit survives an
incoming root edge with the unchanged waiting controller.
The worker outside this digit family remains a separate
global obligation. Consumer: J.compareExact, IN/B0. -/
theorem bankWindowIncomingCompareDigitSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (e : Fin n) (o : RenewalBankOrigin n)
    (p : RenewalBankPayload n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hy : ring.rightNeighbor e = o.root)
    (hm : (r.1 o.root).mode = .CWAIT)
    (hcontrollerKeep :
      ((renewalBankNext ring r e).2.sites o.root).controller =
        (r.2.sites o.root).controller)
    (hw :
      ((renewalBankNext ring r e).2.sites
        (Counter.site ring o.root (j.val + 1))).worker = .payload p)
    (ho : p.origin = some o)
    (hc :
      ((renewalBankNext ring r e).2.sites o.root).controller =
        .waiting []) :
    bankWindowOnlyToken ring (renewalBankNext ring r e)
      o.root (Counter.site ring o.root (j.val + 1)) ∧
    BankTrialLiveComparisonToken
      ((renewalBankNext ring r e).1
        (Counter.site ring o.root (j.val + 1))).tok ∧
    p.heads = bankOriginBinaryValue ring
      (renewalBankNext ring r e).1 o ∧
    bankOriginBinaryValue ring
      (renewalBankNext ring r e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K := by
  have hframe := bankWindowIncomingDigitReadSetFrame
    ring hbank r o.root e hy (j.val + 1)
    (by omega) (by omega)
  have hworkerOld :
      (r.2.sites
        (Counter.site ring o.root (j.val + 1))).worker = .payload p := by
    rw [← hframe.2]
    exact hw
  have hcontrollerOld :
      (r.2.sites o.root).controller = .waiting [] := by
    rw [← hcontrollerKeep]
    exact hc
  obtain ⟨honly, htok, hcredit, hbound⟩ :=
    hJ.compareExact o (Counter.site ring o.root (j.val + 1))
      p hworkerOld ho hm hcontrollerOld
  have htokenFrame := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
    hframe.1
  have hbinary := bankWindowIncomingBinaryValueReadSetFrame
    ring hbank r e o hy
  refine ⟨(bankWindowIncomingOnlyTokenReadSetFrame
    ring hbank r o.root e
    (Counter.site ring o.root (j.val + 1)) hy).2 honly,
    ?_, ?_, ?_⟩
  · rw [htokenFrame]
    exact htok
  · rw [hbinary]
    exact hcredit
  · rw [hbinary]
    exact hbound

/-- IWAIT uniqueness at each framed digit survives a stable
incoming-root edge, provided the IWAIT controller survives.
Consumer: J.iwaitTaintedUnique in row IN/B0. -/
theorem bankWindowIncomingIwaitTaintedSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (hpackOld : (r.1 root).pack.val = 0)
    (hpackPost : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .IWAIT)
    (hcontrollerKeep :
      ((renewalBankNext ring r e).2.sites root).controller =
        (r.2.sites root).controller)
    (hscope : BankWindowScope ring
      (renewalBankNext ring r e) root)
    (hc : ((renewalBankNext ring r e).2.sites root).controller =
      .waiting []) :
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (renewalBankNext ring r e)
        (Counter.site ring root (j.val + 1)) →
      ∃ o p,
        ((renewalBankNext ring r e).2.sites
          (Counter.site ring root (j.val + 1))).worker = .payload p ∧
        p.origin = some o ∧ o.root = root ∧
        bankWindowOnlyToken ring (renewalBankNext ring r e)
          root (Counter.site ring root (j.val + 1)) := by
  have hscopeOld := bankWindowIncomingScopeBackward
    ring hbank r root e hy hpackOld hpackPost hg hscope
  have hcOld : (r.2.sites root).controller = .waiting [] := by
    rw [← hcontrollerKeep]
    exact hc
  intro j ht
  have htOld := (bankWindowIncomingTaintedReadSetFrame
    ring hbank r root e hy j).1 ht
  obtain ⟨o, p, hw, ho, hroot, honly⟩ :=
    hJ.iwaitTaintedUnique root hscopeOld hm hcOld j htOld
  refine ⟨o, p, ?_, ho, hroot, ?_⟩
  · rw [(bankWindowIncomingDigitReadSetFrame
      ring hbank r root e hy (j.val + 1)
      (by omega) (by omega)).2]
    exact hw
  · exact (bankWindowIncomingOnlyTokenReadSetFrame
      ring hbank r root e
      (Counter.site ring root (j.val + 1)) hy).2 honly

/-- The corresponding CWAIT result also transports its live
comparison token and the only-token property.
Consumer: J.cwaitTaintedUnique in row IN/B0. -/
theorem bankWindowIncomingCwaitTaintedSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (hpackOld : (r.1 root).pack.val = 0)
    (hpackPost : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .CWAIT)
    (hcontrollerKeep :
      ((renewalBankNext ring r e).2.sites root).controller =
        (r.2.sites root).controller)
    (hscope : BankWindowScope ring
      (renewalBankNext ring r e) root)
    (hc : ((renewalBankNext ring r e).2.sites root).controller =
      .waiting []) :
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (renewalBankNext ring r e)
        (Counter.site ring root (j.val + 1)) →
      ∃ o p,
        ((renewalBankNext ring r e).2.sites
          (Counter.site ring root (j.val + 1))).worker = .payload p ∧
        p.origin = some o ∧ o.root = root ∧
        BankTrialLiveComparisonToken
          ((renewalBankNext ring r e).1
            (Counter.site ring root (j.val + 1))).tok ∧
        bankWindowOnlyToken ring (renewalBankNext ring r e)
          root (Counter.site ring root (j.val + 1)) := by
  have hscopeOld := bankWindowIncomingScopeBackward
    ring hbank r root e hy hpackOld hpackPost hg hscope
  have hcOld : (r.2.sites root).controller = .waiting [] := by
    rw [← hcontrollerKeep]
    exact hc
  intro j ht
  have htOld := (bankWindowIncomingTaintedReadSetFrame
    ring hbank r root e hy j).1 ht
  obtain ⟨o, p, hw, ho, hroot, htoken, honly⟩ :=
    hJ.cwaitTaintedUnique root hscopeOld hm hcOld j htOld
  refine ⟨o, p, ?_, ho, hroot, ?_, ?_⟩
  · rw [(bankWindowIncomingDigitReadSetFrame
      ring hbank r root e hy (j.val + 1)
      (by omega) (by omega)).2]
    exact hw
  · rw [congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank r root e hy (j.val + 1)
        (by omega) (by omega)).1)]
    exact htoken
  · exact (bankWindowIncomingOnlyTokenReadSetFrame
      ring hbank r root e
      (Counter.site ring root (j.val + 1)) hy).2 honly

/-- With an unchanged controller and no old grant,
post-step inheritedClean follows from the genuinely OLD
scoped inherited-controller fact and digit taint framing.
Consumer: J.inheritedClean for surviving incoming owners. -/
theorem bankWindowIncomingInheritedCleanSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (hpackOld : (r.1 root).pack.val = 0)
    (hpackPost : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hg : (r.1 root).grant = false)
    (hcontrollerKeep :
      ((renewalBankNext ring r e).2.sites root).controller =
        (r.2.sites root).controller)
    (hscope : BankWindowScope ring
      (renewalBankNext ring r e) root)
    (hinherited : BankWindowInheritedController
      (renewalBankNext ring r e) root) :
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted (renewalBankNext ring r e)
        (Counter.site ring root (j.val + 1)) := by
  have hscopeOld := bankWindowIncomingScopeBackward
    ring hbank r root e hy hpackOld hpackPost hg hscope
  have hInheritedOld : BankWindowInheritedController r root := by
    rcases hinherited with ⟨atoms, hc, hne⟩ |
      ⟨p, hc, ho⟩
    · exact Or.inl ⟨atoms, by rw [← hcontrollerKeep]; exact hc, hne⟩
    · exact Or.inr ⟨p, by rw [← hcontrollerKeep]; exact hc, ho⟩
  intro j ht
  have htOld := (bankWindowIncomingTaintedReadSetFrame
    ring hbank r root e hy j).1 ht
  exact (hJ.inheritedClean root hscopeOld hInheritedOld j) htOld

/-- At a stable owner with unchanged physical mode and
controller, J.orphan is preserved even if its lease ticks.
All digit PACK/taint tests refer to the immutable digit sites.
Consumer: J.orphan in the continuing IN/B0 branch. -/
theorem bankWindowIncomingOrphanOwnerSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (hpackOld : (r.1 root).pack.val = 0)
    (hpackPost : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hmodeKeep : ((renewalBankNext ring r e).1 root).mode =
      (r.1 root).mode)
    (hcontrollerKeep :
      ((renewalBankNext ring r e).2.sites root).controller =
        (r.2.sites root).controller) :
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (renewalBankNext ring r e) root j →
      BankWindowTainted (renewalBankNext ring r e)
        (Counter.site ring root (j.val + 1)) →
      ((renewalBankNext ring r e).1 root).mode = .RESET ∨
      (((renewalBankNext ring r e).1 root).mode = .RWAIT ∧
        ((renewalBankNext ring r e).2.sites root).controller =
          .waiting []) := by
  intro j horphan htaint
  have holdOrphan := (bankWindowIncomingOrphanReadSetFrame
    ring hbank r root e hy hpackOld hpackPost j).1 horphan
  have holdTaint := (bankWindowIncomingTaintedReadSetFrame
    ring hbank r root e hy j).1 htaint
  rcases hJ.orphan root j holdOrphan holdTaint with hr | hw
  · exact Or.inl (hmodeKeep.trans hr)
  · exact Or.inr ⟨hmodeKeep.trans hw.1,
      hcontrollerKeep.trans hw.2⟩

/-! Proto and orphan owner fields at the incoming PACK-zero root. -/

/-- If the incoming physical mode and ghost controller survive,
the exact proto-run package survives too: forbidden genuine
controller, inherited cleanliness, leftmost pending RR witness,
and nonwait clean prefix. Consumer: J.proto, ledger IN/B0. -/
theorem bankWindowIncomingProtoOwnerSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (hpackOld : (r.1 root).pack.val = 0)
    (hpackPost : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hmodeKeep : ((renewalBankNext ring r e).1 root).mode =
      (r.1 root).mode)
    (hcontrollerKeep :
      ((renewalBankNext ring r e).2.sites root).controller =
        (r.2.sites root).controller)
    (limit : Nat)
    (hproto : BankWindowProtoRun ring
      (renewalBankNext ring r e) root limit) :
    (∀ p o,
      ((renewalBankNext ring r e).2.sites root).controller =
        .active p → p.origin = some o → False) ∧
    (BankWindowInheritedController (renewalBankNext ring r e)
      root →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted (renewalBankNext ring r e)
          (Counter.site ring root (j.val + 1))) ∧
    ((((renewalBankNext ring r e).1 root).mode = .RWAIT ∧
        ((renewalBankNext ring r e).2.sites root).controller =
          .waiting []) →
      ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit ∧
        ∃ rho : RenewalBankReceipt n,
          ((renewalBankNext ring r e).2.sites
            (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
          ((renewalBankNext ring r e).1
            (Counter.site ring root (j.val + 1))).tok = .RR ∧
          bankWindowZeroPrefix ring (renewalBankNext ring r e)
            root (j.val + 1) ∧
          (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
            k.val < j.val →
            ((renewalBankNext ring r e).1
              (Counter.site ring root (k.val + 1))).tok = .E)) ∧
    (((renewalBankNext ring r e).1 root).mode ≠ .RESET →
      ((renewalBankNext ring r e).1 root).mode ≠ .RWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted (renewalBankNext ring r e)
          (Counter.site ring root (j.val + 1))) := by
  have hprotoOld := (bankWindowIncomingProtoReadSetFrame
    ring hbank r root e hy hpackOld hpackPost limit).1 hproto
  have hold := hJ.proto root limit hprotoOld
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p o hactive horigin
    have hactiveOld :
        (r.2.sites root).controller = .active p := by
      rw [← hcontrollerKeep]
      exact hactive
    exact hold.1 p o hactiveOld horigin
  · intro hinherited j hj htaint
    have hinheritedOld : BankWindowInheritedController r root := by
      rcases hinherited with ⟨atoms, hc, hne⟩ |
        ⟨p, hc, ho⟩
      · exact Or.inl
          ⟨atoms, by rw [← hcontrollerKeep]; exact hc, hne⟩
      · exact Or.inr
          ⟨p, by rw [← hcontrollerKeep]; exact hc, ho⟩
    have htaintOld := (bankWindowIncomingTaintedReadSetFrame
      ring hbank r root e hy j).1 htaint
    exact (hold.2.1 hinheritedOld j hj) htaintOld
  · intro hwait
    have hwaitOld :
        (r.1 root).mode = .RWAIT ∧
        (r.2.sites root).controller = .waiting [] := by
      constructor
      · rw [← hmodeKeep]
        exact hwait.1
      · rw [← hcontrollerKeep]
        exact hwait.2
    obtain ⟨j, hj, rho, hw, ht, hz, hearlier⟩ :=
      hold.2.2.1 hwaitOld
    refine ⟨j, hj, rho, ?_, ?_, ?_, ?_⟩
    · rw [(bankWindowIncomingDigitReadSetFrame
        ring hbank r root e hy (j.val + 1)
        (by omega) (by omega)).2]
      exact hw
    · rw [congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        ((bankWindowIncomingDigitReadSetFrame
          ring hbank r root e hy (j.val + 1)
          (by omega) (by omega)).1)]
      exact ht
    · exact (bankWindowIncomingZeroPrefixReadSetFrame
        ring hbank r root e hy (j.val + 1)).2 hz
    · intro k hk
      rw [congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        ((bankWindowIncomingDigitReadSetFrame
          ring hbank r root e hy (k.val + 1)
          (by omega) (by omega)).1)]
      exact hearlier k hk
  · intro hnotReset hnotRwait j hj htaint
    have hnotOldReset : (r.1 root).mode ≠ .RESET := by
      intro he
      exact hnotReset (hmodeKeep.trans he)
    have hnotOldRwait : (r.1 root).mode ≠ .RWAIT := by
      intro he
      exact hnotRwait (hmodeKeep.trans he)
    exact (hold.2.2.2 hnotOldReset hnotOldRwait j hj)
      ((bankWindowIncomingTaintedReadSetFrame
        ring hbank r root e hy j).1 htaint)

/-- A PACK-zero root that has actually expired to RESET has
no controller or inherited authority; its PROTO clause and
ORPHAN mode alternative are automatically discharged, with
no assumptions on other roots or digit tokens.
Consumer: J.proto/J.orphan IN/B0 timeout and old-grant cases. -/
theorem bankWindowIncomingResetOwnerFields
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (hpostPack :
      ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hmode : ((renewalBankNext ring r e).1 root).mode = .RESET)
    (hframe : BankInFlightAligned ring (renewalBankNext ring r e)) :
    ((renewalBankNext ring r e).2.sites root).controller = .empty ∧
    ¬ BankWindowInheritedController (renewalBankNext ring r e) root ∧
    (∀ limit : Nat,
      BankWindowProtoRun ring (renewalBankNext ring r e)
        root limit →
      (∀ p o,
        ((renewalBankNext ring r e).2.sites root).controller =
          .active p → p.origin = some o → False) ∧
      (BankWindowInheritedController (renewalBankNext ring r e)
        root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted (renewalBankNext ring r e)
            (Counter.site ring root (j.val + 1))) ∧
      ((((renewalBankNext ring r e).1 root).mode = .RWAIT ∧
          ((renewalBankNext ring r e).2.sites root).controller =
            .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((renewalBankNext ring r e).2.sites
              (Counter.site ring root (j.val + 1))).worker =
                .pending rho ∧
            ((renewalBankNext ring r e).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring (renewalBankNext ring r e)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((renewalBankNext ring r e).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((renewalBankNext ring r e).1 root).mode ≠ .RESET →
        ((renewalBankNext ring r e).1 root).mode ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted (renewalBankNext ring r e)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring (renewalBankNext ring r e)
        root j →
      BankWindowTainted (renewalBankNext ring r e)
        (Counter.site ring root (j.val + 1)) →
      ((renewalBankNext ring r e).1 root).mode = .RESET ∨
      (((renewalBankNext ring r e).1 root).mode = .RWAIT ∧
        ((renewalBankNext ring r e).2.sites root).controller =
          .waiting [])) := by
  have hc :
      ((renewalBankNext ring r e).2.sites root).controller =
        .empty := by
    simpa [bankInFlightControllerShape, hpostPack, hmode]
      using (hframe root).1
  have hnInherited :
      ¬ BankWindowInheritedController
        (renewalBankNext ring r e) root := by
    intro hh
    rcases hh with ⟨atoms, hw, _⟩ | ⟨p, hw, _⟩
    · rw [hc] at hw
      cases hw
    · rw [hc] at hw
      cases hw
  refine ⟨hc, hnInherited, ?_, ?_⟩
  · intro limit _hproto
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p o hp _
      rw [hc] at hp
      cases hp
    · intro hinherited
      exact False.elim (hnInherited hinherited)
    · intro hh
      have hbad := hh.1
      rw [hmode] at hbad
      cases hbad
    · intro hnotReset
      exact False.elim (hnotReset hmode)
  · intro j _ _ 
    exact Or.inl hmode

/-! Additional digit-carrier and origin phase fields. -/

/-- A digit-carried comparator at the incoming root retains its
old completeness proof when that root stays in CWAIT and PACK
zero remains unchanged. Consumer: J.phaseComplete, IN/B0. -/
theorem bankWindowIncomingPhaseCompleteDigitSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (e : Fin n) (o : RenewalBankOrigin n)
    (p : RenewalBankPayload n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hy : ring.rightNeighbor e = o.root)
    (hpackOld : (r.1 o.root).pack.val = 0)
    (hpackPost : ((renewalBankNext ring r e).1 o.root).pack.val = 0)
    (hmodeOld : (r.1 o.root).mode = .CWAIT)
    (hcomp :
      BankComparatorOriginWorker ring (renewalBankNext ring r e)
        o (Counter.site ring o.root (j.val + 1)) p) :
    Counter.Complete ring (renewalBankNext ring r e).1 o.root := by
  have hframe := bankWindowIncomingDigitReadSetFrame
    ring hbank r o.root e hy (j.val + 1)
    (by omega) (by omega)
  have hcompOld :
      BankComparatorOriginWorker ring r o
        (Counter.site ring o.root (j.val + 1)) p := by
    unfold BankComparatorOriginWorker at hcomp ⊢
    rcases hcomp with ⟨hw, ho, ht⟩
    refine ⟨?_, ho, ?_⟩
    · rw [← hframe.2]
      exact hw
    · rw [← congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hframe.1]
      exact ht
  have hcomplete := hJ.phaseComplete o
    (Counter.site ring o.root (j.val + 1)) p hcompOld hmodeOld
  intro k hk
  rw [bankWindowIncomingPackReadSetFrame
    ring hbank r o.root e hy hpackOld hpackPost k hk]
  exact hcomplete k hk

/-- When the comparator worker is a framed origin digit and
the origin root's mode survives, the phase exclusions also
survive without inventing a new global phase invariant.
Consumer: J.phaseExcludes, IN/B0. -/
theorem bankWindowIncomingPhaseExcludesDigitSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (e : Fin n) (o : RenewalBankOrigin n)
    (p : RenewalBankPayload n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hy : ring.rightNeighbor e = o.root)
    (hmodeKeep :
      ((renewalBankNext ring r e).1 o.root).mode =
        (r.1 o.root).mode)
    (hcomp :
      BankComparatorOriginWorker ring (renewalBankNext ring r e)
        o (Counter.site ring o.root (j.val + 1)) p) :
    ((renewalBankNext ring r e).1 o.root).mode ≠ .ARMED ∧
    ((renewalBankNext ring r e).1 o.root).mode ≠ .CSTART ∧
    ((renewalBankNext ring r e).1 o.root).mode ≠ .IWAIT := by
  have hframe := bankWindowIncomingDigitReadSetFrame
    ring hbank r o.root e hy (j.val + 1)
    (by omega) (by omega)
  have hcompOld :
      BankComparatorOriginWorker ring r o
        (Counter.site ring o.root (j.val + 1)) p := by
    unfold BankComparatorOriginWorker at hcomp ⊢
    rcases hcomp with ⟨hw, ho, ht⟩
    refine ⟨?_, ho, ?_⟩
    · rw [← hframe.2]
      exact hw
    · rw [← congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hframe.1]
      exact ht
  have hold := hJ.phaseExcludes o
    (Counter.site ring o.root (j.val + 1)) p hcompOld
  rw [hmodeKeep]
  exact hold

/-- The exact uncapped IR/AL arithmetic survives when an IWAIT
payload carrier is a digit of the unchanged root and its
controller survives. The binary value, zero prefix, token,
worker, and PACK exponent are all transported from the SAME
physical digits. Consumer: J.incrementExact, IN/B0. -/
theorem bankWindowIncomingIncrementDigitSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (root e : Fin n) (o : RenewalBankOrigin n)
    (p : RenewalBankPayload n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hy : ring.rightNeighbor e = root)
    (horoot : o.root = root)
    (hpackOld : (r.1 root).pack.val = 0)
    (hpackPost : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hg : (r.1 root).grant = false)
    (hmodeOld : (r.1 root).mode = .IWAIT)
    (hcontrollerKeep :
      ((renewalBankNext ring r e).2.sites root).controller =
        (r.2.sites root).controller)
    (hscope : BankWindowScope ring (renewalBankNext ring r e) root)
    (hcontroller :
      ((renewalBankNext ring r e).2.sites root).controller =
        .waiting [])
    (hworker :
      ((renewalBankNext ring r e).2.sites
        (Counter.site ring root (j.val + 1))).worker = .payload p)
    (ho : p.origin = some o) :
    bankWindowOnlyToken ring (renewalBankNext ring r e)
      root (Counter.site ring root (j.val + 1)) ∧
    ((((renewalBankNext ring r e).1
        (Counter.site ring root (j.val + 1))).tok = .IR ∧
        bankWindowZeroPrefix ring (renewalBankNext ring r e)
          root ((renewalBankNext ring r e).1
            (Counter.site ring root (j.val + 1))).pack.val ∧
        p.heads =
          bankOriginBinaryValue ring (renewalBankNext ring r e).1 o +
            2 ^ ((renewalBankNext ring r e).1
              (Counter.site ring root (j.val + 1))).pack.val ∧
        bankOriginBinaryValue ring (renewalBankNext ring r e).1 o +
          2 ^ ((renewalBankNext ring r e).1
            (Counter.site ring root (j.val + 1))).pack.val ≤
              (compileAdvice (ceilLogTwo n)).K) ∨
      (((renewalBankNext ring r e).1
        (Counter.site ring root (j.val + 1))).tok = .AL ∧
        p.heads =
          bankOriginBinaryValue ring (renewalBankNext ring r e).1 o ∧
        bankOriginBinaryValue ring (renewalBankNext ring r e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K)) := by
  have hframe := bankWindowIncomingDigitReadSetFrame
    ring hbank r root e hy (j.val + 1)
    (by omega) (by omega)
  have hwOld :
      (r.2.sites (Counter.site ring root (j.val + 1))).worker =
        .payload p := by
    rw [← hframe.2]
    exact hworker
  have hcOld : (r.2.sites root).controller = .waiting [] := by
    rw [← hcontrollerKeep]
    exact hcontroller
  have hsOld := bankWindowIncomingScopeBackward
    ring hbank r root e hy hpackOld hpackPost hg hscope
  obtain ⟨honly, hbranch⟩ := hJ.incrementExact
    root o (Counter.site ring root (j.val + 1)) p
    hsOld hmodeOld hcOld hwOld ho horoot
  have htok := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
    hframe.1
  have hpack := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
    hframe.1
  have hbinary := bankWindowIncomingBinaryValueReadSetFrame
    ring hbank r e o (by rw [horoot]; exact hy)
  refine ⟨(bankWindowIncomingOnlyTokenReadSetFrame
    ring hbank r root e (Counter.site ring root (j.val + 1))
    hy).2 honly, ?_⟩
  rcases hbranch with ⟨hir, hzero, hhead, hbound⟩ |
    ⟨hal, hhead, hbound⟩
  · left
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [htok]
      exact hir
    · rw [hpack]
      exact (bankWindowIncomingZeroPrefixReadSetFrame
        ring hbank r root e hy
        (r.1 (Counter.site ring root (j.val + 1))).pack.val).2
        hzero
    · rw [hbinary, hpack]
      exact hhead
    · rw [hbinary, hpack]
      exact hbound
  · right
    refine ⟨?_, ?_, ?_⟩
    · rw [htok]
      exact hal
    · rw [hbinary]
      exact hhead
    · rw [hbinary]
      exact hbound

/-! Workers away from both selected endpoints. Their origin's
root remains a READ of J even though the worker site itself
is off-pair; the unchanged incoming mode/controller must be
used explicitly rather than assuming this read disappears. -/

/-- An off-pair comparison worker of the incoming responder's
origin has unchanged payload, token and PACK role; its
origin's digit read set is separately framed. Consequently
phaseUnique and all four phaseFlags transport when the
origin's CWAIT mode survives. Consumer: J.phaseUnique and
J.phaseFlags, second branch of the worker-site split. -/
theorem bankWindowIncomingComparatorOffPairSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (e i : Fin n) (o : RenewalBankOrigin n)
    (p : RenewalBankPayload n)
    (hy : ring.rightNeighbor e = o.root)
    (hiSource : i ≠ e) (hiRoot : i ≠ o.root)
    (hmode : (r.1 o.root).mode = .CWAIT)
    (hcomp :
      BankComparatorOriginWorker ring
        (renewalBankNext ring r e) o i p) :
    (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((renewalBankNext ring r e).1
          (Counter.site ring o.root (k.val + 1))).tok →
      Counter.site ring o.root (k.val + 1) = i) ∧
    (((renewalBankNext ring r e).1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (renewalBankNext ring r e) o
        ((renewalBankNext ring r e).1 i).pack.val) ∧
    (((renewalBankNext ring r e).1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (renewalBankNext ring r e) o
        ((renewalBankNext ring r e).1 i).pack.val) ∧
    (((renewalBankNext ring r e).1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (renewalBankNext ring r e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
    (((renewalBankNext ring r e).1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (renewalBankNext ring r e) o
        (compileAdvice (ceilLogTwo n)).b) := by
  have htarget : i ≠ ring.rightNeighbor e := by
    rw [hy]
    exact hiRoot
  have hframe := bankWindowExactOffPairFrame
    ring r e i hiSource htarget
  have htoken := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
    hframe.1
  have hpack := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
    hframe.1
  have hcompOld : BankComparatorOriginWorker ring r o i p := by
    unfold BankComparatorOriginWorker at hcomp ⊢
    rcases hcomp with ⟨hw, ho, ht⟩
    refine ⟨?_, ho, ?_⟩
    · rw [← hframe.2]
      exact hw
    · rw [← htoken]
      exact ht
  have hunique := hJ.phaseUnique o i p hcompOld hmode
  have hflags := hJ.phaseFlags o i p hcompOld hmode
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k ht
    have hk := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      ((bankWindowIncomingDigitReadSetFrame
        ring hbank r o.root e hy (k.val + 1)
        (by omega) (by omega)).1)
    rw [hk] at ht
    exact hunique k ht
  · intro ht
    have hold : (r.1 i).tok = .CR1 := by
      rw [← htoken]
      exact ht
    rw [hpack]
    exact (bankWindowIncomingComparatorPrefixReadSetFrame
      ring hbank r e o hy (r.1 i).pack.val).2
      (hflags.1 hold)
  · intro ht hmatch
    have hold : (r.1 i).tok = .CR0 := by
      rw [← htoken]
      exact ht
    rw [hpack] at hmatch
    exact (hflags.2.1 hold)
      ((bankWindowIncomingComparatorPrefixReadSetFrame
        ring hbank r e o hy (r.1 i).pack.val).1 hmatch)
  · intro ht
    have hold : (r.1 i).tok = .CL1 := by
      rw [← htoken]
      exact ht
    exact (bankWindowIncomingComparatorPrefixReadSetFrame
      ring hbank r e o hy
      (compileAdvice (ceilLogTwo n)).b).2
      (hflags.2.2.1 hold)
  · intro ht hmatch
    have hold : (r.1 i).tok = .CL0 := by
      rw [← htoken]
      exact ht
    exact (hflags.2.2.2 hold)
      ((bankWindowIncomingComparatorPrefixReadSetFrame
        ring hbank r e o hy
        (compileAdvice (ceilLogTwo n)).b).1 hmatch)

/-- J.compareExact for an off-pair worker rooted at the
incoming responder, with continuing CWAIT/empty waiting
controller. It is incorrect to drop the origin-root read:
its mode, controller, bit sum and token window are all
transferred explicitly here. Consumer: J.compareExact IN/B0. -/
theorem bankWindowIncomingCompareOffPairSurvivor
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (e i : Fin n) (o : RenewalBankOrigin n)
    (p : RenewalBankPayload n)
    (hy : ring.rightNeighbor e = o.root)
    (hiSource : i ≠ e) (hiRoot : i ≠ o.root)
    (hmodeOld : (r.1 o.root).mode = .CWAIT)
    (hcontrollerKeep :
      ((renewalBankNext ring r e).2.sites o.root).controller =
        (r.2.sites o.root).controller)
    (hworker :
      ((renewalBankNext ring r e).2.sites i).worker = .payload p)
    (ho : p.origin = some o)
    (hcontroller :
      ((renewalBankNext ring r e).2.sites o.root).controller =
        .waiting []) :
    bankWindowOnlyToken ring
      (renewalBankNext ring r e) o.root i ∧
    BankTrialLiveComparisonToken ((renewalBankNext ring r e).1 i).tok ∧
    p.heads = bankOriginBinaryValue ring
      (renewalBankNext ring r e).1 o ∧
    bankOriginBinaryValue ring
      (renewalBankNext ring r e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K := by
  have htarget : i ≠ ring.rightNeighbor e := by
    rw [hy]
    exact hiRoot
  have hframe := bankWindowExactOffPairFrame
    ring r e i hiSource htarget
  have hworkerOld : (r.2.sites i).worker = .payload p := by
    rw [← hframe.2]
    exact hworker
  have hcontrollerOld :
      (r.2.sites o.root).controller = .waiting [] := by
    rw [← hcontrollerKeep]
    exact hcontroller
  obtain ⟨honly, htoken, hcredit, hbound⟩ :=
    hJ.compareExact o i p hworkerOld ho hmodeOld hcontrollerOld
  have htokFrame := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
    hframe.1
  have hbinary := bankWindowIncomingBinaryValueReadSetFrame
    ring hbank r e o hy
  refine ⟨(bankWindowIncomingOnlyTokenReadSetFrame
    ring hbank r o.root e i hy).2 honly,
    ?_, ?_, ?_⟩
  · rw [htokFrame]
    exact htoken
  · rw [hbinary]
    exact hcredit
  · rw [hbinary]
    exact hbound

/-! Selected incoming source: genuine workers whose origin is
the responder root cannot hide at the predecessor. -/

/-- An in-band top-role source cannot hold a post-step genuine
payload originating at its immediate responder: the real
receipt worker-site anchor would place the predecessor inside
the responder's digit window, contradicting ring geometry.
Consumer: selected-source case for J.phaseFlags/compareExact. -/
theorem bankWindowIncomingTopSourceNoResponderOrigin
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (horoot : o.root = ring.rightNeighbor e)
    (htop :
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1 e).pack.val =
        (compileAdvice (ceilLogTwo n)).b)
    (hw :
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).worker =
        .payload p)
    (ho : p.origin = some o) : False := by
  have hb : 1 ≤ (compileAdvice (ceilLogTwo n)).b := by
    change 1 ≤ (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hanchor := bankWindowIncomingPostWorkerAnchor
    ring hn hbank seed pre e e o p hw ho
    (by rw [htop]; exact hb)
    (by rw [htop]; exact Nat.le_refl _)
  rw [htop, horoot] at hanchor
  have hneq := bankWindowIncomingPredecessorOutsideDigits
    ring hbank (ring.rightNeighbor e) e rfl
    (compileAdvice (ceilLogTwo n)).b hb (Nat.le_refl _)
  exact hneq hanchor

/-- An old spacer-role source keeps no ghost worker when it
enters a PACK-zero responder. This is the actual first-match
renewalBankPairMemory code (not a token-based assumption).
Consumer: source-endpoint comparator/taint split, IN/B0. -/
private theorem bankWindowIncomingSpacerSourceEmptyPair
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b + 1)
    (hy : y.pack.val = 0) :
    (renewalBankPairMemory c m e dest x y).1.worker = .empty := by
  have hnonzero : x.pack.val ≠ 0 := by omega
  have hnotInside : ¬ x.pack.val ≤ c.b := by omega
  have hnotLess : ¬ x.pack.val < c.b := by omega
  have hrole : packNext x.pack.val y.pack.val c.b = 0 := by
    rw [hx, hy]
    simp [packNext]
  have hroleZ : packNext (c.b + 1) 0 c.b = 0 := by
    simp [packNext]
  simp [renewalBankPairMemory, bankCell, hx, hy, hrole, hroleZ,
    hnonzero, hnotInside, hnotLess] <;>
      repeat (first | rfl | split)

/-- A real incoming edge with stable responder PACK zero
cannot leave a genuine source worker belonging to that
responder's origin. The top role is ruled out by receipt
provenance plus geometry; the spacer role clears the worker.
Consumer: selected-source case of global J.phaseUnique,
phaseFlags and compareExact, IN/B0. -/
theorem bankWindowIncomingSourceNoResponderOrigin
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hy :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val = 0)
    (hpost :
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).pack.val = 0)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (horoot : o.root = ring.rightNeighbor e)
    (hw :
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).worker =
          .payload p)
    (ho : p.origin = some o) : False := by
  have hpack := bankWindowExactResponderPack
    ring (rbRun ring (renewalBankStart ring seed) pre) e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hnext :
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 0 :=
    hpack.symm.trans hpost
  have hbound :=
    ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.isLt
  have hcap :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val <
        (compileAdvice (ceilLogTwo n)).b + 2 := by
    exact hbound
  by_cases hlt :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val <
        (compileAdvice (ceilLogTwo n)).b
  · rw [hy] at hnext
    simp [packNext, hlt] at hnext
  · by_cases htop :
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val =
          (compileAdvice (ceilLogTwo n)).b
    · have hsourcePack := bankWindowClosureRepairNonresponderPackFixed
        ring (by omega : 2 ≤ n)
        (rbRun ring (renewalBankStart ring seed) pre) e e
        (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
      have htopPost :
          ((renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e).1 e).pack.val =
            (compileAdvice (ceilLogTwo n)).b :=
        hsourcePack.trans htop
      exact bankWindowIncomingTopSourceNoResponderOrigin
        ring hn hbank seed pre e p o horoot htopPost hw ho
    · have hspacer :
          ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val =
            (compileAdvice (ceilLogTwo n)).b + 1 := by omega
      have hpair := bankWindowIncomingSpacerSourceEmptyPair
        (compileAdvice (ceilLogTwo n))
        (rbRun ring (renewalBankStart ring seed) pre).2
        e (ring.rightNeighbor e)
        ((rbRun ring (renewalBankStart ring seed) pre).1 e)
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e))
        hspacer hy
      have hselected := (rbReferenceSelectedPairFrame
        ring (by omega : 2 ≤ n)
        (rbRun ring (renewalBankStart ring seed) pre) e).2.2.1
      have hselectedWorker := congrArg
        (fun s : RenewalBankSite n => s.worker) hselected
      change ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).worker =
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n))
          (rbRun ring (renewalBankStart ring seed) pre).2
          e (ring.rightNeighbor e)
          ((rbRun ring (renewalBankStart ring seed) pre).1 e)
          ((rbRun ring (renewalBankStart ring seed) pre).1
            (ring.rightNeighbor e))).1.worker at hselectedWorker
      have hempty := hselectedWorker.trans hpair
      rw [hempty] at hw
      cases hw

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankCounterRows
open L3.BankHeadThreshold
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! Field-granular observational equality; no lease or service is read. -/

def bankWindowReadPack {n : Nat} (r s : RenewalBankReference n)
    (z : Fin n) : Prop := (s.1 z).pack.val = (r.1 z).pack.val

def bankWindowReadMode {n : Nat} (r s : RenewalBankReference n)
    (z : Fin n) : Prop := (s.1 z).mode = (r.1 z).mode

def bankWindowReadTok {n : Nat} (r s : RenewalBankReference n)
    (z : Fin n) : Prop := (s.1 z).tok = (r.1 z).tok

def bankWindowReadBit {n : Nat} (r s : RenewalBankReference n)
    (z : Fin n) : Prop := (s.1 z).bit = (r.1 z).bit

def bankWindowReadGrant {n : Nat} (r s : RenewalBankReference n)
    (z : Fin n) : Prop := (s.1 z).grant = (r.1 z).grant

def bankWindowReadWorker {n : Nat} (r s : RenewalBankReference n)
    (z : Fin n) : Prop :=
  (s.2.sites z).worker = (r.2.sites z).worker

def bankWindowReadController {n : Nat} (r s : RenewalBankReference n)
    (z : Fin n) : Prop :=
  (s.2.sites z).controller = (r.2.sites z).controller

def bankWindowReadPackPrefix {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (root : Fin n) (last : Nat) : Prop :=
  ∀ k : Nat, k ≤ last →
    bankWindowReadPack r s (Counter.site ring root k)

def bankWindowReadDigitBits {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (root : Fin n) : Prop :=
  ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    bankWindowReadBit r s (Counter.site ring root (j.val + 1))

def bankWindowReadDigitTokens {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (root : Fin n) : Prop :=
  ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    bankWindowReadTok r s (Counter.site ring root (j.val + 1))

/-- Consumers: group 1 R7 frame; physical PACK/mode/token and two ghost slots. -/
def bankWindowFrameReadSet {n : Nat}
    (r s : RenewalBankReference n)
    (z : Fin n) : Prop :=
  bankWindowReadPack r s z ∧ bankWindowReadMode r s z ∧
  bankWindowReadTok r s z ∧ bankWindowReadController r s z ∧
  bankWindowReadWorker r s z

/-- Consumers: group 1 payloadShape; the two ghost slots only. -/
def bankWindowPayloadShapeReadSet {n : Nat}
    (r s : RenewalBankReference n)
    (i : Fin n) (_p : RenewalBankPayload n) : Prop :=
  bankWindowReadWorker r s i ∧ bankWindowReadController r s i

/-- Consumers: group 1 genuinePayloadEmpty; the two ghost slots only. -/
def bankWindowGenuinePayloadEmptyReadSet {n : Nat}
    (r s : RenewalBankReference n)
    (i : Fin n) (_p : RenewalBankPayload n)
    (_o : RenewalBankOrigin n) : Prop :=
  bankWindowReadWorker r s i ∧ bankWindowReadController r s i

/-- Consumers: groups 2--13 phaseExcludes; free worker i and origin root. -/
def bankWindowPhaseExcludesReadSet {n : Nat}
    (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (i : Fin n)
    (_p : RenewalBankPayload n) : Prop :=
  bankWindowReadTok r s i ∧ bankWindowReadWorker r s i ∧
  bankWindowReadMode r s o.root

/-- Consumers: groups 2--13 phaseComplete; the entire origin PACK prefix. -/
def bankWindowPhaseCompleteReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (i : Fin n)
    (_p : RenewalBankPayload n) : Prop :=
  bankWindowPhaseExcludesReadSet r s o i _p ∧
  bankWindowReadPackPrefix ring r s o.root (compileAdvice (ceilLogTwo n)).b

/-- Consumers: groups 2--13 phaseUnique; every origin digit token. -/
def bankWindowPhaseUniqueReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (i : Fin n)
    (_p : RenewalBankPayload n) : Prop :=
  bankWindowPhaseExcludesReadSet r s o i _p ∧
  bankWindowReadDigitTokens ring r s o.root

/-- Consumers: groups 2--13 phaseFlags; free PACK and full origin bit window. -/
def bankWindowPhaseFlagsReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (i : Fin n)
    (_p : RenewalBankPayload n) : Prop :=
  bankWindowPhaseExcludesReadSet r s o i _p ∧
  bankWindowReadPack r s i ∧ bankWindowReadDigitBits ring r s o.root

/-- Consumers: groups 2--13 inheritedClean; scope, root controller, tainted digit. -/
def bankWindowInheritedCleanReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (j : Fin (compileAdvice (ceilLogTwo n)).b) : Prop :=
  bankWindowReadPackPrefix ring r s root (compileAdvice (ceilLogTwo n)).b ∧
  bankWindowReadGrant r s root ∧ bankWindowReadController r s root ∧
  bankWindowReadWorker r s (Counter.site ring root (j.val + 1))

/-- Consumers: groups 2, 3--4, 9, 12--13 resetWait; RL needs full suffix. -/
def bankWindowResetWaitReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) : Prop :=
  bankWindowReadPackPrefix ring r s root (compileAdvice (ceilLogTwo n)).b ∧
  bankWindowReadGrant r s root ∧ bankWindowReadMode r s root ∧
  bankWindowReadController r s root ∧
  bankWindowReadDigitBits ring r s root ∧
  bankWindowReadDigitTokens ring r s root ∧
  (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    bankWindowReadWorker r s (Counter.site ring root (j.val + 1)))

/-- Consumers: groups 2--13 armedExact; controller root and foreign-origin bits. -/
def bankWindowArmedExactReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (o : RenewalBankOrigin n)
    (_p : RenewalBankPayload n) : Prop :=
  bankWindowReadPackPrefix ring r s root (compileAdvice (ceilLogTwo n)).b ∧
  bankWindowReadGrant r s root ∧ bankWindowReadMode r s root ∧
  bankWindowReadController r s root ∧
  bankWindowReadDigitTokens ring r s root ∧
  bankWindowReadDigitBits ring r s o.root

/-- Consumers: groups 2--13 incrementExact; free i and origin bit window. -/
def bankWindowIncrementExactReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (o : RenewalBankOrigin n)
    (i : Fin n) (_p : RenewalBankPayload n) : Prop :=
  bankWindowReadPackPrefix ring r s root (compileAdvice (ceilLogTwo n)).b ∧
  bankWindowReadGrant r s root ∧ bankWindowReadMode r s root ∧
  bankWindowReadController r s root ∧
  bankWindowReadWorker r s i ∧ bankWindowReadPack r s i ∧
  bankWindowReadTok r s i ∧ bankWindowReadDigitTokens ring r s root ∧
  bankWindowReadDigitBits ring r s root ∧
  bankWindowReadDigitBits ring r s o.root

/-- Consumers: groups 2--13 compareExact; no separate Scope premise. -/
def bankWindowCompareExactReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (i : Fin n)
    (_p : RenewalBankPayload n) : Prop :=
  bankWindowReadMode r s o.root ∧
  bankWindowReadController r s o.root ∧
  bankWindowReadWorker r s i ∧ bankWindowReadTok r s i ∧
  bankWindowReadDigitTokens ring r s o.root ∧
  bankWindowReadDigitBits ring r s o.root

/-- Consumers: groups 2--13 iwaitTaintedUnique; all tokens and one worker. -/
def bankWindowIwaitTaintedUniqueReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (j : Fin (compileAdvice (ceilLogTwo n)).b) : Prop :=
  bankWindowReadPackPrefix ring r s root (compileAdvice (ceilLogTwo n)).b ∧
  bankWindowReadGrant r s root ∧ bankWindowReadMode r s root ∧
  bankWindowReadController r s root ∧
  bankWindowReadDigitTokens ring r s root ∧
  bankWindowReadWorker r s (Counter.site ring root (j.val + 1))

/-- Consumers: groups 2--13 cwaitTaintedUnique; comparison token at tainted digit. -/
def bankWindowCwaitTaintedUniqueReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (j : Fin (compileAdvice (ceilLogTwo n)).b) : Prop :=
  bankWindowIwaitTaintedUniqueReadSet ring r s root j

/-- Consumers: groups 2--13 proto; partial PACK prefix through limit+1. -/
def bankWindowProtoReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (limit : Nat) : Prop :=
  bankWindowReadPackPrefix ring r s root (limit + 1) ∧
  bankWindowReadMode r s root ∧ bankWindowReadController r s root ∧
  (∀ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit →
    bankWindowReadTok r s (Counter.site ring root (j.val + 1)) ∧
    bankWindowReadBit r s (Counter.site ring root (j.val + 1)) ∧
    bankWindowReadWorker r s (Counter.site ring root (j.val + 1)))

/-- Consumers: groups 2--13 orphan; no complete-window assumption. -/
def bankWindowOrphanReadSet {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (j : Fin (compileAdvice (ceilLogTwo n)).b) : Prop :=
  bankWindowReadPackPrefix ring r s root (j.val + 1) ∧
  bankWindowReadMode r s root ∧ bankWindowReadController r s root ∧
  bankWindowReadWorker r s (Counter.site ring root (j.val + 1))


/-! Instance-local extensionality for the first seven J fields. -/

/-- Consumer: group 1; live payload membership depends on precisely
the worker and controller slots, not service or physical state. -/
private theorem bankWindowPayloadReadsExt
    {n : Nat} (r s : RenewalBankReference n) (i : Fin n)
    (hw : bankWindowReadWorker r s i)
    (hc : bankWindowReadController r s i) :
    rbSiteLivePayloads (s.2.sites i) =
      rbSiteLivePayloads (r.2.sites i) := by
  unfold rbSiteLivePayloads
  rw [show (s.2.sites i).worker = (r.2.sites i).worker from hw,
    show (s.2.sites i).controller = (r.2.sites i).controller from hc]

theorem bankWindowFrameReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (z : Fin n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowFrameReadSet r s z) :
    bankInFlightControllerShape (s.1 z).pack.val
      (s.1 z).mode (s.2.sites z).controller ∧
    bankInFlightWorkerShape (s.1 z).tok
      (s.2.sites z).worker := by
  obtain ⟨hp, hm, ht, hc, hw⟩ := hread
  obtain ⟨hctl, hwrk⟩ := hJ.frame z
  constructor
  · rw [hp, hm, hc]
    exact hctl
  · rw [ht, hw]
    exact hwrk


/-- Consumer: group 1 payloadShape; no physical read at i. -/
theorem bankWindowPayloadShapeReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowPayloadShapeReadSet r s i p)
    (hlive : p ∈ rbSiteLivePayloads (s.2.sites i))
    (horigin : p.origin = none) :
    p.atoms ≠ [] ∧ p.heads = 0 := by
  have heq := bankWindowPayloadReadsExt r s i hread.1 hread.2
  rw [heq] at hlive
  exact hJ.payloadShape i p hlive horigin

/-- Consumer: group 1 genuinePayloadEmpty; no physical read at i. -/
theorem bankWindowGenuinePayloadEmptyReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (i : Fin n)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowGenuinePayloadEmptyReadSet r s i p o)
    (hlive : p ∈ rbSiteLivePayloads (s.2.sites i))
    (horigin : p.origin = some o) :
    p.atoms = [] := by
  have heq := bankWindowPayloadReadsExt r s i hread.1 hread.2
  rw [heq] at hlive
  exact hJ.genuinePayloadEmpty i p o hlive horigin

theorem bankWindowPhaseExcludesReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowPhaseExcludesReadSet r s o i p)
    (hworker : BankComparatorOriginWorker ring s o i p) :
    (s.1 o.root).mode ≠ .ARMED ∧
    (s.1 o.root).mode ≠ .CSTART ∧
    (s.1 o.root).mode ≠ .IWAIT := by
  obtain ⟨ht, hw, hm⟩ := hread
  have hworkerOld : BankComparatorOriginWorker ring r o i p := by
    obtain ⟨hwp, ho, htok⟩ := hworker
    refine ⟨hw.symm.trans hwp, ho, ?_⟩
    rw [ht] at htok
    exact htok
  have hold := hJ.phaseExcludes o i p hworkerOld
  rw [hm]
  exact hold


theorem bankWindowPhaseCompleteReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowPhaseCompleteReadSet ring r s o i p)
    (hworker : BankComparatorOriginWorker ring s o i p)
    (hmode : (s.1 o.root).mode = .CWAIT) :
    Counter.Complete ring s.1 o.root := by
  obtain ⟨⟨ht, hw, hm⟩, hp⟩ := hread
  have hworkerOld : BankComparatorOriginWorker ring r o i p := by
    obtain ⟨hwp, ho, htok⟩ := hworker
    refine ⟨hw.symm.trans hwp, ho, ?_⟩
    rw [ht] at htok
    exact htok
  have hmodeOld : (r.1 o.root).mode = .CWAIT :=
    hm.symm.trans hmode
  have hold := hJ.phaseComplete o i p hworkerOld hmodeOld
  intro k hk
  exact (hp k hk).trans (hold k hk)


theorem bankWindowPhaseUniqueReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowPhaseUniqueReadSet ring r s o i p)
    (hworker : BankComparatorOriginWorker ring s o i p)
    (hmode : (s.1 o.root).mode = .CWAIT)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (htoken : BankTrialLiveComparisonToken
      (s.1 (Counter.site ring o.root (j.val + 1))).tok) :
    Counter.site ring o.root (j.val + 1) = i := by
  obtain ⟨⟨ht, hw, hm⟩, hdigit⟩ := hread
  have hworkerOld : BankComparatorOriginWorker ring r o i p := by
    obtain ⟨hwp, ho, htok⟩ := hworker
    refine ⟨hw.symm.trans hwp, ho, ?_⟩
    rw [ht] at htok
    exact htok
  have hmodeOld : (r.1 o.root).mode = .CWAIT :=
    hm.symm.trans hmode
  have htokOld : BankTrialLiveComparisonToken
      (r.1 (Counter.site ring o.root (j.val + 1))).tok := by
    rw [hdigit j] at htoken
    exact htoken
  exact hJ.phaseUnique o i p hworkerOld hmodeOld j htokOld


/-- Consumer: groups 2, 9--13, all four CR/CL flag arms. -/
private theorem bankWindowMatchedReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (o : RenewalBankOrigin n)
    (hb : bankWindowReadDigitBits ring r s o.root)
    (last : Nat) :
    bankComparatorPrefixMatched ring s o last ↔
      bankComparatorPrefixMatched ring r o last := by
  unfold bankComparatorPrefixMatched
  constructor
  · intro h j hj
    exact (hb j).symm.trans (h j hj)
  · intro h j hj
    exact (hb j).trans (h j hj)

theorem bankWindowPhaseFlagsReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowPhaseFlagsReadSet ring r s o i p)
    (hworker : BankComparatorOriginWorker ring s o i p)
    (hmode : (s.1 o.root).mode = .CWAIT) :
    ((s.1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring s o (s.1 i).pack.val) ∧
    ((s.1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring s o (s.1 i).pack.val) ∧
    ((s.1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring s o (compileAdvice (ceilLogTwo n)).b) ∧
    ((s.1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring s o (compileAdvice (ceilLogTwo n)).b) := by
  obtain ⟨⟨ht, hw, hm⟩, hp, hb⟩ := hread
  have hworkerOld : BankComparatorOriginWorker ring r o i p := by
    obtain ⟨hwp, ho, htok⟩ := hworker
    refine ⟨hw.symm.trans hwp, ho, ?_⟩
    rw [ht] at htok
    exact htok
  have hmodeOld : (r.1 o.root).mode = .CWAIT :=
    hm.symm.trans hmode
  have hold := hJ.phaseFlags o i p hworkerOld hmodeOld
  have hmatched := bankWindowMatchedReadTransport ring r s o hb
  rw [ht, hp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcr
    exact (hmatched (r.1 i).pack.val).mpr (hold.1 hcr)
  · intro hcr hpost
    exact (hold.2.1 hcr)
      ((hmatched (r.1 i).pack.val).mp hpost)
  · intro hcl
    exact (hmatched (compileAdvice (ceilLogTwo n)).b).mpr
      (hold.2.2.1 hcl)
  · intro hcl hpost
    exact (hold.2.2.2 hcl)
      ((hmatched (compileAdvice (ceilLogTwo n)).b).mp hpost)


/-! Geometric incidence of a selected clockwise edge with a BANK prefix. -/

/-- Consumer: guarded geometric-incidence enumeration, groups 2--13. -/
private theorem bankWindowIncidenceSuccessorInjective
    {n : Nat} (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a c hac
  apply Fin.ext
  have hv := congrArg Fin.val hac
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hc : c.val + 1 < n
    · rw [Nat.mod_eq_of_lt hc] at hv
      omega
    · have hceq : c.val + 1 = n := by omega
      rw [hceq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hc : c.val + 1 < n
    · rw [Nat.mod_eq_of_lt hc] at hv
      omega
    · have hceq : c.val + 1 = n := by omega
      omega

/-- Consumer: incidence-site injectivity, not a protocol countermodel. -/
private theorem bankWindowIncidenceSiteShift
    {n : Nat} (ring : DirectedRing n)
    (a : Fin n) (i j : Nat) :
    Counter.site ring (Counter.site ring a i) j =
      Counter.site ring a (i + j) := by
  induction j with
  | zero =>
      simp only [Counter.site, Nat.add_zero]
  | succ j ih =>
      change ring.rightNeighbor
        (Counter.site ring (Counter.site ring a i) j) =
        ring.rightNeighbor (Counter.site ring a (i + j))
      exact congrArg ring.rightNeighbor ih

/-- Consumer: mutually exclusive root/digit source labels. -/
theorem bankWindowIncidenceSiteDistinct
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (a : Fin n) (i j : Nat) (hij : i < j)
    (hj : j ≤ (compileAdvice (ceilLogTwo n)).b + 1) :
    Counter.site ring a i ≠ Counter.site ring a j := by
  have hsize := Counter.resetColdLargeAtSpatialCutoff n hbank
  change 2 * (13 * ((compileAdvice (ceilLogTwo n)).b + 2)) ≤ n at hsize
  have hshort : j - i < n := by omega
  intro he
  have hreturn :
      Counter.site ring (Counter.site ring a i) (j - i) =
        Counter.site ring a i := by
    rw [bankWindowIncidenceSiteShift,
      show i + (j - i) = j by omega]
    exact he.symm
  exact (bankWindowIncomingSiteNoShortReturn ring
    (Counter.site ring a i) (j - i) (by omega) hshort) hreturn

/-- Consumer: root-entry is disjoint from every source position
zero through b; relies on the exact BANK spatial-cutoff bound. -/
theorem bankWindowIncidenceIncomingSourceOutside
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (a e : Fin n) (hy : ring.rightNeighbor e = a)
    (k : Nat) (hk : k ≤ (compileAdvice (ceilLogTwo n)).b) :
    e ≠ Counter.site ring a k := by
  have hsize := Counter.resetColdLargeAtSpatialCutoff n hbank
  change 2 * (13 * ((compileAdvice (ceilLogTwo n)).b + 2)) ≤ n at hsize
  have hshort : k + 1 < n := by omega
  intro he
  have hreturn : Counter.site ring a (k + 1) = a := by
    calc
      Counter.site ring a (k + 1) =
          ring.rightNeighbor (Counter.site ring a k) := rfl
      _ = ring.rightNeighbor e := by rw [he]
      _ = a := hy
  exact (bankWindowIncomingSiteNoShortReturn ring a
    (k + 1) (by omega) hshort) hreturn

/-- Consumer: the B-position routing of groups 2--13. Together with
SiteDistinct and IncomingSourceOutside, these are exclusive
root-entry/root-first/internal/prefix-exit/disjoint alternatives. -/
theorem bankWindowGuardedGeometricIncidence
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (a e : Fin n) :
    ring.rightNeighbor e = a ∨ e = a ∨
    (∃ k : Nat, 1 ≤ k ∧ k < (compileAdvice (ceilLogTwo n)).b ∧
      e = Counter.site ring a k) ∨
    e = Counter.site ring a (compileAdvice (ceilLogTwo n)).b ∨
    Counter.OutsideSites (q := ceilLogTwo n) ring a e := by
  by_cases hy : ring.rightNeighbor e = a
  · exact Or.inl hy
  · by_cases hex : ∃ k : Nat, k ≤ (compileAdvice (ceilLogTwo n)).b ∧
        e = Counter.site ring a k
    · obtain ⟨k, hk, he⟩ := hex
      by_cases hzero : k = 0
      · subst k
        exact Or.inr (Or.inl (by simpa only [Counter.site] using he))
      · by_cases htop : k = (compileAdvice (ceilLogTwo n)).b
        · subst k
          exact Or.inr (Or.inr (Or.inr (Or.inl he)))
        · exact Or.inr (Or.inr
            (Or.inl ⟨k, by omega, by omega, he⟩))
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      intro j hj
      constructor
      · intro he
        exact hex ⟨j, hj, he⟩
      · intro htarget
        cases j with
        | zero =>
            exact hy (by simpa only [Counter.site] using htarget)
        | succ t =>
            have hp :
                ring.rightNeighbor e =
                  ring.rightNeighbor (Counter.site ring a t) := by
              calc
                ring.rightNeighbor e =
                    Counter.site ring a (t + 1) := htarget
                _ = ring.rightNeighbor (Counter.site ring a t) := rfl
            have he := bankWindowIncidenceSuccessorInjective ring hp
            exact hex ⟨t, by omega, he⟩

/-- Consumer: A-case read-set frame. Any chosen set of sites avoiding
both endpoints has identical entire physical and ghost site snapshots. -/
theorem bankWindowExactDisjointSitesFrame
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (readSite : Fin n → Prop)
    (hdisjoint : ∀ z, readSite z →
      z ≠ e ∧ z ≠ ring.rightNeighbor e) :
    ∀ z, readSite z →
      (renewalBankNext ring r e).1 z = r.1 z ∧
      (renewalBankNext ring r e).2.sites z = r.2.sites z := by
  intro z hz
  exact bankWindowExactOffPairFrame ring r e z
    (hdisjoint z hz).1 (hdisjoint z hz).2

/-! Local equivalence lemmas used by the owner-window fields. -/

/-- Consumers: inheritedClean, resetWait, armedExact, incrementExact,
and the two tainted-uniqueness clauses. -/
private theorem bankWindowScopeReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (root : Fin n)
    (hp : bankWindowReadPackPrefix ring r s root (compileAdvice (ceilLogTwo n)).b)
    (hg : bankWindowReadGrant r s root) :
    BankWindowScope ring s root ↔ BankWindowScope ring r root := by
  constructor
  · rintro ⟨hc, hgrant⟩
    constructor
    · intro k hk
      exact (hp k hk).symm.trans (hc k hk)
    · exact hg.symm.trans hgrant
  · rintro ⟨hc, hgrant⟩
    constructor
    · intro k hk
      exact (hp k hk).trans (hc k hk)
    · exact hg.trans hgrant

/-- Consumers: inheritedClean, proto and root-control sanitation. -/
private theorem bankWindowInheritedReadTransport
    {n : Nat} (r s : RenewalBankReference n) (root : Fin n)
    (hc : bankWindowReadController r s root) :
    BankWindowInheritedController s root ↔
      BankWindowInheritedController r root := by
  unfold BankWindowInheritedController
  rw [show (s.2.sites root).controller =
    (r.2.sites root).controller from hc]

/-- Consumers: inheritedClean, proto, orphan, and tainted uniqueness. -/
private theorem bankWindowTaintedReadTransport
    {n : Nat} (r s : RenewalBankReference n) (z : Fin n)
    (hw : bankWindowReadWorker r s z) :
    BankWindowTainted s z ↔ BankWindowTainted r z := by
  unfold BankWindowTainted
  rw [show (s.2.sites z).worker =
    (r.2.sites z).worker from hw]

/-- Consumers: resetWait, incrementExact, and incomplete proto RR. -/
private theorem bankWindowZeroReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (root : Fin n) (last : Nat)
    (hb : bankWindowReadDigitBits ring r s root) :
    bankWindowZeroPrefix ring s root last ↔
      bankWindowZeroPrefix ring r root last := by
  constructor
  · intro hz j hj
    exact (hb j).symm.trans (hz j hj)
  · intro hz j hj
    exact (hb j).trans (hz j hj)

/-- Consumers: resetWait, incrementExact, compareExact, and uniqueness. -/
private theorem bankWindowOnlyReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (root i : Fin n)
    (ht : bankWindowReadDigitTokens ring r s root) :
    bankWindowOnlyToken ring s root i ↔
      bankWindowOnlyToken ring r root i := by
  constructor
  · intro ho j hn
    apply ho j
    intro hpost
    exact hn ((ht j).symm.trans hpost)
  · intro ho j hn
    apply ho j
    intro hold
    exact hn ((ht j).trans hold)

/-- Consumer: exact heads and origin binary values, not capped heads. -/
private theorem bankWindowBinaryReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (o : RenewalBankOrigin n)
    (hb : bankWindowReadDigitBits ring r s o.root) :
    bankOriginBinaryValue ring s.1 o =
      bankOriginBinaryValue ring r.1 o := by
  unfold bankOriginBinaryValue
  have hfn :
      (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
        if (s.1 (Counter.site ring o.root (j.val + 1))).bit
        then 2 ^ j.val else 0) =
      (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
        if (r.1 (Counter.site ring o.root (j.val + 1))).bit
        then 2 ^ j.val else 0) := by
    funext j
    rw [hb j]
  exact congrArg (fun f : Fin (compileAdvice (ceilLogTwo n)).b → Nat =>
    (List.ofFn f).sum) hfn

/-- Consumer: inheritedClean at an arbitrary possibly overlapping root. -/
theorem bankWindowInheritedCleanReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (root : Fin n) (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowInheritedCleanReadSet ring r s root j)
    (hscope : BankWindowScope ring s root)
    (hinherited : BankWindowInheritedController s root)
    (htainted : BankWindowTainted s
      (Counter.site ring root (j.val + 1))) : False := by
  obtain ⟨hp, hg, hc, hw⟩ := hread
  have hs := (bankWindowScopeReadTransport ring r s root hp hg).mp hscope
  have hi := (bankWindowInheritedReadTransport r s root hc).mp hinherited
  have ht := (bankWindowTaintedReadTransport r s
    (Counter.site ring root (j.val + 1)) hw).mp htainted
  exact hJ.inheritedClean root hs hi j ht

/-- Consumer: groups 2, 3--4, 9 and 12--13 resetWait.
The RL consequence uses all b digit tokens and bits. -/
theorem bankWindowResetWaitReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowResetWaitReadSet ring r s root)
    (hscope : BankWindowScope ring s root)
    (hmode : (s.1 root).mode = .RWAIT)
    (hcontroller : (s.2.sites root).controller = .waiting []) :
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n),
      (s.2.sites (Counter.site ring root (j.val + 1))).worker =
        .pending rho ∧
      ((s.1 (Counter.site ring root (j.val + 1))).tok = .RR ∨
       (s.1 (Counter.site ring root (j.val + 1))).tok = .RL) ∧
      bankWindowZeroPrefix ring s root (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b, k.val < j.val →
        (s.1 (Counter.site ring root (k.val + 1))).tok = .E) ∧
      ((s.1 (Counter.site ring root (j.val + 1))).tok = .RL →
        bankWindowOnlyToken ring s root
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowZeroPrefix ring s root (compileAdvice (ceilLogTwo n)).b) := by
  obtain ⟨hp, hg, hm, hc, hb, ht, hw⟩ := hread
  have hs := (bankWindowScopeReadTransport ring r s root hp hg).mp hscope
  have hmodeOld : (r.1 root).mode = .RWAIT := hm.symm.trans hmode
  have hctlOld : (r.2.sites root).controller = .waiting [] :=
    hc.symm.trans hcontroller
  obtain ⟨j, rho, hpending, htok, hzero, hearlier, hrl⟩ :=
    hJ.resetWait root hs hmodeOld hctlOld
  refine ⟨j, rho, (hw j).trans hpending, ?_, ?_, ?_, ?_⟩
  · rcases htok with hr | hl
    · exact Or.inl ((ht j).trans hr)
    · exact Or.inr ((ht j).trans hl)
  · exact (bankWindowZeroReadTransport ring r s root
      (j.val + 1) hb).mpr hzero
  · intro k hk
    exact (ht k).trans (hearlier k hk)
  · intro hpost
    have hold : (r.1 (Counter.site ring root (j.val + 1))).tok =
        .RL := (ht j).symm.trans hpost
    obtain ⟨honly, hzeroFull⟩ := hrl hold
    exact ⟨(bankWindowOnlyReadTransport ring r s root
      (Counter.site ring root (j.val + 1)) ht).mpr honly,
      (bankWindowZeroReadTransport ring r s root (compileAdvice (ceilLogTwo n)).b
        hb).mpr hzeroFull⟩

/-- Consumer: groups 2--13 armedExact; the two root bit intervals
are kept distinct until a provenance lemma identifies them. -/
theorem bankWindowArmedExactReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (root : Fin n) (o : RenewalBankOrigin n)
    (p : RenewalBankPayload n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowArmedExactReadSet ring r s root o p)
    (hscope : BankWindowScope ring s root)
    (hphase : (s.1 root).mode = .ARMED ∨
      (s.1 root).mode = .CSTART)
    (hcontroller : (s.2.sites root).controller = .active p)
    (horigin : p.origin = some o) :
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      (s.1 (Counter.site ring root (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring s.1 o ∧
    ((s.1 root).mode = .ARMED →
      bankOriginBinaryValue ring s.1 o < (compileAdvice (ceilLogTwo n)).K) ∧
    ((s.1 root).mode = .CSTART →
      bankOriginBinaryValue ring s.1 o ≤ (compileAdvice (ceilLogTwo n)).K) := by
  obtain ⟨hp, hg, hm, hc, ht, hb⟩ := hread
  have hscopeOld := (bankWindowScopeReadTransport
    ring r s root hp hg).mp hscope
  have hphaseOld : (r.1 root).mode = .ARMED ∨
      (r.1 root).mode = .CSTART := by
    rcases hphase with ha | hcstart
    · exact Or.inl (hm.symm.trans ha)
    · exact Or.inr (hm.symm.trans hcstart)
  have hctlOld : (r.2.sites root).controller = .active p :=
    hc.symm.trans hcontroller
  obtain ⟨htokenOld, hheads, harmed, hcstart⟩ :=
    hJ.armedExact root o p hscopeOld hphaseOld hctlOld horigin
  have hvalue := bankWindowBinaryReadTransport ring r s o hb
  refine ⟨?_, hheads.trans hvalue.symm, ?_, ?_⟩
  · intro j
    exact (ht j).trans (htokenOld j)
  · intro hmodePost
    rw [hvalue]
    exact harmed (hm.symm.trans hmodePost)
  · intro hmodePost
    rw [hvalue]
    exact hcstart (hm.symm.trans hmodePost)

theorem bankWindowIncrementExactReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (root : Fin n) (o : RenewalBankOrigin n)
    (i : Fin n) (p : RenewalBankPayload n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowIncrementExactReadSet ring r s root o i p)
    (hscope : BankWindowScope ring s root)
    (hmode : (s.1 root).mode = .IWAIT)
    (hcontroller : (s.2.sites root).controller = .waiting [])
    (hworker : (s.2.sites i).worker = .payload p)
    (horigin : p.origin = some o) (hroot : o.root = root) :
    bankWindowOnlyToken ring s root i ∧
    (((s.1 i).tok = .IR ∧
        bankWindowZeroPrefix ring s root (s.1 i).pack.val ∧
        p.heads = bankOriginBinaryValue ring s.1 o +
          2 ^ (s.1 i).pack.val ∧
        bankOriginBinaryValue ring s.1 o +
          2 ^ (s.1 i).pack.val ≤ (compileAdvice (ceilLogTwo n)).K) ∨
      ((s.1 i).tok = .AL ∧
        p.heads = bankOriginBinaryValue ring s.1 o ∧
        bankOriginBinaryValue ring s.1 o ≤
          (compileAdvice (ceilLogTwo n)).K)) := by
  obtain ⟨hp, hg, hm, hc, hw, hpack, htok, hdt, hdb, hbo⟩ := hread
  have hscopeOld := (bankWindowScopeReadTransport
    ring r s root hp hg).mp hscope
  have hold := hJ.incrementExact root o i p hscopeOld
    (hm.symm.trans hmode) (hc.symm.trans hcontroller)
    (hw.symm.trans hworker) horigin hroot
  have hvalue := bankWindowBinaryReadTransport ring r s o hbo
  refine ⟨(bankWindowOnlyReadTransport ring r s root i hdt).mpr
    hold.1, ?_⟩
  rcases hold.2 with hir | hal
  · obtain ⟨hirTok, hirZero, hirHeads, hirBound⟩ := hir
    refine Or.inl ⟨htok.trans hirTok, ?_, ?_, ?_⟩
    · rw [hpack]
      exact (bankWindowZeroReadTransport ring r s root
        (r.1 i).pack.val hdb).mpr hirZero
    · rw [hvalue, hpack]
      exact hirHeads
    · rw [hvalue, hpack]
      exact hirBound
  · obtain ⟨halTok, halHeads, halBound⟩ := hal
    exact Or.inr ⟨htok.trans halTok,
      by simpa only [hvalue] using halHeads,
      by simpa only [hvalue] using halBound⟩


theorem bankWindowCompareExactReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowCompareExactReadSet ring r s o i p)
    (hworker : (s.2.sites i).worker = .payload p)
    (horigin : p.origin = some o)
    (hmode : (s.1 o.root).mode = .CWAIT)
    (hcontroller : (s.2.sites o.root).controller = .waiting []) :
    bankWindowOnlyToken ring s o.root i ∧
    BankTrialLiveComparisonToken (s.1 i).tok ∧
    p.heads = bankOriginBinaryValue ring s.1 o ∧
    bankOriginBinaryValue ring s.1 o ≤
      (compileAdvice (ceilLogTwo n)).K := by
  obtain ⟨hm, hc, hw, ht, hdt, hdb⟩ := hread
  obtain ⟨honly, htoken, hheads, hbound⟩ :=
    hJ.compareExact o i p (hw.symm.trans hworker) horigin
      (hm.symm.trans hmode) (hc.symm.trans hcontroller)
  have hvalue := bankWindowBinaryReadTransport ring r s o hdb
  refine ⟨(bankWindowOnlyReadTransport ring r s
    o.root i hdt).mpr honly, ?_, ?_, ?_⟩
  · rw [ht]
    exact htoken
  · simpa only [hvalue] using hheads
  · simpa only [hvalue] using hbound


/-- Consumer: groups 2--13 iwaitTaintedUnique for one exact digit. -/
theorem bankWindowIwaitTaintedUniqueReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (root : Fin n) (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowIwaitTaintedUniqueReadSet ring r s root j)
    (hscope : BankWindowScope ring s root)
    (hmode : (s.1 root).mode = .IWAIT)
    (hcontroller : (s.2.sites root).controller = .waiting [])
    (htainted : BankWindowTainted s
      (Counter.site ring root (j.val + 1))) :
    ∃ o p,
      (s.2.sites (Counter.site ring root (j.val + 1))).worker =
        .payload p ∧ p.origin = some o ∧
      o.root = root ∧
      bankWindowOnlyToken ring s root
        (Counter.site ring root (j.val + 1)) := by
  obtain ⟨hp, hg, hm, hc, ht, hw⟩ := hread
  have hscopeOld := (bankWindowScopeReadTransport
    ring r s root hp hg).mp hscope
  have htaintedOld := (bankWindowTaintedReadTransport r s
    (Counter.site ring root (j.val + 1)) hw).mp htainted
  obtain ⟨o, p, hworker, horigin, hroot, honly⟩ :=
    hJ.iwaitTaintedUnique root hscopeOld
      (hm.symm.trans hmode) (hc.symm.trans hcontroller)
      j htaintedOld
  exact ⟨o, p, hw.trans hworker, horigin, hroot,
    (bankWindowOnlyReadTransport ring r s root
      (Counter.site ring root (j.val + 1)) ht).mpr honly⟩

theorem bankWindowCwaitTaintedUniqueReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (root : Fin n) (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowCwaitTaintedUniqueReadSet ring r s root j)
    (hscope : BankWindowScope ring s root)
    (hmode : (s.1 root).mode = .CWAIT)
    (hcontroller : (s.2.sites root).controller = .waiting [])
    (htainted : BankWindowTainted s
      (Counter.site ring root (j.val + 1))) :
    ∃ o p,
      (s.2.sites (Counter.site ring root (j.val + 1))).worker =
        .payload p ∧ p.origin = some o ∧
      o.root = root ∧
      BankTrialLiveComparisonToken
        (s.1 (Counter.site ring root (j.val + 1))).tok ∧
      bankWindowOnlyToken ring s root
        (Counter.site ring root (j.val + 1)) := by
  obtain ⟨hp, hg, hm, hc, ht, hw⟩ := hread
  have hscopeOld := (bankWindowScopeReadTransport
    ring r s root hp hg).mp hscope
  have htaintedOld := (bankWindowTaintedReadTransport r s
    (Counter.site ring root (j.val + 1)) hw).mp htainted
  obtain ⟨o, p, hworker, horigin, hroot, htoken, honly⟩ :=
    hJ.cwaitTaintedUnique root hscopeOld
      (hm.symm.trans hmode) (hc.symm.trans hcontroller)
      j htaintedOld
  refine ⟨o, p, hw.trans hworker, horigin, hroot, ?_,
    (bankWindowOnlyReadTransport ring r s root
      (Counter.site ring root (j.val + 1)) ht).mpr honly⟩
  rw [ht j]
  exact htoken


/-- Consumer: groups 12--13 proto. An aligned prefix ending before b
is not silently upgraded to Counter.Complete. -/
private theorem bankWindowProtoPrefixReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (root : Fin n) (limit : Nat)
    (hp : bankWindowReadPackPrefix ring r s root (limit + 1)) :
    BankWindowProtoRun ring s root limit ↔
      BankWindowProtoRun ring r root limit := by
  unfold BankWindowProtoRun
  constructor
  · rintro ⟨hlt, hpre, hbad⟩
    refine ⟨hlt, ?_, ?_⟩
    · intro k hk
      exact (hp k (by omega)).symm.trans (hpre k hk)
    · intro hcorrect
      exact hbad ((hp (limit + 1) (by omega)).trans hcorrect)
  · rintro ⟨hlt, hpre, hbad⟩
    refine ⟨hlt, ?_, ?_⟩
    · intro k hk
      exact (hp k (by omega)).trans (hpre k hk)
    · intro hcorrect
      exact hbad ((hp (limit + 1) (by omega)).symm.trans hcorrect)

/-- Consumer: arbitrary partial proto owner, including waiting RR
witness and the two independent taint exclusions. -/
theorem bankWindowProtoReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (root : Fin n) (limit : Nat)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowProtoReadSet ring r s root limit)
    (hproto : BankWindowProtoRun ring s root limit) :
    (∀ p o, (s.2.sites root).controller = .active p →
      p.origin = some o → False) ∧
    (BankWindowInheritedController s root →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit →
        ¬ BankWindowTainted s
          (Counter.site ring root (j.val + 1))) ∧
    (((s.1 root).mode = .RWAIT ∧
      (s.2.sites root).controller = .waiting []) →
      ∃ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit ∧
        ∃ rho : RenewalBankReceipt n,
          (s.2.sites (Counter.site ring root (j.val + 1))).worker =
            .pending rho ∧
          (s.1 (Counter.site ring root (j.val + 1))).tok = .RR ∧
          bankWindowZeroPrefix ring s root (j.val + 1) ∧
          (∀ k : Fin (compileAdvice (ceilLogTwo n)).b, k.val < j.val →
            (s.1 (Counter.site ring root (k.val + 1))).tok = .E)) ∧
    ((s.1 root).mode ≠ .RESET →
      (s.1 root).mode ≠ .RWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit →
        ¬ BankWindowTainted s
          (Counter.site ring root (j.val + 1))) := by
  obtain ⟨hp, hm, hc, hsegments⟩ := hread
  have hprotoOld := (bankWindowProtoPrefixReadTransport
    ring r s root limit hp).mp hproto
  obtain ⟨hno, hclean, hwait, hother⟩ :=
    hJ.proto root limit hprotoOld
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p o hactive ho
    exact hno p o (hc.symm.trans hactive) ho
  · intro hinherited j hj htainted
    have hInheritedOld :=
      (bankWindowInheritedReadTransport r s root hc).mp hinherited
    have htOld := (bankWindowTaintedReadTransport r s
      (Counter.site ring root (j.val + 1))
      (hsegments j hj).2.2).mp htainted
    exact hclean hInheritedOld j hj htOld
  · intro hpost
    have hold : (r.1 root).mode = .RWAIT ∧
        (r.2.sites root).controller = .waiting [] :=
      ⟨hm.symm.trans hpost.1, hc.symm.trans hpost.2⟩
    obtain ⟨j, hj, rho, hworker, htok, hzero, hbefore⟩ :=
      hwait hold
    refine ⟨j, hj, rho, ?_, ?_, ?_, ?_⟩
    · exact (hsegments j hj).2.2.trans hworker
    · exact (hsegments j hj).1.trans htok
    · intro k hk
      have hkle : k.val + 1 ≤ limit := by omega
      exact (hsegments k hkle).2.1.trans (hzero k hk)
    · intro k hk
      have hkle : k.val + 1 ≤ limit := by omega
      exact (hsegments k hkle).1.trans (hbefore k hk)
  · intro hnotReset hnotWait j hj htainted
    have hnotResetOld : (r.1 root).mode ≠ .RESET := by
      intro hmode
      exact hnotReset (hm.trans hmode)
    have hnotWaitOld : (r.1 root).mode ≠ .RWAIT := by
      intro hmode
      exact hnotWait (hm.trans hmode)
    have htOld := (bankWindowTaintedReadTransport r s
      (Counter.site ring root (j.val + 1))
      (hsegments j hj).2.2).mp htainted
    exact hother hnotResetOld hnotWaitOld j hj htOld

/-- Consumer: groups 12--13 orphan. Its negated PACK-prefix test
uses only offsets through j+1, even at an incomplete owner. -/
private theorem bankWindowOrphanPrefixReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (root : Fin n) (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hp : bankWindowReadPackPrefix ring r s root (j.val + 1)) :
    BankWindowOrphanOwner ring s root j ↔
      BankWindowOrphanOwner ring r root j := by
  have hprefix :
      (∀ k : Nat, k ≤ j.val + 1 →
        (s.1 (Counter.site ring root k)).pack.val = k) ↔
      (∀ k : Nat, k ≤ j.val + 1 →
        (r.1 (Counter.site ring root k)).pack.val = k) := by
    constructor
    · intro h k hk
      exact (hp k hk).symm.trans (h k hk)
    · intro h k hk
      exact (hp k hk).trans (h k hk)
  unfold BankWindowOrphanOwner
  rw [show (s.1 root).pack.val = (r.1 root).pack.val from
    hp 0 (by omega),
    show (s.1 (Counter.site ring root (j.val + 1))).pack.val =
      (r.1 (Counter.site ring root (j.val + 1))).pack.val from
      hp (j.val + 1) (by omega),
    hprefix]

/-- Consumer: groups 12--13 orphan at an arbitrary foreign partial
owner. This transports the exact RESET/RWAIT restriction. -/
theorem bankWindowOrphanReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (root : Fin n) (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring r)
    (hread : bankWindowOrphanReadSet ring r s root j)
    (howner : BankWindowOrphanOwner ring s root j)
    (htainted : BankWindowTainted s
      (Counter.site ring root (j.val + 1))) :
    (s.1 root).mode = .RESET ∨
    ((s.1 root).mode = .RWAIT ∧
      (s.2.sites root).controller = .waiting []) := by
  obtain ⟨hp, hm, hc, hw⟩ := hread
  have hownerOld := (bankWindowOrphanPrefixReadTransport
    ring r s root j hp).mp howner
  have htaintedOld := (bankWindowTaintedReadTransport r s
    (Counter.site ring root (j.val + 1)) hw).mp htainted
  rcases hJ.orphan root j hownerOld htaintedOld with hreset | hwait
  · exact Or.inl (hm.trans hreset)
  · exact Or.inr ⟨hm.trans hwait.1, hc.trans hwait.2⟩

/-! Combined field-wise transport contract. This is NOT BankWindowExact
for arbitrary s: each field has its own explicit read-set antecedent. -/

structure BankWindowExactReadSetContract
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) : Prop where
  frame : ∀ z, bankWindowFrameReadSet r s z →
    bankInFlightControllerShape (s.1 z).pack.val
      (s.1 z).mode (s.2.sites z).controller ∧
    bankInFlightWorkerShape (s.1 z).tok
      (s.2.sites z).worker
  payloadShape : ∀ i p, bankWindowPayloadShapeReadSet r s i p →
    p ∈ rbSiteLivePayloads (s.2.sites i) →
    p.origin = none → p.atoms ≠ [] ∧ p.heads = 0
  genuinePayloadEmpty : ∀ i p o,
    bankWindowGenuinePayloadEmptyReadSet r s i p o →
    p ∈ rbSiteLivePayloads (s.2.sites i) →
    p.origin = some o → p.atoms = []
  phaseExcludes : ∀ o i p,
    bankWindowPhaseExcludesReadSet r s o i p →
    BankComparatorOriginWorker ring s o i p →
    (s.1 o.root).mode ≠ .ARMED ∧
    (s.1 o.root).mode ≠ .CSTART ∧
    (s.1 o.root).mode ≠ .IWAIT
  phaseComplete : ∀ o i p,
    bankWindowPhaseCompleteReadSet ring r s o i p →
    BankComparatorOriginWorker ring s o i p →
    (s.1 o.root).mode = .CWAIT →
    Counter.Complete ring s.1 o.root
  phaseUnique : ∀ o i p,
    bankWindowPhaseUniqueReadSet ring r s o i p →
    BankComparatorOriginWorker ring s o i p →
    (s.1 o.root).mode = .CWAIT →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        (s.1 (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = i
  phaseFlags : ∀ o i p,
    bankWindowPhaseFlagsReadSet ring r s o i p →
    BankComparatorOriginWorker ring s o i p →
    (s.1 o.root).mode = .CWAIT →
    ((s.1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring s o (s.1 i).pack.val) ∧
    ((s.1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring s o (s.1 i).pack.val) ∧
    ((s.1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring s o (compileAdvice (ceilLogTwo n)).b) ∧
    ((s.1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring s o (compileAdvice (ceilLogTwo n)).b)
  inheritedClean : ∀ root (j : Fin (compileAdvice (ceilLogTwo n)).b),
    bankWindowInheritedCleanReadSet ring r s root j →
    BankWindowScope ring s root →
    BankWindowInheritedController s root →
    ¬ BankWindowTainted s (Counter.site ring root (j.val + 1))
  resetWait : ∀ root,
    bankWindowResetWaitReadSet ring r s root →
    BankWindowScope ring s root →
    (s.1 root).mode = .RWAIT →
    (s.2.sites root).controller = .waiting [] →
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b) (rho : RenewalBankReceipt n),
      (s.2.sites (Counter.site ring root (j.val + 1))).worker =
        .pending rho ∧
      ((s.1 (Counter.site ring root (j.val + 1))).tok = .RR ∨
       (s.1 (Counter.site ring root (j.val + 1))).tok = .RL) ∧
      bankWindowZeroPrefix ring s root (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b, k.val < j.val →
        (s.1 (Counter.site ring root (k.val + 1))).tok = .E) ∧
      ((s.1 (Counter.site ring root (j.val + 1))).tok = .RL →
        bankWindowOnlyToken ring s root
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowZeroPrefix ring s root (compileAdvice (ceilLogTwo n)).b)
  armedExact : ∀ root o p,
    bankWindowArmedExactReadSet ring r s root o p →
    BankWindowScope ring s root →
    ((s.1 root).mode = .ARMED ∨ (s.1 root).mode = .CSTART) →
    (s.2.sites root).controller = .active p →
    p.origin = some o →
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      (s.1 (Counter.site ring root (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring s.1 o ∧
    ((s.1 root).mode = .ARMED →
      bankOriginBinaryValue ring s.1 o < (compileAdvice (ceilLogTwo n)).K) ∧
    ((s.1 root).mode = .CSTART →
      bankOriginBinaryValue ring s.1 o ≤ (compileAdvice (ceilLogTwo n)).K)
  incrementExact : ∀ root o i p,
    bankWindowIncrementExactReadSet ring r s root o i p →
    BankWindowScope ring s root →
    (s.1 root).mode = .IWAIT →
    (s.2.sites root).controller = .waiting [] →
    (s.2.sites i).worker = .payload p →
    p.origin = some o → o.root = root →
    bankWindowOnlyToken ring s root i ∧
    (((s.1 i).tok = .IR ∧
      bankWindowZeroPrefix ring s root (s.1 i).pack.val ∧
      p.heads = bankOriginBinaryValue ring s.1 o +
        2 ^ (s.1 i).pack.val ∧
      bankOriginBinaryValue ring s.1 o +
        2 ^ (s.1 i).pack.val ≤ (compileAdvice (ceilLogTwo n)).K) ∨
     ((s.1 i).tok = .AL ∧
      p.heads = bankOriginBinaryValue ring s.1 o ∧
      bankOriginBinaryValue ring s.1 o ≤ (compileAdvice (ceilLogTwo n)).K))
  compareExact : ∀ o i p,
    bankWindowCompareExactReadSet ring r s o i p →
    (s.2.sites i).worker = .payload p →
    p.origin = some o →
    (s.1 o.root).mode = .CWAIT →
    (s.2.sites o.root).controller = .waiting [] →
    bankWindowOnlyToken ring s o.root i ∧
    BankTrialLiveComparisonToken (s.1 i).tok ∧
    p.heads = bankOriginBinaryValue ring s.1 o ∧
    bankOriginBinaryValue ring s.1 o ≤ (compileAdvice (ceilLogTwo n)).K
  iwaitTaintedUnique : ∀ root (j : Fin (compileAdvice (ceilLogTwo n)).b),
    bankWindowIwaitTaintedUniqueReadSet ring r s root j →
    BankWindowScope ring s root →
    (s.1 root).mode = .IWAIT →
    (s.2.sites root).controller = .waiting [] →
    BankWindowTainted s (Counter.site ring root (j.val + 1)) →
    ∃ o p,
      (s.2.sites (Counter.site ring root (j.val + 1))).worker =
        .payload p ∧ p.origin = some o ∧
      o.root = root ∧
      bankWindowOnlyToken ring s root
        (Counter.site ring root (j.val + 1))
  cwaitTaintedUnique : ∀ root (j : Fin (compileAdvice (ceilLogTwo n)).b),
    bankWindowCwaitTaintedUniqueReadSet ring r s root j →
    BankWindowScope ring s root →
    (s.1 root).mode = .CWAIT →
    (s.2.sites root).controller = .waiting [] →
    BankWindowTainted s (Counter.site ring root (j.val + 1)) →
    ∃ o p,
      (s.2.sites (Counter.site ring root (j.val + 1))).worker =
        .payload p ∧ p.origin = some o ∧
      o.root = root ∧
      BankTrialLiveComparisonToken
        (s.1 (Counter.site ring root (j.val + 1))).tok ∧
      bankWindowOnlyToken ring s root
        (Counter.site ring root (j.val + 1))
  proto : ∀ root limit,
    bankWindowProtoReadSet ring r s root limit →
    BankWindowProtoRun ring s root limit →
    (∀ p o, (s.2.sites root).controller = .active p →
      p.origin = some o → False) ∧
    (BankWindowInheritedController s root →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit →
        ¬ BankWindowTainted s
          (Counter.site ring root (j.val + 1))) ∧
    (((s.1 root).mode = .RWAIT ∧
       (s.2.sites root).controller = .waiting []) →
      ∃ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit ∧
        ∃ rho : RenewalBankReceipt n,
          (s.2.sites (Counter.site ring root (j.val + 1))).worker =
            .pending rho ∧
          (s.1 (Counter.site ring root (j.val + 1))).tok = .RR ∧
          bankWindowZeroPrefix ring s root (j.val + 1) ∧
          (∀ k : Fin (compileAdvice (ceilLogTwo n)).b, k.val < j.val →
            (s.1 (Counter.site ring root (k.val + 1))).tok = .E)) ∧
    ((s.1 root).mode ≠ .RESET →
      (s.1 root).mode ≠ .RWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit →
        ¬ BankWindowTainted s
          (Counter.site ring root (j.val + 1)))
  orphan : ∀ root (j : Fin (compileAdvice (ceilLogTwo n)).b),
    bankWindowOrphanReadSet ring r s root j →
    BankWindowOrphanOwner ring s root j →
    BankWindowTainted s (Counter.site ring root (j.val + 1)) →
    (s.1 root).mode = .RESET ∨
      ((s.1 root).mode = .RWAIT ∧
        (s.2.sites root).controller = .waiting [])


theorem bankWindowExactReadSetTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (hJ : BankWindowExact ring r) :
    BankWindowExactReadSetContract ring r s := by
  refine {
    frame := ?_, payloadShape := ?_, genuinePayloadEmpty := ?_,
    phaseExcludes := ?_, phaseComplete := ?_, phaseUnique := ?_,
    phaseFlags := ?_, inheritedClean := ?_, resetWait := ?_,
    armedExact := ?_, incrementExact := ?_, compareExact := ?_,
    iwaitTaintedUnique := ?_, cwaitTaintedUnique := ?_,
    proto := ?_, orphan := ?_ }
  · intro z hr
    exact bankWindowFrameReadTransport ring r s z hJ hr
  · intro i p hr hl ho
    exact bankWindowPayloadShapeReadTransport ring r s i p hJ hr hl ho
  · intro i p o hr hl ho
    exact bankWindowGenuinePayloadEmptyReadTransport ring r s i p o hJ hr hl ho
  · intro o i p hr hw
    exact bankWindowPhaseExcludesReadTransport ring r s o i p hJ hr hw
  · intro o i p hr hw hm
    exact bankWindowPhaseCompleteReadTransport ring r s o i p hJ hr hw hm
  · intro o i p hr hw hm j ht
    exact bankWindowPhaseUniqueReadTransport ring r s o i p hJ hr hw hm j ht
  · intro o i p hr hw hm
    exact bankWindowPhaseFlagsReadTransport ring r s o i p hJ hr hw hm
  · intro root j hr hs hi ht
    exact bankWindowInheritedCleanReadTransport ring r s root j hJ hr hs hi ht
  · intro root hr hs hm hc
    exact bankWindowResetWaitReadTransport ring r s root hJ hr hs hm hc
  · intro root o p hr hs hm hc ho
    exact bankWindowArmedExactReadTransport ring r s root o p hJ hr hs hm hc ho
  · intro root o i p hr hs hm hc hw ho ha
    exact bankWindowIncrementExactReadTransport ring r s root o i p
      hJ hr hs hm hc hw ho ha
  · intro o i p hr hw ho hm hc
    exact bankWindowCompareExactReadTransport ring r s o i p
      hJ hr hw ho hm hc
  · intro root j hr hs hm hc ht
    exact bankWindowIwaitTaintedUniqueReadTransport ring r s root j
      hJ hr hs hm hc ht
  · intro root j hr hs hm hc ht
    exact bankWindowCwaitTaintedUniqueReadTransport ring r s root j
      hJ hr hs hm hc ht
  · intro root limit hr hp
    exact bankWindowProtoReadTransport ring r s root limit hJ hr hp
  · intro root j hr ho ht
    exact bankWindowOrphanReadTransport ring r s root j hJ hr ho ht


/-! A: off-pair observational framing, without a complete-window
hypothesis and without a condition on the global service counter. -/

/-- Consumer: every group in the disjoint A case. This bundles the
seven atomic physical/ghost reads that the 16 exact masks select. -/
theorem bankWindowExactOffPairAtomicReads
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e z : Fin n)
    (hsource : z ≠ e) (htarget : z ≠ ring.rightNeighbor e) :
    bankWindowReadPack r (renewalBankNext ring r e) z ∧
    bankWindowReadMode r (renewalBankNext ring r e) z ∧
    bankWindowReadTok r (renewalBankNext ring r e) z ∧
    bankWindowReadBit r (renewalBankNext ring r e) z ∧
    bankWindowReadGrant r (renewalBankNext ring r e) z ∧
    bankWindowReadWorker r (renewalBankNext ring r e) z ∧
    bankWindowReadController r (renewalBankNext ring r e) z := by
  obtain ⟨hphysical, hghost⟩ :=
    bankWindowExactOffPairFrame ring r e z hsource htarget
  exact ⟨congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
      hphysical,
    congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
      hphysical,
    congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      hphysical,
    congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      hphysical,
    congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.grant)
      hphysical,
    congrArg (fun a : RenewalBankSite n => a.worker) hghost,
    congrArg (fun a : RenewalBankSite n => a.controller) hghost⟩

theorem bankWindowExactDisjointProtoStep
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e root : Fin n)
    (limit : Nat) (hJ : BankWindowExact ring r)
    (hroot : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hpackAvoid : ∀ k : Nat, k ≤ limit + 1 →
      Counter.site ring root k ≠ e ∧
      Counter.site ring root k ≠ ring.rightNeighbor e)
    (hprefixAvoid : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit →
      Counter.site ring root (j.val + 1) ≠ e ∧
      Counter.site ring root (j.val + 1) ≠ ring.rightNeighbor e)
    (hproto : BankWindowProtoRun ring
      (renewalBankNext ring r e) root limit) :
    (∀ p o, ((renewalBankNext ring r e).2.sites root).controller =
      .active p → p.origin = some o → False) ∧
    (BankWindowInheritedController (renewalBankNext ring r e) root →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit →
        ¬ BankWindowTainted (renewalBankNext ring r e)
          (Counter.site ring root (j.val + 1))) ∧
    ((((renewalBankNext ring r e).1 root).mode = .RWAIT ∧
      ((renewalBankNext ring r e).2.sites root).controller =
        .waiting []) →
      ∃ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit ∧
        ∃ rho : RenewalBankReceipt n,
          ((renewalBankNext ring r e).2.sites
            (Counter.site ring root (j.val + 1))).worker =
            .pending rho ∧
          ((renewalBankNext ring r e).1
            (Counter.site ring root (j.val + 1))).tok = .RR ∧
          bankWindowZeroPrefix ring (renewalBankNext ring r e)
            root (j.val + 1) ∧
          (∀ k : Fin (compileAdvice (ceilLogTwo n)).b, k.val < j.val →
            ((renewalBankNext ring r e).1
              (Counter.site ring root (k.val + 1))).tok = .E)) ∧
    (((renewalBankNext ring r e).1 root).mode ≠ .RESET →
      ((renewalBankNext ring r e).1 root).mode ≠ .RWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit →
        ¬ BankWindowTainted (renewalBankNext ring r e)
          (Counter.site ring root (j.val + 1))) := by
  have hp : bankWindowReadPackPrefix ring r
      (renewalBankNext ring r e) root (limit + 1) := by
    intro k hk
    exact (bankWindowExactOffPairAtomicReads ring r e
      (Counter.site ring root k)
      (hpackAvoid k hk).1 (hpackAvoid k hk).2).1
  have hrootReads := bankWindowExactOffPairAtomicReads ring r e
    root hroot.1 hroot.2
  have hsegment :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b, j.val + 1 ≤ limit →
        bankWindowReadTok r (renewalBankNext ring r e)
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowReadBit r (renewalBankNext ring r e)
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowReadWorker r (renewalBankNext ring r e)
          (Counter.site ring root (j.val + 1)) := by
    intro j hj
    have hf := bankWindowExactOffPairAtomicReads ring r e
      (Counter.site ring root (j.val + 1))
      (hprefixAvoid j hj).1 (hprefixAvoid j hj).2
    exact ⟨hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1⟩
  exact bankWindowProtoReadTransport ring r
    (renewalBankNext ring r e) root limit hJ
    ⟨hp, hrootReads.2.1, hrootReads.2.2.2.2.2.2, hsegment⟩
    hproto


/-- Consumer: A plus groups 12--13, a foreign orphan whose
PACK prefix can be incomplete but whose read sites avoid both endpoints. -/
theorem bankWindowExactDisjointOrphanStep
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b) (hJ : BankWindowExact ring r)
    (hroot : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hpackAvoid : ∀ k : Nat, k ≤ j.val + 1 →
      Counter.site ring root k ≠ e ∧
      Counter.site ring root k ≠ ring.rightNeighbor e)
    (howner : BankWindowOrphanOwner ring
      (renewalBankNext ring r e) root j)
    (htainted : BankWindowTainted (renewalBankNext ring r e)
      (Counter.site ring root (j.val + 1))) :
    ((renewalBankNext ring r e).1 root).mode = .RESET ∨
    (((renewalBankNext ring r e).1 root).mode = .RWAIT ∧
      ((renewalBankNext ring r e).2.sites root).controller =
        .waiting []) := by
  have hp : bankWindowReadPackPrefix ring r
      (renewalBankNext ring r e) root (j.val + 1) := by
    intro k hk
    exact (bankWindowExactOffPairAtomicReads ring r e
      (Counter.site ring root k)
      (hpackAvoid k hk).1 (hpackAvoid k hk).2).1
  have hrootReads := bankWindowExactOffPairAtomicReads ring r e
    root hroot.1 hroot.2
  have hworker := bankWindowExactOffPairAtomicReads ring r e
    (Counter.site ring root (j.val + 1))
    (hpackAvoid (j.val + 1) (by omega)).1
    (hpackAvoid (j.val + 1) (by omega)).2
  exact bankWindowOrphanReadTransport ring r
    (renewalBankNext ring r e) root j hJ
    ⟨hp, hrootReads.2.1, hrootReads.2.2.2.2.2.2,
      hworker.2.2.2.2.2.1⟩ howner htainted

theorem bankWindowExactDisjointReadSetCase
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (readSite : Fin n → Prop)
    (hdisjoint : ∀ z, readSite z →
      z ≠ e ∧ z ≠ ring.rightNeighbor e) :
    (∀ z, readSite z →
      (renewalBankNext ring r e).1 z = r.1 z ∧
      (renewalBankNext ring r e).2.sites z = r.2.sites z) ∧
    BankWindowExactReadSetContract ring r
      (renewalBankNext ring r e) := by
  exact ⟨bankWindowExactDisjointSitesFrame
    ring r e readSite hdisjoint,
    bankWindowExactReadSetTransport ring r
      (renewalBankNext ring r e) hJ⟩


/-- Consumer: disjointness of the four incident geometric labels
in bankWindowGuardedGeometricIncidence. The fifth, OutsideSites,
excludes both endpoints of every prefix site by definition. -/
theorem bankWindowGuardedGeometricExclusive
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (a e : Fin n) :
    (∀ k : Nat, k ≤ (compileAdvice (ceilLogTwo n)).b →
      ring.rightNeighbor e = a →
      e ≠ Counter.site ring a k) ∧
    (∀ k : Nat, 1 ≤ k → k ≤ (compileAdvice (ceilLogTwo n)).b →
      e = a → e ≠ Counter.site ring a k) ∧
    (∀ k : Nat, 1 ≤ k → k < (compileAdvice (ceilLogTwo n)).b →
      e = Counter.site ring a k →
      e ≠ Counter.site ring a (compileAdvice (ceilLogTwo n)).b) := by
  constructor
  · intro k hk hy
    exact bankWindowIncidenceIncomingSourceOutside
      ring hbank a e hy k hk
  constructor
  · intro k hk hbound he
    rw [he]
    have hne := bankWindowIncidenceSiteDistinct
      ring hbank a 0 k (by omega) (by omega)
    change a ≠ Counter.site ring a k at hne
    exact hne
  · intro k hk hlt he
    rw [he]
    exact bankWindowIncidenceSiteDistinct
      ring hbank a k (compileAdvice (ceilLogTwo n)).b hlt (by omega)


end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Consumer: group-13 bankWindowOverlapAlignedCarrierOwnRoot; clockwise fixed-offset cancellation. -/
private theorem bankWindowOverlapFixedOffsetInjective
    {n : Nat} (ring : DirectedRing n) (k : Nat) :
    ∀ a c : Fin n,
      Counter.site ring a k = Counter.site ring c k → a = c := by
  induction k with
  | zero =>
      intro a c h
      exact h
  | succ k ih =>
      intro a c h
      change ring.rightNeighbor (Counter.site ring a k) =
        ring.rightNeighbor (Counter.site ring c k) at h
      exact ih a c (bankWindowIncidenceSuccessorInjective ring h)

/-- Consumer: group-13 foreign proto/orphan owner authentication; no complete-window premise. -/
theorem bankWindowOverlapAlignedCarrierOwnRoot
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (c z : Fin n) (k : Nat)
    (hpositive : 1 ≤ k)
    (hbound : k ≤ (compileAdvice (ceilLogTwo n)).b)
    (hsite : z = Counter.site ring c k)
    (hpack : (r.1 z).pack.val = k) :
    (∀ rho : RenewalBankReceipt n,
      (r.2.sites z).worker = .pending rho → rho.root = c) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      (r.2.sites z).worker = .payload p →
      p.origin = some o → o.root = c) := by
  constructor
  · intro rho hw
    obtain ⟨_, _, j, _, _, hjsite, hjpack, _⟩ :=
      hi.pending z rho hw
    have hj : j = k := hjpack.symm.trans hpack
    rw [hj] at hjsite
    exact bankWindowOverlapFixedOffsetInjective ring k
      rho.root c (hjsite.symm.trans hsite)
  · intro p o hw ho
    have hlow : 1 ≤ (r.1 z).pack.val := by
      rw [hpack]
      exact hpositive
    have hhigh :
        (r.1 z).pack.val ≤
          (compileAdvice (ceilLogTwo n)).b := by
      rw [hpack]
      exact hbound
    have horigin := hi.workerSite z p o hw ho hlow hhigh
    rw [hpack] at horigin
    exact bankWindowOverlapFixedOffsetInjective ring k
      o.root c (horigin.symm.trans hsite)

/-- Consumer: spacer source cases of bankWindowOverlapSpacerSourceWorkerEmpty and bankWindowOverlapTopResponderWorkerEmpty. -/
private theorem bankWindowOverlapPackNextSpacer (b v : Nat) :
    packNext (b + 1) v b = 0 := by
  simp [packNext]

/-- Consumer: role-zero responder cases in the BANK pair row decomposition. -/
private theorem bankWindowOverlapPackNextRoot (b v : Nat)
    (hb : 0 < b) :
    packNext 0 v b = 1 := by
  simp [packNext, hb]

/-- Consumer: bankWindowOverlapPairResponderWorkerBound; an interior source forces the next digit. -/
private theorem bankWindowOverlapPackNextInterior (j v b : Nat)
    (hj : j < b) :
    packNext j v b = j + 1 := by
  simp [packNext, hj]

/-- Consumer: bankWindowOverlapTopZeroResponderWorkerEmpty; top-to-root PACK stays zero. -/
private theorem bankWindowOverlapPackNextTopZero (b : Nat) :
    packNext b 0 b = 0 := by
  simp [packNext]

/-- Consumer: bankWindowOverlapTopSpacerResponderWorkerEmpty and changed responder cases. -/
private theorem bankWindowOverlapPackNextTopNonzero
    (b v : Nat) (hv : v ≠ 0) :
    packNext b v b = b + 1 := by
  simp [packNext, hv]

/-- Consumer: nonroot changed responder. The only selected ghost
wire outcomes are keep-source and erase; both clear the responder. -/
private theorem bankWindowOverlapChangedResponderWorkerEmpty
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonzero : x.pack.val ≠ 0)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hshape :
      renewalBankPairMemory c m e dest x y =
        ({ worker := (m.sites e).worker, controller := .empty },
         { worker := .empty, controller := .empty }) ∨
      renewalBankPairMemory c m e dest x y =
        ({ worker := .empty, controller := .empty },
         { worker := .empty, controller := .empty }) := by
    by_cases hupper : x.pack.val ≤ c.b
    · have hfirst : 1 ≤ x.pack.val := by omega
      simp [renewalBankPairMemory, bankCell,
        hnonzero, hfirst, hupper, hchanged]
      split <;> simp
    · have hpair :
          renewalBankPairMemory c m e dest x y =
            ({ worker := .empty, controller := .empty },
             { worker := .empty, controller := .empty }) := by
        simp [renewalBankPairMemory, bankCell,
          hnonzero, hupper, hchanged]
      exact Or.inr hpair
  rcases hshape with hkeep | herase
  · rw [hkeep]
  · rw [herase]

/-- Consumer: nonroot changed row with source above b. -/
private theorem bankWindowOverlapChangedOutsidePairWorkersEmpty
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonzero : x.pack.val ≠ 0)
    (houtside : ¬ x.pack.val ≤ c.b)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    (renewalBankPairMemory c m e dest x y).1.worker = .empty ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hpair :
      renewalBankPairMemory c m e dest x y =
        ({ worker := .empty, controller := .empty },
         { worker := .empty, controller := .empty }) := by
    simp [renewalBankPairMemory, bankCell,
      hnonzero, houtside, hchanged]
  rw [hpair]
  exact ⟨rfl, rfl⟩

/-- Consumer: selected top-to-root ghost responder erasure. -/
private theorem bankWindowOverlapTopZeroResponderWorkerEmpty
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = c.b)
    (hy : y.pack.val = 0) :
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext c.b 0 c.b = 0 :=
    bankWindowOverlapPackNextTopZero c.b
  by_cases hir : x.tok = .IR
  · cases hg : y.grant <;> cases hm : y.mode <;>
      simp [renewalBankPairMemory, bankCell,
        hx, hy, hb, hbz, hp, hir, hg, hm]
  · cases hg : y.grant <;> cases hm : y.mode <;>
      simp [renewalBankPairMemory, bankCell,
        hx, hy, hb, hbz, hp, hir, hg, hm]

/-- Consumer: selected top-to-spacer responder erasure. -/
private theorem bankWindowOverlapTopSpacerResponderWorkerEmpty
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = c.b)
    (hy : y.pack.val = c.b + 1) :
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hbz : c.b ≠ 0 := by omega
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hp : packNext c.b (c.b + 1) c.b = c.b + 1 :=
    bankWindowOverlapPackNextTopNonzero c.b (c.b + 1) (by omega)
  by_cases hir : x.tok = .IR
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := .empty, controller := .empty },
           { worker := .empty, controller := .empty }) := by
      simp [renewalBankPairMemory, bankCell, hx, hy, hb,
        hbz, houtside, hp, hir]
    rw [hpair]
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := (m.sites e).worker, controller := .empty },
           { worker := .empty, controller := .empty }) := by
      simp [renewalBankPairMemory, bankCell, hx, hy, hb,
        hbz, houtside, hp, hir]
    rw [hpair]

/-- Consumer: spacer-to-root selected-pair erasure. -/
private theorem bankWindowOverlapSpacerZeroPairWorkersEmpty
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b + 1) (hy : y.pack.val = 0) :
    (renewalBankPairMemory c m e dest x y).1.worker = .empty ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hnz : c.b + 1 ≠ 0 := by omega
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hp : packNext (c.b + 1) 0 c.b = 0 :=
    bankWindowOverlapPackNextSpacer c.b 0
  cases hg : y.grant <;> cases hm : y.mode <;>
    simp [renewalBankPairMemory, bankCell,
      hx, hy, hnz, houtside, hp, hg, hm]

/-- Consumer: bankWindowOverlapPairSourceWorkerBound; an out-of-band source leaves no worker. -/
private theorem bankWindowOverlapSpacerSourceWorkerEmpty
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hspacer : x.pack.val = c.b + 1) :
    (renewalBankPairMemory c m e dest x y).1.worker = .empty := by
  by_cases hyzero : y.pack.val = 0
  · exact (bankWindowOverlapSpacerZeroPairWorkersEmpty
      c m e dest x y hspacer hyzero).1
  · have hnonzero : x.pack.val ≠ 0 := by omega
    have houtside : ¬ x.pack.val ≤ c.b := by omega
    have hpost : packNext x.pack.val y.pack.val c.b = 0 := by
      rw [hspacer]
      exact bankWindowOverlapPackNextSpacer c.b y.pack.val
    have hchanged :
        packNext x.pack.val y.pack.val c.b ≠ y.pack.val := by
      rw [hpost]
      exact Ne.symm hyzero
    exact (bankWindowOverlapChangedOutsidePairWorkersEmpty
      c m e dest x y hnonzero houtside hchanged).1

/-- Consumer: bankWindowOverlapGenuineWorkerInBandStep; a surviving source worker is in-band. -/
private theorem bankWindowOverlapPairSourceWorkerBound
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (p : RenewalBankPayload n)
    (hw : (renewalBankPairMemory c m e dest x y).1.worker =
      .payload p) :
    1 ≤ x.pack.val ∧ x.pack.val ≤ c.b := by
  by_cases hzero : x.pack.val = 0
  · have hempty := rbBankRootSourceWorkerEmpty
      c m e dest x y hzero
    rw [hempty] at hw
    cases hw
  · by_cases hupper : x.pack.val ≤ c.b
    · exact ⟨by omega, hupper⟩
    · have hspacer : x.pack.val = c.b + 1 := by
        have hlimit := x.pack.isLt
        omega
      have hempty := bankWindowOverlapSpacerSourceWorkerEmpty
        c m e dest x y hspacer
      rw [hempty] at hw
      cases hw

/-- Consumer: bankWindowOverlapPairResponderWorkerBound; top and spacer responders erase workers. -/
private theorem bankWindowOverlapTopResponderWorkerEmpty
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hpositive : 0 < c.b) (htop : c.b ≤ x.pack.val) :
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hnonzero : x.pack.val ≠ 0 := by omega
  by_cases heq : x.pack.val = c.b
  · by_cases hyzero : y.pack.val = 0
    · exact bankWindowOverlapTopZeroResponderWorkerEmpty
        c m e dest x y hpositive heq hyzero
    · by_cases hyspacer : y.pack.val = c.b + 1
      · exact bankWindowOverlapTopSpacerResponderWorkerEmpty
          c m e dest x y hpositive heq hyspacer
      · have hnext :
            packNext x.pack.val y.pack.val c.b = c.b + 1 := by
          rw [heq]
          exact bankWindowOverlapPackNextTopNonzero
            c.b y.pack.val hyzero
        have hchanged :
            packNext x.pack.val y.pack.val c.b ≠ y.pack.val := by
          rw [hnext]
          exact Ne.symm hyspacer
        exact bankWindowOverlapChangedResponderWorkerEmpty
          c m e dest x y hnonzero hchanged
  · have hspacer : x.pack.val = c.b + 1 := by
      have hlimit := x.pack.isLt
      omega
    by_cases hyzero : y.pack.val = 0
    · exact (bankWindowOverlapSpacerZeroPairWorkersEmpty
        c m e dest x y hspacer hyzero).2
    · have hnext :
          packNext x.pack.val y.pack.val c.b = 0 := by
        rw [hspacer]
        exact bankWindowOverlapPackNextSpacer c.b y.pack.val
      have hchanged :
          packNext x.pack.val y.pack.val c.b ≠ y.pack.val := by
        rw [hnext]
        exact Ne.symm hyzero
      exact bankWindowOverlapChangedResponderWorkerEmpty
        c m e dest x y hnonzero hchanged

/-- Consumer: bankWindowOverlapGenuineWorkerInBandStep; output responder worker implies digit PACK. -/
private theorem bankWindowOverlapPairResponderWorkerBound
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hpositive : 0 < c.b) (p : RenewalBankPayload n)
    (hw : (renewalBankPairMemory c m e dest x y).2.worker =
      .payload p) :
    1 ≤ packNext x.pack.val y.pack.val c.b ∧
      packNext x.pack.val y.pack.val c.b ≤ c.b := by
  by_cases hinside : x.pack.val < c.b
  · have hnext :
        packNext x.pack.val y.pack.val c.b =
          x.pack.val + 1 :=
      bankWindowOverlapPackNextInterior x.pack.val y.pack.val c.b hinside
    rw [hnext]
    omega
  · have hempty := bankWindowOverlapTopResponderWorkerEmpty
      c m e dest x y hpositive (by omega)
    rw [hempty] at hw
    cases hw

/-- Consumer: bankWindowOverlapGenuineWorkerInBandRun; actual two-port worker roles. -/
private theorem bankWindowOverlapGenuineWorkerInBandStep
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hold : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      (r.2.sites i).worker = .payload p →
      p.origin = some o →
      1 ≤ (r.1 i).pack.val ∧
      (r.1 i).pack.val ≤
        (compileAdvice (ceilLogTwo n)).b) :
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      ((renewalBankNext ring r e).2.sites i).worker =
        .payload p →
      p.origin = some o →
      1 ≤ ((renewalBankNext ring r e).1 i).pack.val ∧
      ((renewalBankNext ring r e).1 i).pack.val ≤
        (compileAdvice (ceilLogTwo n)).b := by
  intro i p o hw ho
  have hpair := rbReferenceSelectedPairFrame ring hn r e
  have hpack := rbBankReferencePairPack ring hn r e
  have hwidth : 0 < (compileAdvice (ceilLogTwo n)).b :=
    rbBankWidthPositive (ceilLogTwo n)
  by_cases hsource : i = e
  · subst i
    change ((rbRun ring r [e]).2.sites e).worker = .payload p at hw
    rw [hpair.2.2.1] at hw
    have hbound := bankWindowOverlapPairSourceWorkerBound
      (compileAdvice (ceilLogTwo n)) r.2 e
      (ring.rightNeighbor e) (r.1 e)
      (r.1 (ring.rightNeighbor e)) p hw
    change
      1 ≤ ((rbRun ring r [e]).1 e).pack.val ∧
      ((rbRun ring r [e]).1 e).pack.val ≤
        (compileAdvice (ceilLogTwo n)).b
    rw [hpack.1]
    exact hbound
  · by_cases htarget : i = ring.rightNeighbor e
    · subst i
      change ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker = .payload p at hw
      rw [hpair.2.2.2] at hw
      have hbound := bankWindowOverlapPairResponderWorkerBound
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e) (r.1 e)
        (r.1 (ring.rightNeighbor e)) hwidth p hw
      change
        1 ≤ ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).pack.val ∧
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).pack.val ≤
            (compileAdvice (ceilLogTwo n)).b
      rw [hpack.2]
      exact hbound
    · have hframe := bankWindowExactOffPairFrame
        ring r e i hsource htarget
      rw [hframe.2] at hw
      rw [hframe.1]
      exact hold i p o hw ho

/-- Consumer: bankWindowOverlapGenuineWorkerInBand; entrance payload has origin none. -/
private theorem bankWindowOverlapInitialNoGenuineWorker
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (i : Fin n)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : ((renewalBankStart ring seed).2.sites i).worker =
      .payload p)
    (ho : p.origin = some o) : False := by
  change
    (if (seed.val i).tok = .E then
      (.empty : RenewalBankWorker n)
     else .payload (renewalBankEntrancePayload i false)) =
      .payload p at hw
  by_cases he : (seed.val i).tok = .E
  · rw [if_pos he] at hw
    cases hw
  · rw [if_neg he] at hw
    cases hw
    change (none : Option (RenewalBankOrigin n)) = some o at ho
    cases ho

/-- Consumer: bankWindowOverlapGenuineWorkerInBand; word induction on the actual BANK observer. -/
private theorem bankWindowOverlapGenuineWorkerInBandRun
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) :
    ∀ (pre : List (Fin n)) (r : RenewalBankReference n),
      (∀ (i : Fin n) (p : RenewalBankPayload n)
        (o : RenewalBankOrigin n),
        (r.2.sites i).worker = .payload p →
        p.origin = some o →
        1 ≤ (r.1 i).pack.val ∧
        (r.1 i).pack.val ≤ (compileAdvice (ceilLogTwo n)).b) →
      ∀ (i : Fin n) (p : RenewalBankPayload n)
        (o : RenewalBankOrigin n),
        ((rbRun ring r pre).2.sites i).worker = .payload p →
        p.origin = some o →
        1 ≤ ((rbRun ring r pre).1 i).pack.val ∧
        ((rbRun ring r pre).1 i).pack.val ≤
          (compileAdvice (ceilLogTwo n)).b := by
  intro pre
  induction pre with
  | nil =>
      intro r hinit i p o hw ho
      exact hinit i p o hw ho
  | cons e tail ih =>
      intro r hinit i p o hw ho
      have hnext := bankWindowOverlapGenuineWorkerInBandStep
        ring hn r e hinit
      exact ih (renewalBankNext ring r e) hnext i p o hw ho

/-- Consumer: bankWindowGenuineWorkerSiteOfRun; every genuinely originated reachable worker is in-band. -/
theorem bankWindowOverlapGenuineWorkerInBand
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (_hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (i : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (hw : ((rbRun ring (renewalBankStart ring seed) pre).2.sites i).worker =
      .payload p)
    (ho : p.origin = some o) :
    1 ≤ ((rbRun ring (renewalBankStart ring seed) pre).1 i).pack.val ∧
    ((rbRun ring (renewalBankStart ring seed) pre).1 i).pack.val ≤
      (compileAdvice (ceilLogTwo n)).b := by
  have hinit :
      ∀ (z : Fin n) (q : RenewalBankPayload n)
        (origin : RenewalBankOrigin n),
        ((renewalBankStart ring seed).2.sites z).worker = .payload q →
        q.origin = some origin →
        1 ≤ ((renewalBankStart ring seed).1 z).pack.val ∧
        ((renewalBankStart ring seed).1 z).pack.val ≤
          (compileAdvice (ceilLogTwo n)).b := by
    intro z q origin hworker horigin
    exact False.elim
      (bankWindowOverlapInitialNoGenuineWorker
        ring seed z q origin hworker horigin)
  exact bankWindowOverlapGenuineWorkerInBandRun
    ring (by omega : 2 ≤ n)
    pre (renewalBankStart ring seed) hinit i p o hw ho

/-- Consumer: group-13 phaseFlags/compareExact; ReceiptInv.workerSite without explicit PACK hypotheses. -/
theorem bankWindowGenuineWorkerSiteOfRun
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (i : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (hw : ((rbRun ring (renewalBankStart ring seed) pre).2.sites i).worker =
      .payload p)
    (ho : p.origin = some o) :
    i = Counter.site ring o.root
      ((rbRun ring (renewalBankStart ring seed) pre).1 i).pack.val := by
  have hband := bankWindowOverlapGenuineWorkerInBand
    ring hn hbank seed pre i p o hw ho
  have hi := rbReceiptInvBankWordOfInv
    ring (by omega : 2 ≤ n) seed hbank pre
  exact hi.workerSite i p o hw ho hband.1 hband.2

end L3.BankWindow


#print axioms L3.BankWindow.bankWindowClosureBirthCreatesGenuineRoot
#print axioms L3.BankWindow.bankWindowClosureBirthKeepsPackPrefix
#print axioms L3.BankWindow.bankWindowClosureBirthComplete
#print axioms L3.BankWindow.bankWindowClosureBirthClearedWindow
#print axioms L3.BankWindow.bankWindowClosureBirthPostArmed
#print axioms L3.BankWindow.bankWindowClosureChangedResponderNoOrigin
#print axioms L3.BankWindow.bankWindowClosureResetLaunchGhost
#print axioms L3.BankWindow.bankWindowClosureOrphanForwardFrame
#print axioms L3.BankWindow.bankWindowClosureOrphanTopTurnFrame
#print axioms L3.BankWindow.bankWindowClosureOffWindowAlignedPrefix
#print axioms L3.BankWindow.bankWindowClosureOffWindowScope
#print axioms L3.BankWindow.bankWindowClosureOffWindowZeroPrefix
#print axioms L3.BankWindow.bankWindowClosureOffWindowOnlyToken
#print axioms L3.BankWindow.bankWindowClosureOffWindowTainted
#print axioms L3.BankWindow.bankWindowClosureOffWindowInherited
#print axioms L3.BankWindow.bankWindowClosureOffWindowProto
#print axioms L3.BankWindow.bankWindowClosureOffWindowOrphan
#print axioms L3.BankWindow.bankWindowClosureOffWindowPayloadFields
#print axioms L3.BankWindow.bankWindowClosureOffWindowInheritedClean
#print axioms L3.BankWindow.bankWindowClosureOffWindowProtoNoGenuine
#print axioms L3.BankWindow.bankWindowClosureOffWindowBinaryValue
#print axioms L3.BankWindow.bankWindowClosureOffWindowArmedExact
#print axioms L3.BankWindow.bankWindowClosureCompleteInternalPack
#print axioms L3.BankWindow.bankWindowClosureCompleteResetLaunch
#print axioms L3.BankWindow.bankWindowClosureCompletePendingForward
#print axioms L3.BankWindow.bankWindowClosureCompleteTopTurn
#print axioms L3.BankWindow.bankWindowClosureBirthCompletePost
#print axioms L3.BankWindow.bankWindowClosureChangedDigitClean
#print axioms L3.BankWindow.bankWindowClosureBrokenRootSanitized
#print axioms L3.BankWindow.bankWindowClosureResetLaunchPhysicalPair
#print axioms L3.BankWindow.bankWindowClosureResetLaunchWaitWitness
#print axioms L3.BankWindow.bankWindowClosureInteriorRootWaitFrame
#print axioms L3.BankWindow.bankWindowClosurePendingForwardWaitCarrier
#print axioms L3.BankWindow.bankWindowClosureTopTurnWaitCarrier
#print axioms L3.BankWindow.bankWindowClosureInternalNoProtoOrphan
#print axioms L3.BankWindow.bankWindowClosureBirthNoProtoOrphan
#print axioms L3.BankWindow.bankWindowClosureBrokenRootNoProtoOrphan
#print axioms L3.BankWindow.bankWindowClosureRepairDigitNoTaint
#print axioms L3.BankWindow.bankWindowClosureArmedIssueGenuine
#print axioms L3.BankWindow.bankWindowClosureArmedSetGenuine
#print axioms L3.BankWindow.bankWindowClosureMatchedReturnGenuine
#print axioms L3.BankWindow.bankWindowClosureIncrementReturnExactGhost
#print axioms L3.BankWindow.bankWindowClosureCstartIssueGenuine
#print axioms L3.BankWindow.bankWindowClosureCompareReturnExactGhost
#print axioms L3.BankWindow.bankWindowClosureSelectedBankTrip
#print axioms L3.BankWindow.bankWindowClosureRootWaitTimeout
#print axioms L3.BankWindow.bankWindowClosureInteriorIrCrWorkerForward
#print axioms L3.BankWindow.bankWindowClosureClOneReturnClears
#print axioms L3.BankWindow.bankWindowClosureRepairNonresponderPackFixed
#print axioms L3.BankWindow.bankWindowClosureRepairFirstMismatchAtResponder
#print axioms L3.BankWindow.bankWindowClosureRepairOldProtoAtDigit
#print axioms L3.BankWindow.bankWindowClosureRepairOldSuffixTaintModes
#print axioms L3.BankWindow.bankWindowClosureIncompleteCwaitNoOwnWorker
#print axioms L3.BankWindow.bankWindowClosureRepairProtoReadSetFrame
#print axioms L3.BankWindow.bankWindowClosureRepairOrphanReadSetFrame
#print axioms L3.BankWindow.bankWindowClosureChangedWorkerChoice
#print axioms L3.BankWindow.bankWindowClosureChangedTaintOld
#print axioms L3.BankWindow.bankWindowClosureRepairNonresetPhaseDigitsClean
#print axioms L3.BankWindow.bankWindowClosureRepairCwaitNoOwnWorker
#print axioms L3.BankWindow.bankWindowClosureRepairInheritedDigitsClean
#print axioms L3.BankWindow.bankWindowClosureRepairNonresetScopedClauses
#print axioms L3.BankWindow.bankWindowClosureRepairNonincidentGenuineController
#print axioms L3.BankWindow.bankWindowClosureRepairResetSourceNoLaunch
#print axioms L3.BankWindow.bankWindowExactSelectedPayloadStep
#print axioms L3.BankWindow.bankWindowIncomingRootCoreStep
#print axioms L3.BankWindow.bankWindowIncomingPredecessorOutsideDigits
#print axioms L3.BankWindow.bankWindowIncomingDigitReadSetFrame
#print axioms L3.BankWindow.bankWindowIncomingPackReadSetFrame
#print axioms L3.BankWindow.bankWindowIncomingZeroPrefixReadSetFrame
#print axioms L3.BankWindow.bankWindowIncomingOnlyTokenReadSetFrame
#print axioms L3.BankWindow.bankWindowIncomingTaintedReadSetFrame
#print axioms L3.BankWindow.bankWindowIncomingBinaryValueReadSetFrame
#print axioms L3.BankWindow.bankWindowIncomingComparatorPrefixReadSetFrame
#print axioms L3.BankWindow.bankWindowIncomingProtoReadSetFrame
#print axioms L3.BankWindow.bankWindowIncomingOrphanReadSetFrame
#print axioms L3.BankWindow.bankWindowIncomingScopeBackward
#print axioms L3.BankWindow.bankWindowIncomingResetWaitSurvivor
#print axioms L3.BankWindow.bankWindowIncomingIwaitExact
#print axioms L3.BankWindow.bankWindowIncomingCwaitExact
#print axioms L3.BankWindow.bankWindowIncomingPostWorkerAnchor
#print axioms L3.BankWindow.bankWindowIncomingComparatorDigitSurvivor
#print axioms L3.BankWindow.bankWindowIncomingCompareDigitSurvivor
#print axioms L3.BankWindow.bankWindowIncomingIwaitTaintedSurvivor
#print axioms L3.BankWindow.bankWindowIncomingCwaitTaintedSurvivor
#print axioms L3.BankWindow.bankWindowIncomingInheritedCleanSurvivor
#print axioms L3.BankWindow.bankWindowIncomingOrphanOwnerSurvivor
#print axioms L3.BankWindow.bankWindowIncomingProtoOwnerSurvivor
#print axioms L3.BankWindow.bankWindowIncomingResetOwnerFields
#print axioms L3.BankWindow.bankWindowIncomingPhaseCompleteDigitSurvivor
#print axioms L3.BankWindow.bankWindowIncomingPhaseExcludesDigitSurvivor
#print axioms L3.BankWindow.bankWindowIncomingIncrementDigitSurvivor
#print axioms L3.BankWindow.bankWindowIncomingComparatorOffPairSurvivor
#print axioms L3.BankWindow.bankWindowIncomingCompareOffPairSurvivor
#print axioms L3.BankWindow.bankWindowIncomingTopSourceNoResponderOrigin
#print axioms L3.BankWindow.bankWindowIncomingSourceNoResponderOrigin
#print axioms L3.BankWindow.bankWindowFrameReadTransport
#print axioms L3.BankWindow.bankWindowPayloadShapeReadTransport
#print axioms L3.BankWindow.bankWindowGenuinePayloadEmptyReadTransport
#print axioms L3.BankWindow.bankWindowPhaseExcludesReadTransport
#print axioms L3.BankWindow.bankWindowPhaseCompleteReadTransport
#print axioms L3.BankWindow.bankWindowPhaseUniqueReadTransport
#print axioms L3.BankWindow.bankWindowPhaseFlagsReadTransport
#print axioms L3.BankWindow.bankWindowIncidenceSiteDistinct
#print axioms L3.BankWindow.bankWindowIncidenceIncomingSourceOutside
#print axioms L3.BankWindow.bankWindowGuardedGeometricIncidence
#print axioms L3.BankWindow.bankWindowExactDisjointSitesFrame
#print axioms L3.BankWindow.bankWindowInheritedCleanReadTransport
#print axioms L3.BankWindow.bankWindowResetWaitReadTransport
#print axioms L3.BankWindow.bankWindowArmedExactReadTransport
#print axioms L3.BankWindow.bankWindowIncrementExactReadTransport
#print axioms L3.BankWindow.bankWindowCompareExactReadTransport
#print axioms L3.BankWindow.bankWindowIwaitTaintedUniqueReadTransport
#print axioms L3.BankWindow.bankWindowCwaitTaintedUniqueReadTransport
#print axioms L3.BankWindow.bankWindowProtoReadTransport
#print axioms L3.BankWindow.bankWindowOrphanReadTransport
#print axioms L3.BankWindow.bankWindowExactReadSetTransport
#print axioms L3.BankWindow.bankWindowExactOffPairAtomicReads
#print axioms L3.BankWindow.bankWindowExactDisjointProtoStep
#print axioms L3.BankWindow.bankWindowExactDisjointOrphanStep
#print axioms L3.BankWindow.bankWindowExactDisjointReadSetCase
#print axioms L3.BankWindow.bankWindowGuardedGeometricExclusive
#print axioms L3.BankWindow.bankWindowOverlapAlignedCarrierOwnRoot
#print axioms L3.BankWindow.bankWindowOverlapGenuineWorkerInBand
#print axioms L3.BankWindow.bankWindowGenuineWorkerSiteOfRun
