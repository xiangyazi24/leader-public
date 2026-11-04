import Leader.L3.Bank.InheritedExtinction

/-!
Inherited-atom selected-pair census over the literal BANK ghost
transition.

The proof is split into root
matching, root sanitation, nonroot worker wiring, and top-to-root
waiting-controller families. The first-match ghost program is
renewalBankPairMemory; post-step projection uses the already proved
selected-pair frame.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

private def bankInheritedPairAtomMass {n : Nat}
    (p : RenewalBankSite n × RenewalBankSite n) : Nat :=
  bankInheritedSiteAtomCount p.1 +
    bankInheritedSiteAtomCount p.2

/-- All six existing interior worker-wiring constructors only
move or remove a worker. Controllers are removed in this family. -/
private theorem bankInheritedWiringMassLe {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (s t : RenewalBankSite n)
    (hw : RBWorkerWiring m e dest s t) :
    bankInheritedPairAtomMass (s, t) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  cases hw <;>
    simp [bankInheritedPairAtomMass,
      bankInheritedSiteAtomCount,
      bankInheritedControllerAtomCount,
      bankInheritedWorkerAtomCount] <;>
    omega

/-- The one remaining nonroot special form has a retained/erased
source worker and a nonincreasing responder wait slot. -/
private theorem bankInheritedTargetWaitMassLe {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (w : RenewalBankWorker n)
    (hw :
      bankInheritedWorkerAtomCount w ≤
        bankInheritedWorkerAtomCount (m.sites e).worker)
    (mode : Mode) (lease : Nat) (gate : Bool) :
    bankInheritedPairAtomMass
      ({ worker := w, controller := .empty },
       { worker := .empty,
         controller := if gate then .empty else
           renewalBankWaitSlot mode lease (m.sites dest).controller }) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  have hwait := bankInheritedWaitSlotAtomCountLe
    mode lease (m.sites dest).controller
  cases gate <;>
    simp [bankInheritedPairAtomMass,
      bankInheritedSiteAtomCount,
      bankInheritedControllerAtomCount,
      bankInheritedWorkerAtomCount] at hw hwait ⊢ <;>
    omega

theorem bankInheritedPackNextZero (c b : Nat) (hb : 0 < b) :
    packNext 0 c b = 1 := by
  simp [packNext, hb]

/-- Root sanitation on a changed responder PACK role: erasures
and lease ticks never allocate a label. -/
private theorem bankInheritedChangedRootMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val ≠ 1) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    rw [← hx]
    exact hp
  have hchanged : packNext x.pack.val y.pack.val c.b ≠
      y.pack.val := by
    rw [hp]
    exact Ne.symm hy
  have hchanged0 : packNext 0 y.pack.val c.b ≠ y.pack.val := by
    rw [hp0]
    exact Ne.symm hy
  cases hg : x.grant <;> cases hm : x.mode <;>
    by_cases hlease : 1 < x.lease.val <;>
    simp [renewalBankPairMemory, bankCell,
      bankInheritedPairAtomMass, bankInheritedSiteAtomCount,
      bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount,
      renewalBankWaitSlot, isWaitMode, isRetTok,
      hx, hy, hb, hbz, hp, hp0, bankInheritedPackNextZero, Ne.symm hy, hchanged, hchanged0, hg, hm, hlease] <;>
    omega

/-- On the matched first-digit root row an OLD grant erases
both selected workers/controllers. -/
private theorem bankInheritedMatchedGrantMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = true) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    rw [← hx]
    exact hp
  simp [renewalBankPairMemory, bankCell,
    bankInheritedPairAtomMass, bankInheritedSiteAtomCount,
    bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount,
    hx, hy, hb, hbz, hp, hp0, bankInheritedPackNextZero, hg]

private theorem bankInheritedMatchedResetMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RESET)
    (hsc : bankInFlightControllerShape x.pack.val x.mode
      (m.sites e).controller)
    (htw : bankInFlightWorkerShape y.tok
      (m.sites dest).worker) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
    bankInheritedPairAtomMass
      (m.sites e, m.sites dest) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hinside : 1 < c.b := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    rw [← hx]
    exact hp

  simp [renewalBankPairMemory, bankCell,
      bankInheritedPairAtomMass, bankInheritedSiteAtomCount,
      bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount,
      bankInheritedPayloadAtomCount, renewalBankWaitSlot,
      renewalBankReturned, renewalBankWorkerPayload,
      renewalBankActivePayload, renewalBankWaitingAtoms,
      renewalBankHead, isRetTok, isWaitMode,
      List.length_append, hx, hy, hb, hbz, hp, hp0, bankInheritedPackNextZero, hinside,
      hwide, hg, hm]

private theorem bankInheritedMatchedArmedMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .ARMED)
    (hsc : bankInFlightControllerShape x.pack.val x.mode
      (m.sites e).controller)
    (htw : bankInFlightWorkerShape y.tok
      (m.sites dest).worker) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
    bankInheritedPairAtomMass
      (m.sites e, m.sites dest) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hinside : 1 < c.b := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    rw [← hx]
    exact hp

  have hactive :
      ∃ p : RenewalBankPayload n,
        (m.sites e).controller = .active p := by
    have hc := hsc
    unfold bankInFlightControllerShape at hc
    rw [if_pos hx, hm] at hc
    exact hc
  obtain ⟨p, hsource⟩ := hactive
  cases ht : y.tok <;> cases hw : (m.sites dest).worker <;>
    cases hbit : y.bit <;>
    simp [bankInFlightWorkerShape, ht, hw] at htw <;>
    simp [renewalBankPairMemory, bankCell,
      bankInheritedPairAtomMass, bankInheritedSiteAtomCount,
      bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount,
      bankInheritedPayloadAtomCount, renewalBankWaitSlot,
      renewalBankReturned, renewalBankWorkerPayload,
      renewalBankActivePayload, renewalBankWaitingAtoms,
      renewalBankHead, isRetTok, isWaitMode,
      List.length_append, hx, hy, hb, hbz, hp, hp0, bankInheritedPackNextZero, hinside,
      hwide, hg, hm, ht, hw, hbit, hsource] <;>
    omega

private theorem bankInheritedMatchedCstartMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .CSTART)
    (hsc : bankInFlightControllerShape x.pack.val x.mode
      (m.sites e).controller)
    (htw : bankInFlightWorkerShape y.tok
      (m.sites dest).worker) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
    bankInheritedPairAtomMass
      (m.sites e, m.sites dest) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hinside : 1 < c.b := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    rw [← hx]
    exact hp

  have hactive :
      ∃ p : RenewalBankPayload n,
        (m.sites e).controller = .active p := by
    have hc := hsc
    unfold bankInFlightControllerShape at hc
    rw [if_pos hx, hm] at hc
    exact hc
  obtain ⟨p, hsource⟩ := hactive
  cases ht : y.tok <;> cases hw : (m.sites dest).worker <;>
    cases hbit : y.bit <;>
    simp [bankInFlightWorkerShape, ht, hw] at htw <;>
    simp [renewalBankPairMemory, bankCell,
      bankInheritedPairAtomMass, bankInheritedSiteAtomCount,
      bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount,
      bankInheritedPayloadAtomCount, renewalBankWaitSlot,
      renewalBankReturned, renewalBankWorkerPayload,
      renewalBankActivePayload, renewalBankWaitingAtoms,
      renewalBankHead, isRetTok, isWaitMode,
      List.length_append, hx, hy, hb, hbz, hp, hp0, bankInheritedPackNextZero, hinside,
      hwide, hg, hm, ht, hw, hbit, hsource] <;>
    omega

private theorem bankInheritedMatchedRwaitMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RWAIT)
    (hsc : bankInFlightControllerShape x.pack.val x.mode
      (m.sites e).controller)
    (htw : bankInFlightWorkerShape y.tok
      (m.sites dest).worker) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
    bankInheritedPairAtomMass
      (m.sites e, m.sites dest) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hinside : 1 < c.b := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    rw [← hx]
    exact hp

  have hwaiting :
      ∃ atoms : List (RenewalBankAtom n),
        (m.sites e).controller = .waiting atoms := by
    have hc := hsc
    unfold bankInFlightControllerShape at hc
    rw [if_pos hx, hm] at hc
    exact hc
  obtain ⟨atoms, hsource⟩ := hwaiting
  cases ht : y.tok <;> cases hw : (m.sites dest).worker <;>
    by_cases hlease : 1 < x.lease.val <;>
    simp [bankInFlightWorkerShape, ht, hw] at htw <;>
    simp [renewalBankPairMemory, bankCell,
      bankInheritedPairAtomMass, bankInheritedSiteAtomCount,
      bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount,
      bankInheritedPayloadAtomCount, renewalBankWaitSlot,
      renewalBankReturned, renewalBankWorkerPayload,
      renewalBankActivePayload, renewalBankWaitingAtoms,
      renewalBankHead, isRetTok, isWaitMode,
      List.length_append, hx, hy, hb, hbz, hp, hp0, bankInheritedPackNextZero, hinside,
      hwide, hg, hm, ht, hw, hlease, hsource] <;>
    omega

private theorem bankInheritedMatchedIwaitMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .IWAIT)
    (hsc : bankInFlightControllerShape x.pack.val x.mode
      (m.sites e).controller)
    (htw : bankInFlightWorkerShape y.tok
      (m.sites dest).worker) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
    bankInheritedPairAtomMass
      (m.sites e, m.sites dest) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hinside : 1 < c.b := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    rw [← hx]
    exact hp

  have hwaiting :
      ∃ atoms : List (RenewalBankAtom n),
        (m.sites e).controller = .waiting atoms := by
    have hc := hsc
    unfold bankInFlightControllerShape at hc
    rw [if_pos hx, hm] at hc
    exact hc
  obtain ⟨atoms, hsource⟩ := hwaiting
  cases ht : y.tok <;> cases hw : (m.sites dest).worker <;>
    by_cases hlease : 1 < x.lease.val <;>
    simp [bankInFlightWorkerShape, ht, hw] at htw <;>
    simp [renewalBankPairMemory, bankCell,
      bankInheritedPairAtomMass, bankInheritedSiteAtomCount,
      bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount,
      bankInheritedPayloadAtomCount, renewalBankWaitSlot,
      renewalBankReturned, renewalBankWorkerPayload,
      renewalBankActivePayload, renewalBankWaitingAtoms,
      renewalBankHead, isRetTok, isWaitMode,
      List.length_append, hx, hy, hb, hbz, hp, hp0, bankInheritedPackNextZero, hinside,
      hwide, hg, hm, ht, hw, hlease, hsource] <;>
    omega

private theorem bankInheritedMatchedCwaitMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .CWAIT)
    (hsc : bankInFlightControllerShape x.pack.val x.mode
      (m.sites e).controller)
    (htw : bankInFlightWorkerShape y.tok
      (m.sites dest).worker) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
    bankInheritedPairAtomMass
      (m.sites e, m.sites dest) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hinside : 1 < c.b := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    rw [← hx]
    exact hp

  have hwaiting :
      ∃ atoms : List (RenewalBankAtom n),
        (m.sites e).controller = .waiting atoms := by
    have hc := hsc
    unfold bankInFlightControllerShape at hc
    rw [if_pos hx, hm] at hc
    exact hc
  obtain ⟨atoms, hsource⟩ := hwaiting
  cases ht : y.tok <;> cases hw : (m.sites dest).worker <;>
    by_cases hlease : 1 < x.lease.val <;>
    simp [bankInFlightWorkerShape, ht, hw] at htw <;>
    simp [renewalBankPairMemory, bankCell,
      bankInheritedPairAtomMass, bankInheritedSiteAtomCount,
      bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount,
      bankInheritedPayloadAtomCount, renewalBankWaitSlot,
      renewalBankReturned, renewalBankWorkerPayload,
      renewalBankActivePayload, renewalBankWaitingAtoms,
      renewalBankHead, isRetTok, isWaitMode,
      List.length_append, hx, hy, hb, hbz, hp, hp0, bankInheritedPackNextZero, hinside,
      hwide, hg, hm, ht, hw, hlease, hsource] <;>
    omega


/-- Root matching: the in-flight shape supplies an actual active
controller in ARMED/CSTART, a real waiting list in wait modes,
and a nonempty worker for every non-E token. In the RL/pending
branch only the old waiting list is promoted; in RL/payload,
AL/payload, and CL0/payload the old lists are merged once. -/
private theorem bankInheritedMatchedRootMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hsc : bankInFlightControllerShape x.pack.val x.mode
      (m.sites e).controller)
    (htw : bankInFlightWorkerShape y.tok
      (m.sites dest).worker) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  have hb : 0 < c.b := by
    unfold Compiled.b
    omega
  have hwide : c.b ≠ 1 := by
    unfold Compiled.b
    omega
  cases hg : x.grant with
  | true =>
      exact bankInheritedMatchedGrantMassLe
        c m e dest x y hb hx hy hg
  | false =>
      cases hm : x.mode with
      | RESET =>
          exact bankInheritedMatchedResetMassLe
            c m e dest x y hb hwide hx hy hg hm hsc htw
      | ARMED =>
          exact bankInheritedMatchedArmedMassLe
            c m e dest x y hb hwide hx hy hg hm hsc htw
      | RWAIT =>
          exact bankInheritedMatchedRwaitMassLe
            c m e dest x y hb hwide hx hy hg hm hsc htw
      | IWAIT =>
          exact bankInheritedMatchedIwaitMassLe
            c m e dest x y hb hwide hx hy hg hm hsc htw
      | CSTART =>
          exact bankInheritedMatchedCstartMassLe
            c m e dest x y hb hwide hx hy hg hm hsc htw
      | CWAIT =>
          exact bankInheritedMatchedCwaitMassLe
            c m e dest x y hb hwide hx hy hg hm hsc htw

/-- All root-source cases: either the responder changes role,
or the root's matched role-one action is one of the six
physical-mode families. -/
private theorem bankInheritedRootMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0)
    (hsc : bankInFlightControllerShape x.pack.val x.mode
      (m.sites e).controller)
    (htw : bankInFlightWorkerShape y.tok
      (m.sites dest).worker) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  have hb : 0 < c.b := by
    unfold Compiled.b
    omega
  by_cases hy : y.pack.val = 1
  · exact bankInheritedMatchedRootMassLe
      c m e dest x y hx hy hsc htw
  · exact bankInheritedChangedRootMassLe
      c m e dest x y hb hx hy

/-- Top-to-zero: a possibly inherited destination waiting list
only survives a lease tick; no source controller survives. -/
private theorem bankInheritedTopZeroMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b) (hy : y.pack.val = 0) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext c.b 0 c.b = 0 := by
    simp [packNext]
  by_cases hir : x.tok = .IR
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := .empty, controller := .empty },
           { worker := .empty,
             controller :=
               if y.grant || y.mode == .ARMED then .empty
               else renewalBankWaitSlot y.mode y.lease.val
                 (m.sites dest).controller }) := by
      cases hg : y.grant <;> cases hm : y.mode <;>
        simp [renewalBankPairMemory, bankCell,
          hx, hy, hb, hbz, hp, hir, hg, hm]
    rw [hpair]
    exact bankInheritedTargetWaitMassLe m e dest .empty
      (Nat.zero_le _)
      y.mode y.lease.val (y.grant || y.mode == .ARMED)
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := (m.sites e).worker, controller := .empty },
           { worker := .empty,
             controller :=
               if y.grant || y.mode == .ARMED then .empty
               else renewalBankWaitSlot y.mode y.lease.val
                 (m.sites dest).controller }) := by
      cases hg : y.grant <;> cases hm : y.mode <;>
        simp [renewalBankPairMemory, bankCell,
          hx, hy, hb, hbz, hp, hir, hg, hm]
    rw [hpair]
    exact bankInheritedTargetWaitMassLe m e dest
      (m.sites e).worker (Nat.le_refl _)
      y.mode y.lease.val (y.grant || y.mode == .ARMED)

/-- Spacer-to-zero: the source worker is invalid; only the OLD
destination waiting stock can survive through a wait-slot tick. -/
private theorem bankInheritedSpacerZeroMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b + 1) (hy : y.pack.val = 0) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  have hnz : c.b + 1 ≠ 0 := by omega
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hp : packNext (c.b + 1) 0 c.b = 0 := by
    simp [packNext]
  have hpair :
      renewalBankPairMemory c m e dest x y =
        ({ worker := .empty, controller := .empty },
         { worker := .empty,
           controller :=
             if y.grant || y.mode == .ARMED then .empty
             else renewalBankWaitSlot y.mode y.lease.val
               (m.sites dest).controller }) := by
    cases hg : y.grant <;> cases hm : y.mode <;>
      simp [renewalBankPairMemory, bankCell,
        hx, hy, hnz, houtside, hp, hg, hm]
  rw [hpair]
  exact bankInheritedTargetWaitMassLe m e dest .empty
    (Nat.zero_le _)
    y.mode y.lease.val (y.grant || y.mode == .ARMED)

/-- Unchanged nonroot geometry: interior, top-to-spacer,
top-to-zero, or spacer-to-zero. The first two use the six
noncopying worker wirings already proved in the source. -/
private theorem bankInheritedUnchangedNonrootMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0)
    (hunchanged :
      packNext x.pack.val y.pack.val c.b = y.pack.val) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  have hb : 0 < c.b := by
    unfold Compiled.b
    omega
  by_cases hinside : x.pack.val < c.b
  · have hfirst : 1 ≤ x.pack.val := by omega
    have hp :
        packNext x.pack.val y.pack.val c.b =
          x.pack.val + 1 := by
      simp [packNext, hinside]
    have hy : y.pack.val = x.pack.val + 1 := by omega
    exact bankInheritedWiringMassLe m e dest _ _
      (rbInteriorAnyTokensWiring c m e dest x y
        x.pack.val hfirst hinside rfl hy)
  · by_cases htop : x.pack.val = c.b
    · by_cases hyzero : y.pack.val = 0
      · exact bankInheritedTopZeroMassLe
          c m e dest x y hb htop hyzero
      · have hp :
            packNext c.b y.pack.val c.b = c.b + 1 := by
          simp [packNext, hyzero]
        have hysp : y.pack.val = c.b + 1 := by
          rw [htop] at hunchanged
          omega
        exact bankInheritedWiringMassLe m e dest _ _
          (rbTopSpacerWiring c m e dest x y hb htop hysp)
    · have hupper := x.pack.isLt
      have hxsp : x.pack.val = c.b + 1 := by omega
      have hp :
          packNext (c.b + 1) y.pack.val c.b = 0 := by
        simp [packNext]
      have hyzero : y.pack.val = 0 := by
        rw [hxsp] at hunchanged
        omega
      exact bankInheritedSpacerZeroMassLe
        c m e dest x y hxsp hyzero

/-- Any nonroot source step is a sanitation or one of the
nonduplicating unchanged-role worker transfer families. -/
private theorem bankInheritedNonrootMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  by_cases hunchanged :
      packNext x.pack.val y.pack.val c.b = y.pack.val
  · exact bankInheritedUnchangedNonrootMassLe
      c m e dest x y hnonroot hunchanged
  · exact bankInheritedWiringMassLe m e dest _ _
      (rbChangedNonrootWiring c m e dest x y
        hnonroot hunchanged)

/-- A local count inequality for the literal pair-memory program,
with only physical/ghost C/W in-flight shapes as hypotheses.
No ReceiptInv or reachability is required. -/
private theorem bankInheritedAnyLocalPairMassLe
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hsc : bankInFlightControllerShape x.pack.val x.mode
      (m.sites e).controller)
    (htw : bankInFlightWorkerShape y.tok
      (m.sites dest).worker) :
    bankInheritedPairAtomMass
      (renewalBankPairMemory c m e dest x y) ≤
      bankInheritedPairAtomMass (m.sites e, m.sites dest) := by
  by_cases hx : x.pack.val = 0
  · exact bankInheritedRootMassLe
      c m e dest x y hx hsc htw
  · exact bankInheritedNonrootMassLe c m e dest x y hx

/-- The R7 L10 selected-pair census, reusing the exact old
two-endpoint reference frame and the generic local ledger. -/
theorem bankInheritedSelectedPairCensusHolds
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n) :
    BankInheritedSelectedPairCensus ring := by
  unfold BankInheritedSelectedPairCensus
  intro r hAligned e
  have htwo : 2 ≤ n := by omega
  have hf := rbReferenceSelectedPairFrame ring htwo r e
  have hsource :
      ((renewalBankNext ring r e).2.sites e) =
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 := by
    change ((rbRun ring r [e]).2.sites e) = _
    exact hf.2.2.1
  have hdest :
      ((renewalBankNext ring r e).2.sites
        (ring.rightNeighbor e)) =
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 := by
    change ((rbRun ring r [e]).2.sites
      (ring.rightNeighbor e)) = _
    exact hf.2.2.2
  rw [hsource, hdest]
  exact bankInheritedAnyLocalPairMassLe
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    (hAligned e).1
    (hAligned (ring.rightNeighbor e)).2

/-- L10, unconditional: along every scheduler word from a reachable
BANK reference state the inherited atom count never increases. -/
theorem bankInheritedAtomWordLe
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (z : BankReferenceState ring hbank) (word : List (Fin n))
    (hReplay : z.val = rbRun ring (renewalBankStart ring seed) pre) :
    bankInheritedStateAtomCount ring hbank
        (bankValidAuthorityRun ring hbank z word) ≤
      bankInheritedStateAtomCount ring hbank z :=
  bankInheritedAtomWordLeOfCensus ring hn hbank
    (bankInheritedSelectedPairCensusHolds ring hn) seed pre z word hReplay

/-- L11, unconditional: at a reachable BANK reference state, zero
inherited atoms means inherited authority is extinct. -/
theorem bankInheritedZeroExtinct
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (z : BankReferenceState ring hbank)
    (hReplay : z.val = rbRun ring (renewalBankStart ring seed) pre)
    (hzero : bankInheritedStateAtomCount ring hbank z = 0) :
    InheritedAuthorityExtinct ring hbank z :=
  bankInheritedZeroExtinctOfCensus ring hn hbank
    (bankInheritedSelectedPairCensusHolds ring hn) seed pre z hReplay hzero

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInheritedSelectedPairCensusHolds


#print axioms L3.RenewalReferenceClock.bankInheritedAtomWordLe
#print axioms L3.RenewalReferenceClock.bankInheritedZeroExtinct
