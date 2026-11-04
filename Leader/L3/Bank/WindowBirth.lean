import Leader.L3.Bank.WindowExact

/-!
BANK-PHASE, exact pending-RESET traversal and PACK activation.

The sampled phase-MC closure is not used as a proof.
The chronological traversal step and all-window J repair
activation are not proved by this module.
-/

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankCounterRows
open L3.BankHeadThreshold
open L3.BankRetryCoverage
open L3.BankRootPhase
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ## The actual OLD reset return and creation of an origin -/

private theorem bankWindowBirthResetReturnFields
    (x y : BankCell) (postRole b : Nat)
    (hrow : Counter.resetRootRow x y postRole b =
      .resetReturn) :
    x.role = 0 ∧ x.grant = false ∧
    postRole = y.role ∧ postRole = 1 ∧
    x.mode = .RWAIT ∧ y.tok = .RL := by
  have hroot : x.role = 0 := by
    by_cases hx : x.role = 0
    · exact hx
    · have hbad :
          Counter.resetRootRow x y postRole b =
            .notRoot := by
        simp [Counter.resetRootRow, hx]
      rw [hbad] at hrow
      cases hrow
  have hgrant : x.grant = false := by
    cases hg : x.grant with
    | false => rfl
    | true =>
        have hbad :
          Counter.resetRootRow x y postRole b =
            .grantExit := by
          simp [Counter.resetRootRow, hroot, hg]
        rw [hbad] at hrow
        cases hrow
  have hsame : postRole = y.role := by
    by_cases hs : postRole = y.role
    · exact hs
    · have hbad :
          Counter.resetRootRow x y postRole b =
            .changedRole := by
          simp [Counter.resetRootRow, hroot, hgrant, hs]
      rw [hbad] at hrow
      cases hrow
  have hone : postRole = 1 := by
    by_cases hs : postRole = 1
    · exact hs
    · have hnotY : y.role ≠ 1 := by
        intro hy
        exact hs (hsame.trans hy)
      have hbad :
          Counter.resetRootRow x y postRole b =
            .wrongNeighbor := by
        simp [Counter.resetRootRow, hroot, hgrant,
          hsame, hnotY]
      rw [hbad] at hrow
      cases hrow
  have hother : y.tok = .RL ∧ x.mode = .RWAIT := by
    have hdestRole : y.role = 1 := hsame.symm.trans hone
    cases ht : y.tok <;> cases hm : x.mode <;>
      simp [Counter.resetRootRow, hroot, hgrant,
        hsame, hdestRole, ht, hm, isRetTok] at hrow ⊢
    all_goals (split at hrow <;> cases hrow)
  exact ⟨hroot, hgrant, hsame, hone,
    hother.2, hother.1⟩

theorem bankWindowBirthOldReceipt
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (m : RenewalBankMemory n)
    (e : Fin n) (o : RenewalBankOrigin n)
    (hbirth : renewalBankBirth ring C m e = some o) :
    (C e).pack.val = 0 ∧
    (C e).grant = false ∧
    (C (ring.rightNeighbor e)).pack.val = 1 ∧
    (C e).mode = .RWAIT ∧
    (C (ring.rightNeighbor e)).tok = .RL ∧
    ∃ rho : RenewalBankReceipt n,
      (m.sites (ring.rightNeighbor e)).worker = .pending rho ∧
      o.root = e ∧ o.service = m.service ∧
      o.receipt = rho := by
  have hrow :
      Counter.resetRootRow
        (bankCell (C e) (C e).pack.val)
        (bankCell (C (ring.rightNeighbor e))
          (C (ring.rightNeighbor e)).pack.val)
        (packNext (C e).pack.val
          (C (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b =
          .resetReturn := by
    unfold renewalBankBirth at hbirth
    split at hbirth
    · assumption
    · cases hbirth
  obtain ⟨hroot, hgrant, hsame, hone, hmode, htok⟩ :=
    bankWindowBirthResetReturnFields
      (bankCell (C e) (C e).pack.val)
      (bankCell (C (ring.rightNeighbor e))
        (C (ring.rightNeighbor e)).pack.val)
      (packNext (C e).pack.val
        (C (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b hrow
  have hdest := hsame.symm.trans hone
  change (C e).pack.val = 0 at hroot
  change (C e).grant = false at hgrant
  change (C (ring.rightNeighbor e)).pack.val = 1 at hdest
  change (C e).mode = .RWAIT at hmode
  change (C (ring.rightNeighbor e)).tok = .RL at htok
  refine ⟨hroot, hgrant, hdest, hmode, htok, ?_⟩
  have hmatch := hbirth
  simp only [renewalBankBirth, if_pos hrow] at hmatch
  cases hw : (m.sites (ring.rightNeighbor e)).worker with
  | empty =>
      rw [hw] at hmatch
      cases hmatch
  | payload p =>
      rw [hw] at hmatch
      cases hmatch
  | pending rho =>
      rw [hw] at hmatch
      cases hmatch
      exact ⟨rho, rfl, rfl, rfl, rfl⟩

/-- No completed origin can be created from the initial
arbitrary-private BANK observer before the first reset launch. -/
theorem bankWindowBirthNoInitialBirth
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (e : Fin n) :
    renewalBankBirth ring
      (renewalBankStart ring seed).1
      (renewalBankStart ring seed).2 e = none := by
  cases hbirth : renewalBankBirth ring
      (renewalBankStart ring seed).1
      (renewalBankStart ring seed).2 e with
  | none => rfl
  | some o =>
      obtain ⟨_, _, _, _, _, rho, hworker, _, _, _⟩ :=
        bankWindowBirthOldReceipt ring
          (renewalBankStart ring seed).1
          (renewalBankStart ring seed).2 e o hbirth
      change (renewalBankInitialSite seed.val
        (ring.rightNeighbor e)).worker = .pending rho at hworker
      by_cases ht : (seed.val (ring.rightNeighbor e)).tok = .E
      · simp [renewalBankInitialSite, ht] at hworker
      · simp [renewalBankInitialSite, ht] at hworker

/-! ## Physical and ghost sanitation on a changed responder PACK -/

private theorem bankWindowBirthChangedBankCell
    (b postRole : Nat) (theta : Nat → Bool)
    (x y : BankCell) (hchanged : postRole ≠ y.role) :
    (bankPair x y postRole b theta).2.mode = .RESET ∧
    (bankPair x y postRole b theta).2.bit = false ∧
    (bankPair x y postRole b theta).2.tok = .E := by
  by_cases hx : x.role = 0
  · cases hg : x.grant <;> cases hm : x.mode <;>
      by_cases hl : 1 < x.lease <;>
      simp [bankPair, hchanged, hx, hg, hm, hl,
        isWaitMode, isRetTok]
  · simp [bankPair, hchanged, hx] <;>
      (repeat' split) <;>
      (first | exact ⟨rfl, rfl, rfl⟩ | rfl)

private theorem bankWindowBirthChangedGhostPair
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hchanged :
      packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    (renewalBankPairMemory c m e dest x y).2.worker = .empty ∧
    (renewalBankPairMemory c m e dest x y).2.controller =
      .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  by_cases hx : x.pack.val = 0
  · have hp : packNext 0 y.pack.val c.b = 1 := by
      simp [packNext, hb]
    have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
      rw [hx]
      exact hp
    have hneq : y.pack.val ≠ 1 := by
      intro he
      exact hchanged (hpost.trans he.symm)
    cases hg : x.grant <;> cases hm : x.mode <;>
      by_cases hl : 1 < x.lease.val <;>
      simp [renewalBankPairMemory, bankCell, hx,
        hp, hpost, hneq, Ne.symm hneq, hg, hm, hl,
        renewalBankWaitSlot, isWaitMode] <;>
        (repeat' split) <;>
        (first | exact ⟨rfl, rfl⟩ | rfl)
  · cases ht : x.tok <;>
      simp [renewalBankPairMemory, bankCell,
        hchanged, hx, ht] <;>
        (repeat' split) <;>
        (first | exact ⟨rfl, rfl⟩ | rfl)

/-- Distinct selected endpoints in the real BANK population
regime, used to rule out the source-priority exception. -/
private theorem bankWindowBirthDistinctEdge
    {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      have he := e.isLt
      omega
    rw [heq, Nat.mod_self] at hv
    have he := e.isLt
    omega

theorem bankWindowBirthChangedResponderStep
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
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).bit = false ∧
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).tok = .E ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker = .empty ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).controller = .empty := by
  have hne := bankWindowBirthDistinctEdge ring hn e
  have hphysical :
      (renewalBankNext ring r e).1 (ring.rightNeighbor e) =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 := by
    change renewalMaskedStep ring r.1 e
      (renewalBankCut ring r.1 r.2 e)
      (ring.rightNeighbor e) = _
    exact (if_neg hne).trans (if_pos rfl)
  have hghost :
      (renewalBankNext ring r e).2.sites
          (ring.rightNeighbor e) =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 := by
    change (renewalBankMemoryNext ring r.1 r.2 e).sites
      (ring.rightNeighbor e) = _
    exact (if_neg hne).trans (if_pos rfl)
  have hraw := bankWindowBirthChangedBankCell
    (compileAdvice (ceilLogTwo n)).b
    (packNext (r.1 e).pack.val
      (r.1 (ring.rightNeighbor e)).pack.val
      (compileAdvice (ceilLogTwo n)).b)
    (compileAdvice (ceilLogTwo n)).theta
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    hchanged
  have htrip := (Counter.resetTransitionBankTrip
    (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e)) hbank).2
  have hmask := (renewalMaskedPairFrames
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))).2
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  have hbit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip
  have htok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip
  change (transition (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode at hmode
  change (transition (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit at hbit
  change (transition (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok at htok
  have hmm := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hmask
  have hmb := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
    hmask
  have hmt := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
    hmask
  change (renewalMaskedPair (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode at hmm
  change (renewalMaskedPair (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit at hmb
  change (renewalMaskedPair (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok at hmt
  have hghostPair := bankWindowBirthChangedGhostPair
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hchanged
  rw [hphysical, hghost]
  exact ⟨hmm.trans (hmode.trans hraw.1),
    hmb.trans (hbit.trans hraw.2.1),
    hmt.trans (htok.trans hraw.2.2),
    hghostPair.1, hghostPair.2⟩

/-- A formerly role-zero responder cannot retain a genuine
controller when its PACK role changes: its mode is RESET and
its ghost controller is empty in the actual new reference. -/
theorem bankWindowBirthChangedRootClears
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hroot : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hnew :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val ≠ 0) :
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).mode = .RESET ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).controller = .empty := by
  have hpack := bankWindowExactResponderPack ring r e
    (bankWindowBirthDistinctEdge ring hn e)
  have hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
          (r.1 (ring.rightNeighbor e)).pack.val := by
    intro h
    apply hnew
    exact (hpack.trans h).trans hroot
  have h := bankWindowBirthChangedResponderStep
    ring hn hbank r e hchanged
  exact ⟨h.1, h.2.2.2.2⟩

/-- The newly repaired digit is physically and ghost-empty,
which supplies the local reset contribution when PACK repair
makes some previously incomplete window complete. -/
theorem bankWindowBirthRepairedDigitClear
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
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
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker = .empty ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).controller = .empty := by
  have hpack := bankWindowExactResponderPack ring r e
    (bankWindowBirthDistinctEdge ring hn e)
  have hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
          (r.1 (ring.rightNeighbor e)).pack.val := by
    intro h
    apply hbefore
    exact (h.symm.trans hpack.symm).trans hafter
  have h := bankWindowBirthChangedResponderStep
    ring hn hbank r e hchanged
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-! ## Pending-RESET causal history in the actual rbRun word -/

def BankPendingForwardEvent
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (word : List (Fin n))
    (rho : RenewalBankReceipt n) (k time : Nat) : Prop :=
  word[time]? = some (Counter.site ring rho.root k) ∧
  ((rbRun ring (renewalBankStart ring seed)
    (word.take time)).1
      (Counter.site ring rho.root k)).pack.val = k ∧
  ((rbRun ring (renewalBankStart ring seed)
    (word.take time)).1
      (Counter.site ring rho.root (k + 1))).pack.val = k + 1 ∧
  ((renewalBankNext ring
    (rbRun ring (renewalBankStart ring seed) (word.take time))
    (Counter.site ring rho.root k)).2.sites
      (Counter.site ring rho.root (k + 1))).worker =
        .pending rho

/-- Chronological witnesses to all forward services, with strict
time order. The history is determined by actual rbRun prefixes. -/
def BankPendingForwardHistory
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (word : List (Fin n))
    (rho : RenewalBankReceipt n) (length : Nat) : Prop :=
  ∃ positions : Fin length → Nat,
    (∀ k : Fin length,
      positions k < word.length ∧
      BankPendingForwardEvent ring seed word rho
        k.val (positions k)) ∧
    (∀ k l : Fin length,
      k.val < l.val → positions k < positions l)

def BankPendingTurnHistory
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (word : List (Fin n))
    (rho : RenewalBankReceipt n) : Prop :=
  ∃ time : Nat,
    word[time]? =
      some (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)) ∧
    Counter.Complete ring
      (rbRun ring (renewalBankStart ring seed)
        (word.take time)).1 rho.root ∧
    ((rbRun ring (renewalBankStart ring seed)
      (word.take time)).1
        (Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b)).tok = .RR ∧
    ((rbRun ring (renewalBankStart ring seed)
      (word.take time)).2.sites
        (Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b)).worker =
            .pending rho ∧
    ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed)
        (word.take time))
      (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1))).2.sites
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1))).worker =
            .pending rho

structure BankPendingTraversal
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring)
    (word : List (Fin n)) : Prop where
  pending :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      ((rbRun ring (renewalBankStart ring seed) word).2.sites i).worker =
        .pending rho →
      ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
        i = Counter.site ring rho.root (j.val + 1) ∧
        (((rbRun ring (renewalBankStart ring seed) word).1 i).tok =
          .RR ∧
          BankPendingForwardHistory ring seed word rho
            (j.val + 1) ∧
          (((rbRun ring (renewalBankStart ring seed) word).1
            rho.root).mode = .RWAIT →
            bankWindowZeroPrefix ring
              (rbRun ring (renewalBankStart ring seed) word)
              rho.root (j.val + 1))) ∨
         (((rbRun ring (renewalBankStart ring seed) word).1 i).tok =
          .RL ∧
          BankPendingForwardHistory ring seed word rho
            (compileAdvice (ceilLogTwo n)).b ∧
          BankPendingTurnHistory ring seed word rho)

/-- Traversal at the genuine arbitrary-private entrance has
no pending receipts. This is the base for the outstanding
chronological word induction. -/
theorem bankPendingTraversalStart
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) :
    BankPendingTraversal ring seed [] := by
  refine ⟨?_⟩
  intro i rho h
  change (renewalBankInitialSite seed.val i).worker =
    .pending rho at h
  by_cases ht : (seed.val i).tok = .E
  · simp [renewalBankInitialSite, ht] at h
  · simp [renewalBankInitialSite, ht] at h

/-! ## The matched OLD RR forward row -/

theorem bankWindowBirthPendingForwardPair
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (rho : RenewalBankReceipt n)
    (hfirst : 1 ≤ x.pack.val)
    (hinside : x.pack.val < c.b)
    (hy : y.pack.val = x.pack.val + 1)
    (hrr : x.tok = .RR)
    (hpending : (m.sites e).worker = .pending rho) :
    (renewalBankPairMemory c m e dest x y).1.worker =
      .empty ∧
    (renewalBankPairMemory c m e dest x y).2.worker =
      .pending rho := by
  have hpost :
      packNext x.pack.val (x.pack.val + 1) c.b =
        x.pack.val + 1 := by
    simp [packNext, hinside]
  have hxne : x.pack.val ≠ 0 := by omega
  have hxle : x.pack.val ≤ c.b := by omega
  have hnextLe : x.pack.val + 1 ≤ c.b := by omega
  have hnextNe : x.pack.val + 1 ≠ 0 := by omega
  have htop : x.pack.val ≠ c.b := by omega
  cases ht : y.tok <;>
    simp [renewalBankPairMemory, bankCell, hy, hpost,
      hxne, hxle, hnextLe, hnextNe, htop,
      hfirst, hinside, hrr, hpending, ht] <;>
    (repeat' split) <;>
    (first | exact ⟨rfl, rfl⟩ | rfl)

theorem bankWindowBirthPendingForwardStep
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (rho : RenewalBankReceipt n)
    (hfirst : 1 ≤ (r.1 e).pack.val)
    (hinside :
      (r.1 e).pack.val < (compileAdvice (ceilLogTwo n)).b)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val =
      (r.1 e).pack.val + 1)
    (hrr : (r.1 e).tok = .RR)
    (hpending : (r.2.sites e).worker = .pending rho) :
    ((renewalBankNext ring r e).2.sites e).worker = .empty ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker = .pending rho := by
  have hne := bankWindowBirthDistinctEdge ring hn e
  have hlocal := bankWindowBirthPendingForwardPair
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e) (r.1 e)
    (r.1 (ring.rightNeighbor e)) rho
    hfirst hinside hy hrr hpending
  have hsource :
      ((renewalBankNext ring r e).2.sites e).worker =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker := by
    change ((renewalBankMemoryNext ring r.1 r.2 e).sites e).worker = _
    exact congrArg (fun z : RenewalBankSite n => z.worker)
      (if_pos rfl)
  have htarget :
      ((renewalBankNext ring r e).2.sites
          (ring.rightNeighbor e)).worker =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker := by
    change ((renewalBankMemoryNext ring r.1 r.2 e).sites
      (ring.rightNeighbor e)).worker = _
    exact congrArg (fun z : RenewalBankSite n => z.worker)
      ((if_neg hne).trans (if_pos rfl))
  exact ⟨hsource.trans hlocal.1, htarget.trans hlocal.2⟩

end L3.BankWindow
#print axioms L3.BankWindow.bankWindowBirthOldReceipt
#print axioms L3.BankWindow.bankWindowBirthNoInitialBirth
#print axioms L3.BankWindow.bankWindowBirthChangedResponderStep
#print axioms L3.BankWindow.bankWindowBirthChangedRootClears
#print axioms L3.BankWindow.bankWindowBirthRepairedDigitClear
#print axioms L3.BankWindow.bankPendingTraversalStart
#print axioms L3.BankWindow.bankWindowBirthPendingForwardPair
#print axioms L3.BankWindow.bankWindowBirthPendingForwardStep
