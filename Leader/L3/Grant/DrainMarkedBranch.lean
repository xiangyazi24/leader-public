import Leader.L3.Grant.DrainBranch
import Leader.L3.Grant.DrainLabelTail

/-!
# The physical all-marked grant-drain branch

The source ledger is used at the real first marked cut, not initialized
a second time.  The carrier contains only prefixes of an initial PPlus
state whose live source-ledger labels are all permanently marked.
The per-label remaining budget is counted only at a live host.
There is no global statement about arbitrary forged entrance ghosts.

WEAK is included: an unheld label nominates the immediate incoming
edge, while a requested label nominates its outgoing edge.  Once its
old mark is weak, strong, or terminal, the literal remaining update
takes the minimum of (old remaining minus its nominated hit) and the
new cap.  Consequently a positive budget strictly decreases on the
nominated edge even if that edge retires or promotes the label.

Full immutable grant ancestry identifies the physical surviving host
with one of the original labels.  The established source-level
NoExhaustion theorem prevents a live marked label from having zero
remaining.  These two facts make zero quotas imply physical GrantFree.
-/

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The actual persistent marked branch, based at one original
physical initial state.  The reachability component cannot be forged
without producing a genuine scheduler prefix. -/
def GrantDrainMarkedBranchReach
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (z : GrantDrainEntranceState n Scratch) : Prop :=
  GrantDrainBranchMarkedCut z ∧
    GrantDrainBranchReachable
      (grantDrainEntranceNext ring fresh update)
      (grantDrainEntranceInitial ring start) z

/-- A proof-only subtype, not a modified canonical protocol. -/
abbrev GrantDrainMarkedBranchCarrier
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch) : Type :=
  { z : GrantDrainEntranceState n Scratch //
    GrantDrainMarkedBranchReach ring fresh update start z }

/-- The subtype's physical step is definitionally grantDrainStep,
with the exact source ledger update and no reset at the cut. -/
noncomputable def grantDrainMarkedBranchNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (z : GrantDrainMarkedBranchCarrier ring fresh update start)
    (e : Fin n) :
    GrantDrainMarkedBranchCarrier ring fresh update start := by
  refine ⟨grantDrainEntranceNext ring fresh update z.val e, ?_⟩
  constructor
  · exact grantDrainEntranceAllGrantsMarkedNext
      ring fresh update z.val e z.property.1
  · exact grantDrainBranchReachableStep
      (grantDrainEntranceNext ring fresh update)
      (grantDrainEntranceInitial ring start)
      z.val e z.property.2

/-- Any initial-state prefix satisfying the literal right disjunct
is a well-formed entry into the restricted marked branch. -/
noncomputable def grantDrainMarkedBranchAtCut
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (word : List (Fin n))
    (hMarked : GrantDrainBranchMarkedCut
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word)) :
    GrantDrainMarkedBranchCarrier ring fresh update start := by
  refine ⟨grantDrainEntranceRun ring fresh update
    (grantDrainEntranceInitial ring start) word, ?_⟩
  refine ⟨hMarked, ?_⟩
  exact ⟨word, rfl⟩

/-- The used quota is zero after retirement; even an arbitrary
positive integer in an unrelated retired ghost field is not counted. -/
def grantDrainMarkedBranchQuota
    {n : Nat} {Scratch : Type}
    {ring : DirectedRing n}
    {fresh : GrantDrainState n Scratch → Fin n → Bool}
    {update : GrantDrainState n Scratch → Fin n → Scratch}
    {start : GrantDrainState n Scratch}
    (z : GrantDrainMarkedBranchCarrier ring fresh update start)
    (i : Fin n) : Nat :=
  if (z.val.grantLabels i).host = none then 0
  else (z.val.grantLabels i).remaining

/-- The OLD request chooses outgoing; otherwise a live label chooses
the unique incoming predecessor.  The retired case is arbitrary and
irrelevant to positive quotas. -/
def grantDrainMarkedBranchChosen
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    {fresh : GrantDrainState n Scratch → Fin n → Bool}
    {update : GrantDrainState n Scratch → Fin n → Scratch}
    {start : GrantDrainState n Scratch}
    (z : GrantDrainMarkedBranchCarrier ring fresh update start)
    (i : Fin n) : Fin n :=
  match (z.val.grantLabels i).host with
  | none => i
  | some g =>
      if z.val.physical.request g then g
      else PPL.shiftLeft ring g 1

/-- The immediate predecessor really nominates the current host,
including the wraparound edge. -/
private theorem grantDrainMarkedIncomingRight
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (g : Fin n) :
    ring.rightNeighbor (PPL.shiftLeft ring g 1) = g := by
  apply Fin.ext
  have hOne : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  change (((g.val + n - 1 % n) % n + 1) % n) = g.val
  rw [hOne]
  by_cases hz : g.val = 0
  · have hp : (g.val + n - 1) % n = n - 1 := by
      have heq : g.val + n - 1 = n - 1 := by omega
      rw [heq, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    rw [hp]
    have heq : n - 1 + 1 = n := by omega
    rw [heq, Nat.mod_self]
    exact hz.symm
  · have heq : g.val + n - 1 = n + (g.val - 1) := by omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : g.val - 1 < n)]
    have hplus : g.val - 1 + 1 = g.val := by omega
    rw [hplus, Nat.mod_eq_of_lt g.isLt]

/-- The exact nominated-hit bit is true at the chosen OLD edge,
whether the marked label is weak, strong, or terminal. -/
theorem grantDrainMarkedBranchChosenHits
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    {fresh : GrantDrainState n Scratch → Fin n → Bool}
    {update : GrantDrainState n Scratch → Fin n → Scratch}
    {start : GrantDrainState n Scratch}
    (z : GrantDrainMarkedBranchCarrier ring fresh update start)
    (i g : Fin n)
    (hHost : (z.val.grantLabels i).host = some g) :
    grantDrainLedgerNominatedHit ring z.val.physical
      (grantDrainMarkedBranchChosen ring z i)
      (z.val.grantLabels i).host = true := by
  unfold grantDrainMarkedBranchChosen
  rw [hHost]
  cases hReq : z.val.physical.request g with
  | true =>
      simp [grantDrainLedgerNominatedHit, hHost, hReq]
  | false =>
      simp [grantDrainLedgerNominatedHit, hHost, hReq,
        grantDrainMarkedIncomingRight ring hn g]

/-- For any already marked label, hitting its old nominated edge
spends one unit even if the new cap shrinks or its host retires.
This lemma is purely arithmetic over the literal ledger update. -/
private theorem grantDrainMarkedSpentRemaining
    (n : Nat) (label : GrantDrainLedgerLabel n)
    (host : Option (Fin n))
    (newMark : GrantDrainMark) (held : Bool)
    (hMarked : label.mark ≠ .unmarked) :
    grantDrainLedgerRemainingNext
      n label host newMark true held ≤ label.remaining - 1 := by
  cases host with
  | none =>
      simp [grantDrainLedgerRemainingNext]
  | some g =>
      change min
        (if label.mark = .unmarked then
          grantDrainLedgerQuotaCap n newMark held
        else label.remaining - 1)
        (grantDrainLedgerQuotaCap n newMark held) ≤ label.remaining - 1
      rw [if_neg hMarked]
      exact Nat.min_le_left _ _

/-- No newly unmarked LIVE label is possible on this carrier.
When its host is absent its quota is already zero; for a live
marked label the original source-ledger nonincrease lemma applies. -/
theorem grantDrainMarkedBranchQuotaNonincrease
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (z : GrantDrainMarkedBranchCarrier ring fresh update start)
    (i e : Fin n) :
    grantDrainMarkedBranchQuota
      (grantDrainMarkedBranchNext ring fresh update start z e) i ≤
    grantDrainMarkedBranchQuota z i := by
  cases hHost : (z.val.grantLabels i).host with
  | none =>
      have hGone :
          ((grantDrainEntranceNext ring fresh update z.val e).grantLabels
            i).host = none := by
        change (grantDrainLedgerStep ring fresh update
          z.val.physical e (z.val.grantLabels i)).host = none
        exact grantDrainLedgerStep_retired_absorbing
          ring fresh update z.val.physical e
          (z.val.grantLabels i) hHost
      change
        (if ((grantDrainEntranceNext ring fresh update z.val e).grantLabels
              i).host = none then 0
         else ((grantDrainEntranceNext ring fresh update z.val e).grantLabels
              i).remaining) ≤
        (if (z.val.grantLabels i).host = none then 0
         else (z.val.grantLabels i).remaining)
      rw [hGone, hHost]
      simp
  | some g =>
      have hLive : (z.val.grantLabels i).host ≠ none := by
        rw [hHost]
        intro hh
        cases hh
      have hMarked : (z.val.grantLabels i).mark ≠ .unmarked :=
        z.property.1 i hLive
      have hRemaining :=
        grantDrainLedgerStep_remaining_nonincrease
          ring fresh update z.val.physical e
          (z.val.grantLabels i) hMarked
      change
        (if ((grantDrainEntranceNext ring fresh update z.val e).grantLabels
              i).host = none then 0
         else ((grantDrainEntranceNext ring fresh update z.val e).grantLabels
              i).remaining) ≤
        (if (z.val.grantLabels i).host = none then 0
         else (z.val.grantLabels i).remaining)
      rw [hHost]
      simp only [reduceCtorEq, ite_false]
      split
      · exact Nat.zero_le _
      · exact hRemaining

/-- Every positive quota drops strictly at its chosen scheduler
letter, INCLUDING the weak lock with its 2n budget. -/
theorem grantDrainMarkedBranchQuotaDrop
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (z : GrantDrainMarkedBranchCarrier ring fresh update start)
    (i : Fin n)
    (hPositive : 0 < grantDrainMarkedBranchQuota z i) :
    grantDrainMarkedBranchQuota
      (grantDrainMarkedBranchNext ring fresh update start z
        (grantDrainMarkedBranchChosen ring z i)) i + 1 ≤
      grantDrainMarkedBranchQuota z i := by
  cases hHost : (z.val.grantLabels i).host with
  | none =>
      have hZero :
          grantDrainMarkedBranchQuota z i = 0 := by
        simp [grantDrainMarkedBranchQuota, hHost]
      rw [hZero] at hPositive
      omega
  | some g =>
      have hLive : (z.val.grantLabels i).host ≠ none := by
        rw [hHost]
        intro hh
        cases hh
      have hMarked : (z.val.grantLabels i).mark ≠ .unmarked :=
        z.property.1 i hLive
      have hHit :=
        grantDrainMarkedBranchChosenHits
          ring hn z i g hHost
      have hSpent :
          ((grantDrainEntranceNext ring fresh update z.val
            (grantDrainMarkedBranchChosen ring z i)).grantLabels
              i).remaining ≤
            (z.val.grantLabels i).remaining - 1 := by
        change grantDrainLedgerRemainingNext n
          (z.val.grantLabels i)
          (grantDrainLedgerHost ring fresh z.val.physical
            (grantDrainMarkedBranchChosen ring z i)
            (z.val.grantLabels i).host)
          (grantDrainLedgerMarkNext ring fresh update z.val.physical
            (grantDrainMarkedBranchChosen ring z i)
            (z.val.grantLabels i))
          (grantDrainLedgerNominatedHit ring z.val.physical
            (grantDrainMarkedBranchChosen ring z i)
            (z.val.grantLabels i).host)
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update z.val.physical
              (grantDrainMarkedBranchChosen ring z i))
            (grantDrainLedgerHost ring fresh z.val.physical
              (grantDrainMarkedBranchChosen ring z i)
              (z.val.grantLabels i).host)) ≤
          (z.val.grantLabels i).remaining - 1
        rw [hHit]
        exact grantDrainMarkedSpentRemaining n
          (z.val.grantLabels i) _ _ _ hMarked
      have hNext :
          grantDrainMarkedBranchQuota
            (grantDrainMarkedBranchNext ring fresh update start z
              (grantDrainMarkedBranchChosen ring z i)) i ≤
          ((grantDrainEntranceNext ring fresh update z.val
            (grantDrainMarkedBranchChosen ring z i)).grantLabels
              i).remaining := by
        change (if
          ((grantDrainEntranceNext ring fresh update z.val
            (grantDrainMarkedBranchChosen ring z i)).grantLabels
              i).host = none then 0
          else ((grantDrainEntranceNext ring fresh update z.val
            (grantDrainMarkedBranchChosen ring z i)).grantLabels
              i).remaining) ≤ _
        split
        · exact Nat.zero_le _
        · exact Nat.le_refl _
      have hOld :
          grantDrainMarkedBranchQuota z i =
            (z.val.grantLabels i).remaining := by
        simp [grantDrainMarkedBranchQuota, hHost]
      rw [hOld]
      have hOldPositive : 0 < (z.val.grantLabels i).remaining := by
        rw [hOld] at hPositive
        exact hPositive
      omega

/-- Syntactic cap on every INITIAL source-ledger label, whether
unmarked, weak, strong, terminal, or retired. -/
private theorem grantDrainMarkedInitialCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (i : Fin n) :
    (grantDrainLedgerInitial ring s i).remaining ≤ 2 * n := by
  cases hg : s.grant i with
  | false =>
      simp [grantDrainLedgerInitial, hg]
  | true =>
      simp only [grantDrainLedgerInitial, hg, ↓reduceIte]
      exact grantDrainLedgerQuotaCap_le_double n _ _

/-- Caps propagate on the same entire entrance word because the
source ledger caps every next label independently of its old mark. -/
private theorem grantDrainMarkedWordCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (z : GrantDrainEntranceState n Scratch),
      (∀ i : Fin n, (z.grantLabels i).remaining ≤ 2 * n) →
      ∀ i : Fin n,
        ((grantDrainEntranceRun ring fresh update z word).grantLabels
          i).remaining ≤ 2 * n := by
  intro word
  induction word with
  | nil =>
      intro z hCap i
      exact hCap i
  | cons e rest ih =>
      intro z hCap i
      change ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceNext ring fresh update z e)
        rest).grantLabels i).remaining ≤ 2 * n
      apply ih (grantDrainEntranceNext ring fresh update z e)
      intro j
      change (grantDrainLedgerStep ring fresh update
        z.physical e (z.grantLabels j)).remaining ≤ 2 * n
      exact grantDrainLedgerStep_quota_le_double
        ring fresh update z.physical e (z.grantLabels j)

/-- The global 8n premise of the generic tail holds, in fact with
2n, at every genuinely reachable marked state. -/
theorem grantDrainMarkedBranchQuotaBound
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (z : GrantDrainMarkedBranchCarrier ring fresh update start)
    (i : Fin n) :
    grantDrainMarkedBranchQuota z i ≤ 8 * n := by
  obtain ⟨word, hWord⟩ := z.property.2
  have hCap :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).grantLabels
          i).remaining ≤ 2 * n := by
    exact grantDrainMarkedWordCap ring fresh update word
      (grantDrainEntranceInitial ring start)
      (fun j => grantDrainMarkedInitialCap ring start j) i
  have hCapZ : (z.val.grantLabels i).remaining ≤ 2 * n := by
    rw [hWord]
    exact hCap
  have hQuota :
      grantDrainMarkedBranchQuota z i ≤
        (z.val.grantLabels i).remaining := by
    unfold grantDrainMarkedBranchQuota
    split
    · exact Nat.zero_le _
    · exact Nat.le_refl _
  have hNumeric : 2 * n ≤ 8 * n := by omega
  exact Nat.le_trans (Nat.le_trans hQuota hCapZ) hNumeric

/-- Physical grant coverage by the SAME n source ledger labels,
including an old Y-to-X coalescence at a shared host. -/
theorem grantDrainMarkedBranchPhysicalCover
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (word : List (Fin n)) (g : Fin n)
    (hGrant :
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).physical.grant g =
          true) :
    ∃ i : Fin n,
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).grantLabels
          i).host = some g := by
  have hCover := sharedGrantFaithfulGhostGrantCover
    ring hn fresh update start word
  have hProjection :
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).physical =
      sharedGrantPhysicalRun
        (grantDrainCanonicalModel ring hn fresh update)
        start word := by
    exact grantDrainEntrancePhysicalWordProjection
      ring fresh update word (grantDrainEntranceInitial ring start)
  have hCurrent :
      (sharedGrantPhysicalRun
        (grantDrainCanonicalModel ring hn fresh update)
        start word).grant g = true := by
    rw [← hProjection]
    exact hGrant
  obtain ⟨i, hHost⟩ := (hCover.2 g).mp hCurrent
  have hAlign := sharedGrantFaithfulMarkFullHostEq
    ring hn fresh update start word i
  exact ⟨i, hAlign.symm.trans hHost⟩

/-- A live MARKED original label has positive remaining quota.
The proof uses the genuine full-label cover to recover its OLD
initial grant, and the proved source LockBudget NoExhaustion fact. -/
theorem grantDrainMarkedBranchLivePositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (hPB : PPlus ring start.native)
    (word : List (Fin n)) (i : Fin n)
    (hLive :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).grantLabels
          i).host ≠ none)
    (hMarked :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).grantLabels
          i).mark ≠ .unmarked) :
    0 < ((grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring start) word).grantLabels
        i).remaining := by
  cases hHost :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).grantLabels
          i).host with
  | none =>
      exact False.elim (hLive hHost)
  | some g =>
      have hCover := sharedGrantFaithfulGhostGrantCover
        ring hn fresh update start word
      have hAlign := sharedGrantFaithfulMarkFullHostEq
        ring hn fresh update start word i
      have hGhostHost :
          (sharedGrantFaithfulGhost
            ring hn fresh update start).grantHost i word.reverse =
            some g := by
        rw [hAlign]
        exact hHost
      have hInitialGrant : start.grant i = true :=
        (hCover.1 i g hGhostHost).1
      have hLedgerProjection :=
        grantDrainEntranceGrantLedgerProjection
          ring fresh update word
          (grantDrainEntranceInitial ring start) i
      change
        (grantDrainLedgerRun ring fresh update start
          (grantDrainLedgerInitial ring start i) word).2 =
        ((grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring start) word).grantLabels
            i) at hLedgerProjection
      have hLedgerHost :
          (grantDrainLedgerRun ring fresh update start
            (grantDrainLedgerInitial ring start i) word).2.host ≠
              none := by
        rw [hLedgerProjection]
        exact hLive
      have hLedgerMark :
          (grantDrainLedgerRun ring fresh update start
            (grantDrainLedgerInitial ring start i) word).2.mark ≠
              .unmarked := by
        rw [hLedgerProjection]
        exact hMarked
      have hPositive :=
        (grantDrainLedgerNoExhaustionHolds
          ring hn fresh update start)
          hPB i word hInitialGrant hLedgerHost hLedgerMark
      rw [hLedgerProjection] at hPositive
      exact hPositive

/-- If every marked live-host quota is zero at a real prefix,
no physical OLD grant exists.  NoExhaustion excludes a live
marked label with exhausted remaining, even for weak locks. -/
theorem grantDrainMarkedBranchZeroPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (hPB : PPlus ring start.native)
    (word : List (Fin n))
    (hMarked : GrantDrainBranchMarkedCut
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word))
    (hZero : ∀ i : Fin n,
      (if ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).grantLabels
          i).host = none then 0
       else ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).grantLabels
          i).remaining) = 0) :
    GrantFree
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).physical := by
  intro g
  by_cases hGrant :
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).physical.grant
          g = true
  · obtain ⟨i, hHost⟩ :=
      grantDrainMarkedBranchPhysicalCover
        ring hn fresh update start word g hGrant
    have hLive :
        ((grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring start) word).grantLabels
            i).host ≠ none := by
      rw [hHost]
      intro hh
      cases hh
    have hMark := hMarked i hLive
    have hPositive := grantDrainMarkedBranchLivePositive
      ring hn fresh update start hPB word i hLive hMark
    have hQuota := hZero i
    rw [hHost] at hQuota
    simp only [reduceCtorEq, ite_false] at hQuota
    exact False.elim (Nat.ne_of_gt hPositive hQuota)
  · cases hg :
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring start) word).physical.grant
            g with
    | false =>
        rfl
    | true =>
        exact False.elim (hGrant hg)

/-- The same zero-quota implication, transported to every state
of the reachable marked subtype. -/
theorem grantDrainMarkedBranchZeroOnCarrier
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (hPB : PPlus ring start.native)
    (z : GrantDrainMarkedBranchCarrier ring fresh update start)
    (hZero : ∀ i : Fin n, grantDrainMarkedBranchQuota z i = 0) :
    GrantFree z.val.physical := by
  obtain ⟨word, hWord⟩ := z.property.2
  have hRun : grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring start) word = z.val := hWord.symm
  have hMarked :
      GrantDrainBranchMarkedCut
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring start) word) := by
    rw [hRun]
    exact z.property.1
  have hZeroWord :
      ∀ i : Fin n,
        (if ((grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring start) word).grantLabels
            i).host = none then 0
         else ((grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring start) word).grantLabels
            i).remaining) = 0 := by
    intro i
    rw [hRun]
    exact hZero i
  have hResult := grantDrainMarkedBranchZeroPhysical
    ring hn fresh update start hPB word hMarked hZeroWord
  rw [← hRun]
  exact hResult

/-- Subtype steps commute with the original ghost projection;
first-hit numerators for any target reading only the original
ghost state agree at every finite horizon. -/
theorem grantDrainMarkedBranchCostProjection
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (Target : GrantDrainEntranceState n Scratch → Prop) :
    ∀ T : Nat,
      ∀ z : GrantDrainMarkedBranchCarrier ring fresh update start,
        costNumerator
          (grantDrainMarkedBranchNext ring fresh update start)
          (fun y => Target y.val) z T =
        costNumerator
          (grantDrainEntranceNext ring fresh update)
          Target z.val T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z
      simp only [costNumerator_zero]
  | succ T ih =>
      intro z
      by_cases hTarget : Target z.val
      · have hTargetSubtype :
            (fun y : GrantDrainMarkedBranchCarrier
              ring fresh update start => Target y.val) z := hTarget
        rw [costNumerator_terminal
          (grantDrainMarkedBranchNext ring fresh update start)
          (fun y => Target y.val) z hTargetSubtype (T + 1),
          costNumerator_terminal
          (grantDrainEntranceNext ring fresh update)
          Target z.val hTarget (T + 1)]
      · have hNotSubtype :
            ¬ (fun y : GrantDrainMarkedBranchCarrier
              ring fresh update start => Target y.val) z := hTarget
        rw [costNumerator_succ
          (grantDrainMarkedBranchNext ring fresh update start)
          (fun y => Target y.val) z hNotSubtype T,
          costNumerator_succ
          (grantDrainEntranceNext ring fresh update)
          Target z.val hTarget T]
        have hChildren :
            (fun e : Fin n =>
              costNumerator
                (grantDrainMarkedBranchNext ring fresh update start)
                (fun y => Target y.val)
                (grantDrainMarkedBranchNext ring fresh update start z e) T) =
            (fun e : Fin n =>
              costNumerator (grantDrainEntranceNext ring fresh update)
                Target (grantDrainEntranceNext ring fresh update z.val e)
                T) := by
          funext e
          exact ih (grantDrainMarkedBranchNext ring fresh update start z e)
        rw [hChildren]

/-- The physical R8e right branch costs at most 23n², uniformly
over all PPlus starts, literal all-marked scheduler prefixes,
arbitrary subsequent horizons, and all weak/strong/terminal marks.
No independent scheduler or reinitialized quota is introduced. -/
theorem grantDrainMarkedBranchCost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (hPB : PPlus ring start.native)
    (word : List (Fin n))
    (hMarked : GrantDrainBranchMarkedCut
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word))
    (T : Nat) :
    costNumerator (grantDrainStep ring fresh update)
      (fun z : GrantDrainState n Scratch => GrantFree z)
      (grantDrainEntrancePhysicalWord ring fresh update start word) T ≤
        n ^ T * (23 * n ^ 2) := by
  have hQuotaCost :=
    grantDrainLabelFamilyTwentyThreeSquareCost
      (grantDrainMarkedBranchNext ring fresh update start)
      (fun i z => grantDrainMarkedBranchQuota z i)
      (fun i z => grantDrainMarkedBranchChosen ring z i)
      hn (Nat.le_refl n)
      (fun z i e =>
        grantDrainMarkedBranchQuotaNonincrease
          ring fresh update start z i e)
      (fun z i hp =>
        grantDrainMarkedBranchQuotaDrop
          ring hn fresh update start z i hp)
      (fun z i =>
        grantDrainMarkedBranchQuotaBound
          ring fresh update start z i)
  have hCutCost :
      costNumerator
        (grantDrainMarkedBranchNext ring fresh update start)
        (fun z : GrantDrainMarkedBranchCarrier
          ring fresh update start => GrantFree z.val.physical)
        (grantDrainMarkedBranchAtCut
          ring fresh update start word hMarked) T ≤
          n ^ T * (23 * n ^ 2) := by
    have hTargetCost :=
      L3.Prob.costNumerator_target_mono
        (grantDrainMarkedBranchNext ring fresh update start)
        (fun z : GrantDrainMarkedBranchCarrier
          ring fresh update start =>
          ∀ i : Fin n, grantDrainMarkedBranchQuota z i = 0)
        (fun z : GrantDrainMarkedBranchCarrier
          ring fresh update start => GrantFree z.val.physical)
        (fun z hZero =>
          grantDrainMarkedBranchZeroOnCarrier
            ring hn fresh update start hPB z hZero)
        (grantDrainMarkedBranchAtCut
          ring fresh update start word hMarked) T
    exact Nat.le_trans hTargetCost
      (hQuotaCost (grantDrainMarkedBranchAtCut
        ring fresh update start word hMarked) T)
  have hGhostCost :
      costNumerator (grantDrainEntranceNext ring fresh update)
        (fun z : GrantDrainEntranceState n Scratch =>
          GrantFree z.physical)
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring start) word) T ≤
          n ^ T * (23 * n ^ 2) := by
    have hProjection :=
      grantDrainMarkedBranchCostProjection
        ring fresh update start
        (fun z : GrantDrainEntranceState n Scratch =>
          GrantFree z.physical)
        T (grantDrainMarkedBranchAtCut
          ring fresh update start word hMarked)
    exact Nat.le_trans (Nat.le_of_eq hProjection.symm) hCutCost
  have hGhostPhysical :=
    grantDrainBranchGhostGrantFreeCostEq
      ring fresh update T
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word)
  have hWordProjection :=
    grantDrainEntrancePhysicalWordProjection
      ring fresh update word (grantDrainEntranceInitial ring start)
  rw [hGhostPhysical, hWordProjection] at hGhostCost
  exact hGhostCost

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainMarkedBranchQuotaNonincrease
#print axioms L3.GrantDrainEntrance.grantDrainMarkedBranchQuotaDrop
#print axioms L3.GrantDrainEntrance.grantDrainMarkedBranchPhysicalCover
#print axioms L3.GrantDrainEntrance.grantDrainMarkedBranchLivePositive
#print axioms L3.GrantDrainEntrance.grantDrainMarkedBranchZeroPhysical
#print axioms L3.GrantDrainEntrance.grantDrainMarkedBranchCostProjection
#print axioms L3.GrantDrainEntrance.grantDrainMarkedBranchCost
