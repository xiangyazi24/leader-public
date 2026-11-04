import Leader.L3.Grant.DrainMarkedBranch
import Leader.L3.Grant.DrainWarmAll

/-!
# Literal warm-stage and source-ledger joint accounting

This is a PARTIAL module:
the unconditional physical warm-stage cost is not asserted.

A warm-ending edge is not a quota-increase counterexample:
a warm certified label carries its final service credit, so
its rank is at least one and the combined quota is rank + 2*n.
Every successor source-ledger remaining is at most 2*n.

The unresolved invariant is that each live initially cold
origin, and each initially warm origin after its first cold
edge, has a non-unmarked persistent ledger mark. The full
warm-host / source-ledger identity bridge is likewise required
for the collective zero-quota implies physical GrantFree step.
Nothing below assumes those missing facts as a proof leaf.
-/

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- A synchronized warm family and persistent entrance ledger.
Both read exactly the same canonical physical state. -/
structure GrantDrainWarmStageJoint
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) where
  warm : GrantDrainWarmAllCertified (Scratch := Scratch) ring
  ledger : GrantDrainEntranceState n Scratch
  physicalEq : warm.physical = ledger.physical
  clean : C_native ring warm.physical.native

/-- No separate restart of the marked ledger at a later cut. -/
noncomputable def grantDrainWarmStageJointInitial
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch)
    (hC : C_native ring s.native) :
    GrantDrainWarmStageJoint (Scratch := Scratch) ring :=
  { warm := grantDrainWarmAllCertifiedEntrance ring hn s hC
    ledger := grantDrainEntranceInitial ring s
    physicalEq := rfl
    clean := hC }

/-- The same actual scheduler step updates both ghost families. -/
noncomputable def grantDrainWarmStageJointNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring)
    (e : Fin n) :
    GrantDrainWarmStageJoint (Scratch := Scratch) ring := by
  refine
    { warm := grantDrainWarmAllCertifiedNext
        ring hn fresh update z.warm e
      ledger := grantDrainEntranceNext
        ring fresh update z.ledger e
      physicalEq := ?_
      clean := ?_ }
  · change grantDrainStep ring fresh update z.warm.physical e =
      grantDrainStep ring fresh update z.ledger.physical e
    exact congrArg
      (fun s => grantDrainStep ring fresh update s e)
      z.physicalEq
  · exact grantDrainStepPreservesC_native
      ring hn fresh update z.warm.physical e z.clean

/-- One word for all original identities. -/
noncomputable def grantDrainWarmStageJointRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring)
    (word : List (Fin n)) :
    GrantDrainWarmStageJoint (Scratch := Scratch) ring :=
  word.foldl
    (grantDrainWarmStageJointNext ring hn fresh update) z

/-- Its physical coordinate is the original canonical source word. -/
theorem grantDrainWarmStageJointPhysicalWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring),
      (grantDrainWarmStageJointRun
        ring hn fresh update z word).warm.physical =
        word.foldl (grantDrainStep ring fresh update)
          z.warm.physical := by
  intro word
  induction word with
  | nil =>
      intro z
      rfl
  | cons e rest ih =>
      intro z
      change
        (grantDrainWarmStageJointRun ring hn fresh update
          (grantDrainWarmStageJointNext
            ring hn fresh update z e) rest).warm.physical =
        rest.foldl (grantDrainStep ring fresh update)
          (grantDrainStep ring fresh update z.warm.physical e)
      exact ih (grantDrainWarmStageJointNext
        ring hn fresh update z e)

/-- The original source ledger is never discarded or reset. -/
theorem grantDrainWarmStageJointLedgerWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring),
      (grantDrainWarmStageJointRun
        ring hn fresh update z word).ledger =
        grantDrainEntranceRun ring fresh update
          z.ledger word := by
  intro word
  induction word with
  | nil =>
      intro z
      rfl
  | cons e rest ih =>
      intro z
      change
        (grantDrainWarmStageJointRun ring hn fresh update
          (grantDrainWarmStageJointNext
            ring hn fresh update z e) rest).ledger =
        grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update z.ledger e) rest
      exact ih (grantDrainWarmStageJointNext
        ring hn fresh update z e)

/-- An exact per-label reserve on the synchronized physical row.
The cold branch always reads the persistent source ledger. -/
def grantDrainWarmStageCombinedQuota
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (label : GrantDrainLedgerLabel n) : Nat :=
  if z.label.warm = true then
    grantDrainWarmCertifiedRank ring z + 2 * n
  else if label.host = none then 0
  else label.remaining

/-- The warm-phase rank includes its final charged service. -/
theorem grantDrainWarmStageWarmRankPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (hWarm : z.label.warm = true) :
    0 < grantDrainWarmCertifiedRank ring z := by
  change 0 <
    (if z.label.warm = true then
      grantDrainChargedWarmRank ring z.state z.label + 1
     else 0)
  rw [if_pos hWarm]
  omega

/-- The source ledger's next numeric reserve is never above 2n. -/
theorem grantDrainWarmStageNewLedgerCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) :
    (grantDrainLedgerStep ring fresh update s e label).remaining ≤
      2 * n := by
  exact grantDrainLedgerStep_quota_le_double
    ring fresh update s e label

/-- At a cold endpoint the combined reserve is at most the
literal source-ledger remaining counter. -/
theorem grantDrainWarmStageColdQuotaBound
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (label : GrantDrainLedgerLabel n)
    (hCold : z.label.warm = false) :
    grantDrainWarmStageCombinedQuota ring z label ≤
      label.remaining := by
  have hNot : ¬ z.label.warm = true := by
    rw [hCold]
    decide
  unfold grantDrainWarmStageCombinedQuota
  rw [if_neg hNot]
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- On the FIRST warm-ending edge, the new quota is at most 2n,
whereas the old quota was at least 2n+1. This is a strict
decrease on EVERY possible ending edge, not only nominated ones.
There can be no n=5 counterexample to this specific inequality. -/
theorem grantDrainWarmStageExitStrict
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (label : GrantDrainLedgerLabel n) (e : Fin n)
    (hWarm : z.label.warm = true)
    (hExit : (grantDrainWarmCertifiedNext
      ring hn fresh update z e).label.warm = false) :
    grantDrainWarmStageCombinedQuota ring
      (grantDrainWarmCertifiedNext ring hn fresh update z e)
      (grantDrainLedgerStep ring fresh update z.state e label) + 1 ≤
    grantDrainWarmStageCombinedQuota ring z label := by
  have hNew := grantDrainWarmStageNewLedgerCap
    ring fresh update z.state e label
  have hCold := grantDrainWarmStageColdQuotaBound ring
    (grantDrainWarmCertifiedNext ring hn fresh update z e)
    (grantDrainLedgerStep ring fresh update z.state e label)
    hExit
  have hOldRank := grantDrainWarmStageWarmRankPositive ring z hWarm
  have hOld :
      grantDrainWarmStageCombinedQuota ring z label =
        grantDrainWarmCertifiedRank ring z + 2 * n := by
    simp only [grantDrainWarmStageCombinedQuota, hWarm, if_true]
  rw [hOld]
  omega

/-- If the label stays warm, its original certified rank pays for
the next step; the reserved 2n marked budget is unchanged. -/
theorem grantDrainWarmStageContinuingNonincrease
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (label : GrantDrainLedgerLabel n) (e : Fin n)
    (hWarm : z.label.warm = true)
    (hNextWarm : (grantDrainWarmCertifiedNext
      ring hn fresh update z e).label.warm = true) :
    grantDrainWarmStageCombinedQuota ring
      (grantDrainWarmCertifiedNext ring hn fresh update z e)
      (grantDrainLedgerStep ring fresh update z.state e label) ≤
    grantDrainWarmStageCombinedQuota ring z label := by
  have hRank :=
    grantDrainWarmCertifiedRankNonincrease
      ring hn fresh update z e
  have hOld :
      grantDrainWarmStageCombinedQuota ring z label =
        grantDrainWarmCertifiedRank ring z + 2 * n := by
    simp only [grantDrainWarmStageCombinedQuota, hWarm, if_true]
  have hNew :
      grantDrainWarmStageCombinedQuota ring
        (grantDrainWarmCertifiedNext ring hn fresh update z e)
        (grantDrainLedgerStep ring fresh update z.state e label) =
        grantDrainWarmCertifiedRank ring
          (grantDrainWarmCertifiedNext ring hn fresh update z e) +
          2 * n := by
    simp only [grantDrainWarmStageCombinedQuota, hNextWarm, if_true]
  rw [hOld, hNew]
  omega

/-- Every literal scheduler edge has nonincreasing combined quota
as long as the old certificate is still warm. -/
theorem grantDrainWarmStageActiveNonincrease
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (label : GrantDrainLedgerLabel n) (e : Fin n)
    (hWarm : z.label.warm = true) :
    grantDrainWarmStageCombinedQuota ring
      (grantDrainWarmCertifiedNext ring hn fresh update z e)
      (grantDrainLedgerStep ring fresh update z.state e label) ≤
    grantDrainWarmStageCombinedQuota ring z label := by
  cases hNext : (grantDrainWarmCertifiedNext
      ring hn fresh update z e).label.warm with
  | false =>
      have hDrop := grantDrainWarmStageExitStrict
        ring hn fresh update z label e hWarm hNext
      omega
  | true =>
      exact grantDrainWarmStageContinuingNonincrease
        ring hn fresh update z label e hWarm hNext

/-- The predictable certified warm nomination strictly decreases
the combined reserve, including if it ends warmth. -/
theorem grantDrainWarmStageActiveChosenDrop
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (label : GrantDrainLedgerLabel n)
    (hWarm : z.label.warm = true) :
    grantDrainWarmStageCombinedQuota ring
      (grantDrainWarmCertifiedNext ring hn fresh update z
        (grantDrainWarmCertifiedChosen ring z))
      (grantDrainLedgerStep ring fresh update z.state
        (grantDrainWarmCertifiedChosen ring z) label) + 1 ≤
    grantDrainWarmStageCombinedQuota ring z label := by
  cases hNext : (grantDrainWarmCertifiedNext
      ring hn fresh update z
        (grantDrainWarmCertifiedChosen ring z)).label.warm with
  | false =>
      exact grantDrainWarmStageExitStrict
        ring hn fresh update z label
        (grantDrainWarmCertifiedChosen ring z) hWarm hNext
  | true =>
      have hActive : ¬ z.label.warm = false := by
        intro hFalse
        rw [hWarm] at hFalse
        cases hFalse
      have hRank :=
        grantDrainWarmCertifiedNominatedDrop
          ring hn fresh update z hActive
      have hOld :
          grantDrainWarmStageCombinedQuota ring z label =
            grantDrainWarmCertifiedRank ring z + 2 * n := by
        simp only [grantDrainWarmStageCombinedQuota, hWarm, if_true]
      have hNew :
          grantDrainWarmStageCombinedQuota ring
            (grantDrainWarmCertifiedNext ring hn fresh update z
              (grantDrainWarmCertifiedChosen ring z))
            (grantDrainLedgerStep ring fresh update z.state
              (grantDrainWarmCertifiedChosen ring z) label) =
          grantDrainWarmCertifiedRank ring
            (grantDrainWarmCertifiedNext ring hn fresh update z
              (grantDrainWarmCertifiedChosen ring z)) + 2 * n := by
        simp only [grantDrainWarmStageCombinedQuota, hNext, if_true]
      rw [hOld, hNew]
      omega

/-- At each actual warm certified entrance the combined quota
is initially at most eight n. -/
theorem grantDrainWarmStageEntranceQuotaCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (label : GrantDrainLedgerLabel n) :
    grantDrainWarmStageCombinedQuota ring
      (grantDrainWarmCertifiedEntrance ring hn
        s g hC hWarm hGrant) label ≤ 8 * n := by
  have hCap :=
    grantDrainWarmCertifiedEntranceRankCap
      ring hn s g hC hWarm hGrant
  change grantDrainWarmCertifiedRank ring
      (grantDrainWarmCertifiedEntrance ring hn
        s g hC hWarm hGrant) + 2 * n ≤ 8 * n
  omega

/-- Exact cyclic predecessor for the cold, unrequested label. -/
private theorem grantDrainWarmStageIncomingRight
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (g : Fin n) :
    ring.rightNeighbor (PPL.shiftLeft ring g 1) = g := by
  apply Fin.ext
  have hOne : 1 % n = 1 :=
    Nat.mod_eq_of_lt (by omega)
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

/-- The cold label nominates outgoing on an OLD request,
otherwise the unique incoming predecessor. -/
def grantDrainWarmStageColdChosen
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n) : Fin n :=
  match label.host with
  | none => label.identity
  | some g =>
      if s.request g then g
      else PPL.shiftLeft ring g 1

/-- The chosen OLD edge is a literal nominated-hit for any
live label, including weak marks. -/
theorem grantDrainWarmStageColdChosenHits
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n)
    (g : Fin n) (hHost : label.host = some g) :
    grantDrainLedgerNominatedHit ring s
      (grantDrainWarmStageColdChosen ring s label)
      label.host = true := by
  unfold grantDrainWarmStageColdChosen
  rw [hHost]
  cases hReq : s.request g with
  | true =>
      simp [grantDrainLedgerNominatedHit, hHost, hReq]
  | false =>
      simp [grantDrainLedgerNominatedHit, hHost, hReq,
        grantDrainWarmStageIncomingRight ring hn g]

/-- Marked credits never reset: even when the label promotes,
its nominated service spends one old remaining unit. -/
private theorem grantDrainWarmStageMarkedHitSpent
    (n : Nat) (label : GrantDrainLedgerLabel n)
    (newHost : Option (Fin n)) (newMark : GrantDrainMark)
    (held : Bool)
    (hMarked : label.mark ≠ .unmarked) :
    grantDrainLedgerRemainingNext n label
      newHost newMark true held ≤ label.remaining - 1 := by
  cases newHost with
  | none =>
      simp [grantDrainLedgerRemainingNext]
  | some g =>
      change min
        (if label.mark = .unmarked then
          grantDrainLedgerQuotaCap n newMark held
         else label.remaining - 1)
        (grantDrainLedgerQuotaCap n newMark held) ≤
          label.remaining - 1
      rw [if_neg hMarked]
      exact Nat.min_le_left _ _

/-- Once a cold ledger label is marked, every future edge
preserves nonincrease, with no temporary recharge on promotion. -/
theorem grantDrainWarmStageColdMarkedNonincrease
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (label : GrantDrainLedgerLabel n) (e : Fin n)
    (hCold : z.label.warm = false)
    (hMarked : label.host ≠ none → label.mark ≠ .unmarked) :
    grantDrainWarmStageCombinedQuota ring
      (grantDrainWarmCertifiedNext ring hn fresh update z e)
      (grantDrainLedgerStep ring fresh update z.state e label) ≤
    grantDrainWarmStageCombinedQuota ring z label := by
  have hNextCold :=
    grantDrainD6MergeColdLabelRemainsCold
      ring fresh update z.state e z.label hCold
  have hNextColdCert :
      (grantDrainWarmCertifiedNext
        ring hn fresh update z e).label.warm = false :=
    hNextCold
  cases hHost : label.host with
  | none =>
      have hNextNone :
          (grantDrainLedgerStep ring fresh update
            z.state e label).host = none :=
        grantDrainLedgerStep_retired_absorbing
          ring fresh update z.state e label hHost
      simp [grantDrainWarmStageCombinedQuota, hCold,
        hNextColdCert, hHost, hNextNone]
  | some g =>
      have hLive : label.host ≠ none := by
        rw [hHost]
        intro hh
        cases hh
      have hMono :=
        grantDrainLedgerStep_remaining_nonincrease
          ring fresh update z.state e label (hMarked hLive)
      have hNewBound :=
        grantDrainWarmStageColdQuotaBound
          ring
          (grantDrainWarmCertifiedNext ring hn fresh update z e)
          (grantDrainLedgerStep ring fresh update z.state e label)
          hNextColdCert
      have hOld :
          grantDrainWarmStageCombinedQuota ring z label =
            label.remaining := by
        simp [grantDrainWarmStageCombinedQuota, hCold, hHost]
      rw [hOld]
      exact Nat.le_trans hNewBound hMono

/-- A cold, marked, positive label spends at least one quota
unit on the nominated edge, including WEAK. -/
theorem grantDrainWarmStageColdMarkedChosenDrop
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (label : GrantDrainLedgerLabel n)
    (hCold : z.label.warm = false)
    (hMarked : label.host ≠ none → label.mark ≠ .unmarked)
    (hPositive : 0 <
      grantDrainWarmStageCombinedQuota ring z label) :
    grantDrainWarmStageCombinedQuota ring
      (grantDrainWarmCertifiedNext ring hn fresh update z
        (grantDrainWarmStageColdChosen ring z.state label))
      (grantDrainLedgerStep ring fresh update z.state
        (grantDrainWarmStageColdChosen ring z.state label) label) + 1 ≤
    grantDrainWarmStageCombinedQuota ring z label := by
  cases hHost : label.host with
  | none =>
      have hZero : grantDrainWarmStageCombinedQuota ring z label = 0 := by
        simp [grantDrainWarmStageCombinedQuota, hCold, hHost]
      rw [hZero] at hPositive
      omega
  | some g =>
      have hLive : label.host ≠ none := by
        rw [hHost]
        intro hh
        cases hh
      have hHit :=
        grantDrainWarmStageColdChosenHits
          ring hn z.state label g hHost
      have hNextCold :=
        grantDrainD6MergeColdLabelRemainsCold
          ring fresh update z.state
          (grantDrainWarmStageColdChosen ring z.state label)
          z.label hCold
      have hNextColdCert :
          (grantDrainWarmCertifiedNext ring hn fresh update z
            (grantDrainWarmStageColdChosen ring z.state label)).label.warm =
            false := hNextCold
      have hNextUpper :=
        grantDrainWarmStageColdQuotaBound ring
          (grantDrainWarmCertifiedNext ring hn fresh update z
            (grantDrainWarmStageColdChosen ring z.state label))
          (grantDrainLedgerStep ring fresh update z.state
            (grantDrainWarmStageColdChosen ring z.state label) label)
          hNextColdCert
      have hSpent :
          (grantDrainLedgerStep ring fresh update z.state
            (grantDrainWarmStageColdChosen ring z.state label)
            label).remaining ≤ label.remaining - 1 := by
        change grantDrainLedgerRemainingNext n label
          (grantDrainLedgerHost ring fresh z.state
            (grantDrainWarmStageColdChosen ring z.state label)
            label.host)
          (grantDrainLedgerMarkNext ring fresh update z.state
            (grantDrainWarmStageColdChosen ring z.state label)
            label)
          (grantDrainLedgerNominatedHit ring z.state
            (grantDrainWarmStageColdChosen ring z.state label)
            label.host)
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update z.state
              (grantDrainWarmStageColdChosen ring z.state label))
            (grantDrainLedgerHost ring fresh z.state
              (grantDrainWarmStageColdChosen ring z.state label)
              label.host)) ≤ label.remaining - 1
        rw [hHit]
        exact grantDrainWarmStageMarkedHitSpent
          n label _ _ _ (hMarked hLive)
      have hOld :
          grantDrainWarmStageCombinedQuota ring z label =
            label.remaining := by
        simp [grantDrainWarmStageCombinedQuota, hCold, hHost]
      rw [hOld]
      have hOldPositive : 0 < label.remaining := by
        rw [hOld] at hPositive
        exact hPositive
      omega

/-!
The remaining universal physical statement is the cold-mark
adequacy for each original identity. On the genuine C_native
trajectory, prove that a still-live source-ledger host outside
the warm phase has an inherited weak, strong, or terminal mark;
this must cover origins initially nonwarm and the FIRST cooling
edge. In addition, the warm-label host must agree with the
corresponding immutable ledger host on its warm prefixes, so
zero combined quotas truly imply physical GrantFree.

WarmAll tracks initially warm origins only: absent Option entries
are not proof of retirement of initially cold grants.
These conditions have not been proved in the inspected import
closure. Thus the unrestricted grantDrainWarmStageCost
does not follow from the lemmas above, and no fabricated theorem
or numerical five-site counterexample is claimed.
-/

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainWarmStageJointPhysicalWord
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageJointLedgerWord
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageExitStrict
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageActiveNonincrease
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageActiveChosenDrop
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageColdMarkedNonincrease
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageColdMarkedChosenDrop
