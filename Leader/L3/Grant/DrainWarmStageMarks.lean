import Leader.L3.Grant.DrainWarmStage
import Leader.L3.Grant.DrainWarmQuota

namespace L3.GrantDrainEntrance

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- In a clean sector, every signal-zero follower has a complete
zero-signal prefix back through the sector leader.  The bullet
case uses the zero prefix through the unique bullet and 0*1*
on the suffix.  The bullet-free case also uses the ready-leader
clause, which excludes a one-signal leader followed by zero. -/
theorem grantDrainWarmStageSectorColdZeroPrefix
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1)) (a : Fin n)
    (hC : C_native ring N)
    (hSector : sectorLength ring N p d)
    (ha : 1 ≤ a.val) (had : a.val < d.val)
    (hZero : (N (PPL.shiftRight ring p a.val)).sg = false) :
    ∀ k : Fin n, k.val ≤ a.val →
      (N (PPL.shiftRight ring p k.val)).sg = false := by
  rcases hC.2 p d hSector with hBullet | hEmpty
  · obtain ⟨h, _, _, hClear, hSuffix⟩ := hBullet
    by_cases hAt : a.val ≤ h.val
    · intro k hk
      exact hClear k (by omega)
    · obtain ⟨cut, _, _, hZeros, hOnes⟩ := hSuffix
      have hBeforeCut : a.val < cut.val := by
        by_cases hAfter : cut.val ≤ a.val
        · have hOne := hOnes a hAfter had
          rw [hZero] at hOne
          cases hOne
        · omega
      intro k hk
      by_cases hBeforeBullet : k.val ≤ h.val
      · exact hClear k hBeforeBullet
      · exact hZeros k (by omega) (by omega)
  · obtain ⟨_, hSuffix, hReady⟩ := hEmpty
    obtain ⟨cut, _, _, hZeros, hOnes⟩ := hSuffix
    have hBeforeCut : a.val < cut.val := by
      by_cases hAfter : cut.val ≤ a.val
      · have hOne := hOnes a hAfter had
        rw [hZero] at hOne
        cases hOne
      · omega
    have hLeaderZero : (N p).sg = false := by
      cases hs : (N p).sg with
      | false => rfl
      | true =>
          have hOne := hReady hs a ha had
          rw [hZero] at hOne
          cases hOne
    intro k hk
    by_cases hkZero : k.val = 0
    · have hSite : PPL.shiftRight ring p k.val = p := by
        rw [hkZero]
        apply Fin.ext
        change (p.val + 0) % n = p.val
        simp [Nat.mod_eq_of_lt p.isLt]
      rw [hSite]
      exact hLeaderZero
    · exact hZeros k (by omega) (by omega)

/-- A live or dummy bullet must have signal zero at its own
site in C_native.  In particular the proposed signal-one,
nonzero-bullet cold grant is not a C_native configuration. -/
theorem grantDrainWarmStageBulletSignalZero
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hC : C_native ring N) (g : Fin n)
    (hBullet : HasBullet N g) :
    (N g).sg = false := by
  obtain ⟨p, d, a, hSector, had, hSite⟩ :=
    grantDrainEntranceSectorCoverOfRoot
      ring N hC.1.1.1 g
  have hAt : HasBullet N
      (PPL.shiftRight ring p a.val) := by
    rw [← hSite]
    exact hBullet
  have hZero :=
    (hC.1.2 p d hSector).2 a had hAt a (Nat.le_refl _)
  rw [← hSite] at hZero
  exact hZero

/-- A follower at signal zero is on the Boolean zero corridor
of its nearest preceding leader.  The native sector cover and
scan-to-arc theorem align the clean-sector certificate with the
persistent ledger's actual List.range observer. -/
theorem grantDrainWarmStageColdFollowerCorridor
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) (hC : C_native ring s.native)
    (hFollower : (s.native g).l = false)
    (hZero : (s.native g).sg = false) :
    grantDrainLedgerCorridor ring s g = true := by
  obtain ⟨p, d, a, hSector, had, hSite⟩ :=
    grantDrainEntranceSectorCoverOfRoot
      ring s.native hC.1.1.1 g
  have ha : 1 ≤ a.val := by
    by_cases hzero : a.val = 0
    · have heq : g = p := by
        rw [hSite, hzero]
        apply Fin.ext
        change (p.val + 0) % n = p.val
        simp [Nat.mod_eq_of_lt p.isLt]
      rw [heq, hSector.2.1] at hFollower
      cases hFollower
    · omega
  have hOffset :
      PPL.cyclicOffset ring p g = a.val := by
    rw [hSite]
    change (((p.val + a.val) % n + n - p.val) % n) =
      a.val
    by_cases hNoWrap : p.val + a.val < n
    · rw [Nat.mod_eq_of_lt hNoWrap]
      have hEq : p.val + a.val + n - p.val = n + a.val := by
        omega
      rw [hEq, Nat.add_mod_left, Nat.mod_eq_of_lt a.isLt]
    · have hWrap : n ≤ p.val + a.val := by omega
      have hShort : p.val + a.val - n < n := by omega
      rw [Nat.mod_eq_sub_mod hWrap, Nat.mod_eq_of_lt hShort]
      have hEq : p.val + a.val - n + n - p.val = a.val := by
        omega
      rw [hEq, Nat.mod_eq_of_lt a.isLt]
  have hNearest :
      GrantDrainMarksNearestArc ring s.native p g := by
    refine ⟨?_, hSector.2.1, ?_⟩
    · rw [hOffset]
      exact ha
    · intro k hk hlt
      have hBefore : k < d.val := by
        rw [hOffset] at hlt
        omega
      exact hSector.2.2.2
        (⟨k, show k < n by omega⟩ : Fin n) hk hBefore
  have hZeroAt : (s.native (PPL.shiftRight ring p a.val)).sg =
      false := by
    rw [← hSite]
    exact hZero
  have hPrefix := grantDrainWarmStageSectorColdZeroPrefix
    ring s.native p d a hC hSector ha had hZeroAt
  have hZeroArc :
      GrantDrainMarksZeroOffsetArc ring s.native p g := by
    intro k hk
    have hBefore : k < a.val := by
      rw [hOffset] at hk
      exact hk
    exact hPrefix
      (⟨k, show k < n by omega⟩ : Fin n)
      (Nat.le_of_lt hBefore)
  have hDistance :=
    grantDrainMarksScanOfNearestArc ring s.native p g hNearest
  have hLeft := grantDrainEntranceLeftOffset ring p g
  have hAll :=
    grantDrainMarksOffsetZeroAll ring s.native p g hZeroArc
  unfold grantDrainLedgerCorridor
  dsimp only
  rw [hDistance, hLeft, hSector.2.1, hAll]
  rfl

/-- At every C_native cut an occupied grant which is not
syntactically warm has a non-unmarked local observer: it is
held, leader-hosted, or on a zero corridor (strong or weak).
No reachability restriction beyond C_native is needed. -/
theorem grantDrainWarmStageColdGrantObservedMarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) (hC : C_native ring s.native)
    (hGrant : s.grant g = true)
    (hCold : grantDrainWarmAt s g = false) :
    grantDrainLedgerObservedMark ring s (some g) ≠
      .unmarked := by
  by_cases hLeader : (s.native g).l = true
  · simp [grantDrainLedgerObservedMark, hLeader]
  · by_cases hRequest : s.request g = true
    · simp [grantDrainLedgerObservedMark, hRequest, hGrant]
    · have hNotLeader : (s.native g).l = false := by
        cases h : (s.native g).l with
        | false => rfl
        | true => exact False.elim (hLeader h)
      have hNoRequest : s.request g = false := by
        cases h : s.request g with
        | false => rfl
        | true => exact False.elim (hRequest h)
      have hSignalZero : (s.native g).sg = false := by
        cases hSignal : (s.native g).sg with
        | false => rfl
        | true =>
            have hEmptyBullet : (s.native g).b = (0 : Fin 3) := by
              by_cases hEmpty : (s.native g).b = (0 : Fin 3)
              · exact hEmpty
              · have hZero := grantDrainWarmStageBulletSignalZero
                  ring s.native hC g hEmpty
                rw [hSignal] at hZero
                cases hZero
            have hWarm : grantDrainWarmAt s g = true := by
              simp [grantDrainWarmAt, hNotLeader,
                hNoRequest, hEmptyBullet, hSignal]
            rw [hCold] at hWarm
            cases hWarm
      have hCorridor := grantDrainWarmStageColdFollowerCorridor
        ring s g hC hNotLeader hSignalZero
      cases hShield :
          (s.native (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g))).sh with
      | true =>
          have hStrong : grantDrainLedgerStrongLock ring s g =
              true := by
            simp [grantDrainLedgerStrongLock,
              hCorridor, hShield]
          simp [grantDrainLedgerObservedMark, hNoRequest,
            hGrant, hNotLeader, hStrong]
      | false =>
          have hStrong : grantDrainLedgerStrongLock ring s g =
              false := by
            simp [grantDrainLedgerStrongLock,
              hCorridor, hShield]
          have hWeak : grantDrainLedgerWeakLock ring s g =
              true := by
            simp [grantDrainLedgerWeakLock,
              hCorridor, hShield]
          simp [grantDrainLedgerObservedMark, hNoRequest,
            hGrant, hNotLeader, hStrong, hWeak]

/-- Consequently every initially cold surviving grant already
has a positive-grade persistent ledger identity. -/
theorem grantDrainWarmStageColdInitialMarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) (hC : C_native ring s.native)
    (hGrant : s.grant g = true)
    (hCold : grantDrainWarmAt s g = false) :
    (grantDrainLedgerInitial ring s g).mark ≠ .unmarked := by
  change grantDrainLedgerObservedMark ring s
      (if s.grant g then some g else none) ≠ .unmarked
  rw [if_pos hGrant]
  exact grantDrainWarmStageColdGrantObservedMarked
    ring s g hC hGrant hCold

/-- The join used by the persistent ledger never loses the rank
of its right operand, even when an older rank wins. -/
theorem grantDrainWarmStageMarkJoinRightRank
    (old observed : GrantDrainMark) :
    grantDrainMarkRank observed ≤
      grantDrainMarkRank (grantDrainMarkJoin old observed) := by
  unfold grantDrainMarkJoin
  split
  · exact Nat.le_refl _
  · omega

/-- Every ledger update contains the NEW physical observed mark as
the innermost right operand of three monotone joins.  This is
independent of whether the source label was already marked. -/
theorem grantDrainWarmStagePostObservedRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) :
    grantDrainMarkRank
      (grantDrainLedgerObservedMark ring
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e label.host)) ≤
      grantDrainMarkRank
        (grantDrainLedgerStep ring fresh update s e label).mark := by
  change grantDrainMarkRank
      (grantDrainLedgerObservedMark ring
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e label.host)) ≤
    grantDrainMarkRank
      (grantDrainLedgerMarkNext ring fresh update s e label)
  unfold grantDrainLedgerMarkNext
  exact Nat.le_trans
    (grantDrainWarmStageMarkJoinRightRank _ _)
    (Nat.le_trans
      (grantDrainWarmStageMarkJoinRightRank _ _)
      (grantDrainWarmStageMarkJoinRightRank _ _))

/-- On any first cooling edge whose NEW live host is physically
nonwarm, the persistent ledger acquires a non-unmarked mark
immediately.  The conclusion is a genuine one-step observer fact;
the source dynamics, not this lemma, must establish host equality
and that the warm phase has just ended. -/
theorem grantDrainWarmStagePostColdLedgerMarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hCPost : C_native ring
      (grantDrainStep ring fresh update s e).native)
    (hHostPost :
      grantDrainLedgerHost ring fresh s e label.host = some g)
    (hGrantPost : (grantDrainStep ring fresh update s e).grant g =
      true)
    (hColdPost : grantDrainWarmAt
      (grantDrainStep ring fresh update s e) g = false) :
    (grantDrainLedgerStep ring fresh update s e label).mark ≠
      .unmarked := by
  have hObserved := grantDrainWarmStageColdGrantObservedMarked
    ring (grantDrainStep ring fresh update s e)
    g hCPost hGrantPost hColdPost
  have hPositive : 0 <
      grantDrainMarkRank
        (grantDrainLedgerObservedMark ring
          (grantDrainStep ring fresh update s e) (some g)) := by
    cases hm : grantDrainLedgerObservedMark ring
        (grantDrainStep ring fresh update s e) (some g) with
    | unmarked => exact False.elim (hObserved hm)
    | weak => decide
    | strong => decide
    | terminal => decide
  have hRank := grantDrainWarmStagePostObservedRank
    ring fresh update s e label
  rw [hHostPost] at hRank
  have hNextPositive : 0 <
      grantDrainMarkRank
        (grantDrainLedgerStep ring fresh update s e label).mark :=
    Nat.lt_of_lt_of_le hPositive hRank
  intro hNew
  rw [hNew] at hNextPositive
  have h0 : grantDrainMarkRank GrantDrainMark.unmarked = 0 := rfl
  omega

/-- Once an identity is marked, the installed source-ledger
transition never returns it to the unmarked state. -/
theorem grantDrainWarmStageMarkedPersists
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hMarked : label.mark ≠ .unmarked) :
    (grantDrainLedgerStep ring fresh update s e label).mark ≠
      .unmarked := by
  have hPositive : 0 < grantDrainMarkRank label.mark := by
    cases hm : label.mark with
    | unmarked => exact False.elim (hMarked hm)
    | weak => decide
    | strong => decide
    | terminal => decide
  have hMono :=
    grantDrainLedgerStep_mark_monotone
      ring fresh update s e label
  intro hNext
  rw [hNext] at hMono
  have h0 : grantDrainMarkRank GrantDrainMark.unmarked = 0 := rfl
  omega

/-- For a previously warm identity, the first event making
its warm flag false at a surviving host means that the actual
physical warm guard is false at that NEW host. -/
theorem grantDrainWarmStageCoolingPhysicalCold
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n) (g : Fin n)
    (hOldWarm : label.warm = true)
    (hNewCold :
      (grantDrainWarmLabelStep ring fresh update s e label).warm =
        false)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e label).host =
        some g) :
    grantDrainWarmAt (grantDrainStep ring fresh update s e) g =
      false := by
  change (match
      (grantDrainWarmLabelStep ring fresh update s e label).host with
    | none => false
    | some x => label.warm &&
        grantDrainWarmAt (grantDrainStep ring fresh update s e) x) =
      false at hNewCold
  simpa [hNewHost, hOldWarm] using hNewCold

/-- A first warm-to-cold transition that retains an actual grant
immediately promotes the corresponding persistent source-ledger
identity, using the GREEN warm/ledger host bridge.  This also
covers source HOLD and intermediate non-FIRE cooling rows. -/
theorem grantDrainWarmStageFirstCoolingMarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (warm : GrantDrainWarmLabel n)
    (ledger : GrantDrainLedgerLabel n) (g : Fin n)
    (hC : C_native ring s.native)
    (hOldWarm : warm.warm = true)
    (hOldHost : warm.host = ledger.host)
    (hReal : ∀ p : Fin n, warm.host = some p →
      s.grant p = true)
    (hNewCold :
      (grantDrainWarmLabelStep ring fresh update s e warm).warm =
        false)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e warm).host =
        some g)
    (hGrantPost :
      (grantDrainStep ring fresh update s e).grant g = true) :
    (grantDrainLedgerStep ring fresh update s e ledger).mark ≠
      .unmarked := by
  have hHosts := grantDrainWarmQuotaHostStep
    ring fresh update s e warm ledger hOldHost hReal
  have hLedgerHost :
      grantDrainLedgerHost ring fresh s e ledger.host = some g := by
    change (grantDrainLedgerStep ring fresh update s e ledger).host =
      some g
    exact hHosts.symm.trans hNewHost
  have hPostClean := grantDrainStepPreservesC_native
    ring hn fresh update s e hC
  have hPhysicalCold := grantDrainWarmStageCoolingPhysicalCold
    ring fresh update s e warm g hOldWarm hNewCold hNewHost
  exact grantDrainWarmStagePostColdLedgerMarked
    ring fresh update s e ledger g hPostClean
    hLedgerHost hGrantPost hPhysicalCold

/-- Every established weak, strong, or terminal mark has
positive initial service credit on a nonempty ring. -/
theorem grantDrainWarmStageMarkedQuotaPositive
    (n : Nat) (hn : 1 ≤ n)
    (mark : GrantDrainMark) (held : Bool)
    (hMarked : mark ≠ .unmarked) :
    0 < grantDrainLedgerQuotaCap n mark held := by
  cases mark with
  | unmarked => exact False.elim (hMarked rfl)
  | weak =>
      simp [grantDrainLedgerQuotaCap]
      omega
  | strong =>
      simp [grantDrainLedgerQuotaCap]
      omega
  | terminal =>
      cases held <;>
        simp [grantDrainLedgerQuotaCap] <;> omega

/-- An initially nonwarm physical grant has a positive ledger
quota. It cannot silently start with the unmarked zero cap. -/
theorem grantDrainWarmStageColdInitialQuotaPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 1 ≤ n)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hGrant : s.grant g = true)
    (hCold : grantDrainWarmAt s g = false) :
    0 < (grantDrainLedgerInitial ring s g).remaining := by
  have hMarked := grantDrainWarmStageColdGrantObservedMarked
    ring s g hC hGrant hCold
  have hCap := grantDrainWarmStageMarkedQuotaPositive
    n hn (grantDrainLedgerObservedMark ring s (some g))
    (grantDrainLedgerHeld s (some g)) hMarked
  change 0 <
    (if s.grant g then
      grantDrainLedgerQuotaCap n
        (grantDrainLedgerObservedMark ring s
          (if s.grant g then some g else none))
        (grantDrainLedgerHeld s
          (if s.grant g then some g else none))
     else 0)
  simp only [hGrant, if_true, ↓reduceIte]
  exact hCap

/-- A marked immutable source-ledger identity cannot revert to
unmarked on any finite genuine scheduler word, even after moving,
coalescing, or retiring. -/
theorem grantDrainWarmStageMarkedWordPersists
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n)) (s : GrantDrainState n Scratch)
      (label : GrantDrainLedgerLabel n),
      label.mark ≠ .unmarked →
      (grantDrainLedgerRun ring fresh update s label word).2.mark ≠
        .unmarked := by
  intro word
  induction word with
  | nil =>
      intro s label hMarked
      exact hMarked
  | cons e rest ih =>
      intro s label hMarked
      change
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label)
          rest).2.mark ≠ .unmarked
      exact ih
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e label)
        (grantDrainWarmStageMarkedPersists
          ring fresh update s e label hMarked)

/-- Initially cold identities cannot lose their source-ledger
mark anywhere on the actual scheduler trajectory. The proof
uses the same immutable initialization and actual ledger run. -/
theorem grantDrainWarmStageInitiallyColdWordMarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hGrant : s.grant g = true)
    (hCold : grantDrainWarmAt s g = false)
    (word : List (Fin n)) :
    (grantDrainLedgerRun ring fresh update s
      (grantDrainLedgerInitial ring s g) word).2.mark ≠
        .unmarked := by
  exact grantDrainWarmStageMarkedWordPersists
    ring fresh update word s
    (grantDrainLedgerInitial ring s g)
    (grantDrainWarmStageColdInitialMarked
      ring s g hC hGrant hCold)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainWarmStageSectorColdZeroPrefix
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageBulletSignalZero
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageColdFollowerCorridor
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageColdGrantObservedMarked
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageColdInitialMarked
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageMarkJoinRightRank
#print axioms L3.GrantDrainEntrance.grantDrainWarmStagePostObservedRank
#print axioms L3.GrantDrainEntrance.grantDrainWarmStagePostColdLedgerMarked
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageMarkedPersists
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageCoolingPhysicalCold
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageFirstCoolingMarked
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageMarkedQuotaPositive
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageColdInitialQuotaPositive
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageMarkedWordPersists
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageInitiallyColdWordMarked
