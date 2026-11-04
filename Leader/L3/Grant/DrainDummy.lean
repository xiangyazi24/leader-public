import Leader.L3.Grant.DrainEntrance

/-!
# Grant drain after the entrance stage: DUMMY geometry and the D.6 warm rank

Split from `Leader.L3.Grant.DrainEntrance` on 2026-10-31 so that each file stays below
the 1 MB limit of the GitHub contents API. The declarations keep their names and the
namespaces they had in the single file.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
5 nonclean-DUMMY retirement.
This section supplies exact initial coverage and the logical
all-retired => I interface. Full all-edge identity transport,
clean-bullet persistence, and < n outgoing-hit quota remain OPEN.
-/

private theorem grantDrainDummyScanFirstExact
    {n : Nat} (site : Nat → Fin n) (hit : Fin n → Bool) :
    ∀ fuel start target : Nat,
      start ≤ target → target < start + fuel →
      hit (site target) = true →
      (∀ k, start ≤ k → k < target → hit (site k) = false) →
      PPL.scanDistance site hit fuel start = some target := by
  intro fuel
  induction fuel with
  | zero =>
      intro start target _ hlt _ _
      omega
  | succ fuel ih =>
      intro start target hlo hlt hHit hMiss
      by_cases hEq : start = target
      · subst target
        simp [PPL.scanDistance, hHit]
      · have hAt : hit (site start) = false :=
          hMiss start (Nat.le_refl _) (by omega)
        have hTail :=
          ih (start + 1) target (by omega) (by omega)
            hHit (fun k hk hkt => hMiss k (by omega) hkt)
        simp [PPL.scanDistance, hAt, hTail]

private theorem grantDrainDummyRightOffset
    {n : Nat} (ring : DirectedRing n)
    (p : Fin n) (t : Nat) (ht : t < n) :
    PPL.cyclicOffset ring p (PPL.shiftRight ring p t) = t := by
  change ((p.val + t) % n + n - p.val) % n = t
  by_cases h : p.val + t < n
  · rw [Nat.mod_eq_of_lt h]
    have hs : p.val + t + n - p.val = n + t := by omega
    rw [hs, Nat.add_mod_left, Nat.mod_eq_of_lt ht]
  · have hge : n ≤ p.val + t := by omega
    have hlt : p.val + t - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have hs : p.val + t - n + n - p.val = t := by omega
    rw [hs, Nat.mod_eq_of_lt ht]

/-- An offset in a leader sector has that sector's leader as its
actual nearest counterclockwise leader. -/
private theorem grantDrainDummySectorNearest
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring N p d)
    (a : Fin n) (ha : a.val < d.val) :
    leaderSector ring N p
      (PPL.shiftRight ring p a.val) := by
  have haN : a.val < n := by
    have hd := d.isLt
    omega
  have hAt :
      (N (PPL.shiftLeft ring
        (PPL.shiftRight ring p a.val) a.val)).l = true := by
    rw [grantDrainMarksArcShiftLeftRight
      ring p a.val a.val (Nat.le_refl _) haN]
    simpa only [Nat.sub_self,
      grantDrainEntranceR8eShiftZero] using hSector.2.1
  have hMiss :
      ∀ k : Nat, 0 ≤ k → k < a.val →
        (N (PPL.shiftLeft ring
          (PPL.shiftRight ring p a.val) k)).l = false := by
    intro k _ hk
    rw [grantDrainMarksArcShiftLeftRight
      ring p a.val k (by omega) haN]
    exact hSector.2.2.2
      (⟨a.val - k, (show a.val - k < n by omega)⟩ : Fin n)
      (show 0 < a.val - k by omega) (show a.val - k < d.val by omega)
  have hScan :
      PPL.scanDistance
        (fun k => PPL.shiftLeft ring
          (PPL.shiftRight ring p a.val) k)
        (fun i : Fin n => (N i).l) n 0 = some a.val :=
    grantDrainDummyScanFirstExact
      (fun k => PPL.shiftLeft ring
        (PPL.shiftRight ring p a.val) k)
      (fun i : Fin n => (N i).l)
      n 0 a.val (Nat.zero_le _) (by omega) hAt hMiss
  refine ⟨hSector.2.1, ?_⟩
  change PPL.scanDistance
    (fun k => PPL.shiftLeft ring
      (PPL.shiftRight ring p a.val) k)
    (fun i : Fin n => (N i).l) n 0 =
      some (PPL.cyclicOffset ring p
        (PPL.shiftRight ring p a.val))
  rw [grantDrainDummyRightOffset ring p a.val haN]
  exact hScan

/-- Convert the original CleanAt observer to exact sector-indexed
earliest-bullet and inclusive zero-trail certificates. -/
private theorem grantDrainDummyCleanSectorCertificates
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring N p d)
    (a : Fin n) (ha : a.val < d.val)
    (hClean : GrantDrainEntranceBulletCleanAt ring N
      (PPL.shiftRight ring p a.val)) :
    (∀ b : Fin n, b.val < d.val →
      HasBullet N (PPL.shiftRight ring p b.val) →
      a.val ≤ b.val) ∧
    (∀ k : Fin n, k.val ≤ a.val →
      (N (PPL.shiftRight ring p k.val)).sg = false) := by
  rcases hClean with ⟨_, q, hNear, hFirst, hTrail⟩
  have hHere :=
    grantDrainDummySectorNearest ring N p d hSector a ha
  have hEqOffset :
      PPL.cyclicOffset ring q (PPL.shiftRight ring p a.val) =
      PPL.cyclicOffset ring p (PPL.shiftRight ring p a.val) :=
    Option.some.inj (hNear.2.symm.trans hHere.2)
  have hRoot : q = p := by
    have hLeftQ := grantDrainEntranceLeftOffset
      ring q (PPL.shiftRight ring p a.val)
    have hLeftP := grantDrainEntranceLeftOffset
      ring p (PPL.shiftRight ring p a.val)
    rw [hEqOffset] at hLeftQ
    exact hLeftQ.symm.trans hLeftP
  subst q
  constructor
  · intro b hb hBullet
    have haN : a.val < n := by
      have hd := d.isLt
      omega
    have hbN : b.val < n := by
      have hd := d.isLt
      omega
    have hLe := hFirst
      (PPL.shiftRight ring p b.val)
      (grantDrainDummySectorNearest ring N p d hSector b hb)
      hBullet
    rw [grantDrainDummyRightOffset ring p a.val haN,
      grantDrainDummyRightOffset ring p b.val hbN] at hLe
    exact hLe
  · intro k hk
    have haN : a.val < n := by
      have hd := d.isLt
      omega
    exact hTrail k (by
      rw [grantDrainDummyRightOffset ring p a.val haN]
      exact hk)

/-- Every physical bullet clean => native I, with both uniqueness
and the full zero trail. No ghost or transition assumption enters. -/
theorem grantDrainDummyAllCleanImpliesI
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hPB : PPlus ring N)
    (hEvery : ∀ b : Fin n,
      HasBullet N b →
      GrantDrainEntranceBulletCleanAt ring N b) :
    I ring N := by
  refine ⟨hPB, ?_⟩
  intro p d hSector
  constructor
  · intro a b ha hb hA hB
    have hForward :=
      (grantDrainDummyCleanSectorCertificates
        ring N p d hSector a ha (hEvery _ hA)).1 b hb hB
    have hBackward :=
      (grantDrainDummyCleanSectorCertificates
        ring N p d hSector b hb (hEvery _ hB)).1 a ha hA
    exact Fin.ext (by omega)
  · intro a ha hA k hk
    exact (grantDrainDummyCleanSectorCertificates
      ring N p d hSector a ha (hEvery _ hA)).2 k hk

/-- Under PB and no paper-bad LIVE, even a leader-hosted LIVE is
physically clean: peacefulness supplies the inclusive zero trail,
and any earlier bullet would contradict NoBadLive. -/
theorem grantDrainDummyLiveCleanOfNoBad
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hPB : PPlus ring N)
    (hNoBad : ∀ b : Fin n,
      ¬ SharedPaperNonleftmostLiveExact ring N b)
    (b : Fin n) (hLive : LiveBullet N b) :
    GrantDrainEntranceBulletCleanAt ring N b := by
  obtain ⟨p, d, a, hSector, ha, hSite⟩ :=
    grantDrainEntranceSectorCoverOfRoot ring N hPB.1 b
  have haN : a.val < n := by
    have hd := d.isLt
    omega
  have hNear : leaderSector ring N p b := by
    rw [hSite]
    exact grantDrainDummySectorNearest ring N p d hSector a ha
  have hOffset : PPL.cyclicOffset ring p b = a.val := by
    rw [hSite]
    exact grantDrainDummyRightOffset ring p a.val haN
  have hEarliest :
      ∀ z : Fin n, leaderSector ring N p z →
        HasBullet N z →
        PPL.cyclicOffset ring p b ≤ PPL.cyclicOffset ring p z := by
    intro z hSectorZ hBulletZ
    by_cases hEarlier :
        PPL.cyclicOffset ring p z < PPL.cyclicOffset ring p b
    · have hPositive : 0 < a.val := by
        rw [hOffset] at hEarlier
        omega
      have hFollower : (N b).l = false := by
        rw [hSite]
        exact hSector.2.2.2 a hPositive ha
      exact False.elim
        (hNoBad b ⟨hLive, hFollower, p, z,
          hNear, hSectorZ, hBulletZ, hEarlier⟩)
    · omega
  have hPeace : PPL.PeacefulCore ring
      (fun i : Fin n => (N i).l)
      (fun i : Fin n => (N i).sh)
      (fun i : Fin n => (N i).sg) b :=
    hPB.2 b hLive
  unfold PPL.PeacefulCore at hPeace
  rw [hNear.2] at hPeace
  have hTrail : signalTrail ring N p b := by
    intro k hk
    have hDlt : PPL.cyclicOffset ring p b < n :=
      grantDrainEntranceArcOffsetLt ring p b
    have hIndex :
        PPL.cyclicOffset ring p b - k.val <
          PPL.cyclicOffset ring p b + 1 := by omega
    have hZero :=
      hPeace.2
        (⟨PPL.cyclicOffset ring p b - k.val, hIndex⟩ :
          Fin (PPL.cyclicOffset ring p b + 1))
    have hShift :
        PPL.shiftLeft ring b
          (PPL.cyclicOffset ring p b - k.val) =
        PPL.shiftRight ring p k.val := by
      calc
        PPL.shiftLeft ring b
            (PPL.cyclicOffset ring p b - k.val) =
          PPL.shiftLeft ring
            (PPL.shiftRight ring p (PPL.cyclicOffset ring p b))
            (PPL.cyclicOffset ring p b - k.val) := by
              rw [grantDrainMarksArcShiftRightOffset ring p b]
        _ = PPL.shiftRight ring p
            (PPL.cyclicOffset ring p b -
              (PPL.cyclicOffset ring p b - k.val)) :=
          grantDrainMarksArcShiftLeftRight ring p
            (PPL.cyclicOffset ring p b)
            (PPL.cyclicOffset ring p b - k.val)
            (by omega) hDlt
        _ = PPL.shiftRight ring p k.val := by
          congr 1
          omega
    rw [hShift] at hZero
    exact hZero
  have hHas : HasBullet N b := by
    intro hEmpty
    have hImpossible : (2 : Fin 3) = (0 : Fin 3) :=
      hLive.symm.trans hEmpty
    exact (by decide : (2 : Fin 3) ≠ (0 : Fin 3)) hImpossible
  exact ⟨hHas, p, hNear, hEarliest, hTrail⟩

/-- The remaining unclean bullets at a PPlus/NoBadLive cut
are necessarily DUMMY, including possible leader-hosted ones. -/
theorem grantDrainDummyUncleanIsDummy
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hPB : PPlus ring N)
    (hNoBad : ∀ b : Fin n,
      ¬ SharedPaperNonleftmostLiveExact ring N b)
    (b : Fin n)
    (hBullet : HasBullet N b)
    (hUnclean : ¬ GrantDrainEntranceBulletCleanAt ring N b) :
    (N b).b = (1 : Fin 3) := by
  rcases grantDrainEntranceNonzeroBulletKind
      (N b).b hBullet with hDummy | hLive
  · exact hDummy
  · exact False.elim
      (hUnclean
        (grantDrainDummyLiveCleanOfNoBad
          ring N hPB hNoBad b hLive))

/-- Exact COVER to be preserved by the proposed dummy transport.
It is stated as a Prop, NOT silently asserted for future steps. -/
def GrantDrainDummyHostCover {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (host : Fin n → Option (Fin n)) : Prop :=
  ∀ b : Fin n, HasBullet N b →
    ¬ GrantDrainEntranceBulletCleanAt ring N b →
      ∃ id : Fin n, host id = some b

/-- The OLD-state nonclean dummy identity initialization really
covers ALL initially nonclean physical bullets on NoBadLive.
No dynamically created label is postulated here. -/
theorem grantDrainDummyInitialHostCover
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) :
    GrantDrainDummyHostCover ring s.native
      (fun id => (grantDrainEntranceDummyInitial ring s id).host) := by
  intro b hBullet hUnclean
  have hDummy : (s.native b).b = (1 : Fin 3) :=
    grantDrainDummyUncleanIsDummy
      ring s.native hPB hNoBad b hBullet hUnclean
  refine ⟨b, ?_⟩
  exact (grantDrainEntranceDummyInitialHostIff ring s b).mpr
    ⟨hDummy, hUnclean⟩

/-- Step (2) under the precise remaining dynamic coverage premise:
when every immutable nonclean label is gone, native I holds. -/
theorem grantDrainDummyEmptyCoverImpliesI
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (host : Fin n → Option (Fin n))
    (hPB : PPlus ring N)
    (hCover : GrantDrainDummyHostCover ring N host)
    (hEmpty : ∀ id : Fin n, host id = none) :
    I ring N := by
  apply grantDrainDummyAllCleanImpliesI ring N hPB
  intro b hBullet
  by_cases hClean : GrantDrainEntranceBulletCleanAt ring N b
  · exact hClean
  · obtain ⟨id, hHost⟩ := hCover b hBullet hClean
    rw [hEmpty id] at hHost
    cases hHost

/-- On its selected outgoing edge a physical bullet cannot stutter
at its OLD source, regardless of the selected FIRE branch.
This does not establish the requested less-than-n pathwise quota. -/
theorem grantDrainDummyOutgoingSourceCleared
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    ((grantDrainStep ring fresh update s e).native e).b =
      (0 : Fin 3) := by
  exact sharedPaperNativeSourceEmpty ring (by omega : 2 ≤ n) s e

end L3.GrantDrainEntrance

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
The requested distance-only invariant is NOT a valid unconditional
one-edge induction from PPlus alone. A genuine initial terminal-HOLD
label can have quota 1 while its first-left-leader distance is 2.
Even if the terminal clause is repaired separately, the numeric
strong clause does not imply an actual strong physical lock: an
arbitrary strongly marked label at the old weak-source cut has
budget=oldDistance=1 but the actual native leader-death edge
increases distance to 4 without decrementing its quota.

The latter label is an adversarial proof-only label, NOT a
grantDrainLedgerInitial result; it refutes an induction quantified
over arbitrary (s,label) with PPlus and only the numeric Inv.
It is not a counterexample to GrantDrainLedgerNoExhaustion.

The genuine weak-to-strong numerical cap switch and weak-distance
progress inequalities are proved as Nat lemmas below. The missing
theorem is physical lock/current-source coverage, including the
terminal-HOLD and terminal-leader branches, not the Nat arithmetic.
-/

/-- The literal mark-only interpretation of the proposed R8 potential:
a weak marked label must cover d+n, and a strong/terminal marked
label must cover d. This definition intentionally has NO physical
lock or held-status certificate, so its failure is testable. -/
def GrantDrainR8MarkDistanceInv
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n) : Prop :=
  ∀ g : Fin n, label.host = some g →
    match label.mark with
    | .unmarked => True
    | .weak =>
        grantDrainStrongProtectedDistance ring s (some g) + n ≤
          label.remaining
    | .strong =>
        grantDrainStrongProtectedDistance ring s (some g) ≤
          label.remaining
    | .terminal =>
        grantDrainStrongProtectedDistance ring s (some g) ≤
          label.remaining

/-- A genuine PPlus cut, using the previously weak-death
native geometry. The grant at LIVE site 2 is held by request 2. -/
private def grantDrainR8HeldInitialCut : GrantDrainState 5 Unit :=
  { grantDrainWeakDeathFiveStart with
    request := fun i => i.val == 2
    grant := fun i => i.val == 2 }

private def grantDrainR8HeldInitialLabel :
    GrantDrainLedgerLabel 5 :=
  grantDrainLedgerInitial grantDrainWeakDeathFiveRing
    grantDrainR8HeldInitialCut (2 : Fin 5)

theorem grantDrainR8HeldInitialPPlus :
    PPlus grantDrainWeakDeathFiveRing
      grantDrainR8HeldInitialCut.native := by
  change PPlus grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveStart.native
  exact grantDrainWeakDeathFivePPlus

/-- All four claims use only small, closed n=5 fields:
the label is genuine, hosted, terminal, held with remaining 1,
but the nearest counterclockwise leader is at distance 2. -/
theorem grantDrainR8HeldInitialFacts :
    grantDrainR8HeldInitialLabel.host = some (2 : Fin 5) ∧
    grantDrainR8HeldInitialLabel.mark = .terminal ∧
    grantDrainR8HeldInitialLabel.remaining = 1 ∧
    grantDrainStrongProtectedDistance grantDrainWeakDeathFiveRing
      grantDrainR8HeldInitialCut (some (2 : Fin 5)) = 2 := by
  unfold grantDrainR8HeldInitialLabel
    grantDrainLedgerInitial
    grantDrainR8HeldInitialCut
    grantDrainStrongProtectedDistance
    grantDrainWeakDeathFiveStart
    grantDrainWeakDeathFiveRing
  decide +kernel

/-- The mark-only distance formula already fails for an ACTUAL
ledgerInitial label and the empty canonical word, even under
PPlus. Terminal HOLD legitimately has ONE remaining hit, not d. -/
theorem grantDrainR8MarkDistanceFailsAtHeldSeed :
    PPlus grantDrainWeakDeathFiveRing
      grantDrainR8HeldInitialCut.native ∧
    ¬ GrantDrainR8MarkDistanceInv grantDrainWeakDeathFiveRing
        grantDrainR8HeldInitialCut grantDrainR8HeldInitialLabel := by
  refine ⟨grantDrainR8HeldInitialPPlus, ?_⟩
  intro hInv
  have hHost := grantDrainR8HeldInitialFacts.1
  have hMark := grantDrainR8HeldInitialFacts.2.1
  have hRemaining := grantDrainR8HeldInitialFacts.2.2.1
  have hDistance := grantDrainR8HeldInitialFacts.2.2.2
  have hBound := hInv (2 : Fin 5) hHost
  rw [hMark] at hBound
  change
    grantDrainStrongProtectedDistance grantDrainWeakDeathFiveRing
      grantDrainR8HeldInitialCut (some (2 : Fin 5)) ≤
      grantDrainR8HeldInitialLabel.remaining at hBound
  rw [hDistance, hRemaining] at hBound
  omega

/-!
A separate one-edge obstruction to numerical-only induction.
The OLD source at 3 is a QUIET UNSHIELDED leader, so the
correct initial label at 4 is weak. A forged
strong mark satisfies the bare numeric invariant at distance
one, but is not certified by a shielded zero corridor.
The same real e=2 source death opens the longer distance four.
-/

private def grantDrainR8ForgedStrongLabel :
    GrantDrainLedgerLabel 5 :=
  { identity := (4 : Fin 5)
    host := some (4 : Fin 5)
    mark := .strong
    remaining := 1 }

private def grantDrainR8ForgedStrongAfter :
    GrantDrainLedgerLabel 5 :=
  grantDrainLedgerStep grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainWeakDeathFiveStart (2 : Fin 5)
    grantDrainR8ForgedStrongLabel

theorem grantDrainR8ForgedOldDistance :
    grantDrainStrongProtectedDistance grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveStart (some (4 : Fin 5)) = 1 := by
  unfold grantDrainStrongProtectedDistance
    grantDrainWeakDeathFiveStart
    grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveNative
  decide +kernel

theorem grantDrainR8ForgedAfterFacts :
    grantDrainR8ForgedStrongAfter.host = some (4 : Fin 5) ∧
    grantDrainR8ForgedStrongAfter.mark = .strong ∧
    grantDrainR8ForgedStrongAfter.remaining = 1 := by
  unfold grantDrainR8ForgedStrongAfter
    grantDrainR8ForgedStrongLabel
    grantDrainWeakDeathFiveStart
    grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveNative
    grantDrainLedgerStep
  decide +kernel

theorem grantDrainR8ForgedOldMarkDistanceInv :
    GrantDrainR8MarkDistanceInv grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveStart grantDrainR8ForgedStrongLabel := by
  intro g hg
  change (some (4 : Fin 5) : Option (Fin 5)) = some g at hg
  have hSite : (4 : Fin 5) = g := Option.some.inj hg
  subst g
  change grantDrainStrongProtectedDistance
    grantDrainWeakDeathFiveRing grantDrainWeakDeathFiveStart
    (some (4 : Fin 5)) ≤ 1
  rw [grantDrainR8ForgedOldDistance]
  exact Nat.le_refl 1

/-- Literal PPlus + numeric Inv at the old cut, followed by
ONE ACTUAL canonical service e=2 that violates that Inv.
This does NOT use a legal initial ghost label: the forged mark
is the precise reason numeric Inv alone is not inductive. -/
theorem grantDrainR8MarkDistanceNotOneEdgeClosed :
    PPlus grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveStart.native ∧
    GrantDrainR8MarkDistanceInv grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveStart grantDrainR8ForgedStrongLabel ∧
    ¬ GrantDrainR8MarkDistanceInv grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveNext grantDrainR8ForgedStrongAfter := by
  refine ⟨grantDrainWeakDeathFivePPlus,
    grantDrainR8ForgedOldMarkDistanceInv, ?_⟩
  intro hInv
  have hHost := grantDrainR8ForgedAfterFacts.1
  have hMark := grantDrainR8ForgedAfterFacts.2.1
  have hRemaining := grantDrainR8ForgedAfterFacts.2.2
  have hBound := hInv (4 : Fin 5) hHost
  rw [hMark] at hBound
  change
    grantDrainStrongProtectedDistance grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveNext (some (4 : Fin 5)) ≤
      grantDrainR8ForgedStrongAfter.remaining at hBound
  rw [grantDrainWeakDeathFiveDistance, hRemaining] at hBound
  omega

/-- This is the ordinary canonical edge, not a replacement
transition: the old weak root at 3 dies on edge [2]. -/
theorem grantDrainR8ForgedWitnessCanonicalEdge :
    (GrantDrainShared.grantDrainCanonicalModel
      grantDrainWeakDeathFiveRing (by decide : 5 ≤ 5)
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch).step
      grantDrainWeakDeathFiveStart (2 : Fin 5) =
      grantDrainWeakDeathFiveNext := by
  rfl

/-- Weak-to-strong promotion does not lose a paid distance.
If old remaining ≥ old d+n, old d≥1, even a charged hit leaves
at least n before min-cap. This is the exact algebra needed
once the NEW protected source has distance ≤n. -/
theorem grantDrainR8WeakToStrongBudgetAlgebra
    (n oldDistance newDistance oldRemaining : Nat)
    (hit : Bool)
    (hPositive : 0 < oldDistance)
    (hBudget : oldDistance + n ≤ oldRemaining)
    (hNewBound : newDistance ≤ n) :
    newDistance ≤
      min (oldRemaining - (if hit then 1 else 0)) n := by
  cases hit with
  | false =>
      change newDistance ≤ min oldRemaining n
      apply Nat.le_min.mpr
      constructor
      · omega
      · exact hNewBound
  | true =>
      change newDistance ≤ min (oldRemaining - 1) n
      apply Nat.le_min.mpr
      constructor
      · omega
      · exact hNewBound

/-- Conditional weak-to-weak one-edge arithmetic. Under an
actual weak distance progress certificate, a marked decrement
and the weak 2n cap preserve the additive n reserve. It still
requires a SOURCE lemma giving the stated progress inequality. -/
theorem grantDrainR8WeakPhaseBudgetAlgebra
    (n oldDistance newDistance oldRemaining : Nat)
    (hit : Bool)
    (hOldBound : oldDistance ≤ n)
    (hBudget : oldDistance + n ≤ oldRemaining)
    (hProgress :
      if hit then newDistance + 1 ≤ oldDistance
      else newDistance ≤ oldDistance) :
    newDistance + n ≤
      min (oldRemaining - (if hit then 1 else 0)) (2 * n) := by
  cases hit with
  | false =>
      have hMove : newDistance ≤ oldDistance := by
        simpa using hProgress
      change newDistance + n ≤ min oldRemaining (2 * n)
      apply Nat.le_min.mpr
      constructor
      · omega
      · omega
  | true =>
      have hMove : newDistance + 1 ≤ oldDistance := by
        simpa using hProgress
      change newDistance + n ≤ min (oldRemaining - 1) (2 * n)
      apply Nat.le_min.mpr
      constructor
      · omega
      · omega

/-- The normalization is always strictly positive for a surviving
host and at most n; any VALID distance budget implies positive
remaining. This is the final scalar bridge, not a global invariant
preservation theorem. -/
theorem grantDrainR8DistanceBudgetImpliesPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n)
    (g : Fin n)
    (hHost : label.host = some g)
    (hBudget :
      grantDrainStrongProtectedDistance ring s label.host ≤
        label.remaining) :
    0 < label.remaining := by
  have hPositive :=
    grantDrainStrongProtectedDistance_some_pos ring s g
  rw [hHost] at hBudget
  exact Nat.lt_of_lt_of_le hPositive hBudget

end L3

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
An identity-preserving, collision-aware DUMMY host step.
Local transport soundness and retirement are unconditional.
Reverse coverage is reduced to an explicit native one-edge
unclean-DUMMY origin property, still unproved here.
-/

/-- A ready OLD responder overwrites its resident DUMMY when native
E fires: that resident identity must retire. -/
def GrantDrainDummyReadyResponder
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n) : Prop :=
  (s.native (ring.rightNeighbor e)).l = true ∧
  (s.native (ring.rightNeighbor e)).sg = true

/-- A source DUMMY continues only if its OLD responder is an empty
follower, and its NEW host remains unclean. This prevents the
false reassignment of a collided source to a resident DUMMY. -/
def GrantDrainDummyMovingUnclean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) : Prop :=
  (s.native (ring.rightNeighbor e)).l = false ∧
  (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) ∧
  GrantDrainEntranceUncleanDummyAt ring
    (grantDrainStep ring fresh update s e).native
    (ring.rightNeighbor e)

/-- No rebirth of retired identities. Old source moves through an
empty follower only; ready responder overwrites an old resident
identity; elsewhere a still-unclean DUMMY stays at its site. -/
noncomputable def grantDrainDummyEdgeNextHost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n))
    (e id : Fin n) : Option (Fin n) := by
  classical
  exact
    match host id with
    | none => none
    | some b =>
        if b = e then
          if GrantDrainDummyMovingUnclean ring fresh update s e then
            some (ring.rightNeighbor e)
          else none
        else if b = ring.rightNeighbor e ∧
            GrantDrainDummyReadyResponder ring s e then none
        else if GrantDrainEntranceUncleanDummyAt ring
            (grantDrainStep ring fresh update s e).native b then some b
        else none

/-- A retired/cleaned label remains absent on every later step. -/
theorem grantDrainDummyEdgeRetiredAbsorbing
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n)) (e id : Fin n)
    (h : host id = none) :
    grantDrainDummyEdgeNextHost ring fresh update s host e id =
      none := by
  simp [grantDrainDummyEdgeNextHost, h]

/-- Every active NEW host is physically an unclean DUMMY.
This soundness fact has no global sector hypothesis. -/
theorem grantDrainDummyEdgeHostSound
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n)) (e id b : Fin n)
    (hNew :
      grantDrainDummyEdgeNextHost ring fresh update s host e id =
        some b) :
    GrantDrainEntranceUncleanDummyAt ring
      (grantDrainStep ring fresh update s e).native b := by
  classical
  cases hOld : host id with
  | none =>
      have hImpossible : (none : Option (Fin n)) = some b := by
        simpa [grantDrainDummyEdgeNextHost, hOld] using hNew
      cases hImpossible
  | some old =>
      by_cases hx : old = e
      · by_cases hm : GrantDrainDummyMovingUnclean
          ring fresh update s e
        · have hEq : (some (ring.rightNeighbor e) : Option (Fin n)) =
              some b := by
            simpa [grantDrainDummyEdgeNextHost, hOld, hx, hm]
              using hNew
          have hb : ring.rightNeighbor e = b :=
            Option.some.inj hEq
          rw [← hb]
          exact hm.2.2
        · have hImpossible : (none : Option (Fin n)) = some b := by
            simpa [grantDrainDummyEdgeNextHost, hOld, hx, hm]
              using hNew
          cases hImpossible
      · by_cases hr :
          old = ring.rightNeighbor e ∧
            GrantDrainDummyReadyResponder ring s e
        · have hRet :
              grantDrainDummyEdgeNextHost ring fresh update s host e id =
                none := by
            unfold grantDrainDummyEdgeNextHost
            rw [hOld]
            simp only [if_neg hx, if_pos hr]
          have hImpossible : (none : Option (Fin n)) = some b :=
            hRet.symm.trans hNew
          cases hImpossible
        · by_cases hc : GrantDrainEntranceUncleanDummyAt ring
            (grantDrainStep ring fresh update s e).native old
          · have hEq : (some old : Option (Fin n)) = some b := by
              simpa [grantDrainDummyEdgeNextHost,
                hOld, hx, hr, hc] using hNew
            have hb : old = b := Option.some.inj hEq
            rw [← hb]
            exact hc
          · have hImpossible : (none : Option (Fin n)) = some b := by
              simpa [grantDrainDummyEdgeNextHost,
                hOld, hx, hr, hc] using hNew
            cases hImpossible

/-- At a nominated source service, the host retires or moves
one actual clockwise edge, never stuttering at the source. -/
theorem grantDrainDummyEdgeOutgoing
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n)) (e id : Fin n)
    (hOld : host id = some e) :
    grantDrainDummyEdgeNextHost ring fresh update s host e id = none ∨
    grantDrainDummyEdgeNextHost ring fresh update s host e id =
      some (ring.rightNeighbor e) := by
  classical
  by_cases hm : GrantDrainDummyMovingUnclean ring fresh update s e
  · right
    simp [grantDrainDummyEdgeNextHost, hOld, hm]
  · left
    simp [grantDrainDummyEdgeNextHost, hOld, hm]

/-- No post-step unclean DUMMY can occupy the selected initiator. -/
theorem grantDrainDummyNewUncleanNotSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    ¬ GrantDrainEntranceUncleanDummyAt ring
      (grantDrainStep ring fresh update s e).native e := by
  intro hBad
  have hZero := sharedPaperNativeSourceEmpty ring
    (by omega : 2 ≤ n) s e
  have hOne := hBad.1
  change (grantDrainNativeNext ring s e e).b = (1 : Fin 3) at hOne
  rw [hZero] at hOne
  cases hOne

/-- An unclean DUMMY away from both serviced endpoints was an
OLD DUMMY at the same site. Whether it was also OLD unclean is
the remaining, nonlocal sector-geometry obligation. -/
theorem grantDrainDummyAwayOldKind
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e b : Fin n)
    (hx : b ≠ e) (hy : b ≠ ring.rightNeighbor e)
    (hBad : GrantDrainEntranceUncleanDummyAt ring
      (grantDrainStep ring fresh update s e).native b) :
    (s.native b).b = (1 : Fin 3) := by
  have hFrame := sharedPaperNativeAwayFrame ring s e b hx hy
  have hOne := hBad.1
  change (grantDrainNativeNext ring s e b).b = (1 : Fin 3) at hOne
  rw [hFrame] at hOne
  exact hOne

/-- Exhaustive raw responder-bullet ORIGIN alternatives.
These do NOT alone establish unclean-identity ancestry. -/
theorem grantDrainDummyResponderRawOrigins
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hBad : GrantDrainEntranceUncleanDummyAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)) :
    HasBullet s.native e ∨
    HasBullet s.native (ring.rightNeighbor e) ∨
    ((s.native e).l = true ∧ (s.native e).sg = true) ∨
    ((s.native (ring.rightNeighbor e)).l = true ∧
      (s.native (ring.rightNeighbor e)).sg = true) := by
  have hNew : HasBullet (grantDrainNativeNext ring s e)
      (ring.rightNeighbor e) := by
    intro hEmpty
    have hOne := hBad.1
    change (grantDrainNativeNext ring s e
      (ring.rightNeighbor e)).b = (1 : Fin 3) at hOne
    rw [hEmpty] at hOne
    cases hOne
  exact sharedPaperResponderBulletOrigins
    ring (by omega : 2 ≤ n) s e hNew

/-- FIRST MISSING native geometry theorem, stated as a Prop.
The next unclean DUMMY is either an OLD unclean stationary identity
not overwritten by ready-responder E, or the OLD unclean source
identity moving into an OLD empty follower. No theorem asserting
this property is given in this block. -/
def GrantDrainDummyEdgeOrigin
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) : Prop :=
  ∀ b : Fin n,
    GrantDrainEntranceUncleanDummyAt ring
      (grantDrainStep ring fresh update s e).native b →
    (b ≠ e ∧
      ¬ (b = ring.rightNeighbor e ∧
        GrantDrainDummyReadyResponder ring s e) ∧
      GrantDrainEntranceUncleanDummyAt ring s.native b) ∨
    (b = ring.rightNeighbor e ∧
      (s.native (ring.rightNeighbor e)).l = false ∧
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) ∧
      GrantDrainEntranceUncleanDummyAt ring s.native e)

/-- Strong host invariant: each hosted label is really unclean,
and every physically unclean bullet has a host. -/
def GrantDrainDummyHostFaithful
    {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (host : Fin n → Option (Fin n)) : Prop :=
  (∀ id b : Fin n, host id = some b →
    GrantDrainEntranceUncleanDummyAt ring N b) ∧
  GrantDrainDummyHostCover ring N host

private theorem grantDrainDummyBadHasBullet
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (b : Fin n)
    (hBad : GrantDrainEntranceUncleanDummyAt ring N b) :
    HasBullet N b := by
  intro hZero
  have hContra : (1 : Fin 3) = (0 : Fin 3) :=
    hBad.1.symm.trans hZero
  exact (by decide : (1 : Fin 3) ≠ (0 : Fin 3)) hContra

/-- Both soundness and reverse coverage hold for the actual initial
nonclean-DUMMY identity family at every PPlus/NoBadLive cut. -/
theorem grantDrainDummyInitialFaithful
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) :
    GrantDrainDummyHostFaithful ring s.native
      (fun id => (grantDrainEntranceDummyInitial ring s id).host) := by
  constructor
  · intro id b hHost
    by_cases hBad : GrantDrainEntranceUncleanDummyAt ring s.native id
    · have hInit :
          (grantDrainEntranceDummyInitial ring s id).host =
            some id :=
        (grantDrainEntranceDummyInitialHostIff ring s id).mpr hBad
      have hEq : id = b :=
        Option.some.inj (hInit.symm.trans hHost)
      rw [← hEq]
      exact hBad
    · have hNone :
          (grantDrainEntranceDummyInitial ring s id).host =
            none := by
        simp [grantDrainEntranceDummyInitial, hBad]
      change (grantDrainEntranceDummyInitial ring s id).host =
        some b at hHost
      rw [hNone] at hHost
      cases hHost
  · exact grantDrainDummyInitialHostCover ring s hPB hNoBad

/-- CONDITIONAL full one-edge soundness and reverse coverage.
No ghost fabrication: successor host is the above literal update.
To make this unconditional, discharge GrantDrainDummyEdgeOrigin
for every PPlus/NoBadLive source edge. -/
theorem grantDrainDummyEdgeFaithfulOfOrigin
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n)) (e : Fin n)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hFaithful : GrantDrainDummyHostFaithful ring s.native host)
    (hOrigin : GrantDrainDummyEdgeOrigin ring fresh update s e) :
    GrantDrainDummyHostFaithful ring
      (grantDrainStep ring fresh update s e).native
      (grantDrainDummyEdgeNextHost ring fresh update s host e) := by
  constructor
  · intro id b hNew
    exact grantDrainDummyEdgeHostSound
      ring fresh update s host e id b hNew
  · intro b hBullet hUnclean
    have hPBNext : PPlus ring
        (grantDrainStep ring fresh update s e).native :=
      grantDrainStep_preserves_PPlus
        (by omega : 3 ≤ n) ring fresh update s e hPB
    have hNoBadNext : GrantDrainEntranceNoBadLive ring
        (grantDrainStep ring fresh update s e) :=
      grantDrainEntrancePhysicalNoBadNext
        ring hn fresh update s e hPB hNoBad
    have hBad : GrantDrainEntranceUncleanDummyAt ring
        (grantDrainStep ring fresh update s e).native b :=
      ⟨grantDrainDummyUncleanIsDummy ring
        (grantDrainStep ring fresh update s e).native
        hPBNext hNoBadNext b hBullet hUnclean, hUnclean⟩
    rcases hOrigin b hBad with
      ⟨hAway, hNotReady, hOld⟩ |
      ⟨hResponder, hFollower, hEmpty, hOld⟩
    · obtain ⟨id, hHost⟩ :=
        hFaithful.2 b
          (grantDrainDummyBadHasBullet ring s.native b hOld)
          hOld.2
      refine ⟨id, ?_⟩
      simp [grantDrainDummyEdgeNextHost,
        hHost, hAway, hNotReady, hBad]
    · subst b
      obtain ⟨id, hHost⟩ :=
        hFaithful.2 e
          (grantDrainDummyBadHasBullet ring s.native e hOld)
          hOld.2
      have hMove : GrantDrainDummyMovingUnclean
          ring fresh update s e :=
        ⟨hFollower, hEmpty, hBad⟩
      refine ⟨id, ?_⟩
      simp [grantDrainDummyEdgeNextHost, hHost, hMove]

/-- Same canonical physical step and the deterministic immutable
host update, on the SAME observed scheduler word. -/
noncomputable def grantDrainDummyEdgeWordStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch × (Fin n → Option (Fin n)))
    (e : Fin n) :
    GrantDrainState n Scratch × (Fin n → Option (Fin n)) :=
  (grantDrainStep ring fresh update z.1 e,
    grantDrainDummyEdgeNextHost ring fresh update z.1 z.2 e)

/-- The ghost extension projects exactly to the physical
canonical word, even with hostile request and scratch choices. -/
theorem grantDrainDummyEdgeWordPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (z : GrantDrainState n Scratch × (Fin n → Option (Fin n))),
      (word.foldl (grantDrainDummyEdgeWordStep
        ring fresh update) z).1 =
      word.foldl (grantDrainStep ring fresh update) z.1 := by
  intro word
  induction word with
  | nil =>
      intro z
      rfl
  | cons e rest ih =>
      intro z
      change
        (rest.foldl (grantDrainDummyEdgeWordStep
          ring fresh update)
          (grantDrainDummyEdgeWordStep ring fresh update z e)).1 =
        rest.foldl (grantDrainStep ring fresh update)
          (grantDrainStep ring fresh update z.1 e)
      exact ih (grantDrainDummyEdgeWordStep ring fresh update z e)

/-- Retired or cleaned identities remain retired along every
physical scheduler word. The proof uses the actual pair fold. -/
theorem grantDrainDummyEdgeWordRetired
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (z : GrantDrainState n Scratch × (Fin n → Option (Fin n)))
      (id : Fin n), z.2 id = none →
      (word.foldl (grantDrainDummyEdgeWordStep
        ring fresh update) z).2 id = none := by
  intro word
  induction word with
  | nil =>
      intro z id h
      exact h
  | cons e rest ih =>
      intro z id h
      change
        (rest.foldl (grantDrainDummyEdgeWordStep
          ring fresh update)
          (grantDrainDummyEdgeWordStep ring fresh update z e)).2 id =
        none
      exact ih (grantDrainDummyEdgeWordStep ring fresh update z e) id
        (grantDrainDummyEdgeRetiredAbsorbing ring fresh update
          z.1 z.2 e id h)

/-- Wordwise faithful coverage follows once one-edge native origins
are proved on the closed PPlus/NoBadLive class. This is a logical
composition, NOT an unconditional proof of those origins. -/
theorem grantDrainDummyEdgeWordFaithfulOfOrigins
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hOrigins : ∀ (s : GrantDrainState n Scratch) (e : Fin n),
      PPlus ring s.native →
      GrantDrainEntranceNoBadLive ring s →
      GrantDrainDummyEdgeOrigin ring fresh update s e) :
    ∀ (word : List (Fin n))
      (z : GrantDrainState n Scratch × (Fin n → Option (Fin n))),
      PPlus ring z.1.native →
      GrantDrainEntranceNoBadLive ring z.1 →
      GrantDrainDummyHostFaithful ring z.1.native z.2 →
      GrantDrainDummyHostFaithful ring
        (word.foldl (grantDrainDummyEdgeWordStep
          ring fresh update) z).1.native
        (word.foldl (grantDrainDummyEdgeWordStep
          ring fresh update) z).2 := by
  intro word
  induction word with
  | nil =>
      intro z _ _ hFaithful
      exact hFaithful
  | cons e rest ih =>
      intro z hPB hNoBad hFaithful
      change GrantDrainDummyHostFaithful ring
        (rest.foldl (grantDrainDummyEdgeWordStep ring fresh update)
          (grantDrainDummyEdgeWordStep ring fresh update z e)).1.native
        (rest.foldl (grantDrainDummyEdgeWordStep ring fresh update)
          (grantDrainDummyEdgeWordStep ring fresh update z e)).2
      have hPBNext : PPlus ring
          (grantDrainStep ring fresh update z.1 e).native :=
        grantDrainStep_preserves_PPlus
          (by omega : 3 ≤ n) ring fresh update z.1 e hPB
      have hNoBadNext : GrantDrainEntranceNoBadLive ring
          (grantDrainStep ring fresh update z.1 e) :=
        grantDrainEntrancePhysicalNoBadNext
          ring hn fresh update z.1 e hPB hNoBad
      have hFaithfulNext :=
        grantDrainDummyEdgeFaithfulOfOrigin
          ring hn fresh update z.1 z.2 e
          hPB hNoBad hFaithful (hOrigins z.1 e hPB hNoBad)
      exact ih (grantDrainDummyEdgeWordStep ring fresh update z e)
        hPBNext hNoBadNext hFaithfulNext

end L3.GrantDrainEntrance
namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! An explicit clean-to-unclean regression OUTSIDE NoBadLive.
It shows exactly why the hypothesis cannot be dropped. -/

private def grantDrainDummyFatalFiveRing : DirectedRing 5 :=
  ⟨by decide⟩

private def grantDrainDummyFatalFiveNative (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := false, b := (2 : Fin 3), sh := false, sg := false }
  else if i.val == 1 then
    { l := true, b := (1 : Fin 3), sh := false, sg := false }
  else if i.val == 2 then
    { l := true, b := (2 : Fin 3), sh := true, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

private def grantDrainDummyFatalFiveState : GrantDrainState 5 Unit :=
  { native := grantDrainDummyFatalFiveNative
    request := fun _ => false
    grant := fun _ => false
    scratch := ()
    history := [] }

/-- A clean leader-hosted DUMMY at site 1 becomes unclean when the
non-leftmost LIVE at site 0 kills leader 1 on edge 0 -> 1.
The OLD state is PPlus but violates NoBadLive. -/
theorem grantDrainDummyCleanFailsWithoutNoBad :
    PPlus grantDrainDummyFatalFiveRing
      grantDrainDummyFatalFiveState.native ∧
    GrantDrainEntranceBulletCleanAt grantDrainDummyFatalFiveRing
      grantDrainDummyFatalFiveState.native (1 : Fin 5) ∧
    ((grantDrainStep grantDrainDummyFatalFiveRing
        (fun _ _ => false) (fun _ _ => ())
        grantDrainDummyFatalFiveState (0 : Fin 5)).native
        (1 : Fin 5)).b = (1 : Fin 3) ∧
    ¬ GrantDrainEntranceBulletCleanAt grantDrainDummyFatalFiveRing
      (grantDrainStep grantDrainDummyFatalFiveRing
        (fun _ _ => false) (fun _ _ => ())
        grantDrainDummyFatalFiveState (0 : Fin 5)).native
      (1 : Fin 5) ∧
    ¬ GrantDrainEntranceNoBadLive grantDrainDummyFatalFiveRing
      grantDrainDummyFatalFiveState := by
  have hProtected :
      PPlus grantDrainDummyFatalFiveRing
        grantDrainDummyFatalFiveState.native := by
    unfold grantDrainDummyFatalFiveRing
      grantDrainDummyFatalFiveState
      grantDrainDummyFatalFiveNative
    decide +kernel
  have hClean :
      GrantDrainEntranceBulletCleanAt grantDrainDummyFatalFiveRing
        grantDrainDummyFatalFiveState.native (1 : Fin 5) := by
    unfold GrantDrainEntranceBulletCleanAt
      grantDrainDummyFatalFiveRing
      grantDrainDummyFatalFiveState
      grantDrainDummyFatalFiveNative
    decide +kernel
  have hSurvives :
      ((grantDrainStep grantDrainDummyFatalFiveRing
          (fun _ _ => false) (fun _ _ => ())
          grantDrainDummyFatalFiveState (0 : Fin 5)).native
          (1 : Fin 5)).b = (1 : Fin 3) := by
    unfold grantDrainDummyFatalFiveRing
      grantDrainDummyFatalFiveState
      grantDrainDummyFatalFiveNative
      grantDrainStep grantDrainNativeNext grantDrainSelect
      nativeE certLiteralEPair certFinThree
    decide +kernel
  have hNotClean :
      ¬ GrantDrainEntranceBulletCleanAt grantDrainDummyFatalFiveRing
        (grantDrainStep grantDrainDummyFatalFiveRing
          (fun _ _ => false) (fun _ _ => ())
          grantDrainDummyFatalFiveState (0 : Fin 5)).native
        (1 : Fin 5) := by
    unfold GrantDrainEntranceBulletCleanAt
      grantDrainDummyFatalFiveRing
      grantDrainDummyFatalFiveState
      grantDrainDummyFatalFiveNative
      grantDrainStep grantDrainNativeNext grantDrainSelect
      nativeE certLiteralEPair certFinThree
    decide +kernel
  have hOldBad :
      SharedPaperNonleftmostLiveExact grantDrainDummyFatalFiveRing
        grantDrainDummyFatalFiveState.native (0 : Fin 5) := by
    unfold SharedPaperNonleftmostLiveExact
      grantDrainDummyFatalFiveRing
      grantDrainDummyFatalFiveState
      grantDrainDummyFatalFiveNative
    decide +kernel
  have hNoBadFails :
      ¬ GrantDrainEntranceNoBadLive grantDrainDummyFatalFiveRing
        grantDrainDummyFatalFiveState := by
    intro hNoBad
    exact hNoBad (0 : Fin 5) hOldBad
  exact ⟨hProtected, hClean, hSurvives, hNotClean, hNoBadFails⟩

end L3.GrantDrainEntrance

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
The full weak/terminal physical one-edge closure is NOT claimed here.
The native-leader and HOLD cases are distinct from physical strong
locks; otherwise the genuine n=5 held-seed refutes the invariant.
-/

/-- LockBudget: the requested physical lock and numeric budget,
with the two terminal degeneracies handled explicitly. -/
def LockBudget {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n) : Prop :=
  ∀ g : Fin n, label.host = some g →
    s.grant g = true ∧
      match label.mark with
      | .unmarked => True
      | .weak =>
          s.request g = false ∧
          (s.native g).l = false ∧
          grantDrainLedgerWeakLock ring s g = true ∧
          grantDrainStrongProtectedDistance ring s (some g) + n ≤
            label.remaining
      | .strong =>
          s.request g = false ∧
          (s.native g).l = false ∧
          grantDrainLedgerStrongLock ring s g = true ∧
          grantDrainStrongProtectedDistance ring s (some g) ≤
            label.remaining
      | .terminal =>
          if s.request g then
            0 < label.remaining ∧
              ∀ e : Fin n,
                grantDrainLedgerNominatedHit ring s e label.host = true →
                (grantDrainLedgerStep ring fresh update s e label).host =
                  none
          else if (s.native g).l then
            n ≤ label.remaining
          else
            grantDrainLedgerStrongLock ring s g = true ∧
              grantDrainStrongProtectedDistance ring s (some g) ≤
                label.remaining

/-- The held terminal case uses the exact source row:
the nominated outgoing hit retires that label. -/
theorem grantDrainLockBudgetHeldRetiresOnNomination
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hHost : label.host = some g)
    (hRequest : s.request g = true)
    (hGrant : s.grant g = true) :
    ∀ e : Fin n,
      grantDrainLedgerNominatedHit ring s e label.host = true →
      (grantDrainLedgerStep ring fresh update s e label).host = none := by
  intro e hHit
  have he : e = g := by
    simpa [grantDrainLedgerNominatedHit, hHost, hRequest] using hHit
  subst e
  exact grantDrainHeldOutgoingRetires
    ring fresh update s g label hHost hRequest hGrant

/-- TARGET (1), FIRST. Initialization requires no PPlus hypothesis:
the only live marked cases are exactly the observed terminal,
strong, and weak branches. All three initial quotas cover their
appropriate physical obligations, for every n >= 5. -/
theorem grantDrainLockBudgetInitial
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (i : Fin n) :
    LockBudget ring fresh update s
      (grantDrainLedgerInitial ring s i) := by
  intro g hHost
  cases hg : s.grant i with
  | false =>
      simp [grantDrainLedgerInitial, hg] at hHost
  | true =>
      have hi : i = g := by
        simpa [grantDrainLedgerInitial, hg] using hHost
      subst g
      refine ⟨hg, ?_⟩
      have hDist :=
        grantDrainStrongProtectedDistance_le_n ring s (some i)
      cases hr : s.request i with
      | true =>
          have hObserved :
              grantDrainLedgerObservedMark ring s (some i) =
                .terminal := by
            simp [grantDrainLedgerObservedMark, hg, hr]
          have hMark :
              (grantDrainLedgerInitial ring s i).mark =
                .terminal := by
            simpa [grantDrainLedgerInitial, hg] using hObserved
          have hRem :
              (grantDrainLedgerInitial ring s i).remaining = 1 := by
            have hOne : min 1 n = 1 :=
              Nat.min_eq_left (by omega : 1 ≤ n)
            simp [grantDrainLedgerInitial, hg, hObserved,
              grantDrainLedgerQuotaCap, grantDrainLedgerHeld, hr, hOne]
          have hRetire :=
            grantDrainLockBudgetHeldRetiresOnNomination
              ring fresh update s
              (grantDrainLedgerInitial ring s i) i
              (by simp [grantDrainLedgerInitial, hg]) hr hg
          rw [hMark]
          simp only [hr, ↓reduceIte]
          exact ⟨by rw [hRem]; omega, hRetire⟩
      | false =>
          cases hl : (s.native i).l with
          | true =>
              have hObserved :
                  grantDrainLedgerObservedMark ring s (some i) =
                    .terminal := by
                simp [grantDrainLedgerObservedMark, hg, hr, hl]
              have hMark :
                  (grantDrainLedgerInitial ring s i).mark =
                    .terminal := by
                simpa [grantDrainLedgerInitial, hg] using hObserved
              have hRem :
                  (grantDrainLedgerInitial ring s i).remaining = n := by
                simp [grantDrainLedgerInitial, hg, hObserved,
                  grantDrainLedgerQuotaCap, grantDrainLedgerHeld, hr]
              rw [hMark]
              simp [hr, hl, hRem]
          | false =>
              cases hs : grantDrainLedgerStrongLock ring s i with
              | true =>
                  have hObserved :
                      grantDrainLedgerObservedMark ring s (some i) =
                        .strong := by
                    simp [grantDrainLedgerObservedMark,
                      hg, hr, hl, hs]
                  have hMark :
                      (grantDrainLedgerInitial ring s i).mark =
                        .strong := by
                    simpa [grantDrainLedgerInitial, hg] using hObserved
                  have hRem :
                      (grantDrainLedgerInitial ring s i).remaining = n := by
                    simp [grantDrainLedgerInitial, hg, hObserved,
                      grantDrainLedgerQuotaCap, grantDrainLedgerHeld, hr]
                  rw [hMark]
                  refine ⟨rfl, rfl, rfl, ?_⟩
                  rw [hRem]
                  exact hDist
              | false =>
                  cases hw : grantDrainLedgerWeakLock ring s i with
                  | true =>
                      have hObserved :
                          grantDrainLedgerObservedMark ring s (some i) =
                            .weak := by
                        simp [grantDrainLedgerObservedMark,
                          hg, hr, hl, hs, hw]
                      have hMark :
                          (grantDrainLedgerInitial ring s i).mark =
                            .weak := by
                        simpa [grantDrainLedgerInitial, hg] using hObserved
                      have hRem :
                          (grantDrainLedgerInitial ring s i).remaining =
                            2 * n := by
                        simp [grantDrainLedgerInitial, hg, hObserved,
                          grantDrainLedgerQuotaCap, grantDrainLedgerHeld, hr]
                      rw [hMark]
                      refine ⟨rfl, rfl, rfl, ?_⟩
                      rw [hRem]
                      omega
                  | false =>
                      have hObserved :
                          grantDrainLedgerObservedMark ring s (some i) =
                            .unmarked := by
                        simp [grantDrainLedgerObservedMark,
                          hg, hr, hl, hs, hw]
                      have hMark :
                          (grantDrainLedgerInitial ring s i).mark =
                            .unmarked := by
                        simpa [grantDrainLedgerInitial, hg] using hObserved
                      rw [hMark]
                      trivial

/-- Requested PPlus-initialized form of (1). -/
theorem grantDrainLockBudgetInitialPPlus
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hP : PPlus ring s.native) (i : Fin n) :
    LockBudget ring fresh update s
      (grantDrainLedgerInitial ring s i) := by
  exact grantDrainLockBudgetInitial ring hn fresh update s i

/-- (2), the actual strong-to-strong canonical step. The
R8b arc/physical closure proves the post-lock
and the source-distance drift, including genuine FIRE and merge. -/
theorem grantDrainLockBudgetStrongToStrong
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hStrong : label.mark = .strong)
    (hNextLive :
      (grantDrainLedgerStep ring fresh update s e label).host ≠ none)
    (hNextStrong :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .strong) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨hGrant, hCase⟩ := hInv g hHost
  rw [hStrong] at hCase
  obtain ⟨hRequest, hFollower, hLock, hBudgetAtG⟩ := hCase
  have hBudget :
      grantDrainStrongProtectedDistance ring s label.host ≤
        label.remaining := by
    rw [hHost]
    exact hBudgetAtG
  have hPhysical : GrantDrainStrongPhysical ring s label :=
    ⟨g, hHost, hStrong, hGrant, hRequest, hFollower, hLock⟩
  have hGeometry :
      GrantDrainStrongCorridorGeometry ring fresh update :=
    grantDrainStrongCorridorGeometry_of_arc_coverage
      ring fresh update
      (grantDrainMarksStrongArcCoverageOfThree
        (by omega : 3 ≤ n) ring fresh update)
      (grantDrainMarksStrongPhysicalClosureOfThree
        (by omega : 3 ≤ n) ring fresh update)
  have hNextPhysical :=
    (hGeometry s e label hP hPhysical hNextLive hNextStrong).1
  have hNextBudget :=
    grantDrainStrongStepBudgetOfGeometry
      ring fresh update hGeometry s e label
      hP hPhysical hBudget hNextLive hNextStrong
  intro g' hNewHost
  obtain ⟨j, hjHost, hjMark, hjGrant, hjReq,
    hjFollower, hjLock⟩ := hNextPhysical
  have heq : j = g' :=
    Option.some.inj (hjHost.symm.trans hNewHost)
  subst g'
  refine ⟨hjGrant, ?_⟩
  rw [hNextStrong]
  have hLocalBudget :
      grantDrainStrongProtectedDistance ring
        (grantDrainStep ring fresh update s e) (some j) ≤
        (grantDrainLedgerStep ring fresh update s e label).remaining := by
    rw [hjHost] at hNextBudget
    exact hNextBudget
  exact ⟨hjReq, hjFollower, hjLock, hLocalBudget⟩

/-- The numeric weak-to-strong cap change is also sufficient on
the canonical step, PROVIDED its post StrongPhysical certificate.
This isolates the missing weak-source/birth geometry from the
already proved arithmetic. -/
theorem grantDrainLockBudgetWeakToStrongOfPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextPhysical :
      GrantDrainStrongPhysical ring
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e label)) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨_, hCase⟩ := hInv g hHost
  rw [hWeak] at hCase
  obtain ⟨_, _, _, hWeakBudgetAtG⟩ := hCase
  have hWeakBudget :
      grantDrainStrongProtectedDistance ring s label.host + n ≤
        label.remaining := by
    rw [hHost]
    exact hWeakBudgetAtG
  have hOldPositive :
      0 < grantDrainStrongProtectedDistance ring s label.host := by
    rw [hHost]
    exact grantDrainStrongProtectedDistance_some_pos ring s g
  obtain ⟨j, hjHost, hjMark, hjGrant, hjReq,
    hjFollower, hjLock⟩ := hNextPhysical
  have hHostRaw :
      grantDrainLedgerHost ring fresh s e label.host = some j :=
    hjHost
  have hMarkRaw :
      grantDrainLedgerMarkNext ring fresh update s e label =
        .strong := hjMark
  have hFormula :
      (grantDrainLedgerStep ring fresh update s e label).remaining =
        min
          (label.remaining -
            (if grantDrainLedgerNominatedHit ring s e label.host
              then 1 else 0)) n := by
    change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring fresh s e label.host)
      (grantDrainLedgerMarkNext ring fresh update s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e label.host)) = _
    rw [hHostRaw, hMarkRaw]
    simp [grantDrainLedgerRemainingNext, hWeak,
      grantDrainLedgerQuotaCap]
  have hCap :=
    grantDrainStrongProtectedDistance_le_n ring
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label).host
  have hNewBudget :
      grantDrainStrongProtectedDistance ring
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e label).host ≤
        (grantDrainLedgerStep ring fresh update s e label).remaining := by
    rw [hFormula]
    exact grantDrainR8WeakToStrongBudgetAlgebra
      n
      (grantDrainStrongProtectedDistance ring s label.host)
      (grantDrainStrongProtectedDistance ring
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e label).host)
      label.remaining
      (grantDrainLedgerNominatedHit ring s e label.host)
      hOldPositive hWeakBudget hCap
  intro g' hNewHost
  have heq : j = g' :=
    Option.some.inj (hjHost.symm.trans hNewHost)
  subst g'
  refine ⟨hjGrant, ?_⟩
  rw [hjMark]
  have hLocalBudget :
      grantDrainStrongProtectedDistance ring
        (grantDrainStep ring fresh update s e) (some j) ≤
        (grantDrainLedgerStep ring fresh update s e label).remaining := by
    rw [hjHost] at hNewBudget
    exact hNewBudget
  exact ⟨hjReq, hjFollower, hjLock, hLocalBudget⟩

/-- Any surviving MARKED label satisfying the strengthened
invariant has positive quota. Native-leader terminal labels use
n>=5, held labels use the one-hit clause. -/
theorem grantDrainLockBudgetAlivePositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hMarked : label.mark ≠ .unmarked) :
    0 < label.remaining := by
  obtain ⟨_, hCase⟩ := hInv g hHost
  have hDistance :
      0 < grantDrainStrongProtectedDistance ring s (some g) :=
    grantDrainStrongProtectedDistance_some_pos ring s g
  cases hm : label.mark with
  | unmarked =>
      exact False.elim (hMarked hm)
  | weak =>
      rw [hm] at hCase
      obtain ⟨_, _, _, hBudget⟩ := hCase
      omega
  | strong =>
      rw [hm] at hCase
      obtain ⟨_, _, _, hBudget⟩ := hCase
      exact Nat.lt_of_lt_of_le hDistance hBudget
  | terminal =>
      rw [hm] at hCase
      cases hr : s.request g with
      | true =>
          simp [hr] at hCase
          exact hCase.1
      | false =>
          cases hl : (s.native g).l with
          | true =>
              simp [hr, hl] at hCase
              omega
          | false =>
              simp [hr, hl] at hCase
              exact Nat.lt_of_lt_of_le hDistance hCase.2

/-- Conditional all-word canonical preservation. This DOES NOT
supply the open weak/terminal one-edge row premise hStep. -/
theorem grantDrainLockBudgetRunOfStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hStep : ∀ (s : GrantDrainState n Scratch)
      (e : Fin n) (label : GrantDrainLedgerLabel n),
      PPlus ring s.native →
      LockBudget ring fresh update s label →
      LockBudget ring fresh update
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e label)) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainLedgerLabel n),
      PPlus ring s.native →
      LockBudget ring fresh update s label →
      LockBudget ring fresh update
        (grantDrainLedgerRun ring fresh update s label word).1
        (grantDrainLedgerRun ring fresh update s label word).2 := by
  intro word
  induction word with
  | nil =>
      intro s label hP hInv
      exact hInv
  | cons e es ih =>
      intro s label hP hInv
      change LockBudget ring fresh update
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label) es).1
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label) es).2
      exact ih (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e label)
        (grantDrainStep_preserves_PPlus
          (by omega : 3 ≤ n) ring fresh update s e hP)
        (hStep s e label hP hInv)

/-- (1) + the still-open universal one-edge (2) implies exactly
GrantDrainLedgerNoExhaustion. No new axiom is used. -/
theorem grantDrainNoExhaustionOfLockBudgetStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s0 : GrantDrainState n Scratch)
    (hStep : ∀ (s : GrantDrainState n Scratch)
      (e : Fin n) (label : GrantDrainLedgerLabel n),
      PPlus ring s.native →
      LockBudget ring fresh update s label →
      LockBudget ring fresh update
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e label)) :
    GrantDrainLedgerNoExhaustion ring fresh update s0 := by
  intro hP i word hGrant hLive hMarked
  have hInitial :=
    grantDrainLockBudgetInitial ring hn fresh update s0 i
  have hFinal :=
    grantDrainLockBudgetRunOfStep
      ring hn fresh update hStep word s0
      (grantDrainLedgerInitial ring s0 i) hP hInitial
  cases hh :
      (grantDrainLedgerRun ring fresh update s0
        (grantDrainLedgerInitial ring s0 i) word).2.host with
  | none =>
      exact False.elim (hLive hh)
  | some g =>
      exact grantDrainLockBudgetAlivePositive
        ring hn fresh update
        (grantDrainLedgerRun ring fresh update s0
          (grantDrainLedgerInitial ring s0 i) word).1
        (grantDrainLedgerRun ring fresh update s0
          (grantDrainLedgerInitial ring s0 i) word).2
        g hFinal hh hMarked

end L3

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Canonical DUMMY origin, new unconditional row lemmas
and precise remaining clean-sector geometry obligations.

The generic GrantDrainDummyEdgeOrigin is not asserted here without
the old-clean -> new-clean transport in all affected sectors.
-/

/-- The nearest leader of a site carrying a leader bit is itself,
including the clockwise wraparound case. -/
private theorem grantDrainDummySelfLeaderSector
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (b : Fin n)
    (hLeader : (N b).l = true) :
    leaderSector ring N b b := by
  have hOffset : PPL.cyclicOffset ring b b = 0 := by
    change (b.val + n - b.val) % n = 0
    have hSame : b.val + n - b.val = n := by omega
    rw [hSame, Nat.mod_self]
  constructor
  · exact hLeader
  · change PPL.scanDistance
      (fun k => PPL.shiftLeft ring b k)
      (fun i => (N i).l) n 0 =
        some (PPL.cyclicOffset ring b b)
    rw [hOffset]
    cases n with
    | zero =>
        exact b.elim0
    | succ m =>
        change
          (if (N (PPL.shiftLeft ring b 0)).l = true
            then some 0
            else PPL.scanDistance
              (fun k => PPL.shiftLeft ring b k)
              (fun i => (N i).l) m 1) = some 0
        have hShift : PPL.shiftLeft ring b 0 = b := by
          apply Fin.ext
          change (b.val + Nat.succ m - 0 % Nat.succ m) %
            Nat.succ m = b.val
          simp only [Nat.zero_mod, Nat.sub_zero,
            Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]
        rw [hShift, hLeader]
        rfl

/-- A DUMMY at a signal-zero leader is clean with no extra
assumption about other sites, grants or requests. -/
theorem grantDrainDummyLeaderZeroClean
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (b : Fin n)
    (hLeader : (N b).l = true)
    (hDummy : (N b).b = (1 : Fin 3))
    (hZero : (N b).sg = false) :
    GrantDrainEntranceBulletCleanAt ring N b := by
  have hOffset : PPL.cyclicOffset ring b b = 0 := by
    change (b.val + n - b.val) % n = 0
    have hSame : b.val + n - b.val = n := by omega
    rw [hSame, Nat.mod_self]
  have hBullet : HasBullet N b := by
    intro hEmpty
    have hImpossible : (1 : Fin 3) = (0 : Fin 3) :=
      hDummy.symm.trans hEmpty
    exact (by decide : (1 : Fin 3) ≠ (0 : Fin 3)) hImpossible
  refine ⟨hBullet, b,
    grantDrainDummySelfLeaderSector ring N b hLeader, ?_, ?_⟩
  · intro a _ _
    rw [hOffset]
    exact Nat.zero_le _
  · intro k hk
    rw [hOffset] at hk
    have hK : k.val = 0 := by omega
    rw [hK, grantDrainEntranceR8eShiftZero ring b]
    exact hZero

/-- Every OLD responder leader has signal zero after native E
and any permitted FIRE overlay, independently of readiness and
whether that leader was subsequently killed. -/
theorem grantDrainDummyOldLeaderResponderSignalZero
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true) :
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).sg = false := by
  have hE :=
    (grantDrainEntranceNativeELeaderBulletAfter
      ring (by omega : 2 ≤ n) s.native e hLeader).2
  rcases grantDrainEntranceNativeOwnerCases
      ring fresh update s e with hNative | hSource | hResponder
  · rw [hNative]
    exact hE
  · rw [hSource]
    exact grantDrainEntranceCanonicalBirthPreservesZero
      (nativeE ring s.native e) e (ring.rightNeighbor e) hE
  · rw [hResponder]
    exact grantDrainEntranceCanonicalBirthPreservesZero
      (nativeE ring s.native e)
      (ring.rightNeighbor e) (ring.rightNeighbor e) hE

/-- The ready-responder DUMMY row is resolved when the OLD leader
survives: a DUMMY at that leader is clean. The remaining ready row
is precisely a real death of that leader. -/
theorem grantDrainDummyReadySurvivingLeaderClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hNextLeader :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = true)
    (hNextDummy :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b = (1 : Fin 3)) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  exact grantDrainDummyLeaderZeroClean ring
    (grantDrainStep ring fresh update s e).native
    (ring.rightNeighbor e) hNextLeader hNextDummy
    (grantDrainDummyOldLeaderResponderSignalZero
      ring hn fresh update s e hLeader)

/-- Literal E-row classification: a NEW DUMMY at the responder
comes from the OLD ready responder, a resident OLD DUMMY, or
an OLD source DUMMY entering an OLD empty follower.
This is an all-Boolean, all-bullet-kind two-agent fact. -/
theorem grantDrainDummyLiteralResponderKind
    (x y : CertNative)
    (hNew : (certLiteralEPair x y).2.b = (1 : Fin 3)) :
    (y.l = true ∧ y.sg = true) ∨
    y.b = (1 : Fin 3) ∨
    (x.b = (1 : Fin 3) ∧ y.l = false ∧
      y.b = (0 : Fin 3)) := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with rfl | rfl | rfl <;>
    rcases grantDrainEntranceLocalFinThreeCases yb with rfl | rfl | rfl <;>
    cases xl <;> cases yl <;> cases xh <;> cases yh <;>
    cases xs <;> cases ys <;>
    simp [certLiteralEPair, certFinThree] at *

/-- A canonical birth cannot create a DUMMY. Consequently the
same three-way literal E origin holds for the actual E+FIRE step,
with arbitrary OLD requests, grants, fresh and scratch. -/
theorem grantDrainDummyCanonicalResponderKind
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hNew :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b = (1 : Fin 3)) :
    GrantDrainDummyReadyResponder ring s e ∨
    (s.native (ring.rightNeighbor e)).b = (1 : Fin 3) ∨
    ((s.native e).b = (1 : Fin 3) ∧
      (s.native (ring.rightNeighbor e)).l = false ∧
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3)) := by
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hE :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) := by
    change (grantDrainNativeNext ring s e
      (ring.rightNeighbor e)).b = (1 : Fin 3) at hNew
    cases hf : grantDrainSelect ring s e with
    | none =>
        simpa [grantDrainNativeNext, hf] using hNew
    | leftLocal =>
        simpa [grantDrainNativeNext, hf, canonicalBirth,
          hDistinct] using hNew
    | rightLocal =>
        have hImpossible : (0 : Fin 3) = (1 : Fin 3) := by
          simpa [grantDrainNativeNext, hf, canonicalBirth,
            firedNative] using hNew
        cases hImpossible
    | cross =>
        simpa [grantDrainNativeNext, hf, canonicalBirth,
          hDistinct] using hNew
  have hPair :
      (certLiteralEPair
        (s.native e) (s.native (ring.rightNeighbor e))).2.b =
        (1 : Fin 3) := by
    simpa [nativeE, hDistinct] using hE
  exact grantDrainDummyLiteralResponderKind
    (s.native e) (s.native (ring.rightNeighbor e)) hPair

/-- A fatal responder-leader row with an OLD follower killer is
necessarily caused by an OLD LIVE at the initiator. Under NoBadLive
that killer cannot have an earlier bullet in its OLD leader sector.
This is the non-leftmost-LIVE exclusion used in D.5. -/
theorem grantDrainDummyFatalFollowerNoEarlierBullet
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative)
    (e p a : Fin n)
    (hFollower : (N e).l = false)
    (hLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hNoBad : ∀ b : Fin n,
      ¬ SharedPaperNonleftmostLiveExact ring N b)
    (hSectorE : leaderSector ring N p e)
    (hSectorA : leaderSector ring N p a)
    (hBullet : HasBullet N a)
    (hEarlier :
      PPL.cyclicOffset ring p a <
        PPL.cyclicOffset ring p e) : False := by
  have hEffective :=
    grantDrainEntranceDeathEffectiveSource
      ring (by omega : 2 ≤ n) N e hLeader hDeath
  have hLive : LiveBullet N e := by
    rcases hEffective with hReady | hOldLive
    · have hFalse : true = false := hReady.1.symm.trans hFollower
      cases hFalse
    · exact hOldLive
  exact hNoBad e
    ⟨hLive, hFollower, p, a, hSectorE,
      hSectorA, hBullet, hEarlier⟩

/-- The three global geometric rows remaining after the literal
classification. Stationary includes a resident responder DUMMY,
moving includes an OLD leader-hosted source DUMMY, and the ready
row is restricted to a real responder death (survival is proved).
These are specifications, NOT unconditional native theorems. -/
def GrantDrainDummyCleanGeometry
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) : Prop :=
  (∀ b : Fin n, b ≠ e →
    ¬ (b = ring.rightNeighbor e ∧
      GrantDrainDummyReadyResponder ring s e) →
    (s.native b).b = (1 : Fin 3) →
    GrantDrainEntranceBulletCleanAt ring s.native b →
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b) ∧
  ((s.native e).b = (1 : Fin 3) →
    (s.native (ring.rightNeighbor e)).l = false →
    (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) →
    GrantDrainEntranceBulletCleanAt ring s.native e →
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)) ∧
  (GrantDrainDummyReadyResponder ring s e →
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).l = false →
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).b = (1 : Fin 3) →
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e))

/-- All literal E/FIRE cases compose: the remaining clean-geometry
rows plus the now-proved local origin and surviving-leader facts
imply exactly the preexisting GrantDrainDummyEdgeOrigin.
No extra label or historical hypothesis is introduced. -/
theorem grantDrainDummyEdgeOriginOfCleanGeometry
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hGeom : GrantDrainDummyCleanGeometry ring fresh update s e) :
    GrantDrainDummyEdgeOrigin ring fresh update s e := by
  intro b hNew
  have hNotSource : b ≠ e := by
    intro hbe
    rw [hbe] at hNew
    exact grantDrainDummyNewUncleanNotSource
      ring hn fresh update s e hNew
  by_cases hResponder : b = ring.rightNeighbor e
  · subst b
    have hKind :=
      grantDrainDummyCanonicalResponderKind
        ring hn fresh update s e hNew.1
    rcases hKind with hReady | hResident | hMoved
    · have hNewClean :
          GrantDrainEntranceBulletCleanAt ring
            (grantDrainStep ring fresh update s e).native
            (ring.rightNeighbor e) := by
        by_cases hNewLeader :
          ((grantDrainStep ring fresh update s e).native
            (ring.rightNeighbor e)).l = true
        · exact grantDrainDummyReadySurvivingLeaderClean
            ring hn fresh update s e hReady.1 hNewLeader hNew.1
        · have hDead :
            ((grantDrainStep ring fresh update s e).native
              (ring.rightNeighbor e)).l = false := by
            cases hl :
              ((grantDrainStep ring fresh update s e).native
                (ring.rightNeighbor e)).l with
            | false => rfl
            | true => exact False.elim (hNewLeader hl)
          exact hGeom.2.2 hReady hDead hNew.1
      exact False.elim (hNew.2 hNewClean)
    · have hNotReady :
          ¬ GrantDrainDummyReadyResponder ring s e := by
        intro hReady
        have hNewClean :
            GrantDrainEntranceBulletCleanAt ring
              (grantDrainStep ring fresh update s e).native
              (ring.rightNeighbor e) := by
          by_cases hNewLeader :
            ((grantDrainStep ring fresh update s e).native
              (ring.rightNeighbor e)).l = true
          · exact grantDrainDummyReadySurvivingLeaderClean
              ring hn fresh update s e hReady.1 hNewLeader hNew.1
          · have hDead :
              ((grantDrainStep ring fresh update s e).native
                (ring.rightNeighbor e)).l = false := by
              cases hl :
                ((grantDrainStep ring fresh update s e).native
                  (ring.rightNeighbor e)).l with
              | false => rfl
              | true => exact False.elim (hNewLeader hl)
            exact hGeom.2.2 hReady hDead hNew.1
        exact hNew.2 hNewClean
      have hNotOldClean :
          ¬ GrantDrainEntranceBulletCleanAt ring s.native
            (ring.rightNeighbor e) := by
        intro hOldClean
        exact hNew.2
          (hGeom.1 (ring.rightNeighbor e) hNotSource
            (by intro hForbidden; exact hNotReady hForbidden.2)
            hResident hOldClean)
      exact Or.inl
        ⟨hNotSource,
          (by intro hForbidden; exact hNotReady hForbidden.2),
          ⟨hResident, hNotOldClean⟩⟩
    · have hNotOldClean :
          ¬ GrantDrainEntranceBulletCleanAt ring s.native e := by
        intro hOldClean
        exact hNew.2
          (hGeom.2.1 hMoved.1 hMoved.2.1
            hMoved.2.2 hOldClean)
      exact Or.inr
        ⟨rfl, hMoved.2.1, hMoved.2.2,
          ⟨hMoved.1, hNotOldClean⟩⟩
  · have hOldDummy : (s.native b).b = (1 : Fin 3) :=
      grantDrainDummyAwayOldKind
        ring fresh update s e b hNotSource hResponder hNew
    have hNotOldClean :
        ¬ GrantDrainEntranceBulletCleanAt ring s.native b := by
      intro hOldClean
      exact hNew.2
        (hGeom.1 b hNotSource
          (by intro hForbidden; exact hResponder hForbidden.1)
          hOldDummy hOldClean)
    exact Or.inl
      ⟨hNotSource,
        (by intro hForbidden; exact hResponder hForbidden.1),
        ⟨hOldDummy, hNotOldClean⟩⟩

/-- Existing word-level faithful-cover theorem instantiated with
the exact three remaining native-geometry rows. This is conditional
on those rows at every PPlus/NoBadLive state, not on an arbitrary
hypothetical state transition. -/
theorem grantDrainDummyWordFaithfulOfCleanGeometry
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hGeometry :
      ∀ (s : GrantDrainState n Scratch) (e : Fin n),
        PPlus ring s.native →
        GrantDrainEntranceNoBadLive ring s →
        GrantDrainDummyCleanGeometry ring fresh update s e) :
    ∀ (word : List (Fin n))
      (z : GrantDrainState n Scratch × (Fin n → Option (Fin n))),
      PPlus ring z.1.native →
      GrantDrainEntranceNoBadLive ring z.1 →
      GrantDrainDummyHostFaithful ring z.1.native z.2 →
      GrantDrainDummyHostFaithful ring
        (word.foldl (grantDrainDummyEdgeWordStep
          ring fresh update) z).1.native
        (word.foldl (grantDrainDummyEdgeWordStep
          ring fresh update) z).2 := by
  exact grantDrainDummyEdgeWordFaithfulOfOrigins
    ring hn fresh update
    (fun s e hPB hNoBad =>
      grantDrainDummyEdgeOriginOfCleanGeometry
        ring hn fresh update s e
        (hGeometry s e hPB hNoBad))

end L3.GrantDrainEntrance

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Closure on the actual
canonical grantDrainStep and the existing LockBudget object.

The first theorem isolates the remaining native-geometry requirement
in weak-source death: a new protected nearest zero arc. Both n=5
canonical death edges below discharge the post physical certificate,
including the F0 closer-birth case. The universal first-shielded-root
concatenation and the general weak-to-weak physical progress theorem
are NOT established here; consequently no unconditional
one-edge LockBudget induction or GrantDrainLedgerNoExhaustion is
asserted.
-/

/-- An OLD weak label outside both selected sites has an unchanged
grant, request and follower bit. A NEW actual strong lock therefore
promotes its persistent mark and supplies the full post-step physical
certificate. No alternate transition or proof-only grant is used. -/
theorem grantDrainWeakOffPairPromotesOfPostStrongLock
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainLedgerLabel n)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNotX : g ≠ e)
    (hNotY : g ≠ ring.rightNeighbor e)
    (hNewLock : grantDrainLedgerStrongLock ring
      (grantDrainStep ring fresh update s e) g = true) :
    GrantDrainStrongPhysical ring
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨hOldGrant, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨hOldRequest, hOldFollower, hOldWeakLock, _⟩ :=
    hWeakCase
  have hNewHost :
      grantDrainLedgerHost ring fresh s e label.host = some g := by
    simp [grantDrainLedgerHost, hHost, hNotX, hNotY]
  have hNewGrant :
      (grantDrainStep ring fresh update s e).grant g = true := by
    change
      (if g = e then
        (grantDrainLedgerRow ring fresh s e).1.grant
       else if g = ring.rightNeighbor e then
        (grantDrainLedgerRow ring fresh s e).2.grant
       else s.grant g) = true
    simp [hNotX, hNotY, hOldGrant]
  have hNewRequest :
      (grantDrainStep ring fresh update s e).request g = false := by
    change
      (if g = e then
        (grantDrainLedgerRow ring fresh s e).1.req
       else if g = ring.rightNeighbor e then
        (grantDrainLedgerRow ring fresh s e).2.req
       else s.request g) = false
    simp [hNotX, hNotY, hOldRequest]
  have hNewFollower :
      ((grantDrainStep ring fresh update s e).native g).l = false := by
    change (grantDrainNativeNext ring s e g).l = false
    rw [grantDrainMarksNativeOutsidePairFrame
      ring s e g hNotX hNotY]
    exact hOldFollower
  have hOldNotStrong :
      grantDrainLedgerStrongLock ring s g = false := by
    cases hs :
        (s.native (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))).sh with
    | false =>
        simp [grantDrainLedgerStrongLock, hs]
    | true =>
        simp [grantDrainLedgerWeakLock, hs] at hOldWeakLock
  have hOldObserved :
      grantDrainLedgerObservedMark ring s label.host = .weak := by
    rw [hHost]
    simp [grantDrainLedgerObservedMark, hOldRequest,
      hOldFollower, hOldNotStrong, hOldWeakLock]
  have hNoCoalesce :
      grantDrainLedgerCoalesceMark ring s e label.host
        (grantDrainLedgerHost ring fresh s e label.host) =
          .unmarked := by
    simp [grantDrainLedgerCoalesceMark, hHost, hNotY]
  have hNewObserved :
      grantDrainLedgerObservedMark ring
        (grantDrainStep ring fresh update s e) (some g) =
          .strong := by
    simp [grantDrainLedgerObservedMark, hNewRequest,
      hNewFollower, hNewLock]
  have hNewMark :
      grantDrainLedgerMarkNext ring fresh update s e label =
        .strong := by
    unfold grantDrainLedgerMarkNext
    rw [hOldObserved, hNoCoalesce, hNewHost, hNewObserved, hWeak]
    rfl
  exact ⟨g, hNewHost, hNewMark, hNewGrant,
    hNewRequest, hNewFollower, hNewLock⟩

/-- The actual post-E/post-FIRE first-shielded-root witness is enough
to close physical weak-to-strong promotion AND its budget. This is
the precise open geometric premise, not a newly assumed axiom. -/
theorem grantDrainLockBudgetWeakOffPairOfProtectedArc
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainLedgerLabel n)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNotX : g ≠ e)
    (hNotY : g ≠ ring.rightNeighbor e)
    (hPostArc :
      ∃ p : Fin n,
        GrantDrainMarksNearestArc ring
          (grantDrainStep ring fresh update s e).native p g ∧
        GrantDrainMarksZeroOffsetArc ring
          (grantDrainStep ring fresh update s e).native p g ∧
        ((grantDrainStep ring fresh update s e).native p).sh =
          true) :
    GrantDrainStrongPhysical ring
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) ∧
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨p, hNearest, hZero, hShield⟩ := hPostArc
  have hNewLock :
      grantDrainLedgerStrongLock ring
        (grantDrainStep ring fresh update s e) g = true :=
    grantDrainMarksOffsetArcStrongLock ring
      (grantDrainStep ring fresh update s e)
      p g hNearest hZero hShield
  have hPhysical :=
    grantDrainWeakOffPairPromotesOfPostStrongLock
      ring fresh update s e g label hInv hHost hWeak
      hNotX hNotY hNewLock
  exact ⟨hPhysical,
    grantDrainLockBudgetWeakToStrongOfPhysical
      ring hn fresh update s e label g
      hInv hHost hWeak hPhysical⟩

/-- The earlier literal F0 closer-birth edge, 2 -> 3, with old weak
host 4. It is a canonical PPlus edge and its newly nearest
protected source is site 2, not the old peaceful source at site 0.
This is an actual weak-source-death physical certificate. -/
theorem grantDrainDeathBornFiveStrongPhysicalAtCloserBirth :
    GrantDrainStrongPhysical grantDrainWeakDeathFiveRing
      grantDrainDeathBornFiveAfter grantDrainDeathBornFiveLabelAfter := by
  have hOld :
      LockBudget grantDrainWeakDeathFiveRing
        grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
        grantDrainDeathBornFiveStart grantDrainDeathBornFiveLabel :=
    grantDrainLockBudgetInitial grantDrainWeakDeathFiveRing
      (by decide : 5 ≤ 5)
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainDeathBornFiveStart (4 : Fin 5)
  have hNotX : (4 : Fin 5) ≠ (2 : Fin 5) := by
    decide
  have hNotY :
      (4 : Fin 5) ≠
        grantDrainWeakDeathFiveRing.rightNeighbor (2 : Fin 5) := by
    unfold grantDrainWeakDeathFiveRing
    decide +kernel
  exact grantDrainWeakOffPairPromotesOfPostStrongLock
    grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainDeathBornFiveStart (2 : Fin 5) (4 : Fin 5)
    grantDrainDeathBornFiveLabel hOld
    grantDrainDeathBornFiveOldWeak.1
    grantDrainDeathBornFiveOldWeak.2.1
    hNotX hNotY grantDrainDeathBornFivePromotes.2.2.2

/-- Complete LockBudget across the concrete F0 birth/death edge,
using the existing weak-to-strong budget algebra. -/
theorem grantDrainDeathBornFiveLockBudgetAfterCloserBirth :
    LockBudget grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainDeathBornFiveAfter grantDrainDeathBornFiveLabelAfter := by
  exact grantDrainLockBudgetWeakToStrongOfPhysical
    grantDrainWeakDeathFiveRing (by decide : 5 ≤ 5)
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainDeathBornFiveStart (2 : Fin 5)
    grantDrainDeathBornFiveLabel (4 : Fin 5)
    (grantDrainLockBudgetInitial grantDrainWeakDeathFiveRing
      (by decide : 5 ≤ 5)
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainDeathBornFiveStart (4 : Fin 5))
    grantDrainDeathBornFiveOldWeak.1
    grantDrainDeathBornFiveOldWeak.2.1
    grantDrainDeathBornFiveStrongPhysicalAtCloserBirth

/-- The other literal n=5 death edge, again 2 -> 3 but WITHOUT F0,
also preserves the actual LockBudget after promoting weak to strong.
Its new protected root is the shielded predecessor at site 0. -/
theorem grantDrainWeakDeathFiveLockBudgetAfterQuietDeath :
    LockBudget grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainWeakDeathFiveNext grantDrainWeakDeathFiveLabelNext := by
  exact grantDrainLockBudgetWeakToStrongOfPhysical
    grantDrainWeakDeathFiveRing (by decide : 5 ≤ 5)
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainWeakDeathFiveStart (2 : Fin 5)
    grantDrainWeakDeathFiveLabel (4 : Fin 5)
    (grantDrainLockBudgetInitial grantDrainWeakDeathFiveRing
      (by decide : 5 ≤ 5)
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainWeakDeathFiveStart (4 : Fin 5))
    grantDrainWeakDeathFiveSeed.1
    grantDrainWeakDeathFiveSeed.2.1
    grantDrainWeakDeathFiveStrongPhysical

/-- The weak-to-weak row after supplying its TWO missing native
facts: physical weak lock at the surviving host, and moving-distance
progress. This bridges them to LockBudget on the exact canonical
step, including a nominated hit and the 2*n min-cap. -/
theorem grantDrainLockBudgetWeakToWeakOfPhysicalProgress
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hPhysical : ∀ j : Fin n,
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j →
      (grantDrainStep ring fresh update s e).grant j = true ∧
      (grantDrainStep ring fresh update s e).request j = false ∧
      ((grantDrainStep ring fresh update s e).native j).l =
        false ∧
      grantDrainLedgerWeakLock ring
        (grantDrainStep ring fresh update s e) j = true)
    (hProgress :
      if grantDrainLedgerNominatedHit ring s e label.host then
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label).host +
            1 ≤
        grantDrainStrongProtectedDistance ring s label.host
      else
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label).host ≤
        grantDrainStrongProtectedDistance ring s label.host) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨_, hOldWeakCase⟩ := hInv g hHost
  rw [hWeak] at hOldWeakCase
  obtain ⟨_, _, _, hOldAtG⟩ := hOldWeakCase
  have hOldBudget :
      grantDrainStrongProtectedDistance ring s label.host + n ≤
        label.remaining := by
    rw [hHost]
    exact hOldAtG
  have hOldBound :
      grantDrainStrongProtectedDistance ring s label.host ≤ n :=
    grantDrainStrongProtectedDistance_le_n ring s label.host
  intro j hj
  obtain ⟨hNewGrant, hNewRequest, hNewFollower, hNewWeakLock⟩ :=
    hPhysical j hj
  refine ⟨hNewGrant, ?_⟩
  rw [hNextWeak]
  refine ⟨hNewRequest, hNewFollower, hNewWeakLock, ?_⟩
  have hNextRemaining :
      (grantDrainLedgerStep ring fresh update s e label).remaining =
        min
          (label.remaining -
            (if grantDrainLedgerNominatedHit ring s e label.host
              then 1 else 0)) (2 * n) := by
    change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring fresh s e label.host)
      (grantDrainLedgerMarkNext ring fresh update s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e label.host)) = _
    have hRawHost :
        grantDrainLedgerHost ring fresh s e label.host = some j :=
      hj
    have hRawMark :
        grantDrainLedgerMarkNext ring fresh update s e label =
          .weak := hNextWeak
    rw [hRawHost, hRawMark]
    simp [grantDrainLedgerRemainingNext, hWeak,
      grantDrainLedgerQuotaCap]
  have hLocalProgress :
      if grantDrainLedgerNominatedHit ring s e label.host then
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e) (some j) + 1 ≤
            grantDrainStrongProtectedDistance ring s label.host
      else
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e) (some j) ≤
            grantDrainStrongProtectedDistance ring s label.host := by
    rw [hj] at hProgress
    exact hProgress
  rw [hNextRemaining]
  exact grantDrainR8WeakPhaseBudgetAlgebra
    n
    (grantDrainStrongProtectedDistance ring s label.host)
    (grantDrainStrongProtectedDistance ring
      (grantDrainStep ring fresh update s e) (some j))
    label.remaining
    (grantDrainLedgerNominatedHit ring s e label.host)
    hOldBound hOldBudget hLocalProgress

/-- Native-leader terminal death: once the actual survivor is an
unheld strong-locked follower, its distance is STRICTLY below n,
since the source scan finds a preceding shielded leader. Thus the
old terminal quota >= n still pays a nominated one-hit decrement.
Only the post-step physical-token outcome is a premise here. -/
theorem grantDrainLockBudgetTerminalLeaderDeathOfPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainLedgerLabel n)
    (g j : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hOldTerminal : label.mark = .terminal)
    (hOldRequest : s.request g = false)
    (hOldLeader : (s.native g).l = true)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hNewGrant :
      (grantDrainStep ring fresh update s e).grant j = true)
    (hNewRequest :
      (grantDrainStep ring fresh update s e).request j = false)
    (hNewFollower :
      ((grantDrainStep ring fresh update s e).native j).l = false)
    (hNewLock :
      grantDrainLedgerStrongLock ring
        (grantDrainStep ring fresh update s e) j = true) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  have hOldEnough : n ≤ label.remaining := by
    obtain ⟨_, hCase⟩ := hInv g hOldHost
    rw [hOldTerminal] at hCase
    simpa [hOldRequest, hOldLeader] using hCase
  have hPNext :
      PPlus ring (grantDrainStep ring fresh update s e).native :=
    grantDrainStep_preserves_PPlus
      (by omega : 3 ≤ n) ring fresh update s e hP
  obtain ⟨p, hNearest, _, _⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring (grantDrainStep ring fresh update s e) j
      hPNext hNewFollower hNewLock
  have hScan :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native j =
          PPL.cyclicOffset ring p j :=
    grantDrainMarksScanOfNearestArc ring
      (grantDrainStep ring fresh update s e).native p j hNearest
  have hScanPositive :
      0 < grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native j := by
    rw [hScan]
    exact hNearest.1
  have hScanBound :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native j ≤ n := by
    rw [hScan]
    exact Nat.le_of_lt (GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring p j)
  have hDistanceBound :
      grantDrainStrongProtectedDistance ring
        (grantDrainStep ring fresh update s e) (some j) < n := by
    rw [grantDrainStrongProtectedDistance_eq_raw
      ring (grantDrainStep ring fresh update s e)
      j hScanPositive hScanBound, hScan]
    exact GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring p j
  have hNewTerminal :=
    grantDrainDeathTerminalMarkPersists ring fresh update
      s e label hOldTerminal
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host = some j :=
    hNewHost
  have hRawMark :
      grantDrainLedgerMarkNext ring fresh update s e label =
        .terminal := hNewTerminal
  have hPostNotHeld :
      grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e) (some j) =
          false := by
    simp [grantDrainLedgerHeld, hNewRequest]
  have hRemaining :
      (grantDrainLedgerStep ring fresh update s e label).remaining =
        min
          (label.remaining -
            (if grantDrainLedgerNominatedHit ring s e label.host
              then 1 else 0)) n := by
    change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring fresh s e label.host)
      (grantDrainLedgerMarkNext ring fresh update s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e label.host)) = _
    rw [hRawHost, hRawMark, hPostNotHeld]
    simp [grantDrainLedgerRemainingNext, hOldTerminal,
      grantDrainLedgerQuotaCap]
  have hPostBudget :
      grantDrainStrongProtectedDistance ring
        (grantDrainStep ring fresh update s e) (some j) ≤
      (grantDrainLedgerStep ring fresh update s e label).remaining := by
    rw [hRemaining]
    apply Nat.le_min.mpr
    constructor
    · cases hh : grantDrainLedgerNominatedHit
        ring s e label.host with
      | false =>
          simp [hh]
          omega
      | true =>
          simp [hh]
          omega
    · exact Nat.le_of_lt hDistanceBound
  intro k hk
  have hj : j = k :=
    Option.some.inj (hNewHost.symm.trans hk)
  subst k
  refine ⟨hNewGrant, ?_⟩
  rw [hNewTerminal]
  simp only [hNewRequest, ↓reduceIte, hNewFollower, ↓reduceIte]
  exact ⟨hNewLock, hPostBudget⟩

/-- The existing initial n=5 terminal/native-leader victim at site 3
dies on literal edge 2 -> 3 and its label travels to follower 2.
Its full LockBudget, including the 5 -> 4 quota, survives. -/
theorem grantDrainTerminalDeathFiveLockBudgetAfter :
    LockBudget grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainTerminalDeathFiveAfter
      grantDrainTerminalDeathFiveLabelAfter := by
  obtain ⟨hOldHost, hOldMark, _, _, hOldLeader, _, hNewHost,
    _, _, hNewLock⟩ := grantDrainTerminalDeathFiveWitness
  have hOldRequest :
      grantDrainTerminalDeathFiveStart.request (3 : Fin 5) =
        false := by
    unfold grantDrainTerminalDeathFiveStart
      grantDrainWeakDeathFiveStart
    decide +kernel
  have hNewGrant :
      grantDrainTerminalDeathFiveAfter.grant (2 : Fin 5) =
        true := by
    unfold grantDrainTerminalDeathFiveAfter
      grantDrainTerminalDeathFiveStart
      grantDrainWeakDeathFiveStart
      grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveNative
    decide +kernel
  have hNewRequest :
      grantDrainTerminalDeathFiveAfter.request (2 : Fin 5) =
        false := by
    unfold grantDrainTerminalDeathFiveAfter
      grantDrainTerminalDeathFiveStart
      grantDrainWeakDeathFiveStart
      grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveNative
    decide +kernel
  have hNewFollower :
      (grantDrainTerminalDeathFiveAfter.native (2 : Fin 5)).l =
        false := by
    unfold grantDrainTerminalDeathFiveAfter
      grantDrainTerminalDeathFiveStart
      grantDrainWeakDeathFiveStart
      grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveNative
    decide +kernel
  exact grantDrainLockBudgetTerminalLeaderDeathOfPhysical
    grantDrainWeakDeathFiveRing (by decide : 5 ≤ 5)
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainTerminalDeathFiveStart (2 : Fin 5)
    grantDrainTerminalDeathFiveInitial
    (3 : Fin 5) (2 : Fin 5)
    grantDrainTerminalDeathFivePPlus
    (grantDrainLockBudgetInitial grantDrainWeakDeathFiveRing
      (by decide : 5 ≤ 5)
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainTerminalDeathFiveStart (3 : Fin 5))
    hOldHost hOldMark hOldRequest hOldLeader hNewHost
    hNewGrant hNewRequest hNewFollower hNewLock

end L3

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Leaf proofs for the clean-DUMMY transition.
The full three-row theorem is NOT asserted here.
-/

/-- A clean bullet's own signal is zero. -/
theorem grantDrainDummyCleanOwnSignalZero
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (b : Fin n)
    (hClean : GrantDrainEntranceBulletCleanAt ring N b) :
    (N b).sg = false := by
  obtain ⟨_, p, _, _, hTrail⟩ := hClean
  have hBound : PPL.cyclicOffset ring p b < n :=
    grantDrainEntranceArcOffsetLt ring p b
  have hAt := hTrail
    (⟨PPL.cyclicOffset ring p b, hBound⟩ : Fin n)
    (Nat.le_refl _)
  rw [grantDrainMarksArcShiftRightOffset ring p b] at hAt
  exact hAt

/-- The first follower of a leader has precisely that leader
as its nearest counterclockwise source. -/
theorem grantDrainDummyAdjacentLeaderSector
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (he : (N e).l = true)
    (hy : (N (ring.rightNeighbor e)).l = false) :
    leaderSector ring N e (ring.rightNeighbor e) := by
  obtain ⟨d, hd⟩ :=
    grantDrainEntranceR8eSectorAtLeader
      ring N ⟨e, he⟩ e he
  have hPos : 0 < d.val := hd.1
  have hMore : 1 < d.val := by
    by_cases hOne : d.val = 1
    · have hNext := hd.2.2.1
      rw [hOne] at hNext
      change (N (ring.rightNeighbor e)).l = true at hNext
      rw [hy] at hNext
      cases hNext
    · omega
  change leaderSector ring N e (PPL.shiftRight ring e 1)
  exact grantDrainDummySectorNearest ring N e d hd
    (⟨1, (show 1 < n by omega)⟩ : Fin n)
    (show 1 < d.val by omega)

/-- The DUMMY at the first follower of a zero-signal bullet-free
leader is clean, irrespective of other ring sites. -/
theorem grantDrainDummyAdjacentFollowerClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLeader : (N e).l = true)
    (hEmpty : (N e).b = (0 : Fin 3))
    (hSourceZero : (N e).sg = false)
    (hFollower : (N (ring.rightNeighbor e)).l = false)
    (hDummy :
      (N (ring.rightNeighbor e)).b = (1 : Fin 3))
    (hTargetZero : (N (ring.rightNeighbor e)).sg = false) :
    GrantDrainEntranceBulletCleanAt ring N
      (ring.rightNeighbor e) := by
  have hOffset :
      PPL.cyclicOffset ring e (ring.rightNeighbor e) = 1 :=
    grantDrainDummyRightOffset ring e 1
      (show 1 < n by omega)
  have hBullet : HasBullet N (ring.rightNeighbor e) := by
    intro hZero
    have hImpossible : (1 : Fin 3) = (0 : Fin 3) :=
      hDummy.symm.trans hZero
    exact (by decide : (1 : Fin 3) ≠ (0 : Fin 3)) hImpossible
  refine ⟨hBullet, e,
    grantDrainDummyAdjacentLeaderSector
      ring hn N e hLeader hFollower, ?_, ?_⟩
  · intro a _ haBullet
    rw [hOffset]
    by_cases hAtRoot :
        PPL.cyclicOffset ring e a = 0
    · have hSite :=
        grantDrainMarksArcShiftRightOffset ring e a
      rw [hAtRoot, grantDrainEntranceR8eShiftZero ring e]
        at hSite
      have ha : a = e := hSite.symm
      rw [ha] at haBullet
      exact False.elim (haBullet hEmpty)
    · omega
  · intro k hk
    rw [hOffset] at hk
    have hCases : k.val = 0 ∨ k.val = 1 := by omega
    rcases hCases with hZero | hOne
    · rw [hZero, grantDrainEntranceR8eShiftZero ring e]
      exact hSourceZero
    · rw [hOne]
      change (N (ring.rightNeighbor e)).sg = false
      exact hTargetZero

/-- Row A: a leader-hosted DUMMY away from the interacting pair
has its entire native record framed, and stays clean. -/
theorem grantDrainDummyStationaryLeaderAwayClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e b : Fin n)
    (hLeader : (s.native b).l = true)
    (hDummy : (s.native b).b = (1 : Fin 3))
    (hClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hNotSource : b ≠ e)
    (hNotTarget : b ≠ ring.rightNeighbor e) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hFrame :
      (grantDrainStep ring fresh update s e).native b =
        s.native b :=
    sharedPaperNativeAwayFrame ring s e b hNotSource hNotTarget
  have hZero := grantDrainDummyCleanOwnSignalZero
    ring s.native b hClean
  apply grantDrainDummyLeaderZeroClean ring
    (grantDrainStep ring fresh update s e).native b
  · rw [hFrame]
    exact hLeader
  · rw [hFrame]
    exact hDummy
  · rw [hFrame]
    exact hZero

/-- Row A: a surviving responder leader retains its OLD clean
DUMMY; responder FIRE is blocked by that nonempty DUMMY. -/
theorem grantDrainDummyStationarySurvivingResponderClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hOldLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hOldDummy :
      (s.native (ring.rightNeighbor e)).b = (1 : Fin 3))
    (hOldClean : GrantDrainEntranceBulletCleanAt ring
      s.native (ring.rightNeighbor e))
    (hNextLeader :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = true) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hOldZero :=
    grantDrainDummyCleanOwnSignalZero ring s.native
      (ring.rightNeighbor e) hOldClean
  have hEDummy :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) :=
    (grantDrainEntranceNativeEQuietVictimBulletRetained
      ring (by omega : 2 ≤ n) s.native e hOldLeader hOldZero).trans
        hOldDummy
  have hIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hEDummy]
  have hNoRight : grantDrainSelect ring s e ≠ .rightLocal :=
    grantDrainEntranceResponderIneligibleNoRightFire
      ring s e hIneligible
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hNextDummy :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b = (1 : Fin 3) := by
    change (grantDrainNativeNext ring s e
      (ring.rightNeighbor e)).b = (1 : Fin 3)
    cases hf : grantDrainSelect ring s e with
    | none =>
        simpa [grantDrainNativeNext, hf] using hEDummy
    | leftLocal =>
        simpa [grantDrainNativeNext, hf,
          canonicalBirth, hDistinct] using hEDummy
    | rightLocal =>
        exact False.elim (hNoRight hf)
    | cross =>
        simpa [grantDrainNativeNext, hf,
          canonicalBirth, hDistinct] using hEDummy
  exact grantDrainDummyReadySurvivingLeaderClean
    ring hn fresh update s e hOldLeader hNextLeader hNextDummy

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- Uniform leader-array, backwards-bullet and monotone-zero
frame. This proves clean preservation for a stationary bullet
without requiring global I; the three frame hypotheses are
explicit, and must not be assumed for arbitrary canonical edges. -/
theorem grantDrainDummyCleanUniformFrame
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (b : Fin n)
    (hOld : GrantDrainEntranceBulletCleanAt ring N b)
    (hNewBullet : HasBullet M b)
    (hLeaders : ∀ i : Fin n, (M i).l = (N i).l)
    (hBulletBackward :
      ∀ i : Fin n, HasBullet M i → HasBullet N i)
    (hZeroBackward :
      ∀ i : Fin n, (N i).sg = false → (M i).sg = false) :
    GrantDrainEntranceBulletCleanAt ring M b := by
  obtain ⟨_, p, hOldSector, hFirst, hTrail⟩ := hOld
  have hLeaderFunctions :
      (fun i : Fin n => (M i).l) =
        (fun i : Fin n => (N i).l) := by
    funext i
    exact hLeaders i
  have hNewSector : leaderSector ring M p b := by
    constructor
    · rw [hLeaders p]
      exact hOldSector.1
    · change PPL.dLLBy ring (fun i : Fin n => (M i).l) b =
        some (PPL.cyclicOffset ring p b)
      rw [hLeaderFunctions]
      exact hOldSector.2
  refine ⟨hNewBullet, p, hNewSector, ?_, ?_⟩
  · intro a hNewASector hNewABullet
    have hOldASector : leaderSector ring N p a := by
      constructor
      · have hAt : (M p).l = true := hNewASector.1
        rw [hLeaders p] at hAt
        exact hAt
      · have hScan :
          PPL.dLLBy ring (fun i : Fin n => (M i).l) a =
            some (PPL.cyclicOffset ring p a) :=
          hNewASector.2
        rw [hLeaderFunctions] at hScan
        exact hScan
    exact hFirst a hOldASector
      (hBulletBackward a hNewABullet)
  · intro k hk
    exact hZeroBackward _ (hTrail k hk)

/-- Row B when the OLD clean DUMMY is hosted on the source
leader: an empty follower receives the DUMMY, E leaves a
zero-signal bullet-free source leader, and FIRE is ineligible
at both endpoints. The follower-hosted source case remains open. -/
theorem grantDrainDummyMovedLeaderSourceClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hOldLeader : (s.native e).l = true)
    (hOldDummy : (s.native e).b = (1 : Fin 3))
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native e)
    (hYFollower : (s.native (ring.rightNeighbor e)).l = false)
    (hYEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3)) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hOldZero :=
    grantDrainDummyCleanOwnSignalZero ring s.native e hOldClean
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hERows :=
    grantDrainEntranceLiteralEBulletToFollower
      (s.native e) (s.native (ring.rightNeighbor e))
      hOldClean.1 hOldZero hYFollower hYEmpty
  have hESourceLeader :
      (nativeE ring s.native e e).l = true := by
    have hPair :=
      grantDrainEntranceLiteralESourceLeaderFixed
        (s.native e) (s.native (ring.rightNeighbor e))
    simpa [nativeE] using hPair.trans hOldLeader
  have hESourceZero :
      (nativeE ring s.native e e).sg = false := by
    simpa [nativeE] using hERows.2.1
  have hEResponderFollower :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false := by
    have hPair :=
      grantDrainEntranceLiteralEFollowerResponderRemains
        (s.native e) (s.native (ring.rightNeighbor e)) hYFollower
    simpa [nativeE, hDistinct] using hPair
  have hEResponderDummy :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) := by
    have hPair : (certLiteralEPair
        (s.native e) (s.native (ring.rightNeighbor e))).2.b =
        (1 : Fin 3) := hERows.2.2.1.trans hOldDummy
    simpa [nativeE, hDistinct] using hPair
  have hEResponderZero :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        false := by
    simpa [nativeE, hDistinct] using hERows.2.2.2
  have hSourceIneligible :
      grantDrainEligible (nativeE ring s.native e) e = false := by
    simp [grantDrainEligible, hESourceLeader]
  have hResponderIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hEResponderDummy]
  have hNoFire : grantDrainSelect ring s e = .none := by
    simp [grantDrainSelect, hSourceIneligible, hResponderIneligible]
  have hPhysical :
      (grantDrainStep ring fresh update s e).native =
        nativeE ring s.native e := by
    change grantDrainNativeNext ring s e = nativeE ring s.native e
    simp [grantDrainNativeNext, hNoFire]
  rw [hPhysical]
  exact grantDrainDummyAdjacentFollowerClean ring hn
    (nativeE ring s.native e) e
    hESourceLeader
    (by simpa [nativeE, hDistinct] using hERows.1) hESourceZero
    hEResponderFollower hEResponderDummy hEResponderZero

/-- Literal E row for two OLD ready leaders. The source fires a
LIVE that immediately deletes the ready responder leader; the
result is a zero-signal leader and adjacent zero-signal DUMMY. -/
theorem grantDrainDummyBothReadyLeadersLiteral
    (x y : CertNative)
    (hXL : x.l = true) (hXS : x.sg = true)
    (hYL : y.l = true) (hYS : y.sg = true) :
    (certLiteralEPair x y).1.l = true ∧
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.b = (1 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, certFinThree,
    hXL, hXS, hYL, hYS]

/-- Row C, the ready-source subcase, without a PPlus or I
assumption: two ready leaders leave exactly a clean DUMMY at
the killed responder site. FIRE is ineligible at both endpoints. -/
theorem grantDrainDummyBothReadyLeadersDeathClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hXL : (s.native e).l = true)
    (hXS : (s.native e).sg = true)
    (hYL : (s.native (ring.rightNeighbor e)).l = true)
    (hYS : (s.native (ring.rightNeighbor e)).sg = true) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPair :=
    grantDrainDummyBothReadyLeadersLiteral
      (s.native e) (s.native (ring.rightNeighbor e))
      hXL hXS hYL hYS
  have hESourceLeader :
      (nativeE ring s.native e e).l = true := by
    simpa [nativeE] using hPair.1
  have hESourceEmpty :
      (nativeE ring s.native e e).b = (0 : Fin 3) := by
    simpa [nativeE] using hPair.2.1
  have hESourceZero :
      (nativeE ring s.native e e).sg = false := by
    simpa [nativeE] using hPair.2.2.1
  have hEResponderFollower :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.1
  have hEResponderDummy :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2.1
  have hEResponderZero :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2.2
  have hSourceIneligible :
      grantDrainEligible (nativeE ring s.native e) e = false := by
    simp [grantDrainEligible, hESourceLeader]
  have hResponderIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hEResponderDummy]
  have hNoFire : grantDrainSelect ring s e = .none := by
    simp [grantDrainSelect, hSourceIneligible, hResponderIneligible]
  have hPhysical :
      (grantDrainStep ring fresh update s e).native =
        nativeE ring s.native e := by
    change grantDrainNativeNext ring s e = nativeE ring s.native e
    simp [grantDrainNativeNext, hNoFire]
  rw [hPhysical]
  exact grantDrainDummyAdjacentFollowerClean ring hn
    (nativeE ring s.native e) e
    hESourceLeader hESourceEmpty hESourceZero
    hEResponderFollower hEResponderDummy hEResponderZero

end L3.GrantDrainEntrance

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
The requested universal protected-nearest-arc conclusion is NOT proved
here. The exact E death rule has two distinct effective sources:
an OLD ready leader and an OLD LIVE. PPlus directly constrains the
LIVE predecessor but does not itself say that an OLD ready leader is
protected. The literal E operation, however, makes a ready initiator
leader shielded and quiet. These lemmas close that ready-leader
endpoint on the ACTUAL canonical step and reduce the follower
source-death endpoint to the existing PPlus LIVE hypothesis.

The remaining gap is the arbitrary-n clockwise arc concatenation,
including the surviving host, possible closer F1 birth, and the
weak-to-weak distance/physical-lock cases. No unconditional
LockBudget step or GrantDrainLedgerNoExhaustion is asserted.
-/

/-- The exact quiet unshielded responder-death row for an OLD
ready initiator leader, including the missing shield bit.
An old ready initiator becomes shielded and quiet BEFORE
any optional canonical FIRE. -/
theorem grantDrainWeakDeathReadyPairProtected
    (x y : CertNative)
    (hXL : x.l = true)
    (hXS : x.sg = true)
    (hYL : y.l = true)
    (hYShield : y.sh = false)
    (hYSignal : y.sg = false) :
    (certLiteralEPair x y).1.l = true ∧
    (certLiteralEPair x y).1.sh = true ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.sg = false := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  change xl = true at hXL
  change xsg = true at hXS
  change yl = true at hYL
  change ysh = false at hYShield
  change ysg = false at hYSignal
  subst xl
  subst xsg
  subst yl
  subst ysh
  subst ysg
  simp [certLiteralEPair, certFinThree]

/-- The ready-killer protection is not merely an E-row surrogate:
it holds after the ORIGINAL grantDrainNativeNext for all four
actual FIRE outcomes. In F0/F2 the initiator is overwritten by
firedNative, itself shielded and quiet; in F1 it is untouched. -/
theorem grantDrainWeakDeathReadySourceProtectedActual
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hReadyLeader : (s.native e).l = true)
    (hReadySignal : (s.native e).sg = true)
    (hVictimLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hVictimShield :
      (s.native (ring.rightNeighbor e)).sh = false)
    (hVictimSignal :
      (s.native (ring.rightNeighbor e)).sg = false) :
    ((grantDrainStep ring fresh update s e).native e).l = true ∧
    ((grantDrainStep ring fresh update s e).native e).sh = true ∧
    ((grantDrainStep ring fresh update s e).native e).sg = false := by
  have hPair :=
    grantDrainWeakDeathReadyPairProtected
      (s.native e) (s.native (ring.rightNeighbor e))
      hReadyLeader hReadySignal hVictimLeader
      hVictimShield hVictimSignal
  have hE :
      (nativeE ring s.native e e).l = true ∧
      (nativeE ring s.native e e).sh = true ∧
      (nativeE ring s.native e e).sg = false := by
    simpa [nativeE] using
      ⟨hPair.1, hPair.2.1, hPair.2.2.1⟩
  have hDistinct : e ≠ ring.rightNeighbor e :=
    Ne.symm (grantDrainMarksNeighborDistinct
      (by omega : 3 ≤ n) ring e)
  change
    (grantDrainNativeNext ring s e e).l = true ∧
    (grantDrainNativeNext ring s e e).sh = true ∧
    (grantDrainNativeNext ring s e e).sg = false
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hE
  | leftLocal =>
      simp [grantDrainNativeNext, hf,
        canonicalBirth, firedNative]
  | rightLocal =>
      simpa [grantDrainNativeNext, hf,
        canonicalBirth, hDistinct] using hE
  | cross =>
      simp [grantDrainNativeNext, hf,
        canonicalBirth, firedNative]

/-- If an OLD follower kills a leader responder in E, its
effective killer must be an OLD LIVE. This excludes the ready
emission branch by the old follower bit. Consequently PPlus
supplies that LIVE's shielded predecessor; the arbitrary-n
splicing of the predecessor arc to the old weak corridor
remains a separate geometric obligation. -/
theorem grantDrainWeakDeathFollowerMustBeLive
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hFollower : (N e).l = false)
    (hLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    LiveBullet N e := by
  have hCases :=
    GrantDrainEntrance.grantDrainEntranceDeathEffectiveSource
      ring (by omega : 2 ≤ n) N e hLeader hDeath
  rcases hCases with hReady | hLive
  · have hBad : true = false :=
      hReady.1.symm.trans hFollower
    cases hBad
  · exact hLive

/-- Under PPlus, the OLD follower source of an E-deleted
unshielded leader has a peaceful LIVE certificate, directly
available for the missing nearest-root/zero-prefix splice. -/
theorem grantDrainWeakDeathFollowerHasPeacefulCore
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hP : PPlus ring N)
    (hFollower : (N e).l = false)
    (hLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    PPL.PeacefulCore ring
      (fun i : Fin n => (N i).l)
      (fun i : Fin n => (N i).sh)
      (fun i : Fin n => (N i).sg) e := by
  exact hP.2 e
    (grantDrainWeakDeathFollowerMustBeLive
      ring hn N e hFollower hLeader hDeath)

/-- Both effective source modes of a deleted quiet, unshielded
OLD leader, with the ready mode tied to the actual canonical
post-FIRE state. In the other mode an OLD LIVE is exhibited,
not a speculative protected root. -/
theorem grantDrainWeakDeathEffectiveSourceProtectionOrLive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hUnshielded :
      (s.native (ring.rightNeighbor e)).sh = false)
    (hQuiet :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = false) :
    (((grantDrainStep ring fresh update s e).native e).l = true ∧
      ((grantDrainStep ring fresh update s e).native e).sh = true ∧
      ((grantDrainStep ring fresh update s e).native e).sg = false) ∨
    LiveBullet s.native e := by
  have hCases :=
    GrantDrainEntrance.grantDrainEntranceDeathEffectiveSource
      ring (by omega : 2 ≤ n) s.native e hLeader hDeath
  rcases hCases with hReady | hLive
  · exact Or.inl
      (grantDrainWeakDeathReadySourceProtectedActual
        ring hn fresh update s e hReady.1 hReady.2
        hLeader hUnshielded hQuiet)
  · exact Or.inr hLive

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
The cyclic-offset no-wrap, protected-arc concatenation, and
post-FIRE closer-birth theorems below do not assume protocol geometry
as a new global hypothesis. They are proved from explicit local
native facts and the literal source grantDrainStep.

OPEN: deriving all necessary post-E prefix and suffix facts solely
from the original weak LockBudget certificate and PPlus for every n.
Accordingly this does NOT assert the unrestricted theorem
grantDrainWeakDeathProtectedArcHolds. There is no claimed literal
counterexample. The last theorem spells out the remaining native
premises instead of hiding them in a purported unconditional proof.
-/

/-- Associativity of clockwise shifts in the actual directed ring. -/
theorem grantDrainWeakDeathShiftRightAdd
    {n : Nat} (ring : DirectedRing n)
    (q : Fin n) (a b : Nat) :
    PPL.shiftRight ring (PPL.shiftRight ring q a) b =
      PPL.shiftRight ring q (a + b) := by
  apply Fin.ext
  change (((q.val + a) % n + b) % n) =
    (q.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Inverse offset of a clockwise shift shorter than n. -/
theorem grantDrainWeakDeathOffsetShiftRight
    {n : Nat} (ring : DirectedRing n)
    (q : Fin n) (d : Nat) (hd : d < n) :
    PPL.cyclicOffset ring q (PPL.shiftRight ring q d) = d := by
  change (((q.val + d) % n + n - q.val) % n) = d
  by_cases hs : q.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have he : q.val + d + n - q.val = n + d := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hd]
  · have hge : n ≤ q.val + d := by omega
    have hlt : q.val + d - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have he : q.val + d - n + n - q.val = d := by omega
    rw [he, Nat.mod_eq_of_lt hd]

/-- Requested exact cyclic-offset concatenation, provided the
sum of the two offsets does not complete a full rotation. -/
theorem grantDrainWeakDeathOffsetConcat
    {n : Nat} (ring : DirectedRing n)
    (q p g : Fin n)
    (hNoWrap :
      PPL.cyclicOffset ring q p +
        PPL.cyclicOffset ring p g < n) :
    PPL.cyclicOffset ring q g =
      PPL.cyclicOffset ring q p +
        PPL.cyclicOffset ring p g := by
  have hShift :
      PPL.shiftRight ring q
        (PPL.cyclicOffset ring q p +
          PPL.cyclicOffset ring p g) = g := by
    calc
      PPL.shiftRight ring q
          (PPL.cyclicOffset ring q p +
            PPL.cyclicOffset ring p g) =
        PPL.shiftRight ring
          (PPL.shiftRight ring q
            (PPL.cyclicOffset ring q p))
          (PPL.cyclicOffset ring p g) :=
          (grantDrainWeakDeathShiftRightAdd ring q _ _).symm
      _ = PPL.shiftRight ring p
          (PPL.cyclicOffset ring p g) := by
        rw [grantDrainMarksArcShiftRightOffset ring q p]
      _ = g := grantDrainMarksArcShiftRightOffset ring p g
  have hOffset := grantDrainWeakDeathOffsetShiftRight ring q
    (PPL.cyclicOffset ring q p +
      PPL.cyclicOffset ring p g) hNoWrap
  rw [hShift] at hOffset
  exact hOffset

/-- If q is an old leader strictly behind p and [p,g) has no
internal old leaders, the two offsets cannot wrap. Otherwise
q would lie in the leader-free interior, or at follower g. -/
theorem grantDrainWeakDeathArcNonoverlap
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (q p g : Fin n)
    (hQLeader : (N q).l = true)
    (hBehind : 0 < PPL.cyclicOffset ring q p)
    (hTail : GrantDrainMarksNearestArc ring N p g)
    (hGFollower : (N g).l = false) :
    PPL.cyclicOffset ring q p +
      PPL.cyclicOffset ring p g < n := by
  by_cases hNoWrap :
      PPL.cyclicOffset ring q p +
        PPL.cyclicOffset ring p g < n
  · exact hNoWrap
  · have hALt :=
      GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring q p
    have hBetween :
        0 < n - PPL.cyclicOffset ring q p ∧
        n - PPL.cyclicOffset ring q p ≤
          PPL.cyclicOffset ring p g := by
      omega
    have hFull : PPL.shiftRight ring q n = q := by
      apply Fin.ext
      change (q.val + n) % n = q.val
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt]
    have hQAt :
        PPL.shiftRight ring p
          (n - PPL.cyclicOffset ring q p) = q := by
      calc
        PPL.shiftRight ring p
            (n - PPL.cyclicOffset ring q p) =
          PPL.shiftRight ring
            (PPL.shiftRight ring q
              (PPL.cyclicOffset ring q p))
            (n - PPL.cyclicOffset ring q p) := by
              rw [grantDrainMarksArcShiftRightOffset ring q p]
        _ = PPL.shiftRight ring q
            (PPL.cyclicOffset ring q p +
              (n - PPL.cyclicOffset ring q p)) :=
              grantDrainWeakDeathShiftRightAdd ring q _ _
        _ = PPL.shiftRight ring q n := by
              congr 1
              omega
        _ = q := hFull
    by_cases hLt :
        n - PPL.cyclicOffset ring q p <
          PPL.cyclicOffset ring p g
    · have hInside := hTail.2.2
        (n - PPL.cyclicOffset ring q p) hBetween.1 hLt
      rw [hQAt, hQLeader] at hInside
      cases hInside
    · have hEq :
          n - PPL.cyclicOffset ring q p =
            PPL.cyclicOffset ring p g := by omega
      have hQEqG : q = g := by
        rw [← hQAt, hEq,
          grantDrainMarksArcShiftRightOffset ring p g]
      rw [hQEqG, hGFollower] at hQLeader
      cases hQLeader

theorem grantDrainWeakDeathShiftRightZero
    {n : Nat} (ring : DirectedRing n) (q : Fin n) :
    PPL.shiftRight ring q 0 = q := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt q.isLt]

theorem grantDrainWeakDeathShiftRightNe
    {n : Nat} (ring : DirectedRing n)
    (q : Fin n) (a b : Nat)
    (ha : a < n) (hb : b < n) (hne : a ≠ b) :
    PPL.shiftRight ring q a ≠ PPL.shiftRight ring q b := by
  intro h
  have ho := congrArg (PPL.cyclicOffset ring q) h
  rw [grantDrainWeakDeathOffsetShiftRight ring q a ha,
    grantDrainWeakDeathOffsetShiftRight ring q b hb] at ho
  exact hne ho

/-- The complete protected-nearest-zero-arc concatenation.
The old source p has died: p is a follower in N, and its
right-hand prefix remains follower/zero. The left root q remains
a leader with its own follower/zero prefix. The result combines
both over the exact ring offsets, including physical wraparound. -/
theorem grantDrainWeakDeathProtectedArcConcat
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (q p g : Fin n)
    (hFront : GrantDrainMarksNearestArc ring N q p)
    (hFrontZero : GrantDrainMarksZeroOffsetArc ring N q p)
    (hPDead : (N p).l = false)
    (hRightFollower : ∀ k : Nat,
      0 < k → k < PPL.cyclicOffset ring p g →
      (N (PPL.shiftRight ring p k)).l = false)
    (hRightZero : GrantDrainMarksZeroOffsetArc ring N p g)
    (hRightPositive : 0 < PPL.cyclicOffset ring p g)
    (hNoWrap :
      PPL.cyclicOffset ring q p +
        PPL.cyclicOffset ring p g < n) :
    GrantDrainMarksNearestArc ring N q g ∧
      GrantDrainMarksZeroOffsetArc ring N q g := by
  have hJoin :=
    grantDrainWeakDeathOffsetConcat ring q p g hNoWrap
  have hShift : ∀ k : Nat,
      PPL.cyclicOffset ring q p ≤ k →
      PPL.shiftRight ring q k =
        PPL.shiftRight ring p
          (k - PPL.cyclicOffset ring q p) := by
    intro k hk
    calc
      PPL.shiftRight ring q k =
        PPL.shiftRight ring q
          (PPL.cyclicOffset ring q p +
            (k - PPL.cyclicOffset ring q p)) := by
            congr 1
            omega
      _ = PPL.shiftRight ring
          (PPL.shiftRight ring q
            (PPL.cyclicOffset ring q p))
          (k - PPL.cyclicOffset ring q p) :=
          (grantDrainWeakDeathShiftRightAdd ring q _ _).symm
      _ = PPL.shiftRight ring p
          (k - PPL.cyclicOffset ring q p) := by
            rw [grantDrainMarksArcShiftRightOffset ring q p]
  constructor
  · refine ⟨?_, hFront.2.1, ?_⟩
    · rw [hJoin]
      omega
    · intro k hk hlt
      rw [hJoin] at hlt
      by_cases hLeft : k < PPL.cyclicOffset ring q p
      · exact hFront.2.2 k hk hLeft
      · have hPast :
            PPL.cyclicOffset ring q p ≤ k := by omega
        rw [hShift k hPast]
        by_cases hAt : k - PPL.cyclicOffset ring q p = 0
        · rw [hAt, grantDrainWeakDeathShiftRightZero ring p]
          exact hPDead
        · have hPos :
              0 < k - PPL.cyclicOffset ring q p := by omega
          have hLess :
              k - PPL.cyclicOffset ring q p <
                PPL.cyclicOffset ring p g := by omega
          exact hRightFollower _ hPos hLess
  · intro k hk
    rw [hJoin] at hk
    by_cases hLeft : k < PPL.cyclicOffset ring q p
    · exact hFrontZero k hLeft
    · have hPast :
          PPL.cyclicOffset ring q p ≤ k := by omega
      rw [hShift k hPast]
      have hLess :
          k - PPL.cyclicOffset ring q p <
            PPL.cyclicOffset ring p g := by omega
      exact hRightZero _ hLess

/-- The initiator e and responder p occur at offsets a-1 and a
in the q..g arc, where a=cyclicOffset(q,p). This discharges the
site-location constraints needed for canonical F0/F1/F2 births. -/
theorem grantDrainWeakDeathSpliceBirthSites
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (e q p g : Fin n)
    (hEdge : ring.rightNeighbor e = p)
    (hBehind : 0 < PPL.cyclicOffset ring q p)
    (hRightPositive : 0 < PPL.cyclicOffset ring p g)
    (hNoWrap :
      PPL.cyclicOffset ring q p +
        PPL.cyclicOffset ring p g < n) :
    (∃ j : Nat,
      e = PPL.shiftRight ring q j ∧
      j < PPL.cyclicOffset ring q g) ∧
    (∃ j : Nat,
      ring.rightNeighbor e = PPL.shiftRight ring q j ∧
      j < PPL.cyclicOffset ring q g) := by
  have hPre : PPL.shiftLeft ring p 1 = e := by
    rw [← hEdge]
    apply Fin.ext
    change (((e.val + 1) % n + n - 1 % n) % n) = e.val
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
    by_cases hs : e.val + 1 < n
    · rw [Nat.mod_eq_of_lt hs]
      have heq : e.val + 1 + n - 1 = n + e.val := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt e.isLt]
    · have hlast : e.val + 1 = n := by omega
      rw [hlast, Nat.mod_self]
      have heq : 0 + n - 1 = e.val := by omega
      rw [heq, Nat.mod_eq_of_lt e.isLt]
  have hLeft :=
    grantDrainMarksArcLeftHostSite ring q p
      (PPL.cyclicOffset ring q p) rfl hBehind
  have hEAt :
      e = PPL.shiftRight ring q
        (PPL.cyclicOffset ring q p - 1) := by
    rw [← hPre]
    exact hLeft
  have hPAt :
      p = PPL.shiftRight ring q
        (PPL.cyclicOffset ring q p) :=
    (grantDrainMarksArcShiftRightOffset ring q p).symm
  have hJoin :=
    grantDrainWeakDeathOffsetConcat ring q p g hNoWrap
  constructor
  · refine ⟨PPL.cyclicOffset ring q p - 1, hEAt, ?_⟩
    rw [hJoin]
    omega
  · refine ⟨PPL.cyclicOffset ring q p, ?_, ?_⟩
    · rw [hEdge]
      exact hPAt
    · rw [hJoin]
      omega

/-- The post-native-E protected arc tolerates an intervening
canonical birth at offset j, including j=0 (birth at q).
The newborn becomes the nearest protected root, and the zero
suffix and leader-free suffix are inherited without a gap. -/
theorem grantDrainWeakDeathProtectedArcBirth
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (q g z : Fin n) (j : Nat)
    (hOldNearest : GrantDrainMarksNearestArc ring N q g)
    (hOldZero : GrantDrainMarksZeroOffsetArc ring N q g)
    (hSite : z = PPL.shiftRight ring q j)
    (hInside : j < PPL.cyclicOffset ring q g) :
    GrantDrainMarksNearestArc ring (canonicalBirth N z) z g ∧
    GrantDrainMarksZeroOffsetArc ring (canonicalBirth N z) z g ∧
    (canonicalBirth N z z).sh = true := by
  subst z
  have hOffset :
      PPL.cyclicOffset ring
          (PPL.shiftRight ring q j) g =
        PPL.cyclicOffset ring q g - j :=
    grantDrainMarksArcOffsetSubtract ring q g j
      (Nat.le_of_lt hInside)
  have hBorn :=
    grantDrainMarksBirthIsProtected N (PPL.shiftRight ring q j)
  have hLater : ∀ k : Nat,
      0 < k →
      k < PPL.cyclicOffset ring (PPL.shiftRight ring q j) g →
      canonicalBirth N (PPL.shiftRight ring q j)
        (PPL.shiftRight ring (PPL.shiftRight ring q j) k) =
        N (PPL.shiftRight ring q (j + k)) := by
    intro k hk hlt
    rw [hOffset] at hlt
    have hCombined :
        j + k < PPL.cyclicOffset ring q g := by omega
    have hBound :
        j + k < n := Nat.lt_trans hCombined
          (GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring q g)
    have hJBound :
        j < n := Nat.lt_trans hInside
          (GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring q g)
    have hNe :=
      grantDrainWeakDeathShiftRightNe ring q (j + k) j
        hBound hJBound (by omega)
    rw [grantDrainWeakDeathShiftRightAdd ring q j k]
    exact grantDrainMarksBirthOtherSite N
      (PPL.shiftRight ring q j)
      (PPL.shiftRight ring q (j + k)) hNe
  refine ⟨?_, ?_, hBorn.2.2.1⟩
  · refine ⟨?_, hBorn.1, ?_⟩
    · rw [hOffset]
      omega
    · intro k hk hlt
      rw [hLater k hk hlt]
      have hCombined :
          j + k < PPL.cyclicOffset ring q g := by
        rw [hOffset] at hlt
        omega
      exact hOldNearest.2.2 (j + k) (by omega) hCombined
  · intro k hk
    by_cases hZero : k = 0
    · subst k
      rw [grantDrainWeakDeathShiftRightZero ring
        (PPL.shiftRight ring q j)]
      exact hBorn.2.2.2
    · have hPositive : 0 < k := by omega
      rw [hLater k hPositive hk]
      have hCombined :
          j + k < PPL.cyclicOffset ring q g := by
        rw [hOffset] at hk
        omega
      exact hOldZero (j + k) hCombined

/-- Full actual E+FIRE split. The pre-FIRE nearest zero arc
survives no FIRE. A successful F0/F2 or F1 at either old endpoint
creates a closer protected root at that endpoint, while preserving
every later zero signal and follower site. -/
theorem grantDrainWeakDeathProtectedArcAfterFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e q g : Fin n)
    (hEArc :
      GrantDrainMarksNearestArc ring (nativeE ring s.native e) q g ∧
      GrantDrainMarksZeroOffsetArc ring (nativeE ring s.native e) q g)
    (hEShield : (nativeE ring s.native e q).sh = true)
    (hX : ∃ j : Nat,
      e = PPL.shiftRight ring q j ∧
      j < PPL.cyclicOffset ring q g)
    (hY : ∃ j : Nat,
      ring.rightNeighbor e = PPL.shiftRight ring q j ∧
      j < PPL.cyclicOffset ring q g) :
    ∃ root : Fin n,
      GrantDrainMarksNearestArc ring
        (grantDrainStep ring fresh update s e).native root g ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainStep ring fresh update s e).native root g ∧
      ((grantDrainStep ring fresh update s e).native root).sh =
        true := by
  obtain ⟨jx, hXSite, hXInside⟩ := hX
  obtain ⟨jy, hYSite, hYInside⟩ := hY
  change ∃ root : Fin n,
    GrantDrainMarksNearestArc ring
      (grantDrainNativeNext ring s e) root g ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s e) root g ∧
    (grantDrainNativeNext ring s e root).sh = true
  cases hf : grantDrainSelect ring s e with
  | none =>
      refine ⟨q, ?_, ?_, ?_⟩
      · simpa [grantDrainNativeNext, hf] using hEArc.1
      · simpa [grantDrainNativeNext, hf] using hEArc.2
      · simpa [grantDrainNativeNext, hf] using hEShield
  | leftLocal =>
      obtain ⟨hNearest, hZero, hShield⟩ :=
        grantDrainWeakDeathProtectedArcBirth
          ring (nativeE ring s.native e) q g e jx
          hEArc.1 hEArc.2 hXSite hXInside
      refine ⟨e, ?_, ?_, ?_⟩
      · simpa [grantDrainNativeNext, hf] using hNearest
      · simpa [grantDrainNativeNext, hf] using hZero
      · simpa [grantDrainNativeNext, hf] using hShield
  | rightLocal =>
      obtain ⟨hNearest, hZero, hShield⟩ :=
        grantDrainWeakDeathProtectedArcBirth
          ring (nativeE ring s.native e) q g
          (ring.rightNeighbor e) jy
          hEArc.1 hEArc.2 hYSite hYInside
      refine ⟨ring.rightNeighbor e, ?_, ?_, ?_⟩
      · simpa [grantDrainNativeNext, hf] using hNearest
      · simpa [grantDrainNativeNext, hf] using hZero
      · simpa [grantDrainNativeNext, hf] using hShield
  | cross =>
      obtain ⟨hNearest, hZero, hShield⟩ :=
        grantDrainWeakDeathProtectedArcBirth
          ring (nativeE ring s.native e) q g e jx
          hEArc.1 hEArc.2 hXSite hXInside
      refine ⟨e, ?_, ?_, ?_⟩
      · simpa [grantDrainNativeNext, hf] using hNearest
      · simpa [grantDrainNativeNext, hf] using hZero
      · simpa [grantDrainNativeNext, hf] using hShield

/-- Protocol-aware assembly, conditional ONLY on the still-needed
E-prefix and E-suffix certificates. No global one-edge geometry
is inferred from a bare offset equality. -/
theorem grantDrainWeakDeathProtectedArcOfFramedPieces
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e q p g : Fin n)
    (hEdge : ring.rightNeighbor e = p)
    (hOldRoot : (s.native q).l = true)
    (hBehind : 0 < PPL.cyclicOffset ring q p)
    (hOldRightNearest :
      GrantDrainMarksNearestArc ring s.native p g)
    (hOldHostFollower : (s.native g).l = false)
    (hFront :
      GrantDrainMarksNearestArc ring (nativeE ring s.native e) q p)
    (hFrontZero :
      GrantDrainMarksZeroOffsetArc ring (nativeE ring s.native e) q p)
    (hPDead : (nativeE ring s.native e p).l = false)
    (hRightFollower : ∀ k : Nat,
      0 < k → k < PPL.cyclicOffset ring p g →
      (nativeE ring s.native e
        (PPL.shiftRight ring p k)).l = false)
    (hRightZero :
      GrantDrainMarksZeroOffsetArc ring (nativeE ring s.native e) p g)
    (hShield : (nativeE ring s.native e q).sh = true) :
    ∃ root : Fin n,
      GrantDrainMarksNearestArc ring
        (grantDrainStep ring fresh update s e).native root g ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainStep ring fresh update s e).native root g ∧
      ((grantDrainStep ring fresh update s e).native root).sh =
        true := by
  have hNonoverlap :=
    grantDrainWeakDeathArcNonoverlap
      ring s.native q p g hOldRoot hBehind
      hOldRightNearest hOldHostFollower
  have hEArc :=
    grantDrainWeakDeathProtectedArcConcat
      ring (nativeE ring s.native e) q p g
      hFront hFrontZero hPDead hRightFollower hRightZero
      hOldRightNearest.1 hNonoverlap
  have hSites :=
    grantDrainWeakDeathSpliceBirthSites ring hn e q p g
      hEdge hBehind hOldRightNearest.1 hNonoverlap
  exact grantDrainWeakDeathProtectedArcAfterFire
    ring fresh update s e q g hEArc hShield hSites.1 hSites.2

/-- Feed the explicitly framed native death geometry into the
previously numerical/physical LockBudget preservation theorem
for a weak-to-strong survivor at a site outside the selected pair.
The missing step is still proving these framing premises from PPlus
and the pre-step weak certificate in the arbitrary-n model. -/
theorem grantDrainWeakDeathLockBudgetOfFramedPieces
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e q p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNotX : g ≠ e)
    (hNotY : g ≠ ring.rightNeighbor e)
    (hEdge : ring.rightNeighbor e = p)
    (hOldRoot : (s.native q).l = true)
    (hBehind : 0 < PPL.cyclicOffset ring q p)
    (hOldRightNearest :
      GrantDrainMarksNearestArc ring s.native p g)
    (hFront :
      GrantDrainMarksNearestArc ring (nativeE ring s.native e) q p)
    (hFrontZero :
      GrantDrainMarksZeroOffsetArc ring (nativeE ring s.native e) q p)
    (hPDead : (nativeE ring s.native e p).l = false)
    (hRightFollower : ∀ k : Nat,
      0 < k → k < PPL.cyclicOffset ring p g →
      (nativeE ring s.native e
        (PPL.shiftRight ring p k)).l = false)
    (hRightZero :
      GrantDrainMarksZeroOffsetArc ring (nativeE ring s.native e) p g)
    (hShield : (nativeE ring s.native e q).sh = true) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨_, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨_, hOldFollower, _, _⟩ := hWeakCase
  have hPostArc :=
    grantDrainWeakDeathProtectedArcOfFramedPieces
      ring hn fresh update s e q p g
      hEdge hOldRoot hBehind hOldRightNearest hOldFollower
      hFront hFrontZero hPDead hRightFollower hRightZero hShield
  exact (grantDrainLockBudgetWeakOffPairOfProtectedArc
    ring hn fresh update s e g label
    hInv hHost hWeak hNotX hNotY hPostArc).2

end L3

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Two A' ingredients.  The full stationary
follower DUMMY row is not claimed.
-/

/-- Under a fatal OLD follower-LIVE service, a different clean
bullet cannot belong to the killer's OLD nearest-leader sector.
The clean bullet would have to precede the killer, while NoBadLive
forbids that strict order. -/
theorem grantDrainDummyFatalFollowerCleanDifferentSector
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e b p : Fin n)
    (hFollower : (N e).l = false)
    (hLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hNoBad : ∀ v : Fin n,
      ¬ SharedPaperNonleftmostLiveExact ring N v)
    (hDifferent : b ≠ e)
    (hClean : GrantDrainEntranceBulletCleanAt ring N b)
    (hSectorE : leaderSector ring N p e)
    (hSectorB : leaderSector ring N p b) : False := by
  have hLive : LiveBullet N e :=
    L3.grantDrainWeakDeathFollowerMustBeLive
      ring hn N e hFollower hLeader hDeath
  have hBulletE : HasBullet N e := by
    intro hEmpty
    have hImpossible : (2 : Fin 3) = (0 : Fin 3) :=
      hLive.symm.trans hEmpty
    exact (by decide : (2 : Fin 3) ≠ (0 : Fin 3)) hImpossible
  obtain ⟨hBulletB, q, hSectorQ, hFirst, _⟩ := hClean
  have hSameOffset :
      PPL.cyclicOffset ring q b =
        PPL.cyclicOffset ring p b :=
    Option.some.inj (hSectorQ.2.symm.trans hSectorB.2)
  have hSameRoot : q = p := by
    have hLeftQ := grantDrainEntranceLeftOffset ring q b
    have hLeftP := grantDrainEntranceLeftOffset ring p b
    rw [hSameOffset] at hLeftQ
    exact hLeftQ.symm.trans hLeftP
  subst q
  have hBLeE :
      PPL.cyclicOffset ring p b ≤
        PPL.cyclicOffset ring p e :=
    hFirst e hSectorE hBulletE
  have hELeB :
      PPL.cyclicOffset ring p e ≤
        PPL.cyclicOffset ring p b := by
    by_cases hEarlier :
        PPL.cyclicOffset ring p b <
          PPL.cyclicOffset ring p e
    · exact False.elim
        (grantDrainDummyFatalFollowerNoEarlierBullet
          ring hn N e p b hFollower hLeader hDeath
          hNoBad hSectorE hSectorB hBulletB hEarlier)
    · omega
  have hSame :
      PPL.cyclicOffset ring p b =
        PPL.cyclicOffset ring p e := by omega
  have hSiteB := grantDrainMarksArcShiftRightOffset ring p b
  have hSiteE := grantDrainMarksArcShiftRightOffset ring p e
  rw [hSame] at hSiteB
  exact hDifferent (hSiteB.symm.trans hSiteE)

/-- A quiet follower E pair with no new responder bullet has
unchanged leader fields, no bullet newly introduced, and zero
signals at both endpoints. -/
theorem grantDrainDummyQuietFollowerNoTransferPair
    (x y : CertNative)
    (hxQuiet : x.sg = false)
    (hyFollower : y.l = false)
    (hyQuiet : y.sg = false)
    (hNoTransfer :
      x.b = (0 : Fin 3) ∨ y.b ≠ (0 : Fin 3)) :
    (certLiteralEPair x y).1.l = x.l ∧
    (certLiteralEPair x y).2.l = y.l ∧
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.b = y.b ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.sg = false := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with rfl | rfl | rfl <;>
    rcases grantDrainEntranceLocalFinThreeCases yb with rfl | rfl | rfl <;>
    cases xl <;> cases yl <;> cases xs <;> cases ys <;>
    cases xh <;> cases yh <;>
    simp [certLiteralEPair, certFinThree] at *

/-- A stationary clean bullet (hence also a follower-hosted
clean DUMMY) survives a genuinely no-FIRE, quiet-follower,
no-transfer edge.  This is a physical edge theorem, not a
hypothetical uniform-frame assumption. -/
theorem grantDrainDummyStationaryQuietFollowerNoTransferClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e b : Fin n)
    (hDifferent : b ≠ e)
    (hClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hSourceQuiet : (s.native e).sg = false)
    (hTargetFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hTargetQuiet :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hNoTransfer :
      (s.native e).b = (0 : Fin 3) ∨
      (s.native (ring.rightNeighbor e)).b ≠ (0 : Fin 3))
    (hNoFire : grantDrainSelect ring s e = .none) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPair :=
    grantDrainDummyQuietFollowerNoTransferPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hSourceQuiet hTargetFollower hTargetQuiet hNoTransfer
  have hSourceLeader :
      (nativeE ring s.native e e).l = (s.native e).l := by
    simpa [nativeE] using hPair.1
  have hTargetLeader :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        (s.native (ring.rightNeighbor e)).l := by
    simpa [nativeE, hDistinct] using hPair.2.1
  have hSourceEmpty :
      (nativeE ring s.native e e).b = (0 : Fin 3) := by
    simpa [nativeE] using hPair.2.2.1
  have hTargetBullet :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (s.native (ring.rightNeighbor e)).b := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.1
  have hSourceZero :
      (nativeE ring s.native e e).sg = false := by
    simpa [nativeE] using hPair.2.2.2.2.1
  have hTargetZero :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2.2
  have hLeaders :
      ∀ i : Fin n, (nativeE ring s.native e i).l =
        (s.native i).l := by
    intro i
    by_cases hi : i = e
    · subst i
      exact hSourceLeader
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        exact hTargetLeader
      · have hFrame :=
          grantDrainEntranceNativeEFrame ring s.native e i hi hj
        exact congrArg CertNative.l hFrame
  have hBulletBackward :
      ∀ i : Fin n, HasBullet (nativeE ring s.native e) i →
        HasBullet s.native i := by
    intro i hNew
    by_cases hi : i = e
    · subst i
      exact False.elim (hNew hSourceEmpty)
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        change (nativeE ring s.native e
          (ring.rightNeighbor e)).b ≠ (0 : Fin 3) at hNew
        rw [hTargetBullet] at hNew
        exact hNew
      · have hFrame :=
          grantDrainEntranceNativeEFrame ring s.native e i hi hj
        change (nativeE ring s.native e i).b ≠
          (0 : Fin 3) at hNew
        rw [hFrame] at hNew
        exact hNew
  have hZeroBackward :
      ∀ i : Fin n, (s.native i).sg = false →
        (nativeE ring s.native e i).sg = false := by
    intro i hOldZero
    by_cases hi : i = e
    · subst i
      exact hSourceZero
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        exact hTargetZero
      · have hFrame :=
          grantDrainEntranceNativeEFrame ring s.native e i hi hj
        rw [hFrame]
        exact hOldZero
  have hBulletAt :
      (nativeE ring s.native e b).b = (s.native b).b := by
    by_cases hb : b = ring.rightNeighbor e
    · subst b
      exact hTargetBullet
    · have hFrame :=
        grantDrainEntranceNativeEFrame ring s.native e
          b hDifferent hb
      exact congrArg CertNative.b hFrame
  have hNewBullet : HasBullet (nativeE ring s.native e) b := by
    change (nativeE ring s.native e b).b ≠ (0 : Fin 3)
    rw [hBulletAt]
    exact hClean.1
  have hPhysical :
      (grantDrainStep ring fresh update s e).native =
        nativeE ring s.native e := by
    change grantDrainNativeNext ring s e = nativeE ring s.native e
    simp [grantDrainNativeNext, hNoFire]
  rw [hPhysical]
  exact grantDrainDummyCleanUniformFrame
    ring s.native (nativeE ring s.native e) b
    hClean hNewBullet hLeaders hBulletBackward hZeroBackward

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Native fragments of the fatal-follower stationary DUMMY
merge.  These do not assert the unrestricted row (A').
-/

/-- A clean bullet's zero trail can be read using any certificate
for its actual nearest leader; the witness in CleanAt is unique. -/
theorem grantDrainDummyCleanTrailAtNearest
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p b : Fin n)
    (hClean : GrantDrainEntranceBulletCleanAt ring N b)
    (hSector : leaderSector ring N p b) :
    signalTrail ring N p b := by
  obtain ⟨_, q, hSectorQ, _, hTrail⟩ := hClean
  have hOffsets :
      PPL.cyclicOffset ring q b =
        PPL.cyclicOffset ring p b :=
    Option.some.inj (hSectorQ.2.symm.trans hSector.2)
  have hRoots : q = p := by
    have hLeftQ := grantDrainEntranceLeftOffset ring q b
    have hLeftP := grantDrainEntranceLeftOffset ring p b
    rw [hOffsets] at hLeftQ
    exact hLeftQ.symm.trans hLeftP
  subst q
  exact hTrail

/-- For a real E deletion of a responder leader, if the source
signal was already zero, native E cannot turn any OLD zero
signal into one.  The death-row fact, not old I, supplies both
cleared endpoints. -/
theorem grantDrainDummyDeathEZeroBackward
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e i : Fin n)
    (hLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hSourceOldZero : (N e).sg = false)
    (hOldZero : (N i).sg = false) :
    (nativeE ring N e i).sg = false := by
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hDeathPair :
      (certLiteralEPair (N e) (N (ring.rightNeighbor e))).2.l =
        false := by
    simpa [nativeE, hDistinct] using hDeath
  have hZeroPair :=
    grantDrainEntranceLiteralEDeathSignalsZero
      (N e) (N (ring.rightNeighbor e))
      hLeader (fun _ => hSourceOldZero) hDeathPair
  have hSourceZero :
      (nativeE ring N e e).sg = false := by
    simpa [nativeE] using hZeroPair.1
  have hTargetZero :
      (nativeE ring N e (ring.rightNeighbor e)).sg =
        false := by
    simpa [nativeE, hDistinct] using hZeroPair.2
  by_cases hi : i = e
  · subst i
    exact hSourceZero
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      exact hTargetZero
    · rw [grantDrainEntranceNativeEFrame ring N e i hi hj]
      exact hOldZero

/-- In a PPlus follower-LIVE killing edge the source's OLD signal
is zero by peacefulness.  The previous zero-backward E row lifts
through every canonical F0/F1/F2 outcome on the ACTUAL physical
step, with no restriction on requests or grants. -/
theorem grantDrainDummyFatalFollowerZeroBackward
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e i : Fin n)
    (hP : PPlus ring s.native)
    (hFollower : (s.native e).l = false)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false)
    (hOldZero : (s.native i).sg = false) :
    ((grantDrainStep ring fresh update s e).native i).sg =
      false := by
  have hLive : LiveBullet s.native e :=
    L3.grantDrainWeakDeathFollowerMustBeLive
      ring hn s.native e hFollower hLeader hDeath
  have hSourceOldZero : (s.native e).sg = false :=
    L3.grantDrainDeathLiveOwnSignalZero ring s e hP hLive
  have hEZero :
      (nativeE ring s.native e i).sg = false :=
    grantDrainDummyDeathEZeroBackward
      ring hn s.native e i hLeader hDeath
      hSourceOldZero hOldZero
  change (grantDrainNativeNext ring s e i).sg = false
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hEZero
  | leftLocal =>
      have hBirth :=
        grantDrainEntranceCanonicalBirthPreservesZero
          (nativeE ring s.native e) e i hEZero
      simpa [grantDrainNativeNext, hf] using hBirth
  | rightLocal =>
      have hBirth :=
        grantDrainEntranceCanonicalBirthPreservesZero
          (nativeE ring s.native e)
          (ring.rightNeighbor e) i hEZero
      simpa [grantDrainNativeNext, hf] using hBirth
  | cross =>
      have hBirth :=
        grantDrainEntranceCanonicalBirthPreservesZero
          (nativeE ring s.native e) e i hEZero
      simpa [grantDrainNativeNext, hf] using hBirth

/-- Every OLD signal-zero trail, including the two separate
pieces on either side of the deleted leader, is still zero
on the actual post-E/FIRE native state, in the OLD coordinates. -/
theorem grantDrainDummyFatalFollowerTrailBackward
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hP : PPlus ring s.native)
    (hFollower : (s.native e).l = false)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false)
    (hOldTrail : signalTrail ring s.native p b) :
    signalTrail ring
      (grantDrainStep ring fresh update s e).native p b := by
  intro k hk
  exact grantDrainDummyFatalFollowerZeroBackward
    ring hn fresh update s e (PPL.shiftRight ring p k.val)
    hP hFollower hLeader hDeath (hOldTrail k hk)

/-- The old clean LIVE at the killer and the stationary clean
DUMMY in the doomed leader's old sector provide two surviving
physical zero-trail segments.  This is the zero-signal portion of
the intended merge; no post-merge nearest-leader claim is made. -/
theorem grantDrainDummyFatalFollowerTwoTrailSegments
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hFollower : (s.native e).l = false)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false)
    (hKillerSector : leaderSector ring s.native p e)
    (hVictimSector :
      leaderSector ring s.native (ring.rightNeighbor e) b)
    (hCleanB :
      GrantDrainEntranceBulletCleanAt ring s.native b) :
    signalTrail ring
      (grantDrainStep ring fresh update s e).native p e ∧
    signalTrail ring
      (grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e) b := by
  have hLive : LiveBullet s.native e :=
    L3.grantDrainWeakDeathFollowerMustBeLive
      ring hn s.native e hFollower hLeader hDeath
  have hCleanE : GrantDrainEntranceBulletCleanAt
      ring s.native e :=
    grantDrainDummyLiveCleanOfNoBad
      ring s.native hP hNoBad e hLive
  have hTrailE : signalTrail ring s.native p e :=
    grantDrainDummyCleanTrailAtNearest
      ring s.native p e hCleanE hKillerSector
  have hTrailB :
      signalTrail ring s.native (ring.rightNeighbor e) b :=
    grantDrainDummyCleanTrailAtNearest
      ring s.native (ring.rightNeighbor e) b
      hCleanB hVictimSector
  exact ⟨
    grantDrainDummyFatalFollowerTrailBackward
      ring hn fresh update s e p e
      hP hFollower hLeader hDeath hTrailE,
    grantDrainDummyFatalFollowerTrailBackward
      ring hn fresh update s e (ring.rightNeighbor e) b
      hP hFollower hLeader hDeath hTrailB⟩

/-- A canonical native E/FIRE edge never creates a bullet at a
site other than the responder.  The source is cleared and all
other sites are framed. -/
theorem grantDrainDummyBulletBackwardOffResponder
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e i : Fin n)
    (hNotTarget : i ≠ ring.rightNeighbor e)
    (hNewBullet : HasBullet
      (grantDrainStep ring fresh update s e).native i) :
    HasBullet s.native i := by
  by_cases hi : i = e
  · subst i
    have hEmpty :=
      grantDrainDummyOutgoingSourceCleared
        ring hn fresh update s e
    exact False.elim (hNewBullet hEmpty)
  · have hFrame :=
      sharedPaperNativeAwayFrame
        ring s e i hi hNotTarget
    change (grantDrainNativeNext ring s e i).b ≠
      (0 : Fin 3) at hNewBullet
    rw [hFrame] at hNewBullet
    exact hNewBullet

/-- NoBadLive prohibits a NEW bullet strictly before the killer
in its OLD sector, as long as that site is not the responder
whose own death can emit a DUMMY. -/
theorem grantDrainDummyFatalFollowerNoEarlierBulletAfter
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p a : Fin n)
    (hFollower : (s.native e).l = false)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hKillerSector : leaderSector ring s.native p e)
    (hASector : leaderSector ring s.native p a)
    (hEarlier :
      PPL.cyclicOffset ring p a <
        PPL.cyclicOffset ring p e)
    (hNotTarget : a ≠ ring.rightNeighbor e) :
    ¬ HasBullet
      (grantDrainStep ring fresh update s e).native a := by
  intro hNewBullet
  have hOldBullet : HasBullet s.native a :=
    grantDrainDummyBulletBackwardOffResponder
      ring hn fresh update s e a hNotTarget hNewBullet
  exact grantDrainDummyFatalFollowerNoEarlierBullet
    ring hn s.native e p a hFollower hLeader hDeath
    hNoBad hKillerSector hASector hOldBullet hEarlier

/-- An exact clean-sector constructor from an already identified
nearest leader, a zero-signal half-open arc plus the host signal,
and absence of any earlier bullet.  This is the splice target for
the fatal-merge A' proof; it does not assume global I. -/
theorem grantDrainDummyCleanFromNearestZeroNoBefore
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p b : Fin n)
    (hBullet : HasBullet N b)
    (hFollower : (N b).l = false)
    (hNearest : GrantDrainMarksNearestArc ring N p b)
    (hZero : GrantDrainMarksZeroOffsetArc ring N p b)
    (hOwnZero : (N b).sg = false)
    (hNoBefore : ∀ k : Nat,
      k < PPL.cyclicOffset ring p b →
      (N (PPL.shiftRight ring p k)).b = (0 : Fin 3)) :
    GrantDrainEntranceBulletCleanAt ring N b := by
  have hBound : PPL.cyclicOffset ring p b < n :=
    grantDrainEntranceArcOffsetLt ring p b
  have hAt :
      (N (PPL.shiftLeft ring b
        (PPL.cyclicOffset ring p b))).l = true := by
    rw [grantDrainEntranceLeftOffset ring p b]
    exact hNearest.2.1
  have hLeftZero : PPL.shiftLeft ring b 0 = b := by
    apply Fin.ext
    change (b.val + n - 0 % n) % n = b.val
    simp [Nat.mod_eq_of_lt b.isLt]
  have hMiss :
      ∀ k : Nat, 0 ≤ k →
        k < PPL.cyclicOffset ring p b →
        (N (PPL.shiftLeft ring b k)).l = false := by
    intro k _ hk
    cases k with
    | zero =>
        rw [hLeftZero]
        exact hFollower
    | succ j =>
        have hShift :=
          grantDrainMarksArcShiftLeftRight
            ring p (PPL.cyclicOffset ring p b)
            (j + 1) (by omega) hBound
        rw [grantDrainMarksArcShiftRightOffset ring p b] at hShift
        rw [hShift]
        exact hNearest.2.2
          (PPL.cyclicOffset ring p b - (j + 1))
          (by omega) (by omega)
  have hScan :
      PPL.scanDistance
        (fun k => PPL.shiftLeft ring b k)
        (fun i : Fin n => (N i).l) n 0 =
        some (PPL.cyclicOffset ring p b) :=
    grantDrainDummyScanFirstExact
      (fun k => PPL.shiftLeft ring b k)
      (fun i : Fin n => (N i).l)
      n 0 (PPL.cyclicOffset ring p b)
      (Nat.zero_le _) (by omega) hAt hMiss
  have hSector : leaderSector ring N p b := by
    refine ⟨hNearest.2.1, ?_⟩
    change PPL.scanDistance
      (fun k => PPL.shiftLeft ring b k)
      (fun i : Fin n => (N i).l) n 0 =
        some (PPL.cyclicOffset ring p b)
    exact hScan
  refine ⟨hBullet, p, hSector, ?_, ?_⟩
  · intro a _ hABullet
    by_cases hEarlier :
        PPL.cyclicOffset ring p a <
          PPL.cyclicOffset ring p b
    · have hEmpty :=
        hNoBefore (PPL.cyclicOffset ring p a) hEarlier
      rw [grantDrainMarksArcShiftRightOffset ring p a] at hEmpty
      exact False.elim (hABullet hEmpty)
    · omega
  · intro k hk
    by_cases hLast : k.val = PPL.cyclicOffset ring p b
    · rw [hLast, grantDrainMarksArcShiftRightOffset ring p b]
      exact hOwnZero
    · exact hZero k.val (by omega)

end L3.GrantDrainEntrance

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
The auxiliary shielded copy below is used only to extract the
unchanged old leader/zero arc from the Boolean WEAK lock;
no replacement physical step or extra grant is introduced.
-/

/-- A proof-only native view whose leader, bullet and signal fields
are unchanged; only shield bits are made true. -/
def grantDrainWeakDeathShieldedCopy
    {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch) : GrantDrainState n Scratch :=
  { s with native := fun i => { s.native i with sh := true } }

/-- Strengthening shields preserves PPlus (including the first-hit
peaceful LIVE condition) because leader and signal fields stay fixed. -/
theorem grantDrainWeakDeathShieldedCopyPPlus
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (hP : PPlus ring s.native) :
    PPlus ring (grantDrainWeakDeathShieldedCopy s).native := by
  constructor
  · obtain ⟨q, hq⟩ := hP.1
    exact ⟨q, hq⟩
  · intro b hLive
    have hOldLive : LiveBullet s.native b := hLive
    have hOld := hP.2 b hOldLive
    change PPL.PeacefulCore ring
      (fun i : Fin n => (s.native i).l)
      (fun _ : Fin n => true)
      (fun i : Fin n => (s.native i).sg) b
    unfold PPL.PeacefulCore at hOld ⊢
    cases hd : PPL.dLLBy ring
        (fun i : Fin n => (s.native i).l) b with
    | none =>
        rw [hd] at hOld
        exact hOld
    | some d =>
        rw [hd] at hOld
        exact ⟨rfl, hOld.2⟩

/-- Both conjuncts of a true Boolean conjunction. -/
theorem grantDrainWeakDeathAndTrue {a b : Bool}
    (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-- Any actual Boolean weak corridor becomes a Boolean strong lock
in the proof-only shielded view, without changing its first-hit
distance, source leader, or zero-signal tests. -/
theorem grantDrainWeakDeathShadowStrongLock
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n)
    (hWeak : grantDrainLedgerWeakLock ring s g = true) :
    grantDrainLedgerStrongLock ring
      (grantDrainWeakDeathShieldedCopy s) g = true := by
  have hRaw :
      (grantDrainLedgerCorridor ring s g &&
        !(s.native (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))).sh) =
        true := hWeak
  have hCorr : grantDrainLedgerCorridor ring s g = true :=
    (grantDrainWeakDeathAndTrue hRaw).1
  change (grantDrainLedgerCorridor ring s g && true) = true
  simp [hCorr]

/-- Old weak locks have exactly the same actual nearest-leader
and full zero-signal arcs as strong locks. Only their predecessor's
old shield bit differs. No global weak-geometry assumption is used. -/
theorem grantDrainWeakDeathWeakLockArc
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hP : PPlus ring s.native)
    (hFollower : (s.native g).l = false)
    (hWeak : grantDrainLedgerWeakLock ring s g = true) :
    ∃ p : Fin n,
      GrantDrainMarksNearestArc ring s.native p g ∧
      GrantDrainMarksZeroOffsetArc ring s.native p g := by
  have hShadowP :=
    grantDrainWeakDeathShieldedCopyPPlus ring s hP
  have hShadowFollower :
      ((grantDrainWeakDeathShieldedCopy s).native g).l =
        false := hFollower
  have hShadowStrong :=
    grantDrainWeakDeathShadowStrongLock ring s g hWeak
  obtain ⟨p, hNearest, hZero, _⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring (grantDrainWeakDeathShieldedCopy s) g
      hShadowP hShadowFollower hShadowStrong
  have hOldNearest : GrantDrainMarksNearestArc ring s.native p g := by
    change GrantDrainMarksNearestArc ring s.native p g at hNearest
    exact hNearest
  have hOldZero : GrantDrainMarksZeroOffsetArc ring s.native p g := by
    change GrantDrainMarksZeroOffsetArc ring s.native p g at hZero
    exact hZero
  exact ⟨p, hOldNearest, hOldZero⟩

/-- Identify the extracted weak root with the actual first-hit
shiftLeft site of the old weak host. -/
theorem grantDrainWeakDeathOldRightArc
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (p g : Fin n)
    (hP : PPlus ring s.native)
    (hFollower : (s.native g).l = false)
    (hWeak : grantDrainLedgerWeakLock ring s g = true)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g)) :
    GrantDrainMarksNearestArc ring s.native p g ∧
    GrantDrainMarksZeroOffsetArc ring s.native p g := by
  obtain ⟨q, hNearest, hZero⟩ :=
    grantDrainWeakDeathWeakLockArc ring s g hP hFollower hWeak
  have hScan :=
    grantDrainMarksScanOfNearestArc ring s.native q g hNearest
  have hAt :
      PPL.shiftLeft ring g (PPL.cyclicOffset ring q g) = q := by
    have hs := grantDrainMarksArcShiftLeftRight ring q
      (PPL.cyclicOffset ring q g)
      (PPL.cyclicOffset ring q g)
      (Nat.le_refl _)
      (GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring q g)
    rw [grantDrainMarksArcShiftRightOffset ring q g] at hs
    simpa only [Nat.sub_self,
      grantDrainWeakDeathShiftRightZero] using hs
  have hMatch : q = p := by
    calc
      q = PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g) := by
            rw [hScan]
            exact hAt.symm
      _ = p := hSource.symm
  subst q
  exact ⟨hNearest, hZero⟩

/-- The nearest-left-leader sector of a leader is the trivial
zero-offset sector at that leader. -/
theorem grantDrainWeakDeathSelfLeaderSector
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLeader : (N e).l = true) :
    leaderSector ring N e e := by
  have hOffset : PPL.cyclicOffset ring e e = 0 := by
    change (e.val + n - e.val) % n = 0
    have hSame : e.val + n - e.val = n := by omega
    rw [hSame, Nat.mod_self]
  constructor
  · exact hLeader
  · change PPL.scanDistance
      (fun k => PPL.shiftLeft ring e k)
      (fun i => (N i).l) n 0 =
      some (PPL.cyclicOffset ring e e)
    rw [hOffset]
    cases n with
    | zero => exact e.elim0
    | succ m =>
        change (if (N (PPL.shiftLeft ring e 0)).l = true
          then some 0 else
            PPL.scanDistance
              (fun k => PPL.shiftLeft ring e k)
              (fun i => (N i).l) m 1) = some 0
        have hZero : PPL.shiftLeft ring e 0 = e := by
          apply Fin.ext
          change (e.val + Nat.succ m - 0 % Nat.succ m) %
            Nat.succ m = e.val
          simp only [Nat.zero_mod, Nat.sub_zero,
            Nat.add_mod_right, Nat.mod_eq_of_lt e.isLt]
        rw [hZero, hLeader]
        rfl

/-- A dying quiet unshielded responder immediately after an OLD
leader is preceded, after E, by a protected quiet leader at e.
This covers BOTH ready emission and an OLD leader-hosted LIVE. -/
theorem grantDrainWeakDeathOldLeaderFront
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e p : Fin n)
    (hP : PPlus ring s.native)
    (hEdge : ring.rightNeighbor e = p)
    (hSourceLeader : (s.native e).l = true)
    (hVictimLeader : (s.native p).l = true)
    (hUnshielded : (s.native p).sh = false)
    (hQuiet : (s.native p).sg = false)
    (hDeath : (nativeE ring s.native e p).l = false) :
    (s.native e).l = true ∧
    0 < PPL.cyclicOffset ring e p ∧
    GrantDrainMarksNearestArc ring (nativeE ring s.native e) e p ∧
    GrantDrainMarksZeroOffsetArc ring (nativeE ring s.native e) e p ∧
    (nativeE ring s.native e e).sh = true := by
  have hYLeader :
      (s.native (ring.rightNeighbor e)).l = true := by
    rw [hEdge]
    exact hVictimLeader
  have hYShield :
      (s.native (ring.rightNeighbor e)).sh = false := by
    rw [hEdge]
    exact hUnshielded
  have hYQuiet :
      (s.native (ring.rightNeighbor e)).sg = false := by
    rw [hEdge]
    exact hQuiet
  have hYDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false := by
    rw [hEdge]
    exact hDeath
  have hEffective :=
    GrantDrainEntrance.grantDrainEntranceDeathEffectiveSource
      ring (by omega : 2 ≤ n)
      s.native e hYLeader hYDeath
  have hTriple :
      (nativeE ring s.native e e).l = true ∧
      (nativeE ring s.native e e).sh = true ∧
      (nativeE ring s.native e e).sg = false := by
    rcases hEffective with hReady | hLive
    · have hPair :=
        grantDrainWeakDeathReadyPairProtected
          (s.native e) (s.native (ring.rightNeighbor e))
          hReady.1 hReady.2 hYLeader hYShield hYQuiet
      rw [grantDrainMarksNativeESource]
      exact ⟨hPair.1, hPair.2.1, hPair.2.2.1⟩
    · have hSafe :=
        GrantDrainShared.sharedPaperLiveProtectedSource
          ring s.native e e hP
          (grantDrainWeakDeathSelfLeaderSector
            ring s.native e hSourceLeader) hLive
      rw [grantDrainMarksNativeESource]
      simp [certLiteralEPair, certFinThree,
        hSourceLeader, hSafe.1, hSafe.2,
        hLive, hYLeader, hYShield, hYQuiet]
  have hRight : PPL.shiftRight ring e 1 =
      ring.rightNeighbor e := by
    apply Fin.ext
    rfl
  have hOffset : PPL.cyclicOffset ring e p = 1 := by
    rw [←hEdge, ←hRight]
    exact grantDrainWeakDeathOffsetShiftRight
      ring e 1 (by omega)
  refine ⟨hSourceLeader, ?_, ?_, ?_, hTriple.2.1⟩
  · rw [hOffset]
    omega
  · refine ⟨by rw [hOffset]; omega, hTriple.1, ?_⟩
    intro k hk hlt
    rw [hOffset] at hlt
    omega
  · intro k hk
    rw [hOffset] at hk
    have hkZero : k = 0 := by omega
    subst k
    rw [grantDrainWeakDeathShiftRightZero ring e]
    exact hTriple.2.2

/-- For an OLD follower killing the weak source, PPlus forces an
OLD LIVE at e. Its OLD nearest leader q is shielded and has a
zero-signal corridor to e. The fatal E row appends the now-empty,
signal-zero source e, giving the protected post-E arc q..p. -/
theorem grantDrainWeakDeathOldFollowerFront
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e p : Fin n)
    (hP : PPlus ring s.native)
    (hEdge : ring.rightNeighbor e = p)
    (hSourceFollower : (s.native e).l = false)
    (hVictimLeader : (s.native p).l = true)
    (hUnshielded : (s.native p).sh = false)
    (hQuiet : (s.native p).sg = false)
    (hDeath : (nativeE ring s.native e p).l = false) :
    ∃ q : Fin n,
      (s.native q).l = true ∧
      0 < PPL.cyclicOffset ring q p ∧
      GrantDrainMarksNearestArc ring (nativeE ring s.native e) q p ∧
      GrantDrainMarksZeroOffsetArc ring (nativeE ring s.native e) q p ∧
      (nativeE ring s.native e q).sh = true := by
  have hYLeader :
      (s.native (ring.rightNeighbor e)).l = true := by
    rw [hEdge]
    exact hVictimLeader
  have hYShield :
      (s.native (ring.rightNeighbor e)).sh = false := by
    rw [hEdge]
    exact hUnshielded
  have hYQuiet :
      (s.native (ring.rightNeighbor e)).sg = false := by
    rw [hEdge]
    exact hQuiet
  have hYDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false := by
    rw [hEdge]
    exact hDeath
  have hLive : LiveBullet s.native e :=
    grantDrainWeakDeathFollowerMustBeLive
      ring hn s.native e hSourceFollower hYLeader hYDeath
  have hStrong :
      grantDrainLedgerStrongLock ring s e = true :=
    GrantDrainEntrance.grantDrainEntranceLiveStrongLock
      ring s e hP hLive hSourceFollower
  obtain ⟨q, hOldNearest, hOldZero, hOldShield⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring s e hP hSourceFollower hStrong
  have hNotP : q ≠ p := by
    intro h
    rw [h, hUnshielded] at hOldShield
    cases hOldShield
  have hRightOffset :=
    grantDrainMarksNeighborOfOffset ring q e
  have hAdvance :
      PPL.cyclicOffset ring q e + 1 < n := by
    have hLt :=
      GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring q e
    by_cases hEnd : PPL.cyclicOffset ring q e + 1 = n
    · have hEqual : p = q := by
        calc
          p = ring.rightNeighbor e := hEdge.symm
          _ = PPL.shiftRight ring q
              (PPL.cyclicOffset ring q e + 1) :=
                hRightOffset
          _ = PPL.shiftRight ring q n := by rw [hEnd]
          _ = q := grantDrainMarksFullRotation ring q
      exact False.elim (hNotP hEqual.symm)
    · omega
  have hOffsetP :
      PPL.cyclicOffset ring q p =
        PPL.cyclicOffset ring q e + 1 := by
    rw [←hEdge, hRightOffset]
    exact grantDrainWeakDeathOffsetShiftRight ring q
      (PPL.cyclicOffset ring q e + 1) hAdvance
  have hFrame : ∀ k : Nat,
      k < PPL.cyclicOffset ring q e →
      nativeE ring s.native e (PPL.shiftRight ring q k) =
        s.native (PPL.shiftRight ring q k) := by
    intro k hk
    have hkN : k < n := Nat.lt_trans hk
      (GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring q e)
    have hNotE : PPL.shiftRight ring q k ≠ e := by
      intro hEq
      have ho := congrArg (PPL.cyclicOffset ring q) hEq
      rw [grantDrainWeakDeathOffsetShiftRight ring q k hkN] at ho
      omega
    have hNotP : PPL.shiftRight ring q k ≠ p := by
      intro hEq
      have ho := congrArg (PPL.cyclicOffset ring q) hEq
      rw [grantDrainWeakDeathOffsetShiftRight ring q k hkN,
        hOffsetP] at ho
      omega
    have hNotY :
        PPL.shiftRight ring q k ≠ ring.rightNeighbor e := by
      rw [hEdge]
      exact hNotP
    simp [nativeE, hNotE, hNotY]
  have hELeader :
      (nativeE ring s.native e e).l = false := by
    rw [grantDrainMarksNativeESource,
      grantDrainMarksOutgoingSourceLeaderNative]
    exact hSourceFollower
  have hESignal :
      (nativeE ring s.native e e).sg = false := by
    have hOldSignal :=
      grantDrainDeathLiveOwnSignalZero ring s e hP hLive
    have hPairDeath :
        (certLiteralEPair
          (s.native e) (s.native (ring.rightNeighbor e))).2.l =
            false :=
      (grantDrainWeakSourceQuietDeathPair
        (s.native e) (s.native (ring.rightNeighbor e))
        hLive hYLeader hYShield hYQuiet).2.1
    have hLiteral :=
      (GrantDrainEntrance.grantDrainEntranceLiteralEDeathSignalsZero
        (s.native e) (s.native (ring.rightNeighbor e))
        hYLeader (fun _ => hOldSignal) hPairDeath).1
    rw [grantDrainMarksNativeESource]
    exact hLiteral
  have hQFrame :
      nativeE ring s.native e q = s.native q := by
    have hf := hFrame 0 hOldNearest.1
    rw [grantDrainWeakDeathShiftRightZero ring q] at hf
    exact hf
  have hQLeader : (nativeE ring s.native e q).l =
      true := by
    rw [hQFrame]
    exact hOldNearest.2.1
  have hQShield : (nativeE ring s.native e q).sh =
      true := by
    rw [hQFrame]
    exact hOldShield
  have hFront :
      GrantDrainMarksNearestArc ring
        (nativeE ring s.native e) q p := by
    refine ⟨by rw [hOffsetP]; omega, hQLeader, ?_⟩
    intro k hk hlt
    rw [hOffsetP] at hlt
    by_cases hOld : k < PPL.cyclicOffset ring q e
    · rw [hFrame k hOld]
      exact hOldNearest.2.2 k hk hOld
    · have hAt : k = PPL.cyclicOffset ring q e := by omega
      rw [hAt, grantDrainMarksArcShiftRightOffset ring q e]
      exact hELeader
  have hFrontZero :
      GrantDrainMarksZeroOffsetArc ring
        (nativeE ring s.native e) q p := by
    intro k hk
    rw [hOffsetP] at hk
    by_cases hOld : k < PPL.cyclicOffset ring q e
    · rw [hFrame k hOld]
      exact hOldZero k hOld
    · have hAt : k = PPL.cyclicOffset ring q e := by omega
      rw [hAt, grantDrainMarksArcShiftRightOffset ring q e]
      exact hESignal
  exact ⟨q, hOldNearest.2.1,
    by rw [hOffsetP]; omega,
    hFront, hFrontZero, hQShield⟩

/-- The one-edge fatal weak-source front-arc theorem, independent
of scratch, grants and requests. It splits on the OLD initiator's
leader bit: ready/leader-hosted LIVE or peaceful follower LIVE.
Both branches return an OLD leader q strictly behind the victim,
a post-native-E nearest zero arc q..p, and a protected q. -/
theorem grantDrainWeakDeathFrontRootHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e p : Fin n)
    (hP : PPlus ring s.native)
    (hEdge : ring.rightNeighbor e = p)
    (hVictimLeader : (s.native p).l = true)
    (hUnshielded : (s.native p).sh = false)
    (hQuiet : (s.native p).sg = false)
    (hDeath : (nativeE ring s.native e p).l = false) :
    ∃ q : Fin n,
      (s.native q).l = true ∧
      0 < PPL.cyclicOffset ring q p ∧
      GrantDrainMarksNearestArc ring (nativeE ring s.native e) q p ∧
      GrantDrainMarksZeroOffsetArc ring (nativeE ring s.native e) q p ∧
      (nativeE ring s.native e q).sh = true := by
  cases hE : (s.native e).l with
  | true =>
      refine ⟨e, ?_⟩
      exact grantDrainWeakDeathOldLeaderFront
        ring hn s e p hP hEdge hE
        hVictimLeader hUnshielded hQuiet hDeath
  | false =>
      exact grantDrainWeakDeathOldFollowerFront
        ring hn s e p hP hEdge hE
        hVictimLeader hUnshielded hQuiet hDeath

/-- Every strictly positive offset inside the old weak [p,g)
corridor is outside the two selected E endpoints, when E kills
the old source leader p on incoming edge e -> p. -/
theorem grantDrainWeakDeathRightInteriorEFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (hEdge : ring.rightNeighbor e = p)
    (k : Nat) (hk : 0 < k)
    (hklt : k < PPL.cyclicOffset ring p g) :
    nativeE ring s.native e (PPL.shiftRight ring p k) =
      s.native (PPL.shiftRight ring p k) := by
  have hNotX :
      PPL.shiftRight ring p k ≠ e :=
    grantDrainMarksIncomingSourceArcExceptRoot
      (by omega : 3 ≤ n) ring p g e hEdge k hklt
  have hZeroOffset :
      PPL.cyclicOffset ring p p = 0 := by
    change (p.val + n - p.val) % n = 0
    have hs : p.val + n - p.val = n := by omega
    rw [hs, Nat.mod_self]
  have hkN : k < n := Nat.lt_trans hklt
    (GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring p g)
  have hNotY :
      PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
    rw [hEdge]
    intro hEq
    have ho := congrArg (PPL.cyclicOffset ring p) hEq
    rw [grantDrainWeakDeathOffsetShiftRight ring p k hkN,
      hZeroOffset] at ho
    omega
  simp [nativeE, hNotX, hNotY]

/-- Native E preserves every STRICTLY INTERIOR old follower
of the weak zero corridor, including cyclic wraparound. -/
theorem grantDrainWeakDeathRightFollowersAfterE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (hEdge : ring.rightNeighbor e = p)
    (hOldRight : GrantDrainMarksNearestArc ring s.native p g) :
    ∀ k : Nat, 0 < k →
      k < PPL.cyclicOffset ring p g →
      (nativeE ring s.native e
        (PPL.shiftRight ring p k)).l = false := by
  intro k hk hklt
  rw [grantDrainWeakDeathRightInteriorEFrame
    ring hn s e p g hEdge k hk hklt]
  exact hOldRight.2.2 k hk hklt

/-- The exact quiet-leader responder row zeros p itself.
Every other old corridor site is outside the E pair, hence
the entire weak [p,g) zero arc survives native E. -/
theorem grantDrainWeakDeathRightZeroAfterE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (hEdge : ring.rightNeighbor e = p)
    (hOldLeader : (s.native p).l = true)
    (hOldQuiet : (s.native p).sg = false)
    (hOldZero : GrantDrainMarksZeroOffsetArc ring s.native p g) :
    GrantDrainMarksZeroOffsetArc ring
      (nativeE ring s.native e) p g := by
  have hYLeader :
      (s.native (ring.rightNeighbor e)).l = true := by
    rw [hEdge]
    exact hOldLeader
  have hYQuiet :
      (s.native (ring.rightNeighbor e)).sg = false := by
    rw [hEdge]
    exact hOldQuiet
  have hPair :=
    GrantDrainEntrance.grantDrainEntranceLiteralEQuietLeaderRow
      (s.native e) (s.native (ring.rightNeighbor e))
      hYLeader hYQuiet
  have hDifferent :
      ring.rightNeighbor e ≠ e :=
    grantDrainMarksNeighborDistinct (by omega : 3 ≤ n) ring e
  have hPZero : (nativeE ring s.native e p).sg = false := by
    rw [←hEdge]
    simpa [nativeE, hDifferent] using hPair.2.2.2
  intro k hk
  by_cases hZero : k = 0
  · subst k
    rw [grantDrainWeakDeathShiftRightZero ring p]
    exact hPZero
  · have hPositive : 0 < k := by omega
    rw [grantDrainWeakDeathRightInteriorEFrame
      ring hn s e p g hEdge k hPositive hk]
    exact hOldZero k hk

/-- From a genuine old weak LockBudget identity, a nominated
source-death edge and PPlus, assemble the old right arc, post-E
front arc, post-E right arc, and post-FIRE closer-root alternative.
The same argument proves the live grant host is outside this
death edge: the root-to-host splice is shorter than the ring. -/
theorem grantDrainWeakDeathProtectedArcAndHostAway
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hEdge : ring.rightNeighbor e = p)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))
    (hDeath : (nativeE ring s.native e p).l = false) :
    (∃ root : Fin n,
      GrantDrainMarksNearestArc ring
        (grantDrainStep ring fresh update s e).native root g ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainStep ring fresh update s e).native root g ∧
      ((grantDrainStep ring fresh update s e).native root).sh =
        true) ∧
    g ≠ e ∧ g ≠ ring.rightNeighbor e := by
  obtain ⟨_, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨_, hOldFollower, hWeakLock, _⟩ := hWeakCase
  have hOldRight :=
    grantDrainWeakDeathOldRightArc
      ring s p g hP hOldFollower hWeakLock hSource
  have hOldPLeader : (s.native p).l = true :=
    hOldRight.1.2.1
  have hRawWeak :
      (grantDrainLedgerCorridor ring s g &&
        !(s.native (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))).sh) =
        true := hWeakLock
  have hNegShield :=
    (grantDrainWeakDeathAndTrue hRawWeak).2
  have hNotShield : (!(s.native p).sh) = true := by
    rw [hSource]
    exact hNegShield
  have hOldPUnshield : (s.native p).sh = false := by
    cases hh : (s.native p).sh with
    | false => rfl
    | true => simp [hh] at hNotShield
  have hOldPQuiet : (s.native p).sg = false := by
    have hZeroAt := hOldRight.2 0 hOldRight.1.1
    rw [grantDrainWeakDeathShiftRightZero ring p] at hZeroAt
    exact hZeroAt
  obtain ⟨q, hOldQLeader, hBehind, hFront, hFrontZero,
    hShield⟩ :=
    grantDrainWeakDeathFrontRootHolds
      ring hn s e p hP hEdge hOldPLeader
      hOldPUnshield hOldPQuiet hDeath
  have hRightFollowers :=
    grantDrainWeakDeathRightFollowersAfterE
      ring hn s e p g hEdge hOldRight.1
  have hRightZero :=
    grantDrainWeakDeathRightZeroAfterE
      ring hn s e p g hEdge hOldPLeader
      hOldPQuiet hOldRight.2
  have hPostArc :=
    grantDrainWeakDeathProtectedArcOfFramedPieces
      ring hn fresh update s e q p g
      hEdge hOldQLeader hBehind hOldRight.1 hOldFollower
      hFront hFrontZero hDeath hRightFollowers
      hRightZero hShield
  have hNoWrap :=
    grantDrainWeakDeathArcNonoverlap
      ring s.native q p g hOldQLeader hBehind
      hOldRight.1 hOldFollower
  have hSites :=
    grantDrainWeakDeathSpliceBirthSites ring hn e q p g
      hEdge hBehind hOldRight.1.1 hNoWrap
  have hNotX : g ≠ e := by
    obtain ⟨j, hXSite, hInside⟩ := hSites.1
    intro hEq
    have hOffsetEq :=
      congrArg (PPL.cyclicOffset ring q) hEq
    have hjBound : j < n :=
      Nat.lt_trans hInside
        (GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring q g)
    rw [hXSite,
      grantDrainWeakDeathOffsetShiftRight ring q j hjBound]
      at hOffsetEq
    omega
  have hNotY : g ≠ ring.rightNeighbor e := by
    intro hEq
    have hPG : p = g := hEdge.symm.trans hEq.symm
    rw [hPG, hOldFollower] at hOldPLeader
    cases hOldPLeader
  exact ⟨hPostArc, hNotX, hNotY⟩

/-- Unconditional canonical post-step protected nearest zero arc
for the actual DEATH OF THE OLD WEAK SOURCE. This is the requested
weak-source-death geometry, with the source-identity equation
spelled out as an actual edge fact. -/
theorem grantDrainWeakDeathProtectedArcHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hEdge : ring.rightNeighbor e = p)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))
    (hDeath : (nativeE ring s.native e p).l = false) :
    ∃ root : Fin n,
      GrantDrainMarksNearestArc ring
        (grantDrainStep ring fresh update s e).native root g ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainStep ring fresh update s e).native root g ∧
      ((grantDrainStep ring fresh update s e).native root).sh =
        true := by
  exact (grantDrainWeakDeathProtectedArcAndHostAway
    ring hn fresh update s e p g label
    hP hInv hHost hWeak hEdge hSource hDeath).1

/-- The completed source-death LockBudget step on the literal
grantDrainStep, including F0/F1/F2 birth, cyclic wraparound,
protected-root replacement, and 2n-to-n quota reduction. -/
theorem grantDrainWeakDeathLockBudgetStepHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hEdge : ring.rightNeighbor e = p)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))
    (hDeath : (nativeE ring s.native e p).l = false) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨hPostArc, hNotX, hNotY⟩ :=
    grantDrainWeakDeathProtectedArcAndHostAway
      ring hn fresh update s e p g label
      hP hInv hHost hWeak hEdge hSource hDeath
  exact (grantDrainLockBudgetWeakOffPairOfProtectedArc
    ring hn fresh update s e g label
    hInv hHost hWeak hNotX hNotY hPostArc).2

end L3

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
The requested post-FIRE nearest-leader lemma (1) is false.
PPlus and NoBadLive constrain native fields, not the old request
and grant bits. A permitted F0 birth at the follower killer e
introduces a NEW nearest leader strictly between the old root p
and the stationary clean DUMMY b.

The literal n=5 row below has:
 p=0: leader, shield=1, empty, signal=0;
   1: empty follower, signal=0;
 e=2: LIVE follower, signal=0, request=grant=1;
 y=3: unshielded quiet leader, empty;
 b=4: clean follower-hosted DUMMY, signal=0.
The edge is e=2 -> y=3.  Native E kills leader 3.
The old F0 grant births a leader at 2.  The DUMMY at 4 remains
clean, but its post-step nearest leader is 2, not the old p=0.
-/

private def grantDrainDummyMergeFiveRing : DirectedRing 5 :=
  ⟨by decide⟩

private def grantDrainDummyMergeFiveNative
    (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (0 : Fin 3), sh := true, sg := false }
  else if i.val == 2 then
    { l := false, b := (2 : Fin 3), sh := false, sg := false }
  else if i.val == 3 then
    { l := true, b := (0 : Fin 3), sh := false, sg := false }
  else if i.val == 4 then
    { l := false, b := (1 : Fin 3), sh := false, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

private def grantDrainDummyMergeFiveState :
    GrantDrainState 5 Unit :=
  { native := grantDrainDummyMergeFiveNative
    request := fun i => i.val == 2
    grant := fun i => i.val == 2
    scratch := ()
    history := [] }

private def grantDrainDummyMergeFiveAfter :
    GrantDrainState 5 Unit :=
  grantDrainStep grantDrainDummyMergeFiveRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainDummyMergeFiveState (2 : Fin 5)

/-- The sole old LIVE is the killer at site 2. -/
private theorem grantDrainDummyMergeFiveOnlyLive :
    ∀ v : Fin 5,
      LiveBullet grantDrainDummyMergeFiveNative v →
        v = (2 : Fin 5) := by
  unfold LiveBullet grantDrainDummyMergeFiveNative
  decide +kernel

/-- PPlus includes the killer's peaceful, shielded zero trail
from site 0 through sites 1 and 2. -/
private theorem grantDrainDummyMergeFiveProtected :
    PPlus grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState.native := by
  unfold grantDrainDummyMergeFiveRing
    grantDrainDummyMergeFiveState
    grantDrainDummyMergeFiveNative
  decide +kernel

/-- The sole LIVE at 2 is the first bullet in its old sector. -/
private theorem grantDrainDummyMergeFiveNoBad :
    GrantDrainEntranceNoBadLive grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState := by
  intro v hBad
  have hv : v = (2 : Fin 5) :=
    grantDrainDummyMergeFiveOnlyLive v hBad.1
  subst v
  have hNotBad :
      ¬ SharedPaperNonleftmostLiveExact
        grantDrainDummyMergeFiveRing
        grantDrainDummyMergeFiveState.native
        (2 : Fin 5) := by
    unfold SharedPaperNonleftmostLiveExact
      grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState
      grantDrainDummyMergeFiveNative
    decide +kernel
  exact hNotBad hBad

/-- The killer's nearest OLD leader is 0. -/
private theorem grantDrainDummyMergeFiveKillerSector :
    leaderSector grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState.native
      (0 : Fin 5) (2 : Fin 5) := by
  unfold leaderSector grantDrainDummyMergeFiveRing
    grantDrainDummyMergeFiveState
    grantDrainDummyMergeFiveNative
  decide +kernel

/-- The stationary DUMMY at 4 is in leader 3's OLD sector. -/
private theorem grantDrainDummyMergeFiveVictimSector :
    leaderSector grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState.native
      (3 : Fin 5) (4 : Fin 5) := by
  unfold leaderSector grantDrainDummyMergeFiveRing
    grantDrainDummyMergeFiveState
    grantDrainDummyMergeFiveNative
  decide +kernel

private theorem grantDrainDummyMergeFiveOldClean :
    GrantDrainEntranceBulletCleanAt grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState.native (4 : Fin 5) := by
  unfold GrantDrainEntranceBulletCleanAt
    grantDrainDummyMergeFiveRing
    grantDrainDummyMergeFiveState
    grantDrainDummyMergeFiveNative
  decide +kernel

/-- E really deletes the unshielded leader at responder 3. -/
private theorem grantDrainDummyMergeFiveDeath :
    (nativeE grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState.native
      (2 : Fin 5) (3 : Fin 5)).l = false := by
  unfold grantDrainDummyMergeFiveRing
    grantDrainDummyMergeFiveState
    grantDrainDummyMergeFiveNative
    nativeE certLiteralEPair certFinThree
  decide +kernel

/-- The old tokens select F0, not an assumed no-FIRE edge. -/
private theorem grantDrainDummyMergeFiveSelect :
    grantDrainSelect grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState (2 : Fin 5) =
        .leftLocal := by
  unfold grantDrainSelect grantDrainEligible
    grantDrainDummyMergeFiveRing
    grantDrainDummyMergeFiveState
    grantDrainDummyMergeFiveNative
    nativeE certLiteralEPair certFinThree
  decide +kernel

/-- The actual physical E+F0 step creates a leader at source 2. -/
private theorem grantDrainDummyMergeFiveNewLeader :
    (grantDrainDummyMergeFiveAfter.native
      (2 : Fin 5)).l = true := by
  change (grantDrainNativeNext grantDrainDummyMergeFiveRing
    grantDrainDummyMergeFiveState
    (2 : Fin 5) (2 : Fin 5)).l = true
  simp [grantDrainNativeNext, grantDrainDummyMergeFiveSelect,
    canonicalBirth, firedNative]

/-- The claimed OLD-root-to-b post-step nearest arc is FALSE:
the new leader at offset 2 interrupts the arc from 0 to 4. -/
theorem grantDrainDummyMergeFiveOldRootNotNearest :
    ¬ GrantDrainMarksNearestArc grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveAfter.native
      (0 : Fin 5) (4 : Fin 5) := by
  have hOffset :
      PPL.cyclicOffset grantDrainDummyMergeFiveRing
        (0 : Fin 5) (4 : Fin 5) = 4 := by
    change (4 + 5 - 0) % 5 = 4
    decide
  have hShift :
      PPL.shiftRight grantDrainDummyMergeFiveRing
        (0 : Fin 5) 2 = (2 : Fin 5) := by
    apply Fin.ext
    change (0 + 2) % 5 = 2
    decide
  intro hArc
  have hFollower :
      (grantDrainDummyMergeFiveAfter.native
        (PPL.shiftRight grantDrainDummyMergeFiveRing
          (0 : Fin 5) 2)).l = false :=
    hArc.2.2 2 (by decide : 0 < (2 : Nat)) (by rw [hOffset]; decide)
  rw [hShift, grantDrainDummyMergeFiveNewLeader] at hFollower
  cases hFollower

/-- The new first leader is source 2, so the defect is in the
proposed fixed-root intermediate, not in DUMMY cleanliness. -/
private theorem grantDrainDummyMergeFiveNewClean :
    GrantDrainEntranceBulletCleanAt grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveAfter.native (4 : Fin 5) := by
  unfold GrantDrainEntranceBulletCleanAt
    grantDrainDummyMergeFiveRing
    grantDrainDummyMergeFiveAfter
    grantDrainDummyMergeFiveState
    grantDrainDummyMergeFiveNative
    grantDrainStep grantDrainNativeNext grantDrainSelect
    grantDrainEligible nativeE certLiteralEPair certFinThree
    canonicalBirth firedNative
  decide +kernel

/-- A complete five-site counterrow to step (1), under BOTH
requested hypotheses, with the actual death, clean DUMMY,
source FIRE, and false post-FIRE nearest arc all witnessed. -/
theorem grantDrainDummyMergeFiveCounterexample :
    PPlus grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState.native ∧
    GrantDrainEntranceNoBadLive grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState ∧
    (grantDrainDummyMergeFiveState.native (2 : Fin 5)).l =
      false ∧
    (grantDrainDummyMergeFiveState.native (3 : Fin 5)).l =
      true ∧
    (grantDrainDummyMergeFiveState.native (4 : Fin 5)).l =
      false ∧
    (grantDrainDummyMergeFiveState.native (4 : Fin 5)).b =
      (1 : Fin 3) ∧
    leaderSector grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState.native
      (0 : Fin 5) (2 : Fin 5) ∧
    leaderSector grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState.native
      (3 : Fin 5) (4 : Fin 5) ∧
    GrantDrainEntranceBulletCleanAt grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState.native (4 : Fin 5) ∧
    (nativeE grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState.native
      (2 : Fin 5) (3 : Fin 5)).l = false ∧
    grantDrainSelect grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveState (2 : Fin 5) =
        .leftLocal ∧
    (grantDrainDummyMergeFiveAfter.native (2 : Fin 5)).l =
      true ∧
    ¬ GrantDrainMarksNearestArc grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveAfter.native
      (0 : Fin 5) (4 : Fin 5) ∧
    GrantDrainEntranceBulletCleanAt grantDrainDummyMergeFiveRing
      grantDrainDummyMergeFiveAfter.native (4 : Fin 5) := by
  have hFollower :
      (grantDrainDummyMergeFiveState.native
        (2 : Fin 5)).l = false := by
    unfold grantDrainDummyMergeFiveState
      grantDrainDummyMergeFiveNative
    decide +kernel
  have hLeader :
      (grantDrainDummyMergeFiveState.native
        (3 : Fin 5)).l = true := by
    unfold grantDrainDummyMergeFiveState
      grantDrainDummyMergeFiveNative
    decide +kernel
  have hBFollower :
      (grantDrainDummyMergeFiveState.native
        (4 : Fin 5)).l = false := by
    unfold grantDrainDummyMergeFiveState
      grantDrainDummyMergeFiveNative
    decide +kernel
  have hBDummy :
      (grantDrainDummyMergeFiveState.native
        (4 : Fin 5)).b = (1 : Fin 3) := by
    unfold grantDrainDummyMergeFiveState
      grantDrainDummyMergeFiveNative
    decide +kernel
  exact ⟨grantDrainDummyMergeFiveProtected,
    grantDrainDummyMergeFiveNoBad,
    hFollower, hLeader, hBFollower, hBDummy,
    grantDrainDummyMergeFiveKillerSector,
    grantDrainDummyMergeFiveVictimSector,
    grantDrainDummyMergeFiveOldClean,
    grantDrainDummyMergeFiveDeath,
    grantDrainDummyMergeFiveSelect,
    grantDrainDummyMergeFiveNewLeader,
    grantDrainDummyMergeFiveOldRootNotNearest,
    grantDrainDummyMergeFiveNewClean⟩

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
The no-FIRE, old-killer-root nearest/zero splice.
The remaining earliest-bullet transport and the F0/F1/F2
branches are not asserted by these declarations.
-/

/-- The clockwise offset of a site from itself is zero. -/
theorem grantDrainDummyArcOffsetSelf
    {n : Nat} (ring : DirectedRing n) (p : Fin n) :
    PPL.cyclicOffset ring p p = 0 := by
  unfold PPL.cyclicOffset
  have hs : p.val + n - p.val = n := by omega
  rw [hs, Nat.mod_self]

/-- The existing nearest-leader scan directly provides the
strict clockwise leader-free arc for a follower. -/
theorem grantDrainDummyFollowerSectorNearestArc
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p b : Fin n)
    (hFollower : (N b).l = false)
    (hSector : leaderSector ring N p b) :
    GrantDrainMarksNearestArc ring N p b := by
  have hScan :
      PPL.scanDistance
        (fun k : Nat => PPL.shiftLeft ring b k)
        (fun i : Fin n => (N i).l) n 0 =
          some (PPL.cyclicOffset ring p b) := hSector.2
  have hInfo :=
    grantDrainEntranceScanSomeInfo
      (fun k : Nat => PPL.shiftLeft ring b k)
      (fun i : Fin n => (N i).l)
      n 0 (PPL.cyclicOffset ring p b) hScan
  have hZeroShift : PPL.shiftLeft ring b 0 = b := by
    apply Fin.ext
    change (b.val + n - 0 % n) % n = b.val
    simp [Nat.mod_eq_of_lt b.isLt]
  have hPositive : 0 < PPL.cyclicOffset ring p b := by
    by_cases hd : PPL.cyclicOffset ring p b = 0
    · have hAt :
          (N (PPL.shiftLeft ring b 0)).l = true := by
        simpa only [hd] using hInfo.2.2.1
      rw [hZeroShift, hFollower] at hAt
      cases hAt
    · omega
  refine ⟨hPositive, hSector.1, ?_⟩
  intro k hkPos hkLt
  have hBound : PPL.cyclicOffset ring p b < n :=
    grantDrainEntranceArcOffsetLt ring p b
  have hShift :=
    grantDrainMarksArcShiftLeftRight
      ring p (PPL.cyclicOffset ring p b)
      (PPL.cyclicOffset ring p b - k)
      (by omega) hBound
  rw [grantDrainMarksArcShiftRightOffset ring p b] at hShift
  have hSub :
      PPL.cyclicOffset ring p b -
        (PPL.cyclicOffset ring p b - k) = k := by omega
  rw [hSub] at hShift
  have hMiss :=
    hInfo.2.2.2 (PPL.cyclicOffset ring p b - k)
      (by omega) (by omega)
  rw [hShift] at hMiss
  exact hMiss

/-- On a native E edge, the source retains its leader bit,
and all other sites except the responder are framed. -/
theorem grantDrainDummyNativeELeaderAwayResponder
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e i : Fin n)
    (hi : i ≠ ring.rightNeighbor e) :
    (nativeE ring N e i).l = (N i).l := by
  by_cases hx : i = e
  · subst i
    simpa [nativeE] using
      grantDrainEntranceLiteralESourceLeaderFixed
        (N e) (N (ring.rightNeighbor e))
  · have hFrame :=
      grantDrainEntranceNativeEFrame ring N e i hx hi
    exact congrArg CertNative.l hFrame

/-- In the fatal follower-LIVE case, with an OLD clean follower
DUMMY in the deleted leader's sector, the exact NO-FIRE
post-step nearest leader remains the killer's OLD root p.
The accompanying half-open zero-signal arc is also proved,
with only PPlus/NoBadLive, not I or ILocal. -/
theorem grantDrainDummyFatalFollowerNoFireNearestZero
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hEFollower : (s.native e).l = false)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = false)
    (hBFollower : (s.native b).l = false)
    (hNotE : b ≠ e)
    (hCleanB : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hSectorE : leaderSector ring s.native p e)
    (hSectorB :
      leaderSector ring s.native (ring.rightNeighbor e) b)
    (hNoFire : grantDrainSelect ring s e = .none) :
    GrantDrainMarksNearestArc ring
      (grantDrainStep ring fresh update s e).native p b ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainStep ring fresh update s e).native p b := by
  have hOldFront :=
    grantDrainDummyFollowerSectorNearestArc
      ring s.native p e hEFollower hSectorE
  have hOldTail :=
    grantDrainDummyFollowerSectorNearestArc
      ring s.native (ring.rightNeighbor e) b
      hBFollower hSectorB
  have hpNotY : p ≠ ring.rightNeighbor e := by
    intro hp
    have hAtY :
        leaderSector ring s.native (ring.rightNeighbor e) e := by
      rw [← hp]
      exact hSectorE
    exact grantDrainDummyFatalFollowerCleanDifferentSector
      ring hn s.native e b (ring.rightNeighbor e)
      hEFollower hYLeader hDeath hNoBad hNotE hCleanB
      hAtY hSectorB
  have hYShift :
      PPL.shiftRight ring p
        (PPL.cyclicOffset ring p e + 1) =
          ring.rightNeighbor e := by
    calc
      PPL.shiftRight ring p
          (PPL.cyclicOffset ring p e + 1) =
        ring.rightNeighbor
          (PPL.shiftRight ring p (PPL.cyclicOffset ring p e)) :=
          (grantDrainEntranceAheadShiftSucc ring p
            (PPL.cyclicOffset ring p e)).symm
      _ = ring.rightNeighbor e := by
        rw [grantDrainMarksArcShiftRightOffset ring p e]
  have hSuccBound :
      PPL.cyclicOffset ring p e + 1 < n := by
    by_cases hh : PPL.cyclicOffset ring p e + 1 < n
    · exact hh
    · have hEq : PPL.cyclicOffset ring p e + 1 = n := by
        have hd := grantDrainEntranceArcOffsetLt ring p e
        omega
      have hFull : PPL.shiftRight ring p n = p := by
        apply Fin.ext
        change (p.val + n) % n = p.val
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]
      have hpEq : p = ring.rightNeighbor e := by
        calc
          p = PPL.shiftRight ring p n := hFull.symm
          _ = PPL.shiftRight ring p
              (PPL.cyclicOffset ring p e + 1) := by rw [hEq]
          _ = ring.rightNeighbor e := hYShift
      exact False.elim (hpNotY hpEq)
  have hPY :
      PPL.cyclicOffset ring p (ring.rightNeighbor e) =
        PPL.cyclicOffset ring p e + 1 := by
    rw [← hYShift]
    exact grantDrainDummyRightOffset ring p
      (PPL.cyclicOffset ring p e + 1) hSuccBound
  have hPYPositive :
      0 < PPL.cyclicOffset ring p (ring.rightNeighbor e) := by
    rw [hPY]
    omega
  have hNoWrap :
      PPL.cyclicOffset ring p (ring.rightNeighbor e) +
        PPL.cyclicOffset ring (ring.rightNeighbor e) b < n :=
    grantDrainWeakDeathArcNonoverlap
      ring s.native p (ring.rightNeighbor e) b
      hOldFront.2.1 hPYPositive hOldTail hBFollower
  have hLive : LiveBullet s.native e :=
    L3.grantDrainWeakDeathFollowerMustBeLive
      ring hn s.native e hEFollower hYLeader hDeath
  have hCleanE : GrantDrainEntranceBulletCleanAt
      ring s.native e :=
    grantDrainDummyLiveCleanOfNoBad
      ring s.native hP hNoBad e hLive
  have hSourceOldZero : (s.native e).sg = false :=
    L3.grantDrainDeathLiveOwnSignalZero ring s e hP hLive
  have hTrailE : signalTrail ring s.native p e :=
    grantDrainDummyCleanTrailAtNearest
      ring s.native p e hCleanE hSectorE
  have hTrailB :
      signalTrail ring s.native (ring.rightNeighbor e) b :=
    grantDrainDummyCleanTrailAtNearest
      ring s.native (ring.rightNeighbor e) b hCleanB hSectorB
  have hEFront :
      GrantDrainMarksNearestArc ring
        (nativeE ring s.native e) p (ring.rightNeighbor e) := by
    refine ⟨hPYPositive, ?_, ?_⟩
    · rw [grantDrainDummyNativeELeaderAwayResponder
        ring s.native e p hpNotY]
      exact hOldFront.2.1
    · intro k hkPos hkLt
      have hkBound : k < n :=
        Nat.lt_trans hkLt
          (grantDrainEntranceArcOffsetLt ring p (ring.rightNeighbor e))
      have hNotY :
          PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
        intro hSite
        have hOffK :=
          grantDrainDummyRightOffset ring p k hkBound
        have hOffEq :=
          congrArg (PPL.cyclicOffset ring p) hSite
        rw [hOffK] at hOffEq
        omega
      rw [grantDrainDummyNativeELeaderAwayResponder
        ring s.native e (PPL.shiftRight ring p k) hNotY]
      have hkLe : k ≤ PPL.cyclicOffset ring p e := by
        rw [hPY] at hkLt
        omega
      by_cases hkAt : k = PPL.cyclicOffset ring p e
      · rw [hkAt, grantDrainMarksArcShiftRightOffset ring p e]
        exact hEFollower
      · exact hOldFront.2.2 k hkPos (by omega)
  have hEFrontZero :
      GrantDrainMarksZeroOffsetArc ring
        (nativeE ring s.native e) p (ring.rightNeighbor e) := by
    intro k hk
    have hkBound : k < n :=
      Nat.lt_trans hk
        (grantDrainEntranceArcOffsetLt ring p (ring.rightNeighbor e))
    have hkLe : k ≤ PPL.cyclicOffset ring p e := by
      rw [hPY] at hk
      omega
    have hOldZero :=
      hTrailE (⟨k, hkBound⟩ : Fin n) hkLe
    exact grantDrainDummyDeathEZeroBackward
      ring hn s.native e (PPL.shiftRight ring p k)
      hYLeader hDeath hSourceOldZero hOldZero
  have hERightFollower :
      ∀ k : Nat, 0 < k →
        k < PPL.cyclicOffset ring (ring.rightNeighbor e) b →
        (nativeE ring s.native e
          (PPL.shiftRight ring (ring.rightNeighbor e) k)).l =
          false := by
    intro k hkPos hkLt
    have hkBound : k < n :=
      Nat.lt_trans hkLt
        (grantDrainEntranceArcOffsetLt ring (ring.rightNeighbor e) b)
    have hNotY :
        PPL.shiftRight ring (ring.rightNeighbor e) k ≠
          ring.rightNeighbor e := by
      intro hSite
      have hOffK :=
        grantDrainDummyRightOffset ring (ring.rightNeighbor e) k
          hkBound
      have hOffEq :=
        congrArg (PPL.cyclicOffset ring (ring.rightNeighbor e)) hSite
      rw [hOffK, grantDrainDummyArcOffsetSelf
        ring (ring.rightNeighbor e)] at hOffEq
      omega
    rw [grantDrainDummyNativeELeaderAwayResponder
      ring s.native e
      (PPL.shiftRight ring (ring.rightNeighbor e) k) hNotY]
    exact hOldTail.2.2 k hkPos hkLt
  have hERightZero :
      GrantDrainMarksZeroOffsetArc ring
        (nativeE ring s.native e) (ring.rightNeighbor e) b := by
    intro k hk
    have hkBound : k < n :=
      Nat.lt_trans hk
        (grantDrainEntranceArcOffsetLt ring (ring.rightNeighbor e) b)
    have hOldZero :=
      hTrailB (⟨k, hkBound⟩ : Fin n) (Nat.le_of_lt hk)
    exact grantDrainDummyDeathEZeroBackward
      ring hn s.native e
      (PPL.shiftRight ring (ring.rightNeighbor e) k)
      hYLeader hDeath hSourceOldZero hOldZero
  have hEJoin :=
    grantDrainWeakDeathProtectedArcConcat
      ring (nativeE ring s.native e)
      p (ring.rightNeighbor e) b
      hEFront hEFrontZero hDeath hERightFollower hERightZero
      hOldTail.1 hNoWrap
  change
    GrantDrainMarksNearestArc ring
      (grantDrainNativeNext ring s e) p b ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s e) p b
  simpa [grantDrainNativeNext, hNoFire] using hEJoin

end L3.GrantDrainEntrance

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
PARTIAL result.

ONE-EDGE CASE BILL:
* strong -> strong: grantDrainLockBudgetStrongToStrong;
* weak -> strong: grantDrainLockBudgetWeakToStrongOfPhysical,
  with grantDrainWeakOffPairPromotesOfPostStrongLock;
* weak-source death: grantDrainWeakDeathLockBudgetStepHolds;
* weak -> weak: grantDrainLockBudgetWeakToWeakOfPhysicalProgress
  (its full physical/metric native inputs remain OPEN);
* terminal native-leader death:
  grantDrainLockBudgetTerminalLeaderDeathOfPhysical
  (its general post-token/strong-lock certificate remains OPEN);
* retired: grantDrainLedgerStep_retired_absorbing;
* other untouched/held/promoted marks still require a full
  case assembly.

The lemmas below establish that an actual .weak post-mark cannot
have an observed strong/terminal condition, and reduce the physical
weak-lock input to a zero-corridor and token-host certificate. They
do NOT assert grantDrainLockBudgetStepHolds or the unconditional
GrantDrainLedgerNoExhaustion, because those would require the
still-unproved transition geometry.
-/

/-- Both arguments' ranks are at most the rank of their join.
The existing source lemma only states the bound for the left
argument; the missing right argument is the one used below. -/
theorem grantDrainMarkRankRightLeJoin
    (a b : GrantDrainMark) :
    grantDrainMarkRank b ≤
      grantDrainMarkRank (grantDrainMarkJoin a b) := by
  cases a <;> cases b <;>
    simp [grantDrainMarkJoin, grantDrainMarkRank]

/-- Four-way mark promotion never hides a high-ranked observation.
In particular, if the final join is weak, its innermost post-step
observation is at most weak. -/
theorem grantDrainMarkNestedWeakRightRank
    (a b c d : GrantDrainMark)
    (h :
      grantDrainMarkJoin a
        (grantDrainMarkJoin b (grantDrainMarkJoin c d)) =
          .weak) :
    grantDrainMarkRank d ≤ 1 := by
  have hc := grantDrainMarkRankRightLeJoin c d
  have hb := grantDrainMarkRankRightLeJoin b
    (grantDrainMarkJoin c d)
  have ha := grantDrainMarkRankRightLeJoin a
    (grantDrainMarkJoin b (grantDrainMarkJoin c d))
  rw [h] at ha
  change
    grantDrainMarkRank
      (grantDrainMarkJoin b (grantDrainMarkJoin c d)) ≤ 1
    at ha
  omega

/-- Genuine canonical post-observation rank bound whenever the
persistent ghost mark remains weak. The old mark and both
coalescence contributions are included in the rank argument. -/
theorem grantDrainWeakNextObservedRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hWeakNext :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak) :
    grantDrainMarkRank
      (grantDrainLedgerObservedMark ring
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e label).host) ≤
      1 := by
  have hRaw : grantDrainMarkJoin label.mark
      (grantDrainMarkJoin
        (grantDrainLedgerObservedMark ring s label.host)
        (grantDrainMarkJoin
          (grantDrainLedgerCoalesceMark ring s e label.host
            (grantDrainLedgerHost ring fresh s e label.host))
          (grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerHost ring fresh s e label.host)))) =
        .weak := hWeakNext
  exact grantDrainMarkNestedWeakRightRank
    label.mark
    (grantDrainLedgerObservedMark ring s label.host)
    (grantDrainLedgerCoalesceMark ring s e label.host
      (grantDrainLedgerHost ring fresh s e label.host))
    (grantDrainLedgerObservedMark ring
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerHost ring fresh s e label.host))
    hRaw

/-- A surviving weak-marked label must be physically at a
FOLLOWER; otherwise the actual post observation is terminal,
and the source's monotone mark join cannot be weak. -/
theorem grantDrainWeakNextFollower
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e j : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hWeakNext :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    ((grantDrainStep ring fresh update s e).native j).l =
      false := by
  have hRank := grantDrainWeakNextObservedRank
    ring fresh update s e label hWeakNext
  rw [hHost] at hRank
  cases hLeader :
      ((grantDrainStep ring fresh update s e).native j).l with
  | false => rfl
  | true =>
      have hObserved :
          grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e) (some j) =
              .terminal := by
        cases hHeld :
            (grantDrainStep ring fresh update s e).request j &&
            (grantDrainStep ring fresh update s e).grant j <;>
          simp [grantDrainLedgerObservedMark, hHeld, hLeader]
      rw [hObserved] at hRank
      simp [grantDrainMarkRank] at hRank

/-- A continuing weak-marked label cannot have a new strong
observer at its actual post host. This follows from the mark
join alone; no stable-source geometry is presumed. -/
theorem grantDrainWeakNextNotStrongLock
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e j : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hWeakNext :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    grantDrainLedgerStrongLock ring
      (grantDrainStep ring fresh update s e) j = false := by
  have hRank := grantDrainWeakNextObservedRank
    ring fresh update s e label hWeakNext
  rw [hHost] at hRank
  have hFollower := grantDrainWeakNextFollower
    ring fresh update s e j label hWeakNext hHost
  cases hLock :
      grantDrainLedgerStrongLock ring
        (grantDrainStep ring fresh update s e) j with
  | false => rfl
  | true =>
      cases hHeld :
          (grantDrainStep ring fresh update s e).request j &&
          (grantDrainStep ring fresh update s e).grant j with
      | true =>
          have hObserved :
              grantDrainLedgerObservedMark ring
                (grantDrainStep ring fresh update s e) (some j) =
                  .terminal := by
            simp [grantDrainLedgerObservedMark, hHeld]
          rw [hObserved] at hRank
          simp [grantDrainMarkRank] at hRank
      | false =>
          have hObserved :
              grantDrainLedgerObservedMark ring
                (grantDrainStep ring fresh update s e) (some j) =
                  .strong := by
            simp [grantDrainLedgerObservedMark, hHeld,
              hFollower, hLock]
          rw [hObserved] at hRank
          simp [grantDrainMarkRank] at hRank

/-- Given a continuing physical GRANT and a weak mark, a new
request at that host is impossible, since it would be observed
as terminal. This isolates the grant-host soundness obligation
from the observable mark logic. -/
theorem grantDrainWeakNextRequestFalseOfGrant
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e j : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hWeakNext :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hGrant :
      (grantDrainStep ring fresh update s e).grant j = true) :
    (grantDrainStep ring fresh update s e).request j = false := by
  have hRank := grantDrainWeakNextObservedRank
    ring fresh update s e label hWeakNext
  rw [hHost] at hRank
  cases hRequest :
      (grantDrainStep ring fresh update s e).request j with
  | false => rfl
  | true =>
      have hObserved :
          grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e) (some j) =
              .terminal := by
        simp [grantDrainLedgerObservedMark, hRequest, hGrant]
      rw [hObserved] at hRank
      simp [grantDrainMarkRank] at hRank

/-- A local, non-tautological reduction of the first missing
weak-to-weak input. If native E/FIRE preserves the corridor and
the token row preserves the real grant at the ghost host, the
remaining weak mark itself forces every other physical field
(request=false, follower, UNshielded predecessor). -/
theorem grantDrainWeakToWeakPhysicalOfPostCorridor
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e j : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hWeakNext :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hGrant :
      (grantDrainStep ring fresh update s e).grant j = true)
    (hCorridor :
      grantDrainLedgerCorridor ring
        (grantDrainStep ring fresh update s e) j = true) :
    (grantDrainStep ring fresh update s e).grant j = true ∧
    (grantDrainStep ring fresh update s e).request j = false ∧
    ((grantDrainStep ring fresh update s e).native j).l =
      false ∧
    grantDrainLedgerWeakLock ring
      (grantDrainStep ring fresh update s e) j = true := by
  have hNoStrong := grantDrainWeakNextNotStrongLock
    ring fresh update s e j label hWeakNext hHost
  have hShieldFalse :
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring j
          (grantDrainLeftLeaderDistance ring
            (grantDrainStep ring fresh update s e).native j))).sh =
          false := by
    cases hh :
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring j
            (grantDrainLeftLeaderDistance ring
              (grantDrainStep ring fresh update s e).native j))).sh with
    | false => rfl
    | true =>
        have hStrong :
            grantDrainLedgerStrongLock ring
              (grantDrainStep ring fresh update s e) j = true := by
          simp [grantDrainLedgerStrongLock, hCorridor, hh]
        rw [hStrong] at hNoStrong
        cases hNoStrong
  refine ⟨hGrant, ?_, ?_, ?_⟩
  · exact grantDrainWeakNextRequestFalseOfGrant
      ring fresh update s e j label hWeakNext hHost hGrant
  · exact grantDrainWeakNextFollower
      ring fresh update s e j label hWeakNext hHost
  · simp [grantDrainLedgerWeakLock, hCorridor, hShieldFalse]

end L3

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Stationary OLD clean follower DUMMY across an actual fatal
follower-LIVE edge.  The geometric lemmas use the OLD nearest
sectors; FIRE is handled only after E has been certified.
-/

/-- Every strictly earlier offset of a genuine nearest-leader arc
has that same leader as its nearest counterclockwise leader. -/
theorem grantDrainDummyNearestPrefixSector
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p b : Fin n)
    (hArc : GrantDrainMarksNearestArc ring N p b)
    (k : Nat) (hk : k < PPL.cyclicOffset ring p b) :
    leaderSector ring N p (PPL.shiftRight ring p k) := by
  have hkN : k < n :=
    Nat.lt_trans hk (grantDrainEntranceArcOffsetLt ring p b)
  have hAt :
      (N (PPL.shiftLeft ring
        (PPL.shiftRight ring p k) k)).l = true := by
    rw [grantDrainMarksArcShiftLeftRight ring p k k
      (Nat.le_refl _) hkN]
    rw [Nat.sub_self, grantDrainWeakDeathShiftRightZero ring p]
    exact hArc.2.1
  have hMiss :
      ∀ j : Nat, 0 ≤ j → j < k →
      (N (PPL.shiftLeft ring
        (PPL.shiftRight ring p k) j)).l = false := by
    intro j _ hj
    rw [grantDrainMarksArcShiftLeftRight ring p k j
      (by omega) hkN]
    exact hArc.2.2 (k - j) (by omega) (by omega)
  have hScan :=
    grantDrainDummyScanFirstExact
      (fun j : Nat =>
        PPL.shiftLeft ring (PPL.shiftRight ring p k) j)
      (fun i : Fin n => (N i).l)
      n 0 k (Nat.zero_le _) (by omega) hAt hMiss
  refine ⟨hArc.2.1, ?_⟩
  change PPL.scanDistance
    (fun j : Nat =>
      PPL.shiftLeft ring (PPL.shiftRight ring p k) j)
    (fun i : Fin n => (N i).l) n 0 =
      some (PPL.cyclicOffset ring p (PPL.shiftRight ring p k))
  rw [grantDrainDummyRightOffset ring p k hkN]
  exact hScan

/-- The earliest-bullet half of CleanAt gives an ACTUALLY empty
prefix, without requiring global I or one bullet per sector. -/
theorem grantDrainDummyCleanPrefixEmpty
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p b : Fin n)
    (hArc : GrantDrainMarksNearestArc ring N p b)
    (hSector : leaderSector ring N p b)
    (hClean : GrantDrainEntranceBulletCleanAt ring N b) :
    ∀ k : Nat, k < PPL.cyclicOffset ring p b →
      (N (PPL.shiftRight ring p k)).b = (0 : Fin 3) := by
  obtain ⟨_, q, hQSector, hFirst, _⟩ := hClean
  have hSameOffset :
      PPL.cyclicOffset ring q b =
        PPL.cyclicOffset ring p b :=
    Option.some.inj (hQSector.2.symm.trans hSector.2)
  have hRoot : q = p := by
    have hLeftQ := grantDrainEntranceLeftOffset ring q b
    have hLeftP := grantDrainEntranceLeftOffset ring p b
    rw [hSameOffset] at hLeftQ
    exact hLeftQ.symm.trans hLeftP
  subst q
  intro k hk
  by_cases hEmpty :
      (N (PPL.shiftRight ring p k)).b = (0 : Fin 3)
  · exact hEmpty
  · have hSectorK :=
      grantDrainDummyNearestPrefixSector ring N p b hArc k hk
    have hkN : k < n :=
      Nat.lt_trans hk (grantDrainEntranceArcOffsetLt ring p b)
    have hFirstK := hFirst (PPL.shiftRight ring p k)
      hSectorK hEmpty
    rw [grantDrainDummyRightOffset ring p k hkN] at hFirstK
    omega

/-- In the fatal follower case, the old victim leader y is one
clockwise position beyond e. The two old sector offsets concatenate
without wraparound, because b is a follower in y's old sector. -/
theorem grantDrainDummyFatalFollowerOffsetSplice
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e p b : Fin n)
    (hFollower : (N e).l = false)
    (hLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hNoBad : ∀ v : Fin n,
      ¬ SharedPaperNonleftmostLiveExact ring N v)
    (hBFollower : (N b).l = false)
    (hNotE : b ≠ e)
    (hClean : GrantDrainEntranceBulletCleanAt ring N b)
    (hSectorE : leaderSector ring N p e)
    (hSectorB :
      leaderSector ring N (ring.rightNeighbor e) b) :
    PPL.cyclicOffset ring p (ring.rightNeighbor e) =
        PPL.cyclicOffset ring p e + 1 ∧
    PPL.cyclicOffset ring p b =
        PPL.cyclicOffset ring p (ring.rightNeighbor e) +
          PPL.cyclicOffset ring (ring.rightNeighbor e) b ∧
    PPL.cyclicOffset ring p (ring.rightNeighbor e) +
        PPL.cyclicOffset ring (ring.rightNeighbor e) b < n := by
  have hOldFront :=
    grantDrainDummyFollowerSectorNearestArc
      ring N p e hFollower hSectorE
  have hOldTail :=
    grantDrainDummyFollowerSectorNearestArc
      ring N (ring.rightNeighbor e) b hBFollower hSectorB
  have hpNotY : p ≠ ring.rightNeighbor e := by
    intro hp
    have hAtY :
        leaderSector ring N (ring.rightNeighbor e) e := by
      rw [← hp]
      exact hSectorE
    exact grantDrainDummyFatalFollowerCleanDifferentSector
      ring hn N e b (ring.rightNeighbor e)
      hFollower hLeader hDeath hNoBad hNotE hClean
      hAtY hSectorB
  have hYShift :
      PPL.shiftRight ring p
        (PPL.cyclicOffset ring p e + 1) =
          ring.rightNeighbor e := by
    calc
      PPL.shiftRight ring p
          (PPL.cyclicOffset ring p e + 1) =
        ring.rightNeighbor
          (PPL.shiftRight ring p
            (PPL.cyclicOffset ring p e)) :=
          (grantDrainEntranceAheadShiftSucc ring p
            (PPL.cyclicOffset ring p e)).symm
      _ = ring.rightNeighbor e := by
        rw [grantDrainMarksArcShiftRightOffset ring p e]
  have hSuccBound :
      PPL.cyclicOffset ring p e + 1 < n := by
    by_cases hh : PPL.cyclicOffset ring p e + 1 < n
    · exact hh
    · have hEq : PPL.cyclicOffset ring p e + 1 = n := by
        have hd := grantDrainEntranceArcOffsetLt ring p e
        omega
      have hFull : PPL.shiftRight ring p n = p := by
        apply Fin.ext
        change (p.val + n) % n = p.val
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]
      have hpEq : p = ring.rightNeighbor e := by
        calc
          p = PPL.shiftRight ring p n := hFull.symm
          _ = PPL.shiftRight ring p
              (PPL.cyclicOffset ring p e + 1) := by rw [hEq]
          _ = ring.rightNeighbor e := hYShift
      exact False.elim (hpNotY hpEq)
  have hPY :
      PPL.cyclicOffset ring p (ring.rightNeighbor e) =
        PPL.cyclicOffset ring p e + 1 := by
    rw [← hYShift]
    exact grantDrainDummyRightOffset ring p
      (PPL.cyclicOffset ring p e + 1) hSuccBound
  have hPositive :
      0 < PPL.cyclicOffset ring p (ring.rightNeighbor e) := by
    rw [hPY]
    omega
  have hNoWrap :
      PPL.cyclicOffset ring p (ring.rightNeighbor e) +
        PPL.cyclicOffset ring (ring.rightNeighbor e) b < n :=
    grantDrainWeakDeathArcNonoverlap
      ring N p (ring.rightNeighbor e) b
      hSectorE.1 hPositive hOldTail hBFollower
  exact ⟨hPY,
    grantDrainWeakDeathOffsetConcat
      ring p (ring.rightNeighbor e) b hNoWrap,
    hNoWrap⟩

/-- The victim sector's old clean follower DUMMY forces the
victim leader to be quiet and bullet-free. These facts ensure
that its E-death does not create a new DUMMY before b; any
canonical FIRE at the responder likewise creates no bullet. -/
theorem grantDrainDummyCleanVictimEmptyAfter
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e b : Fin n)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hBFollower : (s.native b).l = false)
    (hSectorB :
      leaderSector ring s.native (ring.rightNeighbor e) b)
    (hCleanB : GrantDrainEntranceBulletCleanAt ring s.native b) :
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).b = (0 : Fin 3) := by
  have hOldArc :=
    grantDrainDummyFollowerSectorNearestArc
      ring s.native (ring.rightNeighbor e) b
      hBFollower hSectorB
  have hOldPrefix :=
    grantDrainDummyCleanPrefixEmpty
      ring s.native (ring.rightNeighbor e) b
      hOldArc hSectorB hCleanB
  have hOldYEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) := by
    have hAt := hOldPrefix 0 hOldArc.1
    simpa only [grantDrainWeakDeathShiftRightZero] using hAt
  have hOldTrail :=
    grantDrainDummyCleanTrailAtNearest
      ring s.native (ring.rightNeighbor e) b hCleanB hSectorB
  have hOldYZero :
      (s.native (ring.rightNeighbor e)).sg = false := by
    have hAt := hOldTrail
      (⟨0, (show 0 < n by omega)⟩ : Fin n) (Nat.zero_le _)
    simpa only [grantDrainWeakDeathShiftRightZero] using hAt
  have hEEmpty :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (0 : Fin 3) := by
    exact (grantDrainEntranceNativeEQuietVictimBulletRetained
      ring (by omega : 2 ≤ n) s.native e
      hYLeader hOldYZero).trans hOldYEmpty
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  change (grantDrainNativeNext ring s e
    (ring.rightNeighbor e)).b = (0 : Fin 3)
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hEEmpty
  | leftLocal =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hDistinct]
        using hEEmpty
  | rightLocal =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]
  | cross =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hDistinct]
        using hEEmpty

/-- Earlier-bullet exclusion for the ENTIRE merged arc p..b,
independently of which of the four canonical FIRE outcomes occurs.
Before e, NoBadLive forbids a bullet; at e and y the literal
endpoint rows clear bullets; after y, OLD clean earliestness
and the physical away-frame exclude a bullet. -/
theorem grantDrainDummyFatalFollowerNoEarlierAfter
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hEFollower : (s.native e).l = false)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = false)
    (hBFollower : (s.native b).l = false)
    (hNotE : b ≠ e)
    (hCleanB : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hSectorE : leaderSector ring s.native p e)
    (hSectorB :
      leaderSector ring s.native (ring.rightNeighbor e) b) :
    ∀ k : Nat, k < PPL.cyclicOffset ring p b →
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftRight ring p k)).b = (0 : Fin 3) := by
  obtain ⟨hPY, hJoin, _⟩ :=
    grantDrainDummyFatalFollowerOffsetSplice
      ring hn s.native e p b
      hEFollower hYLeader hDeath hNoBad hBFollower
      hNotE hCleanB hSectorE hSectorB
  have hOldFront :=
    grantDrainDummyFollowerSectorNearestArc
      ring s.native p e hEFollower hSectorE
  have hOldTail :=
    grantDrainDummyFollowerSectorNearestArc
      ring s.native (ring.rightNeighbor e) b
      hBFollower hSectorB
  have hTailEmpty :=
    grantDrainDummyCleanPrefixEmpty
      ring s.native (ring.rightNeighbor e) b
      hOldTail hSectorB hCleanB
  have hYEmpty :=
    grantDrainDummyCleanVictimEmptyAfter
      ring hn fresh update s e b
      hYLeader hBFollower hSectorB hCleanB
  intro k hk
  have hkN : k < n :=
    Nat.lt_trans hk (grantDrainEntranceArcOffsetLt ring p b)
  by_cases hBeforeE : k < PPL.cyclicOffset ring p e
  · have hSectorK :=
      grantDrainDummyNearestPrefixSector
        ring s.native p e hOldFront k hBeforeE
    have hNotY :
        PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
      intro hSite
      have hOffsetEq :=
        congrArg (PPL.cyclicOffset ring p) hSite
      rw [grantDrainDummyRightOffset ring p k hkN, hPY]
        at hOffsetEq
      omega
    have hNoNew :=
      grantDrainDummyFatalFollowerNoEarlierBulletAfter
        ring hn fresh update s e p
        (PPL.shiftRight ring p k)
        hEFollower hYLeader hDeath hNoBad
        hSectorE hSectorK
        (by rw [grantDrainDummyRightOffset ring p k hkN]; exact hBeforeE)
        hNotY
    by_cases hEmpty :
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftRight ring p k)).b = (0 : Fin 3)
    · exact hEmpty
    · exact False.elim (hNoNew hEmpty)
  · by_cases hAtE : k = PPL.cyclicOffset ring p e
    · rw [hAtE, grantDrainMarksArcShiftRightOffset ring p e]
      exact grantDrainDummyOutgoingSourceCleared
        ring hn fresh update s e
    · have hPastY :
          PPL.cyclicOffset ring p (ring.rightNeighbor e) ≤ k := by
        rw [hPY]
        omega
      have hTailK :
          k - PPL.cyclicOffset ring p (ring.rightNeighbor e) <
            PPL.cyclicOffset ring (ring.rightNeighbor e) b := by
        rw [hJoin] at hk
        omega
      have hSite :
          PPL.shiftRight ring p k =
            PPL.shiftRight ring (ring.rightNeighbor e)
              (k - PPL.cyclicOffset ring p (ring.rightNeighbor e)) := by
        calc
          PPL.shiftRight ring p k =
            PPL.shiftRight ring p
              (PPL.cyclicOffset ring p (ring.rightNeighbor e) +
                (k - PPL.cyclicOffset ring p (ring.rightNeighbor e))) := by
                  congr 1
                  omega
          _ = PPL.shiftRight ring
                (PPL.shiftRight ring p
                  (PPL.cyclicOffset ring p (ring.rightNeighbor e)))
                (k - PPL.cyclicOffset ring p (ring.rightNeighbor e)) :=
                  (grantDrainWeakDeathShiftRightAdd ring p _ _).symm
          _ = PPL.shiftRight ring (ring.rightNeighbor e)
                (k - PPL.cyclicOffset ring p (ring.rightNeighbor e)) := by
                  rw [grantDrainMarksArcShiftRightOffset ring p
                    (ring.rightNeighbor e)]
      rw [hSite]
      by_cases hAtY :
          k - PPL.cyclicOffset ring p (ring.rightNeighbor e) = 0
      · rw [hAtY, grantDrainWeakDeathShiftRightZero ring
          (ring.rightNeighbor e)]
        exact hYEmpty
      · have hTailN :
            k - PPL.cyclicOffset ring p (ring.rightNeighbor e) < n :=
          Nat.lt_trans hTailK
            (grantDrainEntranceArcOffsetLt ring (ring.rightNeighbor e) b)
        have hNotE :
            PPL.shiftRight ring (ring.rightNeighbor e)
              (k - PPL.cyclicOffset ring p (ring.rightNeighbor e)) ≠ e :=
          grantDrainMarksIncomingSourceArcExceptRoot
            (by omega : 3 ≤ n) ring (ring.rightNeighbor e) b e
            rfl _ hTailK
        have hNotY :
            PPL.shiftRight ring (ring.rightNeighbor e)
              (k - PPL.cyclicOffset ring p (ring.rightNeighbor e)) ≠
                ring.rightNeighbor e := by
          intro hEq
          have hOffEq :=
            congrArg (PPL.cyclicOffset ring (ring.rightNeighbor e)) hEq
          rw [grantDrainDummyRightOffset ring (ring.rightNeighbor e)
                _ hTailN,
              grantDrainDummyArcOffsetSelf ring (ring.rightNeighbor e)]
            at hOffEq
          exact hAtY hOffEq
        have hFrame :=
          sharedPaperNativeAwayFrame
            ring s e
            (PPL.shiftRight ring (ring.rightNeighbor e)
              (k - PPL.cyclicOffset ring p (ring.rightNeighbor e)))
            hNotE hNotY
        change
          (grantDrainNativeNext ring s e
            (PPL.shiftRight ring (ring.rightNeighbor e)
              (k - PPL.cyclicOffset ring p (ring.rightNeighbor e)))).b =
                (0 : Fin 3)
        rw [hFrame]
        exact hTailEmpty _ hTailK

/-- The stationary DUMMY host is untouched, including its leader
and signal fields. This is common to no FIRE, F0/F2 and F1. -/
theorem grantDrainDummyFatalFollowerHostFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e b : Fin n)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hBFollower : (s.native b).l = false)
    (hNotE : b ≠ e) :
    (grantDrainStep ring fresh update s e).native b =
      s.native b := by
  have hNotY : b ≠ ring.rightNeighbor e := by
    intro hb
    rw [hb, hYLeader] at hBFollower
    cases hBFollower
  exact sharedPaperNativeAwayFrame ring s e b hNotE hNotY

/-- The actual no-FIRE fatal follower-LIVE edge preserves the
stationary follower-hosted clean DUMMY. It uses both components
of the already nearest/zero arc theorem, plus the new
earlier-bullet exclusion and the unchanged host record. -/
theorem grantDrainDummyFatalFollowerNoFireClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hEFollower : (s.native e).l = false)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = false)
    (hBFollower : (s.native b).l = false)
    (hNotE : b ≠ e)
    (hOldDummy : (s.native b).b = (1 : Fin 3))
    (hCleanB : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hSectorE : leaderSector ring s.native p e)
    (hSectorB :
      leaderSector ring s.native (ring.rightNeighbor e) b)
    (hNoFire : grantDrainSelect ring s e = .none) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hArc :=
    grantDrainDummyFatalFollowerNoFireNearestZero
      ring hn fresh update s e p b hP hNoBad
      hEFollower hYLeader hDeath hBFollower
      hNotE hCleanB hSectorE hSectorB hNoFire
  have hFrame :=
    grantDrainDummyFatalFollowerHostFrame
      ring fresh update s e b hYLeader hBFollower hNotE
  have hBullet : HasBullet
      (grantDrainStep ring fresh update s e).native b := by
    unfold HasBullet
    rw [hFrame]
    exact hCleanB.1
  have hNewFollower :
      ((grantDrainStep ring fresh update s e).native b).l =
        false := by
    rw [hFrame]
    exact hBFollower
  have hOwnZero :
      ((grantDrainStep ring fresh update s e).native b).sg =
        false := by
    rw [hFrame]
    exact grantDrainDummyCleanOwnSignalZero
      ring s.native b hCleanB
  have hNoBefore :=
    grantDrainDummyFatalFollowerNoEarlierAfter
      ring hn fresh update s e p b hNoBad hEFollower
      hYLeader hDeath hBFollower hNotE hCleanB
      hSectorE hSectorB
  exact grantDrainDummyCleanFromNearestZeroNoBefore
    ring (grantDrainStep ring fresh update s e).native p b
    hBullet hNewFollower hArc.1 hArc.2 hOwnZero hNoBefore

/-- A shadow with the same native state and no OLD tokens.
It allows the proved no-FIRE nearest/zero splice to be
instantiated as a pure statement about native E, independently
of which FIRE the ACTUAL state subsequently selects. -/
private def grantDrainDummyFirelessShadow
    {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch) : GrantDrainState n Scratch :=
  { s with request := fun _ => false, grant := fun _ => false }

/-- Native-E nearest/zero arc for a fatal follower LIVE and a
clean DUMMY in the deleted leader's sector, without an actual
no-FIRE assumption. -/
theorem grantDrainDummyFatalFollowerNativeENearestZero
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hEFollower : (s.native e).l = false)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = false)
    (hBFollower : (s.native b).l = false)
    (hNotE : b ≠ e)
    (hCleanB : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hSectorE : leaderSector ring s.native p e)
    (hSectorB :
      leaderSector ring s.native (ring.rightNeighbor e) b) :
    GrantDrainMarksNearestArc ring (nativeE ring s.native e) p b ∧
    GrantDrainMarksZeroOffsetArc ring (nativeE ring s.native e) p b := by
  have hNoFire :
      grantDrainSelect ring (grantDrainDummyFirelessShadow s) e =
        .none := by
    simp [grantDrainSelect, grantDrainDummyFirelessShadow]
  have hArc :=
    grantDrainDummyFatalFollowerNoFireNearestZero
      ring hn (fun _ _ => false) (fun t _ => t.scratch)
      (grantDrainDummyFirelessShadow s) e p b
      hP hNoBad hEFollower hYLeader hDeath
      hBFollower hNotE hCleanB hSectorE hSectorB hNoFire
  have hNative :
      (grantDrainStep ring (fun _ _ => false)
        (fun t _ => t.scratch)
        (grantDrainDummyFirelessShadow s) e).native =
          nativeE ring s.native e := by
    change grantDrainNativeNext ring
      (grantDrainDummyFirelessShadow s) e = nativeE ring s.native e
    unfold grantDrainNativeNext
    rw [hNoFire]
    rfl
  rw [hNative] at hArc
  exact hArc

/-- F0/F2: the canonical born leader at e becomes the new nearest
root. The birth-arc lemma cuts off the old root and its already
verified prefix; the inclusive host, earliest-bullet certificate,
and zero trail then give CleanAt. -/
theorem grantDrainDummyFatalFollowerBirthAtSourceClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hEFollower : (s.native e).l = false)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = false)
    (hBFollower : (s.native b).l = false)
    (hNotE : b ≠ e)
    (hOldDummy : (s.native b).b = (1 : Fin 3))
    (hCleanB : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hSectorE : leaderSector ring s.native p e)
    (hSectorB :
      leaderSector ring s.native (ring.rightNeighbor e) b)
    (hFire :
      grantDrainSelect ring s e = .leftLocal ∨
        grantDrainSelect ring s e = .cross) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hEArc :=
    grantDrainDummyFatalFollowerNativeENearestZero
      ring hn s e p b hP hNoBad hEFollower hYLeader
      hDeath hBFollower hNotE hCleanB hSectorE hSectorB
  obtain ⟨hPY, hJoin, _⟩ :=
    grantDrainDummyFatalFollowerOffsetSplice
      ring hn s.native e p b hEFollower hYLeader hDeath
      hNoBad hBFollower hNotE hCleanB hSectorE hSectorB
  have hEInside :
      PPL.cyclicOffset ring p e <
        PPL.cyclicOffset ring p b := by
    rw [hJoin, hPY]
    omega
  have hBirth :=
    grantDrainWeakDeathProtectedArcBirth
      ring (nativeE ring s.native e) p b e
      (PPL.cyclicOffset ring p e)
      hEArc.1 hEArc.2
      (grantDrainMarksArcShiftRightOffset ring p e).symm hEInside
  have hActual :
      GrantDrainMarksNearestArc ring
        (grantDrainStep ring fresh update s e).native e b ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainStep ring fresh update s e).native e b := by
    change
      GrantDrainMarksNearestArc ring (grantDrainNativeNext ring s e) e b ∧
      GrantDrainMarksZeroOffsetArc ring (grantDrainNativeNext ring s e) e b
    rcases hFire with hf | hf
    · simpa [grantDrainNativeNext, hf] using
        (show GrantDrainMarksNearestArc ring
          (canonicalBirth (nativeE ring s.native e) e) e b ∧
          GrantDrainMarksZeroOffsetArc ring
          (canonicalBirth (nativeE ring s.native e) e) e b
          from ⟨hBirth.1, hBirth.2.1⟩)
    · simpa [grantDrainNativeNext, hf] using
        (show GrantDrainMarksNearestArc ring
          (canonicalBirth (nativeE ring s.native e) e) e b ∧
          GrantDrainMarksZeroOffsetArc ring
          (canonicalBirth (nativeE ring s.native e) e) e b
          from ⟨hBirth.1, hBirth.2.1⟩)
  have hFrame :=
    grantDrainDummyFatalFollowerHostFrame
      ring fresh update s e b hYLeader hBFollower hNotE
  have hBullet : HasBullet
      (grantDrainStep ring fresh update s e).native b := by
    unfold HasBullet
    rw [hFrame]
    exact hCleanB.1
  have hNewFollower :
      ((grantDrainStep ring fresh update s e).native b).l =
        false := by
    rw [hFrame]
    exact hBFollower
  have hOwnZero :
      ((grantDrainStep ring fresh update s e).native b).sg =
        false := by
    rw [hFrame]
    exact grantDrainDummyCleanOwnSignalZero
      ring s.native b hCleanB
  have hNoBefore :=
    grantDrainDummyFatalFollowerNoEarlierAfter
      ring hn fresh update s e p b hNoBad hEFollower
      hYLeader hDeath hBFollower hNotE hCleanB
      hSectorE hSectorB
  have hNoBeforeE :
      ∀ k : Nat, k < PPL.cyclicOffset ring e b →
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftRight ring e k)).b = (0 : Fin 3) := by
    intro k hk
    have hEOffset :
        PPL.cyclicOffset ring p e + k <
          PPL.cyclicOffset ring p b := by
      have hESuffix :=
        grantDrainMarksArcOffsetSubtract
          ring p b (PPL.cyclicOffset ring p e)
          (Nat.le_of_lt hEInside)
      have hSite :
          PPL.cyclicOffset ring e b =
            PPL.cyclicOffset ring p b -
              PPL.cyclicOffset ring p e := by
        simpa only [grantDrainMarksArcShiftRightOffset ring p e]
          using hESuffix
      rw [hSite] at hk
      omega
    have hShift :
        PPL.shiftRight ring e k =
          PPL.shiftRight ring p (PPL.cyclicOffset ring p e + k) := by
      calc
        PPL.shiftRight ring e k =
          PPL.shiftRight ring
            (PPL.shiftRight ring p (PPL.cyclicOffset ring p e)) k := by
              rw [grantDrainMarksArcShiftRightOffset ring p e]
        _ = PPL.shiftRight ring p
              (PPL.cyclicOffset ring p e + k) :=
                grantDrainWeakDeathShiftRightAdd ring p _ _
    rw [hShift]
    exact hNoBefore (PPL.cyclicOffset ring p e + k) hEOffset
  exact grantDrainDummyCleanFromNearestZeroNoBefore
    ring (grantDrainStep ring fresh update s e).native e b
    hBullet hNewFollower hActual.1 hActual.2
    hOwnZero hNoBeforeE

/-- F1: a leader is born at the old victim y. It becomes the new
nearest root, and the old victim-sector clean prefix alone suffices
for its no-earlier-bullet certificate. -/
theorem grantDrainDummyFatalFollowerBirthAtResponderClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hEFollower : (s.native e).l = false)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = false)
    (hBFollower : (s.native b).l = false)
    (hNotE : b ≠ e)
    (hOldDummy : (s.native b).b = (1 : Fin 3))
    (hCleanB : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hSectorE : leaderSector ring s.native p e)
    (hSectorB :
      leaderSector ring s.native (ring.rightNeighbor e) b)
    (hFire : grantDrainSelect ring s e = .rightLocal) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hEArc :=
    grantDrainDummyFatalFollowerNativeENearestZero
      ring hn s e p b hP hNoBad hEFollower hYLeader
      hDeath hBFollower hNotE hCleanB hSectorE hSectorB
  obtain ⟨_, hJoin, _⟩ :=
    grantDrainDummyFatalFollowerOffsetSplice
      ring hn s.native e p b hEFollower hYLeader hDeath
      hNoBad hBFollower hNotE hCleanB hSectorE hSectorB
  have hOldTail :=
    grantDrainDummyFollowerSectorNearestArc
      ring s.native (ring.rightNeighbor e) b
      hBFollower hSectorB
  have hYInside :
      PPL.cyclicOffset ring p (ring.rightNeighbor e) <
        PPL.cyclicOffset ring p b := by
    have hbne : b ≠ ring.rightNeighbor e := by
      intro h
      rw [h, hYLeader] at hBFollower
      cases hBFollower
    have hpos : 0 < PPL.cyclicOffset ring (ring.rightNeighbor e) b := by
      rcases Nat.eq_zero_or_pos
          (PPL.cyclicOffset ring (ring.rightNeighbor e) b) with h0 | h0
      · exfalso
        have hs := grantDrainMarksArcShiftRightOffset ring
          (ring.rightNeighbor e) b
        rw [h0, grantDrainWeakDeathShiftRightZero ring] at hs
        exact hbne hs.symm
      · exact h0
    rw [hJoin]
    omega
  have hBirth :=
    grantDrainWeakDeathProtectedArcBirth
      ring (nativeE ring s.native e) p b
      (ring.rightNeighbor e)
      (PPL.cyclicOffset ring p (ring.rightNeighbor e))
      hEArc.1 hEArc.2
      (grantDrainMarksArcShiftRightOffset ring p
        (ring.rightNeighbor e)).symm hYInside
  have hActual :
      GrantDrainMarksNearestArc ring
        (grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e) b ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e) b := by
    change
      GrantDrainMarksNearestArc ring (grantDrainNativeNext ring s e)
        (ring.rightNeighbor e) b ∧
      GrantDrainMarksZeroOffsetArc ring (grantDrainNativeNext ring s e)
        (ring.rightNeighbor e) b
    simpa [grantDrainNativeNext, hFire] using
      (show GrantDrainMarksNearestArc ring
        (canonicalBirth (nativeE ring s.native e)
          (ring.rightNeighbor e)) (ring.rightNeighbor e) b ∧
        GrantDrainMarksZeroOffsetArc ring
        (canonicalBirth (nativeE ring s.native e)
          (ring.rightNeighbor e)) (ring.rightNeighbor e) b
        from ⟨hBirth.1, hBirth.2.1⟩)
  have hFrame :=
    grantDrainDummyFatalFollowerHostFrame
      ring fresh update s e b hYLeader hBFollower hNotE
  have hBullet : HasBullet
      (grantDrainStep ring fresh update s e).native b := by
    unfold HasBullet
    rw [hFrame]
    exact hCleanB.1
  have hNewFollower :
      ((grantDrainStep ring fresh update s e).native b).l =
        false := by
    rw [hFrame]
    exact hBFollower
  have hOwnZero :
      ((grantDrainStep ring fresh update s e).native b).sg =
        false := by
    rw [hFrame]
    exact grantDrainDummyCleanOwnSignalZero
      ring s.native b hCleanB
  have hNoBefore :=
    grantDrainDummyFatalFollowerNoEarlierAfter
      ring hn fresh update s e p b hNoBad hEFollower
      hYLeader hDeath hBFollower hNotE hCleanB
      hSectorE hSectorB
  have hNoBeforeY :
      ∀ k : Nat,
        k < PPL.cyclicOffset ring (ring.rightNeighbor e) b →
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftRight ring (ring.rightNeighbor e) k)).b =
            (0 : Fin 3) := by
    intro k hk
    have hYOffset :
        PPL.cyclicOffset ring p (ring.rightNeighbor e) + k <
          PPL.cyclicOffset ring p b := by
      rw [hJoin]
      omega
    have hShift :
        PPL.shiftRight ring (ring.rightNeighbor e) k =
          PPL.shiftRight ring p
            (PPL.cyclicOffset ring p (ring.rightNeighbor e) + k) := by
      calc
        PPL.shiftRight ring (ring.rightNeighbor e) k =
          PPL.shiftRight ring
            (PPL.shiftRight ring p
              (PPL.cyclicOffset ring p (ring.rightNeighbor e))) k := by
                rw [grantDrainMarksArcShiftRightOffset ring p
                  (ring.rightNeighbor e)]
        _ = PPL.shiftRight ring p
              (PPL.cyclicOffset ring p (ring.rightNeighbor e) + k) :=
                grantDrainWeakDeathShiftRightAdd ring p _ _
    rw [hShift]
    exact hNoBefore
      (PPL.cyclicOffset ring p (ring.rightNeighbor e) + k)
      hYOffset
  exact grantDrainDummyCleanFromNearestZeroNoBefore
    ring (grantDrainStep ring fresh update s e).native
    (ring.rightNeighbor e) b
    hBullet hNewFollower hActual.1 hActual.2
    hOwnZero hNoBeforeY

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
The three fatal-follower-victim FIRE
branches are assembled first. The full stationary row still has
nonfatal follower/follower and resident responder cases, and an
OLD responder-leader-hosted DUMMY that dies, to be discharged.

The unrestricted moving row (B') is FALSE. A literal n=5
PPlus/NoBadLive state and its actual E+FIRE step below exhibit
a clean follower DUMMY that moves into an OLD empty follower
and becomes nonclean. No theorem asserting B', CleanGeometry
or EdgeOriginHolds is introduced.
-/

/-- A' fatal-follower-victim sector: all four actual FIRE outcomes
are discharged, with the two old sector certificates and no other
global invariant beyond PPlus and NoBadLive. -/
theorem grantDrainDummyStationaryFatalFollowerVictimClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hEFollower : (s.native e).l = false)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = false)
    (hBFollower : (s.native b).l = false)
    (hNotE : b ≠ e)
    (hOldDummy : (s.native b).b = (1 : Fin 3))
    (hCleanB : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hSectorE : leaderSector ring s.native p e)
    (hSectorB :
      leaderSector ring s.native (ring.rightNeighbor e) b) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  cases hf : grantDrainSelect ring s e with
  | none =>
      exact grantDrainDummyFatalFollowerNoFireClean
        ring hn fresh update s e p b hP hNoBad
        hEFollower hYLeader hDeath hBFollower hNotE
        hOldDummy hCleanB hSectorE hSectorB hf
  | leftLocal =>
      exact grantDrainDummyFatalFollowerBirthAtSourceClean
        ring hn fresh update s e p b hP hNoBad
        hEFollower hYLeader hDeath hBFollower hNotE
        hOldDummy hCleanB hSectorE hSectorB (Or.inl hf)
  | rightLocal =>
      exact grantDrainDummyFatalFollowerBirthAtResponderClean
        ring hn fresh update s e p b hP hNoBad
        hEFollower hYLeader hDeath hBFollower hNotE
        hOldDummy hCleanB hSectorE hSectorB hf
  | cross =>
      exact grantDrainDummyFatalFollowerBirthAtSourceClean
        ring hn fresh update s e p b hP hNoBad
        hEFollower hYLeader hDeath hBFollower hNotE
        hOldDummy hCleanB hSectorE hSectorB (Or.inr hf)

/-- Literal ready-responder death by an OLD follower LIVE:
E clears the source, deletes the leader responder, and leaves
a zero-signal DUMMY at the responder. -/
theorem grantDrainDummyReadyFollowerLiveLiteral
    (x y : CertNative)
    (hXFollower : x.l = false)
    (hXLive : x.b = (2 : Fin 3))
    (hXZero : x.sg = false)
    (hYLeader : y.l = true)
    (hYReady : y.sg = true) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.b = (1 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, certFinThree,
    hXFollower, hXLive, hXZero, hYLeader, hYReady]

/-- C' subcase: when an OLD follower LIVE kills a ready leader
and the literal selector subsequently births at the initiator
(F0 or F2), the ready responder's DUMMY is immediately adjacent
to a new zero-signal empty leader, hence clean. -/
theorem grantDrainDummyReadyFollowerLiveBirthSourceClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hXFollower : (s.native e).l = false)
    (hXLive : LiveBullet s.native e)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hYReady : (s.native (ring.rightNeighbor e)).sg = true)
    (hFire : grantDrainSelect ring s e = .leftLocal ∨
      grantDrainSelect ring s e = .cross) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hXZero : (s.native e).sg = false :=
    L3.grantDrainDeathLiveOwnSignalZero ring s e hP hXLive
  have hPair :=
    grantDrainDummyReadyFollowerLiveLiteral
      (s.native e) (s.native (ring.rightNeighbor e))
      hXFollower hXLive hXZero hYLeader hYReady
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hEFollower :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.1
  have hEDummy :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.1
  have hEZero :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2
  have hPhysical :
      (grantDrainStep ring fresh update s e).native =
        canonicalBirth (nativeE ring s.native e) e := by
    change grantDrainNativeNext ring s e =
      canonicalBirth (nativeE ring s.native e) e
    rcases hFire with hf | hf
    · simp [grantDrainNativeNext, hf]
    · simp [grantDrainNativeNext, hf]
  rw [hPhysical]
  exact grantDrainDummyAdjacentFollowerClean
    ring hn (canonicalBirth (nativeE ring s.native e) e) e
    (by simp [canonicalBirth, firedNative])
    (by simp [canonicalBirth, firedNative])
    (by simp [canonicalBirth, firedNative])
    (by simpa [canonicalBirth, hDistinct] using hEFollower)
    (by simpa [canonicalBirth, hDistinct] using hEDummy)
    (by simpa [canonicalBirth, hDistinct] using hEZero)

end L3.GrantDrainEntrance

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
The first new theorem isolates the only missing SOURCE row branch for
surviving Y labels: some true YSource implies the Y output grant bit.
The second/third theorems identify the two physical token projections.
The fourth theorem combines these with the existing Y-movement
soundness to prove that EVERY surviving label at its current ghost
host owns a physical grant. No PPlus, mark, or corridor assumption
is needed for this source-token fact.

The later results derive full native corridor and source-distance
progress in each cyclic edge class, followed by a seven-way
weak-to-weak LockBudget case assembly.
-/

/-- The Y ancestry observer can report "stays at Y" only when
the actual token row's Y output contains a grant. -/
theorem grantDrainWeakYSourceStaySound
    (ry gy lx ly : Bool) (fire : GrantDrainFire)
    (row : TokPair × TokPair)
    (h : grantDrainLedgerYSource ry gy lx ly fire row =
      some true) :
    row.2.grant = true := by
  cases hg : gy <;>
    cases hy : row.2.grant <;>
    simp [grantDrainLedgerYSource, hg, hy] at h ⊢

/-- The literal source grant step and proof-only ledger row
have EXACTLY the same initiator grant bit. -/
theorem grantDrainWeakStepGrantAtSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    (grantDrainStep ring fresh update s e).grant e =
      (grantDrainLedgerRow ring fresh s e).1.grant := by
  change (if e = e then
      (grantDrainLedgerRow ring fresh s e).1.grant
    else if e = ring.rightNeighbor e then
      (grantDrainLedgerRow ring fresh s e).2.grant
    else s.grant e) =
      (grantDrainLedgerRow ring fresh s e).1.grant
  simp

/-- The responder grant projection is also exact on rings
where the initiator and responder are distinct. -/
theorem grantDrainWeakStepGrantAtResponder
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (grantDrainStep ring fresh update s e).grant
        (ring.rightNeighbor e) =
      (grantDrainLedgerRow ring fresh s e).2.grant := by
  change (if ring.rightNeighbor e = e then
      (grantDrainLedgerRow ring fresh s e).1.grant
    else if ring.rightNeighbor e = ring.rightNeighbor e then
      (grantDrainLedgerRow ring fresh s e).2.grant
    else s.grant (ring.rightNeighbor e)) =
      (grantDrainLedgerRow ring fresh s e).2.grant
  simp [hne]

theorem grantDrainWeakSurvivingHostGrant
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hOldHost : label.host = some g)
    (hOldGrant : s.grant g = true)
    (hNextHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    (grantDrainStep ring fresh update s e).grant j = true := by
  have hDifferent :
      ring.rightNeighbor e ≠ e :=
    grantDrainMarksNeighborDistinct (by omega : 3 ≤ n) ring e
  have hRaw :
      grantDrainLedgerHost ring fresh s e (some g) =
        some j := by
    change grantDrainLedgerHost ring fresh s e label.host =
      some j at hNextHost
    rw [hOldHost] at hNextHost
    exact hNextHost
  by_cases hX : g = e
  · subst g
    cases hr : (grantDrainLedgerRow ring fresh s e).1.grant with
    | false =>
        have hEval :
            grantDrainLedgerHost ring fresh s e (some e) =
              none := by
          simp [grantDrainLedgerHost, hOldGrant, hr]
        rw [hEval] at hRaw
        cases hRaw
    | true =>
        have hEval :
            grantDrainLedgerHost ring fresh s e (some e) =
              some e := by
          simp [grantDrainLedgerHost, hOldGrant, hr]
        have hEq : some e = some j := hEval.symm.trans hRaw
        have hj : e = j := Option.some.inj hEq
        subst j
        rw [grantDrainWeakStepGrantAtSource ring fresh update s e]
        exact hr
  · by_cases hY : g = ring.rightNeighbor e
    · subst g
      cases hs : grantDrainLedgerYSource
          (s.request (ring.rightNeighbor e))
          (s.grant (ring.rightNeighbor e))
          (grantDrainNativeNext ring s e e).l
          (grantDrainNativeNext ring s e
            (ring.rightNeighbor e)).l
          (grantDrainSelect ring s e)
          (grantDrainLedgerRow ring fresh s e) with
      | none =>
          have hEval :
              grantDrainLedgerHost ring fresh s e
                (some (ring.rightNeighbor e)) = none := by
            simp only [grantDrainLedgerHost,
              if_neg hDifferent, if_pos rfl, hs, if_true]
          rw [hEval] at hRaw
          cases hRaw
      | some stay =>
          cases stay with
          | false =>
              have hEval :
                  grantDrainLedgerHost ring fresh s e
                    (some (ring.rightNeighbor e)) = some e := by
                simp only [grantDrainLedgerHost,
                  if_neg hDifferent, if_pos rfl, hs, if_true]
              have hEq : some e = some j := hEval.symm.trans hRaw
              have hj : e = j := Option.some.inj hEq
              subst j
              have hRow := (grantDrainLedgerYSource_move_sound
                (s.request (ring.rightNeighbor e))
                (s.grant (ring.rightNeighbor e))
                (grantDrainNativeNext ring s e e).l
                (grantDrainNativeNext ring s e
                  (ring.rightNeighbor e)).l
                (grantDrainSelect ring s e)
                (grantDrainLedgerRow ring fresh s e) hs).1
              rw [grantDrainWeakStepGrantAtSource
                ring fresh update s e]
              exact hRow
          | true =>
              have hEval :
                  grantDrainLedgerHost ring fresh s e
                    (some (ring.rightNeighbor e)) =
                      some (ring.rightNeighbor e) := by
                simp only [grantDrainLedgerHost,
                  if_neg hDifferent, if_pos rfl, hs, if_true]
              have hEq :
                  some (ring.rightNeighbor e) = some j :=
                hEval.symm.trans hRaw
              have hj :
                  ring.rightNeighbor e = j := Option.some.inj hEq
              subst j
              have hRow := grantDrainWeakYSourceStaySound
                (s.request (ring.rightNeighbor e))
                (s.grant (ring.rightNeighbor e))
                (grantDrainNativeNext ring s e e).l
                (grantDrainNativeNext ring s e
                  (ring.rightNeighbor e)).l
                (grantDrainSelect ring s e)
                (grantDrainLedgerRow ring fresh s e) hs
              rw [grantDrainWeakStepGrantAtResponder
                ring fresh update s e hDifferent]
              exact hRow
    · have hEq : some g = some j := by
        simpa [grantDrainLedgerHost, hX, hY] using hRaw
      have hj : g = j := Option.some.inj hEq
      subst j
      exact (grantDrainMarksInteriorTokenFrame
        ring fresh update s e g hX hY).2.trans hOldGrant

/-- The requested hGrant input, in its exact weak-to-weak form,
is a direct corollary of physical token ancestry and LockBudget.
No adjacency or special FIRE case needs to be assumed. -/
theorem grantDrainWeakToWeakGrantHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hOldWeak : label.mark = .weak) :
    ∀ j : Fin n,
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j →
      (grantDrainStep ring fresh update s e).grant j = true := by
  obtain ⟨hGrant, _⟩ := hInv g hOldHost
  intro j hNewHost
  exact grantDrainWeakSurvivingHostGrant
    ring hn fresh update s e label g j
    hOldHost hGrant hNewHost


/-- Any nearest zero arc, shielded or not, entails the literal
Boolean corridor observer at its host. The proof-only all-shielded
copy is used only to reuse the proved reverse arc-to-strong-lock
bridge; it does not change the physical transition. -/
theorem grantDrainWeakArcImpliesCorridor
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (p g : Fin n)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g) :
    grantDrainLedgerCorridor ring s g = true := by
  have hShadowNearest :
      GrantDrainMarksNearestArc ring
        (grantDrainWeakDeathShieldedCopy s).native p g := by
    change GrantDrainMarksNearestArc ring s.native p g
    exact hNearest
  have hShadowZero :
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainWeakDeathShieldedCopy s).native p g := by
    change GrantDrainMarksZeroOffsetArc ring s.native p g
    exact hZero
  have hShadowShield :
      ((grantDrainWeakDeathShieldedCopy s).native p).sh =
        true := rfl
  have hShadowStrong :
      grantDrainLedgerStrongLock ring
        (grantDrainWeakDeathShieldedCopy s) g = true :=
    grantDrainMarksOffsetArcStrongLock ring
      (grantDrainWeakDeathShieldedCopy s) p g
      hShadowNearest hShadowZero hShadowShield
  have hShadowCorr :
      grantDrainLedgerCorridor ring
        (grantDrainWeakDeathShieldedCopy s) g = true :=
    (grantDrainWeakDeathAndTrue hShadowStrong).1
  change grantDrainLedgerCorridor ring s g = true at hShadowCorr
  exact hShadowCorr

/-- For an edge wholly within the old nearest follower corridor,
native E preserves ALL leader bits and every zero signal of its
old source prefix. Both selected native sites were old followers
with old signal zero. -/
theorem grantDrainWeakStrictInteriorEArc
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e) :
    GrantDrainMarksNearestArc ring
      (nativeE ring s.native e) p g ∧
    GrantDrainMarksZeroOffsetArc ring
      (nativeE ring s.native e) p g := by
  rcases hInside with ⟨hXPos, hXLt, hYPos, hYLt⟩
  have hXSite :=
    grantDrainMarksArcShiftRightOffset ring p e
  have hYSite :=
    grantDrainMarksArcShiftRightOffset ring p (ring.rightNeighbor e)
  have hLX : (s.native e).l = false := by
    have hOld := hNearest.2.2
      (PPL.cyclicOffset ring p e) hXPos hXLt
    rw [hXSite] at hOld
    exact hOld
  have hLY :
      (s.native (ring.rightNeighbor e)).l = false := by
    have hOld := hNearest.2.2
      (PPL.cyclicOffset ring p (ring.rightNeighbor e))
      hYPos hYLt
    rw [hYSite] at hOld
    exact hOld
  have hSX : (s.native e).sg = false := by
    have hOld := hZero (PPL.cyclicOffset ring p e) hXLt
    rw [hXSite] at hOld
    exact hOld
  have hSY :
      (s.native (ring.rightNeighbor e)).sg = false := by
    have hOld :=
      hZero (PPL.cyclicOffset ring p (ring.rightNeighbor e)) hYLt
    rw [hYSite] at hOld
    exact hOld
  have hLeaderFrame : ∀ i : Fin n,
      (nativeE ring s.native e i).l = (s.native i).l := by
    intro i
    exact grantDrainMarksInteriorNativeELeaderAt
      ring s e i hLX hLY hSX hSY
  constructor
  · refine ⟨hNearest.1, ?_, ?_⟩
    · rw [hLeaderFrame p]
      exact hNearest.2.1
    · intro k hk hLt
      rw [hLeaderFrame (PPL.shiftRight ring p k)]
      exact hNearest.2.2 k hk hLt
  · intro k hk
    exact grantDrainMarksInteriorNativeEZeroAt
      ring s e (PPL.shiftRight ring p k)
      hLX hLY hSX hSY (hZero k hk)

/-- Full physical native nearest-zero arc after a strict interior
follower/follower edge. E preserves the old arc; F0/F2 can create
a closer protected root at X, and F1 a closer root at Y.
The returned root is the ACTUAL post-step nearest leader. -/
theorem grantDrainWeakStrictInteriorArcStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e) :
    ∃ root : Fin n,
      GrantDrainMarksNearestArc ring
        (grantDrainStep ring fresh update s e).native root g ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainStep ring fresh update s e).native root g := by
  have hEArc :=
    grantDrainWeakStrictInteriorEArc
      ring s e p g hNearest hZero hInside
  obtain ⟨hXPos, hXLt, hYPos, hYLt⟩ := hInside
  have hXSite : e =
      PPL.shiftRight ring p (PPL.cyclicOffset ring p e) :=
    (grantDrainMarksArcShiftRightOffset ring p e).symm
  have hYSite : ring.rightNeighbor e =
      PPL.shiftRight ring p
        (PPL.cyclicOffset ring p (ring.rightNeighbor e)) :=
    (grantDrainMarksArcShiftRightOffset
      ring p (ring.rightNeighbor e)).symm
  change ∃ root : Fin n,
    GrantDrainMarksNearestArc ring
      (grantDrainNativeNext ring s e) root g ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s e) root g
  cases hf : grantDrainSelect ring s e with
  | none =>
      refine ⟨p, ?_, ?_⟩
      · simpa [grantDrainNativeNext, hf] using hEArc.1
      · simpa [grantDrainNativeNext, hf] using hEArc.2
  | leftLocal =>
      obtain ⟨hNewNearest, hNewZero, _⟩ :=
        grantDrainWeakDeathProtectedArcBirth
          ring (nativeE ring s.native e) p g e
          (PPL.cyclicOffset ring p e)
          hEArc.1 hEArc.2 hXSite hXLt
      refine ⟨e, ?_, ?_⟩
      · simpa [grantDrainNativeNext, hf] using hNewNearest
      · simpa [grantDrainNativeNext, hf] using hNewZero
  | rightLocal =>
      obtain ⟨hNewNearest, hNewZero, _⟩ :=
        grantDrainWeakDeathProtectedArcBirth
          ring (nativeE ring s.native e) p g
          (ring.rightNeighbor e)
          (PPL.cyclicOffset ring p (ring.rightNeighbor e))
          hEArc.1 hEArc.2 hYSite hYLt
      refine ⟨ring.rightNeighbor e, ?_, ?_⟩
      · simpa [grantDrainNativeNext, hf] using hNewNearest
      · simpa [grantDrainNativeNext, hf] using hNewZero
  | cross =>
      obtain ⟨hNewNearest, hNewZero, _⟩ :=
        grantDrainWeakDeathProtectedArcBirth
          ring (nativeE ring s.native e) p g e
          (PPL.cyclicOffset ring p e)
          hEArc.1 hEArc.2 hXSite hXLt
      refine ⟨e, ?_, ?_⟩
      · simpa [grantDrainNativeNext, hf] using hNewNearest
      · simpa [grantDrainNativeNext, hf] using hNewZero

/-- The literal Boolean post corridor is TRUE for every
strictly interior selected edge, including all canonical FIRE
outcomes and arbitrary scratch/request/grant data. -/
theorem grantDrainWeakStrictInteriorCorridorStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e) :
    grantDrainLedgerCorridor ring
      (grantDrainStep ring fresh update s e) g = true := by
  obtain ⟨root, hNearestNow, hZeroNow⟩ :=
    grantDrainWeakStrictInteriorArcStep ring fresh update
      s e p g hNearest hZero hInside
  exact grantDrainWeakArcImpliesCorridor
    ring (grantDrainStep ring fresh update s e)
    root g hNearestNow hZeroNow

/-- First requested weak-to-weak hPhysical input, completed for
the STRICTLY INTERIOR class with no conditional post geometry.
The post grant is obtained from exact ghost-token soundness;
native leader/zero arc are proved on the literal E+FIRE step;
the surviving weak mark excludes a protected post source. -/
theorem grantDrainWeakToWeakStrictInteriorPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e) :
    ∀ j : Fin n,
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j →
      (grantDrainStep ring fresh update s e).grant j = true ∧
      (grantDrainStep ring fresh update s e).request j = false ∧
      ((grantDrainStep ring fresh update s e).native j).l =
        false ∧
      grantDrainLedgerWeakLock ring
        (grantDrainStep ring fresh update s e) j = true := by
  obtain ⟨hOldGrant, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨_, hFollower, hWeakLock, _⟩ := hWeakCase
  have hOldArc := grantDrainWeakDeathOldRightArc
    ring s p g hP hFollower hWeakLock hSource
  have hAvoid := grantDrainMarksStrictInteriorAvoidEndpoints
    ring p g e hInside
  have hHostNow :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some g := by
    change grantDrainLedgerHost ring fresh s e label.host = some g
    exact grantDrainMarksInteriorHostFrame
      ring fresh s e g label hHost
      (Ne.symm hAvoid.2.2.1)
      (Ne.symm hAvoid.2.2.2)
  have hGrantNow :
      (grantDrainStep ring fresh update s e).grant g = true :=
    grantDrainWeakSurvivingHostGrant
      ring hn fresh update s e label g g
      hHost hOldGrant hHostNow
  have hCorridorNow :
      grantDrainLedgerCorridor ring
        (grantDrainStep ring fresh update s e) g = true :=
    grantDrainWeakStrictInteriorCorridorStep
      ring fresh update s e p g
      hOldArc.1 hOldArc.2 hInside
  have hPhysicalG := grantDrainWeakToWeakPhysicalOfPostCorridor
    ring fresh update s e g label
    hNextWeak hHostNow hGrantNow hCorridorNow
  intro j hNewHost
  have heq : g = j :=
    Option.some.inj (hHostNow.symm.trans hNewHost)
  subst j
  exact hPhysicalG


/-- The protected-distance observer on two genuine nearest arcs
is ordered exactly by their underlying actual first-hit scans.
No Boolean shields are needed in this comparison. -/
theorem grantDrainWeakDistanceLeOfScans
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s t : GrantDrainState n Scratch)
    (p q g : Fin n)
    (hOldArc : GrantDrainMarksNearestArc ring s.native p g)
    (hNewArc : GrantDrainMarksNearestArc ring t.native q g)
    (hScanLe :
      grantDrainLeftLeaderDistance ring t.native g ≤
        grantDrainLeftLeaderDistance ring s.native g) :
    grantDrainStrongProtectedDistance ring t (some g) ≤
      grantDrainStrongProtectedDistance ring s (some g) := by
  have hOldScan :=
    grantDrainMarksScanOfNearestArc ring s.native p g hOldArc
  have hNewScan :=
    grantDrainMarksScanOfNearestArc ring t.native q g hNewArc
  have hOldDistance :=
    grantDrainMarksProtectedDistanceOfArc ring s p g hOldArc
  have hNewDistance :=
    grantDrainMarksProtectedDistanceOfArc ring t q g hNewArc
  rw [hNewScan, hOldScan] at hScanLe
  rw [hNewDistance, hOldDistance]
  exact hScanLe

/-- For an arbitrary strictly interior selected edge, the ACTUAL
first preceding leader cannot become farther away from the same
follower host g: E leaves all leader flags fixed; a canonical birth
at either selected site creates a closer leader. F0/F1/F2 all
satisfy the same nonincrease, including n-wrap. -/
theorem grantDrainWeakStrictInteriorDistanceLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e) :
    grantDrainStrongProtectedDistance ring
      (grantDrainStep ring fresh update s e) (some g) ≤
      grantDrainStrongProtectedDistance ring s (some g) := by
  obtain ⟨root, hNearestNow, _⟩ :=
    grantDrainWeakStrictInteriorArcStep
      ring fresh update s e p g hNearest hZero hInside
  have hEArc :=
    grantDrainWeakStrictInteriorEArc
      ring s e p g hNearest hZero hInside
  have hEScan :
      grantDrainLeftLeaderDistance ring
        (nativeE ring s.native e) g =
      grantDrainLeftLeaderDistance ring s.native g := by
    rw [grantDrainMarksScanOfNearestArc ring
      (nativeE ring s.native e) p g hEArc.1,
      grantDrainMarksScanOfNearestArc ring s.native p g hNearest]
  obtain ⟨hXPos, hXLt, hYPos, hYLt⟩ := hInside
  have hRawLe :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g ≤
      grantDrainLeftLeaderDistance ring s.native g := by
    change grantDrainLeftLeaderDistance ring
      (grantDrainNativeNext ring s e) g ≤
      grantDrainLeftLeaderDistance ring s.native g
    cases hf : grantDrainSelect ring s e with
    | none =>
        simpa [grantDrainNativeNext, hf] using
          Nat.le_of_eq hEScan
    | leftLocal =>
        have hBirth :=
          grantDrainMarksArcCanonicalBirthCloser
            ring (nativeE ring s.native e) p g
            (PPL.cyclicOffset ring p e)
            hEArc.1 hXPos hXLt
        rw [grantDrainMarksArcShiftRightOffset ring p e,
          hEScan] at hBirth
        have hFinal : grantDrainLeftLeaderDistance ring
            (canonicalBirth (nativeE ring s.native e) e) g ≤
          grantDrainLeftLeaderDistance ring s.native g :=
            Nat.le_of_lt hBirth
        simpa [grantDrainNativeNext, hf] using hFinal
    | rightLocal =>
        have hBirth :=
          grantDrainMarksArcCanonicalBirthCloser
            ring (nativeE ring s.native e) p g
            (PPL.cyclicOffset ring p (ring.rightNeighbor e))
            hEArc.1 hYPos hYLt
        rw [grantDrainMarksArcShiftRightOffset
          ring p (ring.rightNeighbor e), hEScan] at hBirth
        have hFinal : grantDrainLeftLeaderDistance ring
            (canonicalBirth (nativeE ring s.native e)
              (ring.rightNeighbor e)) g ≤
          grantDrainLeftLeaderDistance ring s.native g :=
            Nat.le_of_lt hBirth
        simpa [grantDrainNativeNext, hf] using hFinal
    | cross =>
        have hBirth :=
          grantDrainMarksArcCanonicalBirthCloser
            ring (nativeE ring s.native e) p g
            (PPL.cyclicOffset ring p e)
            hEArc.1 hXPos hXLt
        rw [grantDrainMarksArcShiftRightOffset ring p e,
          hEScan] at hBirth
        have hFinal : grantDrainLeftLeaderDistance ring
            (canonicalBirth (nativeE ring s.native e) e) g ≤
          grantDrainLeftLeaderDistance ring s.native g :=
            Nat.le_of_lt hBirth
        simpa [grantDrainNativeNext, hf] using hFinal
  exact grantDrainWeakDistanceLeOfScans
    ring s (grantDrainStep ring fresh update s e)
    p root g hNearest hNearestNow hRawLe

theorem grantDrainWeakStrictInteriorNotNominated
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hOldHost : label.host = some g)
    (hOldRequest : s.request g = false)
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e) :
    grantDrainLedgerNominatedHit ring s e label.host = false := by
  have hAvoid :=
    grantDrainMarksStrictInteriorAvoidEndpoints ring p g e hInside
  simp [grantDrainLedgerNominatedHit, hOldHost,
    hOldRequest, hAvoid.2.2.2]

/-- Complete weak-to-weak distance progress in the STRICTLY
INTERIOR class: the nominated bit is false, the grant remains
at g, and the source distance cannot increase under E+FIRE. -/
theorem grantDrainWeakToWeakStrictInteriorProgress
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e) :
    (if grantDrainLedgerNominatedHit ring s e label.host then
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label).host +
          1 ≤ grantDrainStrongProtectedDistance ring s label.host
      else
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label).host ≤
          grantDrainStrongProtectedDistance ring s label.host) := by
  obtain ⟨_, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨hOldRequest, hFollower, hWeakLock, _⟩ := hWeakCase
  have hOldArc := grantDrainWeakDeathOldRightArc
    ring s p g hP hFollower hWeakLock hSource
  have hNoHit := grantDrainWeakStrictInteriorNotNominated
    ring s e p g label hHost hOldRequest hInside
  have hAvoid :=
    grantDrainMarksStrictInteriorAvoidEndpoints ring p g e hInside
  have hHostNow :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some g := by
    change grantDrainLedgerHost ring fresh s e label.host = some g
    exact grantDrainMarksInteriorHostFrame
      ring fresh s e g label hHost
      (Ne.symm hAvoid.2.2.1)
      (Ne.symm hAvoid.2.2.2)
  have hDistanceLe :=
    grantDrainWeakStrictInteriorDistanceLe
      ring fresh update s e p g hOldArc.1 hOldArc.2 hInside
  rw [hNoHit, hHost, hHostNow]
  exact hDistanceLe

/-- COMPLETE weak -> weak LockBudget preservation for all
strictly interior edges, arbitrary n>=5 and all canonical
FIRE outcomes, with exact actual post physical and distance
certificates. Source and host boundary cases remain separate. -/
theorem grantDrainLockBudgetWeakToWeakStrictInteriorHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  have hPhysical :=
    grantDrainWeakToWeakStrictInteriorPhysical
      ring hn fresh update s e p g label
      hP hInv hHost hWeak hNextWeak hSource hInside
  have hProgress :=
    grantDrainWeakToWeakStrictInteriorProgress
      ring fresh update s e p g label
      hP hInv hHost hWeak hSource hInside
  exact grantDrainLockBudgetWeakToWeakOfPhysicalProgress
    ring fresh update s e label g hInv hHost hWeak hNextWeak
    hPhysical hProgress


/-- An edge outside every site of the old half-open source arc
[p,g) preserves its nearest leader and its full zero prefix,
even with arbitrary F0/F1/F2 activity elsewhere. This is an
exact pointwise native frame, not a protocol simulation premise. -/
theorem grantDrainWeakAwayArcFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (hOldNearest :
      GrantDrainMarksNearestArc ring s.native p g)
    (hOldZero :
      GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hAway : ∀ k : Nat,
      k < PPL.cyclicOffset ring p g →
      PPL.shiftRight ring p k ≠ e ∧
      PPL.shiftRight ring p k ≠ ring.rightNeighbor e) :
    GrantDrainMarksNearestArc ring
      (grantDrainStep ring fresh update s e).native p g ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainStep ring fresh update s e).native p g := by
  have hFrame : ∀ k : Nat,
      k < PPL.cyclicOffset ring p g →
      (grantDrainStep ring fresh update s e).native
        (PPL.shiftRight ring p k) =
      s.native (PPL.shiftRight ring p k) := by
    intro k hk
    have hOutside := hAway k hk
    change grantDrainNativeNext ring s e
      (PPL.shiftRight ring p k) =
      s.native (PPL.shiftRight ring p k)
    exact grantDrainMarksNativeOutsidePairFrame
      ring s e (PPL.shiftRight ring p k)
      hOutside.1 hOutside.2
  constructor
  · refine ⟨hOldNearest.1, ?_, ?_⟩
    · have hAt := hFrame 0 hOldNearest.1
      rw [grantDrainWeakDeathShiftRightZero ring p] at hAt
      rw [hAt]
      exact hOldNearest.2.1
    · intro k hk hlt
      rw [hFrame k hlt]
      exact hOldNearest.2.2 k hk hlt
  · intro k hk
    rw [hFrame k hk]
    exact hOldZero k hk

/-- For the exterior/off-pair class, the old weak zero
corridor remains true after an arbitrary native E+FIRE step,
and its first-leader distance is EXACTLY unchanged. -/
theorem grantDrainWeakAwayCorridorAndDistance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (hOldNearest :
      GrantDrainMarksNearestArc ring s.native p g)
    (hOldZero :
      GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hAway : ∀ k : Nat,
      k < PPL.cyclicOffset ring p g →
      PPL.shiftRight ring p k ≠ e ∧
      PPL.shiftRight ring p k ≠ ring.rightNeighbor e) :
    grantDrainLedgerCorridor ring
      (grantDrainStep ring fresh update s e) g = true ∧
    grantDrainStrongProtectedDistance ring
      (grantDrainStep ring fresh update s e) (some g) =
      grantDrainStrongProtectedDistance ring s (some g) := by
  have hPostArc := grantDrainWeakAwayArcFrame
    ring fresh update s e p g hOldNearest hOldZero hAway
  have hPostCorr := grantDrainWeakArcImpliesCorridor
    ring (grantDrainStep ring fresh update s e) p g
    hPostArc.1 hPostArc.2
  have hOldDistance :=
    grantDrainMarksProtectedDistanceOfArc
      ring s p g hOldNearest
  have hNewDistance :=
    grantDrainMarksProtectedDistanceOfArc
      ring (grantDrainStep ring fresh update s e)
      p g hPostArc.1
  constructor
  · exact hPostCorr
  · calc
      grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e) (some g) =
        PPL.cyclicOffset ring p g := hNewDistance
      _ = grantDrainStrongProtectedDistance ring s (some g) :=
        hOldDistance.symm

/-- The requested weak -> weak post physical certificate and
progress for an OFF-PAIR edge wholly away from the old source arc.
No unproved geometric premise is used; both input facts follow from the
literal native and token frames. -/
theorem grantDrainLockBudgetWeakToWeakAwayHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))
    (hNotX : g ≠ e)
    (hNotY : g ≠ ring.rightNeighbor e)
    (hAway : ∀ k : Nat,
      k < PPL.cyclicOffset ring p g →
      PPL.shiftRight ring p k ≠ e ∧
      PPL.shiftRight ring p k ≠ ring.rightNeighbor e) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨hGrantOld, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨hRequestOld, hFollowerOld, hLockOld, _⟩ :=
    hWeakCase
  have hOldArc := grantDrainWeakDeathOldRightArc
    ring s p g hP hFollowerOld hLockOld hSource
  have hFrame := grantDrainWeakAwayCorridorAndDistance
    ring fresh update s e p g hOldArc.1 hOldArc.2 hAway
  have hPostHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some g := by
    change grantDrainLedgerHost ring fresh s e label.host = some g
    exact grantDrainMarksInteriorHostFrame
      ring fresh s e g label hHost hNotX hNotY
  have hPostGrant :
      (grantDrainStep ring fresh update s e).grant g = true :=
    grantDrainWeakSurvivingHostGrant
      ring hn fresh update s e label g g
      hHost hGrantOld hPostHost
  have hPostPhysicalG :=
    grantDrainWeakToWeakPhysicalOfPostCorridor
      ring fresh update s e g label
      hNextWeak hPostHost hPostGrant hFrame.1
  have hPhysical : ∀ j : Fin n,
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j →
      (grantDrainStep ring fresh update s e).grant j = true ∧
      (grantDrainStep ring fresh update s e).request j = false ∧
      ((grantDrainStep ring fresh update s e).native j).l =
        false ∧
      grantDrainLedgerWeakLock ring
        (grantDrainStep ring fresh update s e) j = true := by
    intro j hj
    have hjEq : g = j :=
      Option.some.inj (hPostHost.symm.trans hj)
    subst j
    exact hPostPhysicalG
  have hNoHit :
      grantDrainLedgerNominatedHit ring s e label.host = false := by
    simp [grantDrainLedgerNominatedHit,
      hHost, hRequestOld, Ne.symm hNotY]
  have hProgress :
      (if grantDrainLedgerNominatedHit ring s e label.host then
          grantDrainStrongProtectedDistance ring
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerStep ring fresh update s e label).host +
            1 ≤ grantDrainStrongProtectedDistance ring s label.host
        else
          grantDrainStrongProtectedDistance ring
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerStep ring fresh update s e label).host ≤
            grantDrainStrongProtectedDistance ring s label.host) := by
    rw [hNoHit, hHost, hPostHost]
    exact Nat.le_of_eq hFrame.2
  exact grantDrainLockBudgetWeakToWeakOfPhysicalProgress
    ring fresh update s e label g hInv hHost hWeak hNextWeak
    hPhysical hProgress


/-- A QUIET OLD LEADER at X interacting with a zero-signal
follower at Y cannot create a positive signal or remove a leader.
Unlike the protected-source theorem, the source SHIELD is arbitrary:
this is the previously missing weak-root outgoing literal row. -/
theorem grantDrainWeakQuietLeaderOutgoingPair
    (a b : CertNative)
    (hal : a.l = true) (has : a.sg = false)
    (hbl : b.l = false) (hbs : b.sg = false) :
    (certLiteralEPair a b).1.l = true ∧
    (certLiteralEPair a b).1.sg = false ∧
    (certLiteralEPair a b).2.l = false ∧
    (certLiteralEPair a b).2.sg = false := by
  rcases a with ⟨al, ab, ah, asg⟩
  rcases b with ⟨bl, bb, bh, bsg⟩
  cases al <;> cases asg <;> cases bl <;> cases bsg <;>
    simp [certLiteralEPair] at hal has hbl hbs ⊢

/-- Exact native E frame at a quiet OLD leader source, with
no assumption on its shield field. This is the weak analogue
of grantDrainMarksProtectedSourceEFrame: all leader flags stay,
and each OLD zero-signal site remains zero-signal. -/
theorem grantDrainWeakQuietSourceEFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (p i : Fin n)
    (hPL : (s.native p).l = true)
    (hPS : (s.native p).sg = false)
    (hYL : (s.native (ring.rightNeighbor p)).l = false)
    (hYS : (s.native (ring.rightNeighbor p)).sg = false) :
    (nativeE ring s.native p i).l = (s.native i).l ∧
    ((s.native i).sg = false →
      (nativeE ring s.native p i).sg = false) := by
  have hPair := grantDrainWeakQuietLeaderOutgoingPair
    (s.native p) (s.native (ring.rightNeighbor p))
    hPL hPS hYL hYS
  have hDistinct :=
    grantDrainMarksNeighborDistinct
      (by omega : 3 ≤ n) ring p
  have hResponder :
      nativeE ring s.native p (ring.rightNeighbor p) =
        (certLiteralEPair
          (s.native p) (s.native (ring.rightNeighbor p))).2 := by
    unfold nativeE
    simp only [if_neg hDistinct, if_pos rfl, ↓reduceIte]
  by_cases hi : i = p
  · subst i
    rw [grantDrainMarksNativeESource]
    refine ⟨?_, ?_⟩
    · rw [hPair.1, hPL]
    · intro _
      exact hPair.2.1
  · by_cases hy : i = ring.rightNeighbor p
    · subst i
      rw [hResponder]
      refine ⟨?_, ?_⟩
      · rw [hPair.2.2.1, hYL]
      · intro _
        exact hPair.2.2.2
    · have hFrame :
          nativeE ring s.native p i = s.native i := by
        simp [nativeE, hi, hy]
      rw [hFrame]
      exact ⟨rfl, fun h => h⟩

/-- An outgoing weak-source edge p -> p+1, when the host is
strictly farther than its immediate successor, preserves the
whole old nearest zero arc THROUGH native E. Root p may be
unshielded; all that matters is its zero-signal bit. -/
theorem grantDrainWeakOutgoingSourceEArc
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (p g : Fin n)
    (hOldNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hOldZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hLong : 1 < PPL.cyclicOffset ring p g) :
    GrantDrainMarksNearestArc ring (nativeE ring s.native p) p g ∧
    GrantDrainMarksZeroOffsetArc ring (nativeE ring s.native p) p g := by
  have hRightSite :
      ring.rightNeighbor p = PPL.shiftRight ring p 1 := by
    apply Fin.ext
    rfl
  have hYL : (s.native (ring.rightNeighbor p)).l = false := by
    rw [hRightSite]
    exact hOldNearest.2.2 1 (by omega) hLong
  have hYS : (s.native (ring.rightNeighbor p)).sg = false := by
    rw [hRightSite]
    exact hOldZero 1 hLong
  have hPS : (s.native p).sg = false := by
    have h := hOldZero 0 hOldNearest.1
    rw [grantDrainWeakDeathShiftRightZero ring p] at h
    exact h
  have hFrame : ∀ i : Fin n,
      (nativeE ring s.native p i).l = (s.native i).l ∧
      ((s.native i).sg = false →
        (nativeE ring s.native p i).sg = false) := by
    intro i
    exact grantDrainWeakQuietSourceEFrame
      ring hn s p i hOldNearest.2.1 hPS hYL hYS
  constructor
  · refine ⟨hOldNearest.1, ?_, ?_⟩
    · rw [(hFrame p).1]
      exact hOldNearest.2.1
    · intro k hk hLt
      rw [(hFrame (PPL.shiftRight ring p k)).1]
      exact hOldNearest.2.2 k hk hLt
  · intro k hk
    exact (hFrame (PPL.shiftRight ring p k)).2
      (hOldZero k hk)

/-- For the long outgoing source edge, the ACTUAL E+FIRE
native step still has a nearest zero arc, rooted either at
the old leader p or a NEW leader at its immediate successor.
This handles F0/F1/F2 without assuming the source was shielded. -/
theorem grantDrainWeakOutgoingSourceArcStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (p g : Fin n)
    (hOldNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hOldZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hLong : 1 < PPL.cyclicOffset ring p g) :
    ∃ root : Fin n,
      GrantDrainMarksNearestArc ring
        (grantDrainStep ring fresh update s p).native root g ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainStep ring fresh update s p).native root g ∧
      (root = p ∨ root = ring.rightNeighbor p) := by
  have hEArc :=
    grantDrainWeakOutgoingSourceEArc
      ring hn s p g hOldNearest hOldZero hLong
  have hPAt :
      p = PPL.shiftRight ring p 0 :=
    (grantDrainWeakDeathShiftRightZero ring p).symm
  have hYAt :
      ring.rightNeighbor p = PPL.shiftRight ring p 1 := by
    apply Fin.ext
    rfl
  change ∃ root : Fin n,
    GrantDrainMarksNearestArc ring
      (grantDrainNativeNext ring s p) root g ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s p) root g ∧
    (root = p ∨ root = ring.rightNeighbor p)
  cases hf : grantDrainSelect ring s p with
  | none =>
      refine ⟨p, ?_, ?_, Or.inl rfl⟩
      · simpa [grantDrainNativeNext, hf] using hEArc.1
      · simpa [grantDrainNativeNext, hf] using hEArc.2
  | leftLocal =>
      obtain ⟨hNearest, hZero, _⟩ :=
        grantDrainWeakDeathProtectedArcBirth
          ring (nativeE ring s.native p) p g p 0
          hEArc.1 hEArc.2 hPAt hOldNearest.1
      refine ⟨p, ?_, ?_, Or.inl rfl⟩
      · simpa [grantDrainNativeNext, hf] using hNearest
      · simpa [grantDrainNativeNext, hf] using hZero
  | rightLocal =>
      obtain ⟨hNearest, hZero, _⟩ :=
        grantDrainWeakDeathProtectedArcBirth
          ring (nativeE ring s.native p) p g
          (ring.rightNeighbor p) 1
          hEArc.1 hEArc.2 hYAt hLong
      refine ⟨ring.rightNeighbor p, ?_, ?_, Or.inr rfl⟩
      · simpa [grantDrainNativeNext, hf] using hNearest
      · simpa [grantDrainNativeNext, hf] using hZero
  | cross =>
      obtain ⟨hNearest, hZero, _⟩ :=
        grantDrainWeakDeathProtectedArcBirth
          ring (nativeE ring s.native p) p g p 0
          hEArc.1 hEArc.2 hPAt hOldNearest.1
      refine ⟨p, ?_, ?_, Or.inl rfl⟩
      · simpa [grantDrainNativeNext, hf] using hNearest
      · simpa [grantDrainNativeNext, hf] using hZero

/-- The actual weak-source outgoing edge cannot increase the
protected distance at the SAME host g. If F1 fires at p+1,
the nearest source moves one step right; otherwise it remains p. -/
theorem grantDrainWeakOutgoingSourceCorridorDistance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (p g : Fin n)
    (hOldNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hOldZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hLong : 1 < PPL.cyclicOffset ring p g) :
    grantDrainLedgerCorridor ring
      (grantDrainStep ring fresh update s p) g = true ∧
    grantDrainStrongProtectedDistance ring
      (grantDrainStep ring fresh update s p) (some g) ≤
      grantDrainStrongProtectedDistance ring s (some g) := by
  obtain ⟨root, hPostNearest, hPostZero, hChoice⟩ :=
    grantDrainWeakOutgoingSourceArcStep
      ring hn fresh update s p g
      hOldNearest hOldZero hLong
  have hCorridor := grantDrainWeakArcImpliesCorridor
    ring (grantDrainStep ring fresh update s p)
    root g hPostNearest hPostZero
  have hOldDistance :=
    grantDrainMarksProtectedDistanceOfArc
      ring s p g hOldNearest
  have hNewDistance :=
    grantDrainMarksProtectedDistanceOfArc
      ring (grantDrainStep ring fresh update s p)
      root g hPostNearest
  constructor
  · exact hCorridor
  · rw [hNewDistance, hOldDistance]
    rcases hChoice with hp | hy
    · subst root
      exact Nat.le_refl _
    · subst root
      have hYAt :
          ring.rightNeighbor p = PPL.shiftRight ring p 1 := by
        apply Fin.ext
        rfl
      have hOffset :
          PPL.cyclicOffset ring (ring.rightNeighbor p) g =
            PPL.cyclicOffset ring p g - 1 := by
        rw [hYAt]
        exact grantDrainMarksArcOffsetSubtract
          ring p g 1 (by omega)
      rw [hOffset]
      omega

/-- The complete weak-to-weak LockBudget case for a long
OUTGOING edge from the old weak root p (p -> p+1), provided
the old host lies beyond p+1. Every FIRE selector is included.
The adjacent p -> g case is a sink rather than a surviving label. -/
theorem grantDrainLockBudgetWeakToWeakOutgoingRootHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (p g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s p label).mark =
        .weak)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))
    (hLong : 1 < PPL.cyclicOffset ring p g) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s p)
      (grantDrainLedgerStep ring fresh update s p label) := by
  obtain ⟨hOldGrant, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨hOldRequest, hOldFollower, hOldWeakLock, _⟩ :=
    hWeakCase
  have hOldArc := grantDrainWeakDeathOldRightArc
    ring s p g hP hOldFollower hOldWeakLock hSource
  have hNotX : g ≠ p := by
    intro hEq
    rw [hEq, hOldArc.1.2.1] at hOldFollower
    cases hOldFollower
  have hNotY : g ≠ ring.rightNeighbor p := by
    intro hEq
    have hOffsetOne :
        PPL.cyclicOffset ring p g = 1 := by
      rw [hEq]
      have hYAt :
          ring.rightNeighbor p = PPL.shiftRight ring p 1 := by
        apply Fin.ext
        rfl
      rw [hYAt]
      exact grantDrainWeakDeathOffsetShiftRight
        ring p 1 (by omega)
    omega
  have hHostNow :
      (grantDrainLedgerStep ring fresh update s p label).host =
        some g := by
    change grantDrainLedgerHost ring fresh s p label.host = some g
    exact grantDrainMarksInteriorHostFrame
      ring fresh s p g label hHost hNotX hNotY
  have hNewGrant :
      (grantDrainStep ring fresh update s p).grant g = true :=
    grantDrainWeakSurvivingHostGrant
      ring hn fresh update s p label g g
      hHost hOldGrant hHostNow
  have hNowGeometry :=
    grantDrainWeakOutgoingSourceCorridorDistance
      ring hn fresh update s p g
      hOldArc.1 hOldArc.2 hLong
  have hPhysicalAtG :=
    grantDrainWeakToWeakPhysicalOfPostCorridor
      ring fresh update s p g label
      hNextWeak hHostNow hNewGrant hNowGeometry.1
  have hPhysical : ∀ j : Fin n,
      (grantDrainLedgerStep ring fresh update s p label).host =
        some j →
      (grantDrainStep ring fresh update s p).grant j = true ∧
      (grantDrainStep ring fresh update s p).request j = false ∧
      ((grantDrainStep ring fresh update s p).native j).l =
        false ∧
      grantDrainLedgerWeakLock ring
        (grantDrainStep ring fresh update s p) j = true := by
    intro j hj
    have heq : g = j :=
      Option.some.inj (hHostNow.symm.trans hj)
    subst j
    exact hPhysicalAtG
  have hNoHit :
      grantDrainLedgerNominatedHit ring s p label.host = false := by
    simp [grantDrainLedgerNominatedHit,
      hHost, hOldRequest, Ne.symm hNotY]
  have hProgress :
      (if grantDrainLedgerNominatedHit ring s p label.host then
          grantDrainStrongProtectedDistance ring
            (grantDrainStep ring fresh update s p)
            (grantDrainLedgerStep ring fresh update s p label).host +
              1 ≤ grantDrainStrongProtectedDistance ring s label.host
        else
          grantDrainStrongProtectedDistance ring
            (grantDrainStep ring fresh update s p)
            (grantDrainLedgerStep ring fresh update s p label).host ≤
            grantDrainStrongProtectedDistance ring s label.host) := by
    rw [hNoHit, hHost, hHostNow]
    exact hNowGeometry.2
  exact grantDrainLockBudgetWeakToWeakOfPhysicalProgress
    ring fresh update s p label g
    hInv hHost hWeak hNextWeak hPhysical hProgress


/-- A surviving old ledger identity whose OLD host is NOT the
selected responder never changes its host location. If it was X,
it may retire but cannot move; if it was off-pair it is framed.
This handles the n-1 wrap case where the weak grant host itself
is the initiator on an incoming-to-root edge. -/
theorem grantDrainWeakHostUnmovedIfNotResponder
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g j : Fin n) (label : GrantDrainLedgerLabel n)
    (hOldHost : label.host = some g)
    (hNotResponder : g ≠ ring.rightNeighbor e)
    (hNextHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    j = g := by
  have hRaw :
      grantDrainLedgerHost ring fresh s e (some g) = some j := by
    change grantDrainLedgerHost ring fresh s e label.host =
      some j at hNextHost
    rw [hOldHost] at hNextHost
    exact hNextHost
  by_cases hX : g = e
  · subst g
    cases hh :
        (s.grant e &&
          (grantDrainLedgerRow ring fresh s e).1.grant) with
    | false =>
        have hc : (none : Option (Fin n)) = some j := by
          simpa [grantDrainLedgerHost, hh] using hRaw
        cases hc
    | true =>
        have he : some e = some j := by
          simpa [grantDrainLedgerHost, hh] using hRaw
        exact (Option.some.inj he).symm
  · have he : some g = some j := by
      simpa [grantDrainLedgerHost, hX, hNotResponder] using hRaw
    exact (Option.some.inj he).symm

/-- Incoming-to-old-source service e -> p: if native E leaves
p a leader, every later old corridor site is still a zero-signal
follower and p itself is a zero-signal leader. F0/F1/F2 may only
overwrite an endpoint, so the result holds after the actual FIRE. -/
theorem grantDrainWeakIncomingSourceSurvivingArc
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (hOldNearest :
      GrantDrainMarksNearestArc ring s.native p g)
    (hOldZero :
      GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hESurvives : (nativeE ring s.native e p).l = true) :
    GrantDrainMarksNearestArc ring
      (grantDrainStep ring fresh update s e).native p g ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainStep ring fresh update s e).native p g := by
  have hOldZeroP : (s.native p).sg = false := by
    have hh := hOldZero 0 hOldNearest.1
    rw [grantDrainWeakDeathShiftRightZero ring p] at hh
    exact hh
  have hEZero :
      GrantDrainMarksZeroOffsetArc ring
        (nativeE ring s.native e) p g :=
    grantDrainWeakDeathRightZeroAfterE
      ring hn s e p g hIncoming
      hOldNearest.2.1 hOldZeroP hOldZero
  have hNextLeader :
      (grantDrainNativeNext ring s e p).l = true :=
    GrantDrainShared.sharedPaperNativeKeepsELeader
      ring s e p hESurvives
  have hPostZero :
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainNativeNext ring s e) p g := by
    intro k hk
    have hz := hEZero k hk
    cases hf : grantDrainSelect ring s e with
    | none =>
        simpa [grantDrainNativeNext, hf] using hz
    | leftLocal =>
        have hh := grantDrainMarksInteriorBirthPreservesZero
          (nativeE ring s.native e) e
          (PPL.shiftRight ring p k) hz
        simpa [grantDrainNativeNext, hf] using hh
    | rightLocal =>
        have hh := grantDrainMarksInteriorBirthPreservesZero
          (nativeE ring s.native e) (ring.rightNeighbor e)
          (PPL.shiftRight ring p k) hz
        simpa [grantDrainNativeNext, hf] using hh
    | cross =>
        have hh := grantDrainMarksInteriorBirthPreservesZero
          (nativeE ring s.native e) e
          (PPL.shiftRight ring p k) hz
        simpa [grantDrainNativeNext, hf] using hh
  change GrantDrainMarksNearestArc ring
      (grantDrainNativeNext ring s e) p g ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s e) p g
  constructor
  · refine ⟨hOldNearest.1, hNextLeader, ?_⟩
    intro k hk hklt
    have hFrame := grantDrainMarksIncomingSourceInteriorFrame
      (by omega : 3 ≤ n) ring s p g e
      hIncoming k hk hklt
    rw [hFrame]
    exact hOldNearest.2.2 k hk hklt
  · exact hPostZero

theorem grantDrainLockBudgetWeakToWeakIncomingRootHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hIncoming : ring.rightNeighbor e = p)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g)) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨hOldGrant, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨hOldRequest, hOldFollower, hOldLock, _⟩ := hWeakCase
  have hOldArc := grantDrainWeakDeathOldRightArc
    ring s p g hP hOldFollower hOldLock hSource
  have hNotPG : p ≠ g := by
    intro heq
    have hOldLeader := hOldArc.1.2.1
    rw [heq, hOldFollower] at hOldLeader
    cases hOldLeader
  have hNotY : g ≠ ring.rightNeighbor e := by
    rw [hIncoming]
    exact Ne.symm hNotPG
  cases hESurvives : (nativeE ring s.native e p).l with
  | false =>
      exact grantDrainWeakDeathLockBudgetStepHolds
        ring hn fresh update s e p g label
        hP hInv hHost hWeak hIncoming hSource hESurvives
  | true =>
      have hPostArc :=
        grantDrainWeakIncomingSourceSurvivingArc
          ring hn fresh update s e p g
          hIncoming hOldArc.1 hOldArc.2 hESurvives
      have hPostCorr :=
        grantDrainWeakArcImpliesCorridor
          ring (grantDrainStep ring fresh update s e)
          p g hPostArc.1 hPostArc.2
      have hOldDistance :=
        grantDrainMarksProtectedDistanceOfArc
          ring s p g hOldArc.1
      have hNewDistance :=
        grantDrainMarksProtectedDistanceOfArc
          ring (grantDrainStep ring fresh update s e)
          p g hPostArc.1
      have hDistanceEq :
          grantDrainStrongProtectedDistance ring
            (grantDrainStep ring fresh update s e) (some g) =
          grantDrainStrongProtectedDistance ring s (some g) :=
        hNewDistance.trans hOldDistance.symm
      have hPhysical : ∀ j : Fin n,
          (grantDrainLedgerStep ring fresh update s e label).host =
            some j →
          (grantDrainStep ring fresh update s e).grant j = true ∧
          (grantDrainStep ring fresh update s e).request j = false ∧
          ((grantDrainStep ring fresh update s e).native j).l =
            false ∧
          grantDrainLedgerWeakLock ring
            (grantDrainStep ring fresh update s e) j = true := by
        intro j hj
        have hSame := grantDrainWeakHostUnmovedIfNotResponder
          ring fresh update s e g j label hHost hNotY hj
        subst j
        have hNewGrant := grantDrainWeakSurvivingHostGrant
          ring hn fresh update s e label g g
          hHost hOldGrant hj
        exact grantDrainWeakToWeakPhysicalOfPostCorridor
          ring fresh update s e g label
          hNextWeak hj hNewGrant hPostCorr
      have hNoHit :
          grantDrainLedgerNominatedHit ring s e label.host =
            false := by
        simp [grantDrainLedgerNominatedHit,
          hHost, hOldRequest, Ne.symm hNotY]
      have hProgress :
          (if grantDrainLedgerNominatedHit ring s e label.host then
              grantDrainStrongProtectedDistance ring
                (grantDrainStep ring fresh update s e)
                (grantDrainLedgerStep ring fresh update s e label).host +
                1 ≤ grantDrainStrongProtectedDistance ring s label.host
            else
              grantDrainStrongProtectedDistance ring
                (grantDrainStep ring fresh update s e)
                (grantDrainLedgerStep ring fresh update s e label).host ≤
                grantDrainStrongProtectedDistance ring s label.host) := by
        rw [hNoHit]
        cases hh :
            (grantDrainLedgerStep ring fresh update s e label).host with
        | none =>
            simp [grantDrainStrongProtectedDistance_none]
        | some j =>
            have hSame := grantDrainWeakHostUnmovedIfNotResponder
              ring fresh update s e g j label hHost hNotY hh
            subst j
            simpa [hHost] using (Nat.le_of_eq hDistanceEq)
      exact grantDrainLockBudgetWeakToWeakOfPhysicalProgress
        ring fresh update s e label g hInv hHost hWeak hNextWeak
        hPhysical hProgress


/-- An incoming host edge e -> g places its initiator at the
immediate left neighbor of the host, including the 0/n wrap. -/
theorem grantDrainWeakIncomingHostLeftNeighbor
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (e g : Fin n) (hEdge : ring.rightNeighbor e = g) :
    PPL.shiftLeft ring g 1 = e := by
  rw [← hEdge]
  apply Fin.ext
  change (((e.val + 1) % n + n - 1 % n) % n) = e.val
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt]
    have heq : e.val + 1 + n - 1 = n + e.val := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt e.isLt]
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self]
    have hs : 0 + n - 1 = e.val := by omega
    rw [hs, Nat.mod_eq_of_lt e.isLt]

/-- Full source-level scan-distance DROP on an incoming edge
e -> g with old source-to-host length d>=2. Every old leader
bit STRICTLY BEFORE the new host e is untouched, so even a
simultaneous canonical birth at e or g cannot change the first
preceding leader scan at e. The distance decreases exactly one,
not merely nonincreases, for EVERY n>=5. -/
theorem grantDrainWeakIncomingHostScanDrops
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (d : Nat)
    (hEdge : ring.rightNeighbor e = g)
    (hOldArc : GrantDrainMarksNearestArc ring s.native p g)
    (hOff : PPL.cyclicOffset ring p g = d)
    (hLong : 2 ≤ d) :
    grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native e + 1 =
      grantDrainLeftLeaderDistance ring s.native g := by
  have hDlt : d < n := by
    rw [← hOff]
    exact GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring p g
  have hPre := grantDrainWeakIncomingHostLeftNeighbor
    ring hn e g hEdge
  have hEAt : e = PPL.shiftRight ring p (d - 1) := by
    have hLeft := grantDrainMarksArcLeftHostSite
      ring p g d hOff (by omega)
    rw [hPre] at hLeft
    exact hLeft
  have hGAt : g = PPL.shiftRight ring p d := by
    rw [← hOff]
    exact (grantDrainMarksArcShiftRightOffset ring p g).symm
  have hFrame : ∀ k : Nat, k < d - 1 →
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftRight ring p k)).l =
      (s.native (PPL.shiftRight ring p k)).l := by
    intro k hk
    have hklt : k < n := by omega
    have hdlt : d - 1 < n := by omega
    have hNotX :
        PPL.shiftRight ring p k ≠ e := by
      rw [hEAt]
      exact grantDrainWeakDeathShiftRightNe
        ring p k (d - 1) hklt hdlt (by omega)
    have hNotY :
        PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
      rw [hEdge, hGAt]
      exact grantDrainWeakDeathShiftRightNe
        ring p k d hklt hDlt (by omega)
    have hf := grantDrainMarksNativeOutsidePairFrame
      ring s e (PPL.shiftRight ring p k) hNotX hNotY
    exact congrArg CertNative.l hf
  have hScan := grantDrainMarksArcLeftHostDistance
    ring s.native
    (grantDrainStep ring fresh update s e).native
    p g d hOff hLong hOldArc hFrame
  rw [hPre] at hScan
  exact hScan

/-- The actual protected-distance observer, not just its
unclamped raw scan, drops EXACTLY one when a weak grant moves
counterclockwise from old host g to e on an incoming edge,
provided its old leader distance is >=2. This holds for any
canonical FIRE outcome; label survival is a separate token fact. -/
theorem grantDrainWeakIncomingHostProtectedDistanceDrops
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (d : Nat)
    (hEdge : ring.rightNeighbor e = g)
    (hOldArc : GrantDrainMarksNearestArc ring s.native p g)
    (hOff : PPL.cyclicOffset ring p g = d)
    (hLong : 2 ≤ d) :
    grantDrainStrongProtectedDistance ring
        (grantDrainStep ring fresh update s e) (some e) + 1 =
      grantDrainStrongProtectedDistance ring s (some g) := by
  have hScan := grantDrainWeakIncomingHostScanDrops
    ring hn fresh update s e p g d
    hEdge hOldArc hOff hLong
  have hOldRaw := grantDrainMarksScanOfNearestArc
    ring s.native p g hOldArc
  rw [hOff] at hOldRaw
  have hNewPositive :
      0 < grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native e := by
    omega
  have hNewBound :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native e ≤ n := by
    have hdlt : d < n := by
      rw [← hOff]
      exact GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring p g
    omega
  have hNewDistance := grantDrainStrongProtectedDistance_eq_raw
    ring (grantDrainStep ring fresh update s e)
    e hNewPositive hNewBound
  have hOldDistance :=
    grantDrainMarksProtectedDistanceOfArc ring s p g hOldArc
  rw [hNewDistance, hOldDistance, hOff]
  omega


theorem grantDrainWeakIncomingHostSurvivorMoves
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g j : Fin n) (label : GrantDrainLedgerLabel n)
    (hOldHost : label.host = some g)
    (hEdge : ring.rightNeighbor e = g)
    (hOldRequest : s.request g = false)
    (hOldGrant : s.grant g = true)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    j = e := by
  have hDistinct : g ≠ e := by
    rw [← hEdge]
    exact grantDrainMarksNeighborDistinct
      (by omega : 3 ≤ n) ring e
  have hYRow :
      (grantDrainLedgerRow ring fresh s e).2.grant = false := by
    unfold grantDrainLedgerRow
    rw [hEdge, hOldRequest, hOldGrant]
    exact grantDrainMarksUnheldResponderNoStutter
      (s.request e) (s.grant e)
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e g).l
      (fresh s e) (grantDrainSelect ring s e)
  have hRaw :
      grantDrainLedgerHost ring fresh s e (some g) = some j := by
    change grantDrainLedgerHost ring fresh s e label.host =
      some j at hNewHost
    rw [hOldHost] at hNewHost
    exact hNewHost
  cases hs : grantDrainLedgerYSource
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l
      (grantDrainSelect ring s e)
      (grantDrainLedgerRow ring fresh s e) with
  | none =>
      have hEval :
          grantDrainLedgerHost ring fresh s e (some g) =
            none := by
        simp only [grantDrainLedgerHost, if_neg hDistinct,
          if_pos hEdge.symm, hs]
      rw [hEval] at hRaw
      cases hRaw
  | some stayed =>
      cases stayed with
      | true =>
          have hYGrant := grantDrainWeakYSourceStaySound
            (s.request (ring.rightNeighbor e))
            (s.grant (ring.rightNeighbor e))
            (grantDrainNativeNext ring s e e).l
            (grantDrainNativeNext ring s e
              (ring.rightNeighbor e)).l
            (grantDrainSelect ring s e)
            (grantDrainLedgerRow ring fresh s e) hs
          rw [hYRow] at hYGrant
          cases hYGrant
      | false =>
          have hEval :
              grantDrainLedgerHost ring fresh s e (some g) =
                some e := by
            simp only [grantDrainLedgerHost, if_neg hDistinct,
              if_pos hEdge.symm, hs]
          have heq : some e = some j := hEval.symm.trans hRaw
          exact (Option.some.inj heq).symm

/-- The entire prefix [p,e) before the new moving host is
framed on the actual canonical E+FIRE step, even when the
selected pair (e,g) crosses the representation wrap. Only
distance d>=2 and the old-nearest-arc coordinates are needed. -/
theorem grantDrainWeakIncomingHostPrefixFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (d : Nat)
    (hEdge : ring.rightNeighbor e = g)
    (hOff : PPL.cyclicOffset ring p g = d)
    (hLong : 2 ≤ d) :
    ∀ k : Nat, k < d - 1 →
      (grantDrainStep ring fresh update s e).native
        (PPL.shiftRight ring p k) =
      s.native (PPL.shiftRight ring p k) := by
  have hDlt : d < n := by
    rw [← hOff]
    exact GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring p g
  have hPre := grantDrainWeakIncomingHostLeftNeighbor
    ring hn e g hEdge
  have hEAt : e = PPL.shiftRight ring p (d - 1) := by
    have hLeft := grantDrainMarksArcLeftHostSite
      ring p g d hOff (by omega)
    rw [hPre] at hLeft
    exact hLeft
  have hGAt : g = PPL.shiftRight ring p d := by
    rw [← hOff]
    exact (grantDrainMarksArcShiftRightOffset ring p g).symm
  intro k hk
  have hKBound : k < n := by omega
  have hEMinusBound : d - 1 < n := by omega
  have hNotX :
      PPL.shiftRight ring p k ≠ e := by
    rw [hEAt]
    exact grantDrainWeakDeathShiftRightNe
      ring p k (d - 1) hKBound hEMinusBound (by omega)
  have hNotY :
      PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
    rw [hEdge, hGAt]
    exact grantDrainWeakDeathShiftRightNe
      ring p k d hKBound hDlt (by omega)
  change grantDrainNativeNext ring s e
    (PPL.shiftRight ring p k) =
    s.native (PPL.shiftRight ring p k)
  exact grantDrainMarksNativeOutsidePairFrame
    ring s e (PPL.shiftRight ring p k) hNotX hNotY

/-- The exact new zero corridor p..e, EXCLUDING the newly moved
host e, survives every E/FIRE outcome on its incoming edge.
The old source p remains the nearest predecessor of e because
all intervening leader bits are outside the selected pair. -/
theorem grantDrainWeakIncomingHostPrefixArc
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (d : Nat)
    (hEdge : ring.rightNeighbor e = g)
    (hOldNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hOldZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hOff : PPL.cyclicOffset ring p g = d)
    (hLong : 2 ≤ d) :
    GrantDrainMarksNearestArc ring
      (grantDrainStep ring fresh update s e).native p e ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainStep ring fresh update s e).native p e := by
  have hDlt : d < n := by
    rw [← hOff]
    exact GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring p g
  have hPre := grantDrainWeakIncomingHostLeftNeighbor
    ring hn e g hEdge
  have hEAt : e = PPL.shiftRight ring p (d - 1) := by
    have hLeft := grantDrainMarksArcLeftHostSite
      ring p g d hOff (by omega)
    rw [hPre] at hLeft
    exact hLeft
  have hOffE :
      PPL.cyclicOffset ring p e = d - 1 := by
    rw [hEAt]
    exact grantDrainWeakDeathOffsetShiftRight
      ring p (d - 1) (by omega)
  have hFrame := grantDrainWeakIncomingHostPrefixFrame
    ring hn fresh update s e p g d hEdge hOff hLong
  constructor
  · refine ⟨by rw [hOffE]; omega, ?_, ?_⟩
    · have hh := hFrame 0 (by omega)
      rw [grantDrainWeakDeathShiftRightZero ring p] at hh
      rw [hh]
      exact hOldNearest.2.1
    · intro k hk hklt
      rw [hOffE] at hklt
      rw [hFrame k hklt]
      exact hOldNearest.2.2 k hk (by omega)
  · intro k hk
    rw [hOffE] at hk
    rw [hFrame k hk]
    exact hOldZero k (by omega)

theorem grantDrainWeakIncomingHostLiveDistanceLong
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hEdge : ring.rightNeighbor e = g)
    (hOldNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hWeakNext :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some e) :
    2 ≤ PPL.cyclicOffset ring p g := by
  have hPositive : 0 < PPL.cyclicOffset ring p g :=
    hOldNearest.1
  by_cases hOne : PPL.cyclicOffset ring p g = 1
  · have hPre := grantDrainWeakIncomingHostLeftNeighbor
      ring hn e g hEdge
    have hSite := grantDrainMarksArcLeftHostSite
      ring p g 1 hOne (by omega)
    rw [hPre, Nat.sub_self,
      grantDrainWeakDeathShiftRightZero ring p] at hSite
    have heq : e = p := hSite
    have hOldLeader : (s.native p).l = true :=
      hOldNearest.2.1
    have hFinalLeader :=
      grantDrainMarksOutgoingLeaderNext ring s p hOldLeader
    have hPostFollower := grantDrainWeakNextFollower
      ring fresh update s e e label hWeakNext hNewHost
    rw [heq] at hPostFollower
    change (grantDrainNativeNext ring s p p).l = false
      at hPostFollower
    rw [hFinalLeader] at hPostFollower
    cases hPostFollower
  · omega


/-- First missing hPhysical input, now unconditional for the
NOMINATED INCOMING edge e -> g with a surviving weak mark.
The physical unheld Y grant moves to e; the old zero corridor
[p,g) shortens to [p,e), and the surviving host is a follower
with a weak rather than protected nearest source. -/
theorem grantDrainWeakIncomingHostPhysicalHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hEdge : ring.rightNeighbor e = g) :
    ∀ j : Fin n,
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j →
      (grantDrainStep ring fresh update s e).grant j = true ∧
      (grantDrainStep ring fresh update s e).request j = false ∧
      ((grantDrainStep ring fresh update s e).native j).l =
        false ∧
      grantDrainLedgerWeakLock ring
        (grantDrainStep ring fresh update s e) j = true := by
  obtain ⟨hOldGrant, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨hOldRequest, hOldFollower, hOldWeakLock, _⟩ :=
    hWeakCase
  obtain ⟨p, hOldNearest, hOldZero⟩ :=
    grantDrainWeakDeathWeakLockArc ring s g hP
      hOldFollower hOldWeakLock
  intro j hj
  have hMove := grantDrainWeakIncomingHostSurvivorMoves
    ring hn fresh update s e g j label
    hHost hEdge hOldRequest hOldGrant hj
  subst j
  have hLong := grantDrainWeakIncomingHostLiveDistanceLong
    ring hn fresh update s e p g label
    hEdge hOldNearest hNextWeak hj
  have hPostArc :=
    grantDrainWeakIncomingHostPrefixArc
      ring hn fresh update s e p g
      (PPL.cyclicOffset ring p g)
      hEdge hOldNearest hOldZero rfl hLong
  have hCorr := grantDrainWeakArcImpliesCorridor
    ring (grantDrainStep ring fresh update s e)
    p e hPostArc.1 hPostArc.2
  have hNewGrant := grantDrainWeakSurvivingHostGrant
    ring hn fresh update s e label g e hHost hOldGrant hj
  exact grantDrainWeakToWeakPhysicalOfPostCorridor
    ring fresh update s e e label
    hNextWeak hj hNewGrant hCorr

theorem grantDrainWeakIncomingHostProgressHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hEdge : ring.rightNeighbor e = g) :
    (if grantDrainLedgerNominatedHit ring s e label.host then
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label).host +
          1 ≤ grantDrainStrongProtectedDistance ring s label.host
      else
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label).host ≤
          grantDrainStrongProtectedDistance ring s label.host) := by
  obtain ⟨hOldGrant, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨hOldRequest, hOldFollower, hOldWeakLock, _⟩ :=
    hWeakCase
  obtain ⟨p, hOldNearest, _⟩ :=
    grantDrainWeakDeathWeakLockArc ring s g hP
      hOldFollower hOldWeakLock
  have hHit :
      grantDrainLedgerNominatedHit ring s e label.host = true := by
    simp [grantDrainLedgerNominatedHit,
      hHost, hOldRequest, hEdge]
  have hOldPositive :
      0 < grantDrainStrongProtectedDistance ring s (some g) :=
    grantDrainStrongProtectedDistance_some_pos ring s g
  rw [hHit]
  cases hh :
      (grantDrainLedgerStep ring fresh update s e label).host with
  | none =>
      simpa [hHost, grantDrainStrongProtectedDistance_none]
        using Nat.succ_le_of_lt hOldPositive
  | some j =>
      have hMove := grantDrainWeakIncomingHostSurvivorMoves
        ring hn fresh update s e g j label
        hHost hEdge hOldRequest hOldGrant hh
      subst j
      have hLong := grantDrainWeakIncomingHostLiveDistanceLong
        ring hn fresh update s e p g label
        hEdge hOldNearest hNextWeak hh
      have hDistanceDrop :=
        grantDrainWeakIncomingHostProtectedDistanceDrops
          ring hn fresh update s e p g
          (PPL.cyclicOffset ring p g)
          hEdge hOldNearest rfl hLong
      simpa [hHost] using (Nat.le_of_eq hDistanceDrop)

/-- COMPLETE weak-to-weak one-edge LockBudget preservation for
a NOMINATED INCOMING edge e -> g under only PPlus, old LockBudget
and persistent weak mark. No post-state premise is assumed.
This is the precise physical/metric input required by the
existing weak-to-weak budget algebra. -/
theorem grantDrainLockBudgetWeakToWeakIncomingHostHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak)
    (hEdge : ring.rightNeighbor e = g) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  have hPhysical := grantDrainWeakIncomingHostPhysicalHolds
    ring hn fresh update s e g label hP hInv hHost hWeak
    hNextWeak hEdge
  have hProgress := grantDrainWeakIncomingHostProgressHolds
    ring hn fresh update s e g label hP hInv hHost hWeak
    hNextWeak hEdge
  exact grantDrainLockBudgetWeakToWeakOfPhysicalProgress
    ring fresh update s e label g hInv hHost hWeak hNextWeak
    hPhysical hProgress


/-- The edge outgoing from an old follower-host g is strictly
outside its own half-open source corridor [p,g), provided
the old offset d is less than n-1. If d=n-1 instead, the
responder is the old source p; that boundary is handled by
grantDrainLockBudgetWeakToWeakIncomingRootHolds. -/
theorem grantDrainWeakOutgoingHostAwayArc
    {n : Nat} (ring : DirectedRing n)
    (p g : Fin n)
    (hShort :
      PPL.cyclicOffset ring p g + 1 < n) :
    ∀ k : Nat, k < PPL.cyclicOffset ring p g →
      PPL.shiftRight ring p k ≠ g ∧
      PPL.shiftRight ring p k ≠ ring.rightNeighbor g := by
  intro k hk
  have hkBound : k < n := by omega
  have hAtG := grantDrainMarksArcShiftRightOffset ring p g
  have hAtY := grantDrainMarksNeighborOffsetAdvance
    ring p g hShort
  constructor
  · intro heq
    have ho := congrArg (PPL.cyclicOffset ring p) heq
    rw [grantDrainWeakDeathOffsetShiftRight
      ring p k hkBound] at ho
    omega
  · intro heq
    have ho := congrArg (PPL.cyclicOffset ring p) heq
    rw [grantDrainWeakDeathOffsetShiftRight
      ring p k hkBound, hAtY] at ho
    omega

theorem grantDrainLockBudgetWeakToWeakOutgoingHostHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (g p : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s g label).mark =
        .weak)
    (hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g)) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s g)
      (grantDrainLedgerStep ring fresh update s g label) := by
  obtain ⟨_, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨hOldRequest, hFollower, hWeakLock, _⟩ := hWeakCase
  have hOldArc := grantDrainWeakDeathOldRightArc
    ring s p g hP hFollower hWeakLock hSource
  by_cases hShort :
      PPL.cyclicOffset ring p g + 1 < n
  · have hAway := grantDrainWeakOutgoingHostAwayArc
      ring p g hShort
    have hNotY : g ≠ ring.rightNeighbor g :=
      Ne.symm (grantDrainMarksNeighborDistinct
        (by omega : 3 ≤ n) ring g)
    have hNowGeometry := grantDrainWeakAwayCorridorAndDistance
      ring fresh update s g p g hOldArc.1 hOldArc.2 hAway
    have hOldGrant : s.grant g = true :=
      (hInv g hHost).1
    have hPhysical : ∀ j : Fin n,
        (grantDrainLedgerStep ring fresh update s g label).host =
          some j →
        (grantDrainStep ring fresh update s g).grant j = true ∧
        (grantDrainStep ring fresh update s g).request j = false ∧
        ((grantDrainStep ring fresh update s g).native j).l =
          false ∧
        grantDrainLedgerWeakLock ring
          (grantDrainStep ring fresh update s g) j = true := by
      intro j hj
      have hSame := grantDrainWeakHostUnmovedIfNotResponder
        ring fresh update s g g j label hHost hNotY hj
      subst j
      have hNowGrant := grantDrainWeakSurvivingHostGrant
        ring hn fresh update s g label g g hHost hOldGrant hj
      exact grantDrainWeakToWeakPhysicalOfPostCorridor
        ring fresh update s g g label
        hNextWeak hj hNowGrant hNowGeometry.1
    have hNoHit :
        grantDrainLedgerNominatedHit ring s g label.host =
          false := by
      simp [grantDrainLedgerNominatedHit,
        hHost, hOldRequest, Ne.symm hNotY]
    have hProgress :
        (if grantDrainLedgerNominatedHit ring s g label.host then
            grantDrainStrongProtectedDistance ring
              (grantDrainStep ring fresh update s g)
              (grantDrainLedgerStep ring fresh update s g label).host +
              1 ≤ grantDrainStrongProtectedDistance ring s label.host
          else
            grantDrainStrongProtectedDistance ring
              (grantDrainStep ring fresh update s g)
              (grantDrainLedgerStep ring fresh update s g label).host ≤
              grantDrainStrongProtectedDistance ring s label.host) := by
      rw [hNoHit]
      cases hh :
          (grantDrainLedgerStep ring fresh update s g label).host with
      | none =>
          simp [grantDrainStrongProtectedDistance_none]
      | some j =>
          have hSame := grantDrainWeakHostUnmovedIfNotResponder
            ring fresh update s g g j label hHost hNotY hh
          subst j
          simpa [hHost] using (Nat.le_of_eq hNowGeometry.2)
    exact grantDrainLockBudgetWeakToWeakOfPhysicalProgress
      ring fresh update s g label g
      hInv hHost hWeak hNextWeak hPhysical hProgress
  · have hOffLt :=
      GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring p g
    have hLast :
        PPL.cyclicOffset ring p g = n - 1 := by omega
    have hIncoming :
        ring.rightNeighbor g = p :=
      grantDrainMarksNeighborWrapsToProtected
        ring p g hLast (by omega : 1 ≤ n)
    exact grantDrainLockBudgetWeakToWeakIncomingRootHolds
      ring hn fresh update s g p g label
      hP hInv hHost hWeak hNextWeak hIncoming hSource


/-- Universal weak-to-weak one-edge preservation: the seven
cyclic positions around the old weak nearest zero corridor.
All native/token/metric inputs are supplied by the preceding
source-level theorems, including nominated Y->X movement. -/
theorem grantDrainLockBudgetWeakToWeakHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNextWeak :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨_, hWeakCase⟩ := hInv g hHost
  rw [hWeak] at hWeakCase
  obtain ⟨_, hFollower, hWeakLock, _⟩ := hWeakCase
  generalize hSourceEq :
      PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g) = p
  have hSource : p = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g) :=
    hSourceEq.symm
  have hArc := grantDrainWeakDeathOldRightArc
    ring s p g hP hFollower hWeakLock hSource
  obtain ⟨kind, hKind, _⟩ :=
    grantDrainMarksCyclicEdgePartition
      (by omega : 3 ≤ n) ring s.native p g e hArc.1
  cases kind with
  | protectedAdjacent =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have he := grantDrainMarksSourceAtOffsetZero ring p e hKind.1
      subst e
      have hNeighbor := grantDrainMarksHostAtOffsetOne
        ring p g hKind.2
      exact grantDrainLockBudgetWeakToWeakIncomingHostHolds
        ring hn fresh update s p g label
        hP hInv hHost hWeak hNextWeak hNeighbor
  | protectedLong =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have he := grantDrainMarksSourceAtOffsetZero ring p e hKind.1
      subst e
      exact grantDrainLockBudgetWeakToWeakOutgoingRootHolds
        ring hn fresh update s p g label
        hP hInv hHost hWeak hNextWeak hSource hKind.2
  | wholeBoundary =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have hSame :
          PPL.cyclicOffset ring p e =
            PPL.cyclicOffset ring p g := by omega
      have he := grantDrainMarksEqualOffsetSite ring p e g hSame
      subst e
      exact grantDrainLockBudgetWeakToWeakOutgoingHostHolds
        ring hn fresh update s g p label
        hP hInv hHost hWeak hNextWeak hSource
  | incomingHost =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have hEdge := grantDrainMarksNeighborIsHost
        ring p g e hKind.2
      exact grantDrainLockBudgetWeakToWeakIncomingHostHolds
        ring hn fresh update s e g label
        hP hInv hHost hWeak hNextWeak hEdge
  | strictInterior =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have hYOff :
          PPL.cyclicOffset ring p (ring.rightNeighbor e) =
            PPL.cyclicOffset ring p e + 1 :=
        grantDrainMarksNeighborOffsetAdvance
          ring p e (by
            have hlt :=
              GrantDrainEntrance.grantDrainEntranceArcOffsetLt ring p g
            omega)
      have hInside :
          GrantDrainMarksStrictInteriorEdge ring p g e := by
        change
          0 < PPL.cyclicOffset ring p e ∧
          PPL.cyclicOffset ring p e <
            PPL.cyclicOffset ring p g ∧
          0 < PPL.cyclicOffset ring p (ring.rightNeighbor e) ∧
          PPL.cyclicOffset ring p (ring.rightNeighbor e) <
            PPL.cyclicOffset ring p g
        refine ⟨hKind.1, by omega, ?_, ?_⟩
        · rw [hYOff]
          omega
        · rw [hYOff]
          exact hKind.2
      exact grantDrainLockBudgetWeakToWeakStrictInteriorHolds
        ring hn fresh update s e p g label
        hP hInv hHost hWeak hNextWeak hSource hInside
  | incomingProtected =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have hEdge := grantDrainMarksNeighborWrapsToProtected
        ring p e hKind.1 (by omega : 1 ≤ n)
      exact grantDrainLockBudgetWeakToWeakIncomingRootHolds
        ring hn fresh update s e p g label
        hP hInv hHost hWeak hNextWeak hEdge hSource
  | exterior =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have hYOff := grantDrainMarksNeighborOffsetAdvance
        ring p e hKind.2
      have hAway : ∀ k : Nat,
          k < PPL.cyclicOffset ring p g →
          PPL.shiftRight ring p k ≠ e ∧
          PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
        intro k hk
        have hklt : k < n :=
          Nat.lt_trans hk
            (GrantDrainEntrance.grantDrainEntranceArcOffsetLt
              ring p g)
        constructor
        · intro he
          have ho := congrArg (PPL.cyclicOffset ring p) he
          rw [grantDrainWeakDeathOffsetShiftRight
            ring p k hklt] at ho
          omega
        · intro hy
          have ho := congrArg (PPL.cyclicOffset ring p) hy
          rw [grantDrainWeakDeathOffsetShiftRight
            ring p k hklt, hYOff] at ho
          omega
      have hNotY : ring.rightNeighbor e ≠ g := by
        intro he
        have ho := congrArg (PPL.cyclicOffset ring p) he
        rw [hYOff] at ho
        omega
      by_cases hAtG : e = g
      · subst e
        exact grantDrainLockBudgetWeakToWeakOutgoingHostHolds
          ring hn fresh update s g p label
          hP hInv hHost hWeak hNextWeak hSource
      · exact grantDrainLockBudgetWeakToWeakAwayHolds
          ring hn fresh update s e p g label
          hP hInv hHost hWeak hNextWeak hSource
          (Ne.symm hAtG) (Ne.symm hNotY) hAway

end L3



namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Correct literal E row for a follower-hosted DUMMY,
then the full physical moving-follower clean theorem B'.
The same clean-successor geometry also closes the no-FIRE
ready-responder death with a follower LIVE killer.
-/

/-- The source signal stays false even if the OLD empty
responder's signal is true: the E row resets rSg before the
final source signal OR. All Boolean shield/responder-signal
possibilities are covered. -/
theorem grantDrainDummyMovedFollowerLiteral
    (x y : CertNative)
    (hXFollower : x.l = false)
    (hXDummy : x.b = (1 : Fin 3))
    (hXZero : x.sg = false)
    (hYFollower : y.l = false)
    (hYEmpty : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.l = false ∧
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.b = (1 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = false := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  simp only at hXFollower hXDummy hXZero hYFollower hYEmpty
  subst hXFollower hXDummy hXZero hYFollower hYEmpty
  cases xh <;> cases yh <;> cases ys <;> decide

/-- The next site after e has offset d+1 from p whenever it
is not p itself; this includes the cyclic wraparound case. -/
theorem grantDrainDummySourceSuccessorOffset
    {n : Nat} (ring : DirectedRing n)
    (e p : Fin n) (hNotRoot : p ≠ ring.rightNeighbor e) :
    PPL.cyclicOffset ring p (ring.rightNeighbor e) =
      PPL.cyclicOffset ring p e + 1 := by
  have hShift :
      PPL.shiftRight ring p
        (PPL.cyclicOffset ring p e + 1) =
          ring.rightNeighbor e := by
    calc
      PPL.shiftRight ring p
          (PPL.cyclicOffset ring p e + 1) =
        ring.rightNeighbor
          (PPL.shiftRight ring p
            (PPL.cyclicOffset ring p e)) :=
          (grantDrainEntranceAheadShiftSucc ring p
            (PPL.cyclicOffset ring p e)).symm
      _ = ring.rightNeighbor e := by
        rw [grantDrainMarksArcShiftRightOffset ring p e]
  have hBound :
      PPL.cyclicOffset ring p e + 1 < n := by
    by_cases hb : PPL.cyclicOffset ring p e + 1 < n
    · exact hb
    · have hEq : PPL.cyclicOffset ring p e + 1 = n := by
        have hOld := grantDrainEntranceArcOffsetLt ring p e
        omega
      have hFull : PPL.shiftRight ring p n = p := by
        apply Fin.ext
        change (p.val + n) % n = p.val
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]
      have hRootAtY : p = ring.rightNeighbor e := by
        calc
          p = PPL.shiftRight ring p n := hFull.symm
          _ = PPL.shiftRight ring p
              (PPL.cyclicOffset ring p e + 1) := by rw [hEq]
          _ = ring.rightNeighbor e := hShift
      exact False.elim (hNotRoot hRootAtY)
  rw [← hShift]
  exact grantDrainDummyRightOffset ring p
    (PPL.cyclicOffset ring p e + 1) hBound

/-- Abstract one-edge clean-bullet transport. The old source
e is a clean follower bullet, the new host is y=rightNeighbor e.
New leaders may differ at y only. Before y the old nearest
leader stays put, the source bullet is removed, and old zeros
remain zeros. The new bullet is necessarily earliest and its
inclusive leader-to-host signal trail is zero. -/
theorem grantDrainDummyCleanFollowerSuccessorCore
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (e p : Fin n)
    (hXFollower : (N e).l = false)
    (hRootNotY : p ≠ ring.rightNeighbor e)
    (hOldSector : leaderSector ring N p e)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring N e)
    (hLeaderFrame : ∀ i : Fin n,
      i ≠ ring.rightNeighbor e → (M i).l = (N i).l)
    (hSourceEmpty : (M e).b = (0 : Fin 3))
    (hNewFollower : (M (ring.rightNeighbor e)).l = false)
    (hNewBullet : HasBullet M (ring.rightNeighbor e))
    (hNewZero : (M (ring.rightNeighbor e)).sg = false)
    (hZeroBackward : ∀ i : Fin n,
      (N i).sg = false → (M i).sg = false)
    (hBulletBackward : ∀ i : Fin n,
      i ≠ ring.rightNeighbor e →
        HasBullet M i → HasBullet N i) :
    GrantDrainEntranceBulletCleanAt ring M
      (ring.rightNeighbor e) := by
  have hOldArc :=
    grantDrainDummyFollowerSectorNearestArc
      ring N p e hXFollower hOldSector
  have hOldTrail :=
    grantDrainDummyCleanTrailAtNearest
      ring N p e hOldClean hOldSector
  have hOldEmpty :=
    grantDrainDummyCleanPrefixEmpty
      ring N p e hOldArc hOldSector hOldClean
  have hOffset :=
    grantDrainDummySourceSuccessorOffset
      ring e p hRootNotY
  have hRootPos :
      0 < PPL.cyclicOffset ring p (ring.rightNeighbor e) := by
    rw [hOffset]
    omega
  have hInsideNotY :
      ∀ k : Nat,
        k < PPL.cyclicOffset ring p (ring.rightNeighbor e) →
        PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
    intro k hk hSite
    have hkN : k < n :=
      Nat.lt_trans hk
        (grantDrainEntranceArcOffsetLt ring p (ring.rightNeighbor e))
    have hOffsetSite :=
      congrArg (PPL.cyclicOffset ring p) hSite
    rw [grantDrainDummyRightOffset ring p k hkN]
      at hOffsetSite
    omega
  have hNewArc :
      GrantDrainMarksNearestArc ring M p
        (ring.rightNeighbor e) := by
    refine ⟨hRootPos, ?_, ?_⟩
    · rw [hLeaderFrame p hRootNotY]
      exact hOldArc.2.1
    · intro k hkPos hkLt
      have hkLe :
          k ≤ PPL.cyclicOffset ring p e := by
        rw [hOffset] at hkLt
        omega
      rw [hLeaderFrame (PPL.shiftRight ring p k)
        (hInsideNotY k hkLt)]
      by_cases hkAt : k = PPL.cyclicOffset ring p e
      · rw [hkAt, grantDrainMarksArcShiftRightOffset ring p e]
        exact hXFollower
      · exact hOldArc.2.2 k hkPos (by omega)
  have hNewArcZero :
      GrantDrainMarksZeroOffsetArc ring M p
        (ring.rightNeighbor e) := by
    intro k hk
    have hkN : k < n :=
      Nat.lt_trans hk
        (grantDrainEntranceArcOffsetLt ring p (ring.rightNeighbor e))
    have hkLe :
        k ≤ PPL.cyclicOffset ring p e := by
      rw [hOffset] at hk
      omega
    exact hZeroBackward (PPL.shiftRight ring p k)
      (hOldTrail (⟨k, hkN⟩ : Fin n) hkLe)
  have hNewNoBefore :
      ∀ k : Nat,
        k < PPL.cyclicOffset ring p (ring.rightNeighbor e) →
          (M (PPL.shiftRight ring p k)).b = (0 : Fin 3) := by
    intro k hk
    have hkLe :
        k ≤ PPL.cyclicOffset ring p e := by
      rw [hOffset] at hk
      omega
    by_cases hkAt : k = PPL.cyclicOffset ring p e
    · rw [hkAt, grantDrainMarksArcShiftRightOffset ring p e]
      exact hSourceEmpty
    · have hOldZero := hOldEmpty k (by omega)
      by_cases hNewEmpty :
          (M (PPL.shiftRight ring p k)).b = (0 : Fin 3)
      · exact hNewEmpty
      · have hOldBullet :=
          hBulletBackward (PPL.shiftRight ring p k)
            (hInsideNotY k hk) hNewEmpty
        exact False.elim (hOldBullet hOldZero)
  exact grantDrainDummyCleanFromNearestZeroNoBefore
    ring M p (ring.rightNeighbor e) hNewBullet
    hNewFollower hNewArc hNewArcZero hNewZero hNewNoBefore

/-- Native E removes any source bullet and frames bullet sites
other than the responder. -/
theorem grantDrainDummyNativeEBulletBackwardExceptResponder
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e i : Fin n)
    (hSourceEmpty :
      (nativeE ring N e e).b = (0 : Fin 3))
    (hNotY : i ≠ ring.rightNeighbor e)
    (hBullet : HasBullet (nativeE ring N e) i) :
    HasBullet N i := by
  by_cases hAtSource : i = e
  · subst i
    exact False.elim (hBullet hSourceEmpty)
  · have hFrame :=
      grantDrainEntranceNativeEFrame
        ring N e i hAtSource hNotY
    unfold HasBullet at hBullet ⊢
    rw [hFrame] at hBullet
    exact hBullet

/-- Native E transfers an old clean follower DUMMY to an OLD
empty follower and preserves cleanliness, with arbitrary old
signal and shield at the responder. -/
theorem grantDrainDummyMovedFollowerSourceNativeEClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hXFollower : (N e).l = false)
    (hXDummy : (N e).b = (1 : Fin 3))
    (hYFollower : (N (ring.rightNeighbor e)).l = false)
    (hYEmpty : (N (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hOldClean : GrantDrainEntranceBulletCleanAt ring N e) :
    GrantDrainEntranceBulletCleanAt ring
      (nativeE ring N e) (ring.rightNeighbor e) := by
  have hXZero :=
    grantDrainDummyCleanOwnSignalZero ring N e hOldClean
  have hPair :=
    grantDrainDummyMovedFollowerLiteral
      (N e) (N (ring.rightNeighbor e))
      hXFollower hXDummy hXZero hYFollower hYEmpty
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hESourceEmpty :
      (nativeE ring N e e).b = (0 : Fin 3) := by
    simpa [nativeE] using hPair.2.1
  have hEYFollower :
      (nativeE ring N e (ring.rightNeighbor e)).l =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.1
  have hEYDummy :
      (nativeE ring N e (ring.rightNeighbor e)).b =
        (1 : Fin 3) := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2.1
  have hEYZero :
      (nativeE ring N e (ring.rightNeighbor e)).sg =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2.2
  have hEYBullet :
      HasBullet (nativeE ring N e)
        (ring.rightNeighbor e) := by
    unfold HasBullet
    rw [hEYDummy]
    exact (by decide : (1 : Fin 3) ≠ (0 : Fin 3))
  have hLeaderFrame :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        (nativeE ring N e i).l = (N i).l := by
    intro i hi
    exact grantDrainDummyNativeELeaderAwayResponder
      ring N e i hi
  have hBulletX : HasBullet N e := by
    unfold HasBullet
    rw [hXDummy]
    exact (by decide : (1 : Fin 3) ≠ (0 : Fin 3))
  have hZeroBackward :
      ∀ i : Fin n, (N i).sg = false →
        (nativeE ring N e i).sg = false := by
    intro i hZero
    exact grantDrainEntranceNonleaderBulletNativeEZeroPreserved
      ring (by omega : 2 ≤ n) N e
      hXFollower hYFollower hBulletX hYEmpty hXZero i hZero
  have hOldSectorExists :
      ∃ p : Fin n, leaderSector ring N p e := by
    obtain ⟨_, p, hSector, _, _⟩ := hOldClean
    exact ⟨p, hSector⟩
  obtain ⟨p, hSector⟩ := hOldSectorExists
  have hpNotY : p ≠ ring.rightNeighbor e := by
    intro hp
    have hAtY : (N (ring.rightNeighbor e)).l = true := by
      rw [← hp]
      exact hSector.1
    rw [hYFollower] at hAtY
    cases hAtY
  exact grantDrainDummyCleanFollowerSuccessorCore
    ring N (nativeE ring N e) e p hXFollower hpNotY
    hSector hOldClean hLeaderFrame hESourceEmpty
    hEYFollower hEYBullet hEYZero hZeroBackward
    (fun i hi hBullet =>
      grantDrainDummyNativeEBulletBackwardExceptResponder
        ring N e i hESourceEmpty hi hBullet)

/-- Full (B'): actual E+FIRE moves the OLD clean follower
DUMMY into the OLD empty follower. Since the new responder
has a DUMMY, F1 is impossible. F0/F2 instead birth at e,
immediately before the transferred DUMMY. -/
theorem grantDrainDummyMovedFollowerSourceClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hXFollower : (s.native e).l = false)
    (hXDummy : (s.native e).b = (1 : Fin 3))
    (hYFollower : (s.native (ring.rightNeighbor e)).l = false)
    (hYEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native e) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hXZero :=
    grantDrainDummyCleanOwnSignalZero
      ring s.native e hOldClean
  have hPair :=
    grantDrainDummyMovedFollowerLiteral
      (s.native e) (s.native (ring.rightNeighbor e))
      hXFollower hXDummy hXZero hYFollower hYEmpty
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hEYFollower :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.1
  have hEYDummy :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2.1
  have hEYZero :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2.2
  have hIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hEYDummy]
  have hNoRight : grantDrainSelect ring s e ≠ .rightLocal :=
    grantDrainEntranceResponderIneligibleNoRightFire
      ring s e hIneligible
  have hPlain :=
    grantDrainDummyMovedFollowerSourceNativeEClean
      ring hn s.native e hXFollower hXDummy
      hYFollower hYEmpty hOldClean
  have hBirth :
      GrantDrainEntranceBulletCleanAt ring
        (canonicalBirth (nativeE ring s.native e) e)
        (ring.rightNeighbor e) := by
    exact grantDrainDummyAdjacentFollowerClean
      ring hn (canonicalBirth (nativeE ring s.native e) e) e
      (by simp [canonicalBirth, firedNative])
      (by simp [canonicalBirth, firedNative])
      (by simp [canonicalBirth, firedNative])
      (by simpa [canonicalBirth, hDistinct] using hEYFollower)
      (by simpa [canonicalBirth, hDistinct] using hEYDummy)
      (by simpa [canonicalBirth, hDistinct] using hEYZero)
  change GrantDrainEntranceBulletCleanAt ring
    (grantDrainNativeNext ring s e) (ring.rightNeighbor e)
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hPlain
  | leftLocal =>
      simpa [grantDrainNativeNext, hf] using hBirth
  | rightLocal =>
      exact False.elim (hNoRight hf)
  | cross =>
      simpa [grantDrainNativeNext, hf] using hBirth

/-- C' remaining no-FIRE ready-responder death: an OLD
follower LIVE at e is clean by PPlus+NoBadLive, y is ready,
and literal E converts that LIVE into a DUMMY at y while
clearing both changed signals. This is the same abstract
successor-clean geometry as B', but with a deleted leader. -/
theorem grantDrainDummyReadyFollowerLiveNoFireClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hXFollower : (s.native e).l = false)
    (hXLive : LiveBullet s.native e)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hYReady : (s.native (ring.rightNeighbor e)).sg = true)
    (hNoFire : grantDrainSelect ring s e = .none) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hXZero : (s.native e).sg = false :=
    L3.grantDrainDeathLiveOwnSignalZero ring s e hP hXLive
  have hPair :=
    grantDrainDummyReadyFollowerLiveLiteral
      (s.native e) (s.native (ring.rightNeighbor e))
      hXFollower hXLive hXZero hYLeader hYReady
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hESourceEmpty :
      (nativeE ring s.native e e).b = (0 : Fin 3) := by
    simpa [nativeE] using hPair.1
  have hEYFollower :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.1
  have hEYDummy :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.1
  have hEYZero :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2
  have hEYBullet :
      HasBullet (nativeE ring s.native e)
        (ring.rightNeighbor e) := by
    unfold HasBullet
    rw [hEYDummy]
    exact (by decide : (1 : Fin 3) ≠ (0 : Fin 3))
  have hOldClean :=
    grantDrainDummyLiveCleanOfNoBad
      ring s.native hP hNoBad e hXLive
  have hOldSectorExists :
      ∃ p : Fin n,
        leaderSector ring s.native p e ∧
          signalTrail ring s.native p e := by
    obtain ⟨_, p, hSector, _, hTrail⟩ := hOldClean
    exact ⟨p, hSector, hTrail⟩
  obtain ⟨p, hSector, hTrail⟩ := hOldSectorExists
  have hRootZero : (s.native p).sg = false := by
    have hAt := hTrail
      (⟨0, (show 0 < n by omega)⟩ : Fin n) (Nat.zero_le _)
    simpa [grantDrainWeakDeathShiftRightZero] using hAt
  have hpNotY : p ≠ ring.rightNeighbor e := by
    intro hp
    have hAtY : (s.native (ring.rightNeighbor e)).sg = false := by
      rw [← hp]
      exact hRootZero
    rw [hYReady] at hAtY
    cases hAtY
  have hZeroBackward :
      ∀ i : Fin n, (s.native i).sg = false →
        (nativeE ring s.native e i).sg = false := by
    intro i hOldZero
    exact grantDrainDummyDeathEZeroBackward
      ring hn s.native e i hYLeader hEYFollower hXZero hOldZero
  have hPlain :
      GrantDrainEntranceBulletCleanAt ring
        (nativeE ring s.native e) (ring.rightNeighbor e) :=
    grantDrainDummyCleanFollowerSuccessorCore
      ring s.native (nativeE ring s.native e) e p
      hXFollower hpNotY hSector hOldClean
      (fun i hi =>
        grantDrainDummyNativeELeaderAwayResponder
          ring s.native e i hi)
      hESourceEmpty hEYFollower hEYBullet hEYZero hZeroBackward
      (fun i hi hBullet =>
        grantDrainDummyNativeEBulletBackwardExceptResponder
          ring s.native e i hESourceEmpty hi hBullet)
  have hPhysical :
      (grantDrainStep ring fresh update s e).native =
        nativeE ring s.native e := by
    change grantDrainNativeNext ring s e =
      nativeE ring s.native e
    simp [grantDrainNativeNext, hNoFire]
  rw [hPhysical]
  exact hPlain

/-- The ready-responder follower-LIVE death C' row is now
closed for ALL four actual FIRE outcomes. F1 is impossible,
since E produces a nonempty responder DUMMY. -/
theorem grantDrainDummyReadyFollowerLiveClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hXFollower : (s.native e).l = false)
    (hXLive : LiveBullet s.native e)
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hYReady : (s.native (ring.rightNeighbor e)).sg = true) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hXZero : (s.native e).sg = false :=
    L3.grantDrainDeathLiveOwnSignalZero ring s e hP hXLive
  have hPair :=
    grantDrainDummyReadyFollowerLiveLiteral
      (s.native e) (s.native (ring.rightNeighbor e))
      hXFollower hXLive hXZero hYLeader hYReady
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hEYDummy :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.1
  have hIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hEYDummy]
  have hNoRight : grantDrainSelect ring s e ≠ .rightLocal :=
    grantDrainEntranceResponderIneligibleNoRightFire
      ring s e hIneligible
  cases hf : grantDrainSelect ring s e with
  | none =>
      exact grantDrainDummyReadyFollowerLiveNoFireClean
        ring hn fresh update s e hP hNoBad
        hXFollower hXLive hYLeader hYReady hf
  | leftLocal =>
      exact grantDrainDummyReadyFollowerLiveBirthSourceClean
        ring hn fresh update s e hP hXFollower hXLive
        hYLeader hYReady (Or.inl hf)
  | rightLocal =>
      exact False.elim (hNoRight hf)
  | cross =>
      exact grantDrainDummyReadyFollowerLiveBirthSourceClean
        ring hn fresh update s e hP hXFollower hXLive
        hYLeader hYReady (Or.inr hf)

end L3.GrantDrainEntrance


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Source-level case closures.
The global one-edge theorem is NOT asserted.
-/

/-- A retired identity cannot acquire a host, so its LockBudget
postcondition is vacuous. This holds without PPlus or an old budget. -/
theorem grantDrainLockBudgetRetiredStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hNone : label.host = none) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  have hRetired := grantDrainLedgerStep_retired_absorbing
    ring fresh update s e label hNone
  intro j hj
  rw [hRetired] at hj
  cases hj

/-- Every surviving ledger identity owns a REAL physical grant
at its post-step host. This works for every old mark and every
FIRE, HOLD, movement and coalescence outcome. -/
theorem grantDrainLockBudgetSuccessorGrant
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hInv : LockBudget ring fresh update s label) :
    ∀ j : Fin n,
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j →
      (grantDrainStep ring fresh update s e).grant j = true := by
  intro j hj
  cases hh : label.host with
  | none =>
      have hRetired := grantDrainLedgerStep_retired_absorbing
        ring fresh update s e label hh
      rw [hRetired] at hj
      cases hj
  | some g =>
      have hOldGrant := (hInv g hh).1
      exact grantDrainWeakSurvivingHostGrant
        ring hn fresh update s e label g j
        hh hOldGrant hj

/-- The unmarked post-observation branch has no physical or
budget requirements beyond the grant-owner invariant. -/
theorem grantDrainLockBudgetUnmarkedNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hInv : LockBudget ring fresh update s label)
    (hNewUnmarked :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .unmarked) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  intro j hj
  have hGrant := grantDrainLockBudgetSuccessorGrant
    ring hn fresh update s e label hInv j hj
  refine ⟨hGrant, ?_⟩
  rw [hNewUnmarked]
  trivial

/-- The seven-position weak-to-weak theorem closes
the full weak-stable branch with no extra physical premise. -/
theorem grantDrainLockBudgetWeakStableNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hOldWeak : label.mark = .weak)
    (hNewWeak :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .weak) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  exact grantDrainLockBudgetWeakToWeakHolds
    ring hn fresh update s e label g
    hP hInv hOldHost hOldWeak hNewWeak

/-- The D.1 strong physical closure and budget algebra
close strong-to-strong for every surviving host; a retired host
satisfies LockBudget vacuously. No outside geometric premise. -/
theorem grantDrainLockBudgetStrongStableNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hOldStrong : label.mark = .strong)
    (hNewStrong :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .strong) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  cases hh :
      (grantDrainLedgerStep ring fresh update s e label).host with
  | none =>
      intro j hj
      rw [hh] at hj
      cases hj
  | some j =>
      have hLive :
          (grantDrainLedgerStep ring fresh update s e label).host ≠
            none := by
        rw [hh]
        simp
      exact grantDrainLockBudgetStrongToStrong
        ring hn fresh update s e label g hP hInv
        hOldHost hOldStrong hLive hNewStrong

/-- A ledger mark cannot decrease, regardless of the native
transition or the observed post-host status. This is an
unconditional exclusion for all downward case-table cells. -/
theorem grantDrainLockBudgetDecreasingMarkImpossible
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hDecrease :
      grantDrainMarkRank
          (grantDrainLedgerStep ring fresh update s e label).mark <
        grantDrainMarkRank label.mark) : False := by
  have hMono := grantDrainLedgerStep_mark_monotone
    ring fresh update s e label
  omega

end L3


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Terminal-held row of the literal GrantDrain ledger.
This is unconditional on the revealed edge and on the
adversary's fresh request.
-/

/-- An OLD held responder cannot survive with its grant while
losing its request. This finite token row covers all source
request/grant bits, final leader bits, fresh bits and FIRE rows. -/
theorem grantDrainTerminalHeldIncomingGrantImpliesRequest
    (rx gx lx ly fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow rx gx true true lx ly fresh fire).2.grant =
        true →
      (grantDrainTokenRow rx gx true true lx ly fresh fire).2.req =
        true := by
  cases rx <;> cases gx <;> cases lx <;> cases ly <;>
    cases fresh <;> cases fire <;>
    simp [grantDrainTokenRow] <;> decide

/-- On every NON-nominated edge, a surviving terminal OLD held
identity remains request-bearing. When the old host is the
responder, this is the finite token row and exact YSource
classification; away from both endpoints request is framed. -/
theorem grantDrainTerminalHeldSurvivorRequested
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hOldHost : label.host = some g)
    (hOldRequest : s.request g = true)
    (hOldGrant : s.grant g = true)
    (hNotOutgoing : e ≠ g)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    (grantDrainStep ring fresh update s e).request j = true := by
  have hRawHost :
      grantDrainLedgerHost ring fresh s e (some g) = some j := by
    change grantDrainLedgerHost ring fresh s e label.host =
      some j at hNewHost
    rw [hOldHost] at hNewHost
    exact hNewHost
  by_cases hY : g = ring.rightNeighbor e
  · subst g
    have hDistinct : ring.rightNeighbor e ≠ e :=
      grantDrainMarksNeighborDistinct (by omega : 3 ≤ n) ring e
    have hYHost :
        (if (grantDrainLedgerRow ring fresh s e).2.grant
          then some (ring.rightNeighbor e) else none) =
            some j := by
      cases hh0 : (grantDrainLedgerRow ring fresh s e).2.grant with
      | false =>
          simp [grantDrainLedgerHost, hDistinct,
            grantDrainLedgerYSource, hOldRequest, hOldGrant, hh0]
            at hRawHost
      | true =>
          simpa [grantDrainLedgerHost, hDistinct,
            grantDrainLedgerYSource, hOldRequest, hOldGrant, hh0]
            using hRawHost
    cases hh : (grantDrainLedgerRow ring fresh s e).2.grant with
    | false =>
        simp [hh] at hYHost
    | true =>
        have hj : ring.rightNeighbor e = j := by
          simpa [hh] using hYHost
        subst j
        have hLiteralGrant :
            (grantDrainTokenRow
              (s.request e) (s.grant e) true true
              (grantDrainNativeNext ring s e e).l
              (grantDrainNativeNext ring s e
                (ring.rightNeighbor e)).l
              (fresh s e) (grantDrainSelect ring s e)).2.grant =
                true := by
          simpa [grantDrainLedgerRow, hOldRequest, hOldGrant]
            using hh
        have hLiteralReq :=
          grantDrainTerminalHeldIncomingGrantImpliesRequest
            (s.request e) (s.grant e)
            (grantDrainNativeNext ring s e e).l
            (grantDrainNativeNext ring s e
              (ring.rightNeighbor e)).l
            (fresh s e) (grantDrainSelect ring s e)
            hLiteralGrant
        have hRowReq :
            (grantDrainLedgerRow ring fresh s e).2.req =
              true := by
          simpa [grantDrainLedgerRow, hOldRequest, hOldGrant]
            using hLiteralReq
        change
          (if ring.rightNeighbor e = e then
            (grantDrainLedgerRow ring fresh s e).1.req
           else if ring.rightNeighbor e = ring.rightNeighbor e then
            (grantDrainLedgerRow ring fresh s e).2.req
           else s.request (ring.rightNeighbor e)) = true
        simp [hDistinct, hRowReq]
  · have hUnchanged :
        grantDrainLedgerHost ring fresh s e (some g) =
          some g := by
        simp [grantDrainLedgerHost,
          Ne.symm hNotOutgoing, hY]
    have hj : g = j :=
      Option.some.inj (hUnchanged.symm.trans hRawHost)
    subst j
    change
      (if g = e then (grantDrainLedgerRow ring fresh s e).1.req
       else if g = ring.rightNeighbor e then
         (grantDrainLedgerRow ring fresh s e).2.req
       else s.request g) = true
    simp [Ne.symm hNotOutgoing, hY, hOldRequest]

/-- Complete OLD held terminal row. Outgoing nomination retires.
On every other edge a surviving identity remains physically
held, its terminal mark persists, and its new quota is one.
The future nominated-hit retirement in the NEW LockBudget is
derived from the actual post-step held state. -/
theorem grantDrainLockBudgetTerminalHeldHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hOldTerminal : label.mark = .terminal)
    (hOldRequest : s.request g = true) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨hOldGrant, hOldCase⟩ := hInv g hOldHost
  rw [hOldTerminal] at hOldCase
  have hOldHeld :
      0 < label.remaining ∧
        ∀ edge : Fin n,
          grantDrainLedgerNominatedHit ring s edge label.host =
            true →
          (grantDrainLedgerStep ring fresh update s edge label).host =
            none := by
    simpa only [hOldRequest, ↓reduceIte] using hOldCase
  by_cases hOutgoing : e = g
  · subst e
    have hRetired :=
      grantDrainHeldOutgoingRetires ring fresh update s g
        label hOldHost hOldRequest hOldGrant
    intro j hNewHost
    rw [hRetired] at hNewHost
    cases hNewHost
  · intro j hNewHost
    have hNewGrant :
        (grantDrainStep ring fresh update s e).grant j = true :=
      grantDrainLockBudgetSuccessorGrant
        ring hn fresh update s e label hInv j hNewHost
    have hNewRequest :
        (grantDrainStep ring fresh update s e).request j = true :=
      grantDrainTerminalHeldSurvivorRequested
        ring hn fresh update s e label g j
        hOldHost hOldRequest hOldGrant hOutgoing hNewHost
    have hNewTerminal :=
      grantDrainDeathTerminalMarkPersists
        ring fresh update s e label hOldTerminal
    have hNoHit :
        grantDrainLedgerNominatedHit ring s e label.host =
          false := by
      rw [hOldHost]
      simp [grantDrainLedgerNominatedHit, hOldRequest, hOutgoing]
    have hRawHost :
        grantDrainLedgerHost ring fresh s e label.host =
          some j := hNewHost
    have hRawMark :
        grantDrainLedgerMarkNext ring fresh update s e label =
          .terminal := hNewTerminal
    have hNewHeld :
        grantDrainLedgerHeld
          (grantDrainStep ring fresh update s e) (some j) =
            true := by
      simp [grantDrainLedgerHeld, hNewRequest, hNewGrant]
    have hNewRemaining :
        (grantDrainLedgerStep ring fresh update s e label).remaining =
          1 := by
      change
        grantDrainLedgerRemainingNext n label
          (grantDrainLedgerHost ring fresh s e label.host)
          (grantDrainLedgerMarkNext ring fresh update s e label)
          (grantDrainLedgerNominatedHit ring s e label.host)
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerHost ring fresh s e label.host)) = 1
      rw [hRawHost, hRawMark, hNoHit, hNewHeld]
      have hOne : min 1 n = 1 :=
        Nat.min_eq_left (by omega : 1 ≤ n)
      have hOldAtLeastOne : 1 ≤ label.remaining :=
        Nat.succ_le_of_lt hOldHeld.1
      simp [grantDrainLedgerRemainingNext, hOldTerminal,
        grantDrainLedgerQuotaCap, hOne,
        Nat.min_eq_right hOldAtLeastOne]
    refine ⟨hNewGrant, ?_⟩
    rw [hNewTerminal]
    simp only [hNewRequest, ↓reduceIte]
    constructor
    · rw [hNewRemaining]
      omega
    · exact grantDrainLockBudgetHeldRetiresOnNomination
        ring fresh update
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e label)
        j hNewHost hNewRequest hNewGrant

/-- A terminal native-leader host away from the selected
two-site edge keeps its physical leader/request/grant fields.
Its old quota is at least n and the actual non-nominated
terminal step caps that quota at exactly n. This is an
unconditional proof of the away-edge class, not of leader death. -/
theorem grantDrainLockBudgetTerminalLeaderAwayHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hTerminal : label.mark = .terminal)
    (hOldRequest : s.request g = false)
    (hOldLeader : (s.native g).l = true)
    (hNotSource : g ≠ e)
    (hNotResponder : g ≠ ring.rightNeighbor e) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  have hOldQuota : n ≤ label.remaining := by
    have hOldCase := (hInv g hHost).2
    rw [hTerminal] at hOldCase
    simpa only [hOldRequest, Bool.false_eq_true, ↓reduceIte,
      hOldLeader] using hOldCase
  have hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some g := by
    change grantDrainLedgerHost ring fresh s e label.host = some g
    rw [hHost]
    simp [grantDrainLedgerHost, hNotSource, hNotResponder]
  have hNewRequest :
      (grantDrainStep ring fresh update s e).request g =
        false := by
    change
      (if g = e then (grantDrainLedgerRow ring fresh s e).1.req
       else if g = ring.rightNeighbor e then
         (grantDrainLedgerRow ring fresh s e).2.req
       else s.request g) = false
    simp [hNotSource, hNotResponder, hOldRequest]
  have hNewLeader :
      ((grantDrainStep ring fresh update s e).native g).l =
        true := by
    change (grantDrainNativeNext ring s e g).l = true
    rw [grantDrainMarksNativeOutsidePairFrame
      ring s e g hNotSource hNotResponder]
    exact hOldLeader
  have hNewMark :=
    grantDrainDeathTerminalMarkPersists
      ring fresh update s e label hTerminal
  have hNoHit :
      grantDrainLedgerNominatedHit ring s e label.host =
        false := by
    rw [hHost]
    simp [grantDrainLedgerNominatedHit, hOldRequest,
      Ne.symm hNotResponder]
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host = some g :=
    hNewHost
  have hRawMark :
      grantDrainLedgerMarkNext ring fresh update s e label =
        .terminal := hNewMark
  have hHeldPost :
      grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e) (some g) =
          false := by
    simp [grantDrainLedgerHeld, hNewRequest]
  have hNewQuota :
      (grantDrainLedgerStep ring fresh update s e label).remaining =
        n := by
    change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring fresh s e label.host)
      (grantDrainLedgerMarkNext ring fresh update s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e label.host)) = n
    rw [hRawHost, hRawMark, hNoHit, hHeldPost]
    simp [grantDrainLedgerRemainingNext, hTerminal,
      grantDrainLedgerQuotaCap, Nat.min_eq_right hOldQuota]
  intro j hj
  have hjEq : g = j :=
    Option.some.inj (hNewHost.symm.trans hj)
  subst j
  have hGrant :=
    grantDrainLockBudgetSuccessorGrant
      ring hn fresh update s e label hInv g hNewHost
  refine ⟨hGrant, ?_⟩
  rw [hNewMark]
  simp only [hNewRequest, Bool.false_eq_true, ↓reduceIte,
    hNewLeader]
  rw [hNewQuota]
  exact Nat.le_refl n

end L3


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Source-level weak-to-strong closure, without a post-physical
hypothesis. This covers the requested non-death branch
(and also any death branch satisfying the same weak-to-strong premise).
The only two origins of a strong promotion are a new strong observation
or an old coalesced strong observation. In the second case a separate
shadow label invokes the already proved physical strong corridor
geometry on the literal grantDrainStep.
-/

private theorem grantDrainWeakRiseSource
    (coalesced observed : GrantDrainMark)
    (h : grantDrainMarkJoin .weak
      (grantDrainMarkJoin .weak
        (grantDrainMarkJoin coalesced observed)) = .strong) :
    coalesced = .strong ∨ observed = .strong := by
  cases coalesced <;> cases observed <;>
    simp [grantDrainMarkJoin, grantDrainMarkRank] at h ⊢

private def grantDrainWeakRiseShadow {n : Nat}
    (e : Fin n) : GrantDrainLedgerLabel n :=
  { identity := e
    host := some e
    mark := .strong
    remaining := n }

/-- If the old initiator itself has an observed strong lock and keeps a
real grant, the canonical strong-corridor theorem transports its physical
certificate. A shadow mark is used only inside this proof; no physical
state, transition, or actual ledger mark is replaced. -/
private theorem grantDrainWeakRiseCoalescedPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hOldGrant : s.grant e = true)
    (hOldObserved :
      grantDrainLedgerObservedMark ring s (some e) = .strong)
    (hPostGrant :
      (grantDrainStep ring fresh update s e).grant e = true)
    (hPostNotTerminal :
      grantDrainLedgerObservedMark ring
        (grantDrainStep ring fresh update s e) (some e) ≠
          .terminal) :
    (grantDrainStep ring fresh update s e).request e = false ∧
    ((grantDrainStep ring fresh update s e).native e).l = false ∧
    grantDrainLedgerStrongLock ring
      (grantDrainStep ring fresh update s e) e = true := by
  have hOldRequest : s.request e = false := by
    cases hr : s.request e with
    | false => rfl
    | true =>
        simp [grantDrainLedgerObservedMark, hr, hOldGrant]
          at hOldObserved
  have hOldFollower : (s.native e).l = false := by
    cases hl : (s.native e).l with
    | false => rfl
    | true =>
        simp [grantDrainLedgerObservedMark, hOldRequest, hl]
          at hOldObserved
  have hOldLock : grantDrainLedgerStrongLock ring s e = true := by
    cases hs : grantDrainLedgerStrongLock ring s e with
    | true => rfl
    | false =>
        simp [grantDrainLedgerObservedMark, hOldRequest,
          hOldFollower, hs] at hOldObserved
        all_goals (split at hOldObserved <;> cases hOldObserved)
  have hShadowPhysical :
      GrantDrainStrongPhysical ring s
        (grantDrainWeakRiseShadow e) :=
    ⟨e, rfl, rfl, hOldGrant, hOldRequest, hOldFollower, hOldLock⟩
  have hRowGrant :
      (grantDrainLedgerRow ring fresh s e).1.grant = true := by
    rw [← grantDrainWeakStepGrantAtSource ring fresh update s e]
    exact hPostGrant
  have hShadowRawHost :
      grantDrainLedgerHost ring fresh s e (some e) = some e := by
    simp [grantDrainLedgerHost, hOldGrant, hRowGrant]
  have hShadowHost :
      (grantDrainLedgerStep ring fresh update s e
        (grantDrainWeakRiseShadow e)).host = some e :=
    hShadowRawHost
  have hNotY : e ≠ ring.rightNeighbor e :=
    Ne.symm (EWord.rightNeighborDifferent ring
      (by omega : 2 ≤ n) e)
  have hNoCoalesce :
      grantDrainLedgerCoalesceMark ring s e (some e) (some e) =
        .unmarked := by
    have hNo :
        ¬ (some e = some (ring.rightNeighbor e) ∧
          some e = some e ∧ s.grant e = true) := by
      intro h
      exact hNotY (Option.some.inj h.1)
    simp [grantDrainLedgerCoalesceMark, hNotY]
  have hShadowMark :
      (grantDrainLedgerStep ring fresh update s e
        (grantDrainWeakRiseShadow e)).mark = .strong := by
    change grantDrainMarkJoin .strong
      (grantDrainMarkJoin
        (grantDrainLedgerObservedMark ring s (some e))
        (grantDrainMarkJoin
          (grantDrainLedgerCoalesceMark ring s e (some e)
            (grantDrainLedgerHost ring fresh s e (some e)))
          (grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerHost ring fresh s e (some e))))) =
              .strong
    rw [hOldObserved, hShadowRawHost, hNoCoalesce]
    cases hp : grantDrainLedgerObservedMark ring
        (grantDrainStep ring fresh update s e) (some e) with
    | unmarked => rfl
    | weak => rfl
    | strong => rfl
    | terminal =>
        exact False.elim (hPostNotTerminal hp)
  have hShadowLive :
      (grantDrainLedgerStep ring fresh update s e
        (grantDrainWeakRiseShadow e)).host ≠ none := by
    rw [hShadowHost]
    simp
  have hGeometry :
      GrantDrainStrongCorridorGeometry ring fresh update :=
    grantDrainStrongCorridorGeometry_of_arc_coverage
      ring fresh update
      (grantDrainMarksStrongArcCoverageOfThree
        (by omega : 3 ≤ n) ring fresh update)
      (grantDrainMarksStrongPhysicalClosureOfThree
        (by omega : 3 ≤ n) ring fresh update)
  obtain ⟨j, hjHost, _, _, hjRequest, hjFollower, hjLock⟩ :=
    (hGeometry s e (grantDrainWeakRiseShadow e)
      hP hShadowPhysical hShadowLive hShadowMark).1
  have hjEq : j = e :=
    Option.some.inj (hjHost.symm.trans hShadowHost)
  subst j
  exact ⟨hjRequest, hjFollower, hjLock⟩

/-- Complete weak-to-strong one-edge LockBudget for the actual
grantDrainStep/grantDrainLedgerStep. No assumed post-step physical
certificate, death test, or synthetic source step occurs in the
statement. The new protected-distance quota is supplied by the
previously proved weak-to-strong budget algebra. -/
theorem grantDrainLockBudgetWeakToStrongHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNewStrong :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .strong) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  cases hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host with
  | none =>
      intro j hj
      rw [hNewHost] at hj
      cases hj
  | some j =>
      have hRawHost :
          grantDrainLedgerHost ring fresh s e label.host = some j :=
        hNewHost
      obtain ⟨hOldGrant, hOldCase⟩ := hInv g hHost
      rw [hWeak] at hOldCase
      obtain ⟨hOldRequest, hOldFollower, hOldWeakLock, _⟩ :=
        hOldCase
      have hOldNotStrong :
          grantDrainLedgerStrongLock ring s g = false := by
        cases hs :
            (s.native (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))).sh with
        | false =>
            simp [grantDrainLedgerStrongLock, hs]
        | true =>
            simp [grantDrainLedgerWeakLock, hs] at hOldWeakLock
      have hOldObserved :
          grantDrainLedgerObservedMark ring s label.host = .weak := by
        rw [hHost]
        simp [grantDrainLedgerObservedMark, hOldRequest,
          hOldFollower, hOldNotStrong, hOldWeakLock]
      have hRawMark :
          grantDrainMarkJoin .weak
            (grantDrainMarkJoin .weak
              (grantDrainMarkJoin
                (grantDrainLedgerCoalesceMark ring s e label.host
                  (grantDrainLedgerHost ring fresh s e label.host))
                (grantDrainLedgerObservedMark ring
                  (grantDrainStep ring fresh update s e)
                  (some j)))) = .strong := by
        have hm :
            grantDrainLedgerMarkNext ring fresh update s e label =
              .strong := hNewStrong
        unfold grantDrainLedgerMarkNext at hm
        rw [hWeak, hOldObserved, hRawHost] at hm
        rw [hRawHost]
        exact hm
      have hPostNotTerminal :
          grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e)
            (some j) ≠ .terminal := by
        intro ht
        have hBad : (.terminal : GrantDrainMark) = .strong := by
          simpa only [ht, grantDrainMarkJoin_terminal_right]
            using hRawMark
        cases hBad
      have hPostGrant :
          (grantDrainStep ring fresh update s e).grant j = true :=
        grantDrainLockBudgetSuccessorGrant
          ring hn fresh update s e label hInv j hNewHost
      have hRise :=
        grantDrainWeakRiseSource
          (grantDrainLedgerCoalesceMark ring s e label.host
            (grantDrainLedgerHost ring fresh s e label.host))
          (grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e) (some j))
          hRawMark
      cases hRise with
      | inr hPostObserved =>
          have hPostRequest :
              (grantDrainStep ring fresh update s e).request j =
                false := by
            cases hr :
                (grantDrainStep ring fresh update s e).request j with
            | false => rfl
            | true =>
                simp [grantDrainLedgerObservedMark, hr, hPostGrant]
                  at hPostObserved
          have hPostFollower :
              ((grantDrainStep ring fresh update s e).native j).l =
                false := by
            cases hl :
                ((grantDrainStep ring fresh update s e).native j).l with
            | false => rfl
            | true =>
                simp [grantDrainLedgerObservedMark, hPostRequest, hl]
                  at hPostObserved
          have hPostLock :
              grantDrainLedgerStrongLock ring
                (grantDrainStep ring fresh update s e) j = true := by
            cases hs :
                grantDrainLedgerStrongLock ring
                  (grantDrainStep ring fresh update s e) j with
            | true => rfl
            | false =>
                simp [grantDrainLedgerObservedMark, hPostRequest,
                  hPostFollower, hs] at hPostObserved
                all_goals (split at hPostObserved <;> cases hPostObserved)
          have hPhysical :
              GrantDrainStrongPhysical ring
                (grantDrainStep ring fresh update s e)
                (grantDrainLedgerStep ring fresh update s e label) :=
            ⟨j, hNewHost, hNewStrong, hPostGrant,
              hPostRequest, hPostFollower, hPostLock⟩
          exact grantDrainLockBudgetWeakToStrongOfPhysical
            ring hn fresh update s e label g
            hInv hHost hWeak hPhysical
      | inl hCoalesced =>
          have hCondition :
              label.host = some (ring.rightNeighbor e) ∧
              grantDrainLedgerHost ring fresh s e label.host =
                some e ∧
              s.grant e = true := by
            by_cases hc :
                label.host = some (ring.rightNeighbor e) ∧
                grantDrainLedgerHost ring fresh s e label.host =
                  some e ∧
                s.grant e = true
            · exact hc
            · have hNo :
                  grantDrainLedgerCoalesceMark ring s e label.host
                    (grantDrainLedgerHost ring fresh s e label.host) =
                    .unmarked := by
                simp [grantDrainLedgerCoalesceMark, hc]
              rw [hNo] at hCoalesced
              cases hCoalesced
          have hCoalesceObserved :
              grantDrainLedgerCoalesceMark ring s e label.host
                (grantDrainLedgerHost ring fresh s e label.host) =
                  grantDrainLedgerObservedMark ring s (some e) := by
            unfold grantDrainLedgerCoalesceMark
            simp only [if_pos hCondition]
          have hOldXObserved :
              grantDrainLedgerObservedMark ring s (some e) =
                .strong :=
            hCoalesceObserved.symm.trans hCoalesced
          have hjEq : j = e :=
            Option.some.inj (hRawHost.symm.trans hCondition.2.1)
          subst j
          obtain ⟨hPostRequest, hPostFollower, hPostLock⟩ :=
            grantDrainWeakRiseCoalescedPhysical
              ring hn fresh update s e hP hCondition.2.2
              hOldXObserved hPostGrant hPostNotTerminal
          have hPhysical :
              GrantDrainStrongPhysical ring
                (grantDrainStep ring fresh update s e)
                (grantDrainLedgerStep ring fresh update s e label) :=
            ⟨e, hNewHost, hNewStrong, hPostGrant,
              hPostRequest, hPostFollower, hPostLock⟩
          exact grantDrainLockBudgetWeakToStrongOfPhysical
            ring hn fresh update s e label g
            hInv hHost hWeak hPhysical

end L3


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Closure of the terminal native-leader
on-pair row. The old leader at the selected initiator always retires.
For an old responder leader, a surviving identity requires that the
responder has ceased being a leader. The remaining survivor-to-strong
physical certificate is NOT claimed here.
-/

/-- A final native leader at the responder sinks its own grant,
independently of requests, other grants, FIRE, and fresh input. -/
private theorem grantDrainTerminalLeaderResponderSinkRow
    (rx gx ry gy lx fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow rx gx ry gy lx true fresh fire).2.grant =
      false := by
  cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases lx <;> cases fresh <;> cases fire <;>
    simp [grantDrainTokenRow] <;> decide

/-- A final native leader at the initiator sinks its own grant for
every responder grant bit (the general form of
grantDrainMarksOutgoingSourceLeaderSinksPair, which fixes it to true). -/
private theorem grantDrainTerminalLeaderSourceSinkRow
    (rx gx ry gy ly fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow rx gx ry gy true ly fresh fire).1.grant =
      false := by
  cases rx <;> cases gx <;> cases ry <;> cases gy <;> cases ly <;>
    cases fresh <;> cases fire <;>
    simp [grantDrainTokenRow] <;> decide

/-- The literal native initiator leader cannot be killed by E or FIRE.
The physical token row sinks both grants at the initiator, hence
the old initiator label retires (even if it was previously terminal). -/
theorem grantDrainTerminalLeaderOutgoingRetired
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hHost : label.host = some e)
    (hLeader : (s.native e).l = true) :
    (grantDrainLedgerStep ring fresh update s e label).host =
      none := by
  have hFinalX :
      (grantDrainNativeNext ring s e e).l = true :=
    grantDrainMarksOutgoingLeaderNext ring s e hLeader
  have hRowX :
      (grantDrainLedgerRow ring fresh s e).1.grant = false := by
    unfold grantDrainLedgerRow
    rw [hFinalX]
    exact grantDrainTerminalLeaderSourceSinkRow
      (s.request e) (s.grant e)
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
      (fresh s e) (grantDrainSelect ring s e)
  change grantDrainLedgerHost ring fresh s e label.host = none
  rw [hHost]
  simp [grantDrainLedgerHost, hRowX]

/-- The entire outgoing half of terminal native-leader LockBudget is
vacuous after the actual old leader's grant is consumed. -/
theorem grantDrainLockBudgetTerminalLeaderOutgoingHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some e)
    (hTerminal : label.mark = .terminal)
    (hRequest : s.request e = false)
    (hLeader : (s.native e).l = true) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  intro j hj
  have hRetired :=
    grantDrainTerminalLeaderOutgoingRetired
      ring fresh update s e label hHost hLeader
  rw [hRetired] at hj
  cases hj

/-- If the old responder's final physical leader flag is true,
the final token row has no responder grant; its Y-source cannot
move to X either, because that move requires a follower at Y.
Thus the old responder identity retires. -/
theorem grantDrainTerminalLeaderResponderRetiredIfLeader
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hNewLeader :
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l =
        true) :
    (grantDrainLedgerStep ring fresh update s e label).host =
      none := by
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainMarksNeighborDistinct (by omega : 3 ≤ n) ring e
  have hRowY :
      (grantDrainLedgerRow ring fresh s e).2.grant = false := by
    unfold grantDrainLedgerRow
    rw [hNewLeader]
    exact grantDrainTerminalLeaderResponderSinkRow
      (s.request e) (s.grant e)
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (fresh s e) (grantDrainSelect ring s e)
  have hYSource :
      grantDrainLedgerYSource
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring s e e).l
        (grantDrainNativeNext ring s e
          (ring.rightNeighbor e)).l
        (grantDrainSelect ring s e)
        (grantDrainLedgerRow ring fresh s e) = none := by
    cases hg : s.grant (ring.rightNeighbor e) with
    | false =>
        simp [grantDrainLedgerYSource, hg]
    | true =>
        simp [grantDrainLedgerYSource, hg, hRowY, hNewLeader]
  change grantDrainLedgerHost ring fresh s e label.host = none
  rw [hHost]
  simp [grantDrainLedgerHost, hDistinct, hYSource]

/-- No survivor of an old responder-hosted identity can have the
responder still physically a leader. This is an unconditional
necessary classification on the literal ledger/source step. -/
theorem grantDrainTerminalLeaderResponderSurvivorHasDied
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e j : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).l = false := by
  change (grantDrainNativeNext ring s e
    (ring.rightNeighbor e)).l = false
  cases hFinal :
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l with
  | false => rfl
  | true =>
      have hRetired :=
        grantDrainTerminalLeaderResponderRetiredIfLeader
          ring hn fresh update s e label hHost hFinal
      rw [hRetired] at hNewHost
      cases hNewHost

end L3


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Independently closed source-row facts for the two remaining
terminal-target cells. These are not a proof of either
full LockBudget step-preservation cell.
-/

/-- A live grant at the source of a literal token row requires
the final source native leader bit to be false. -/
theorem grantDrainTerminalSourceGrantForcesFollower
    (rx gx ry gy lx ly fresh : Bool) (fire : GrantDrainFire)
    (h :
      (grantDrainTokenRow rx gx ry gy lx ly fresh fire).1.grant =
        true) : lx = false := by
  revert h
  cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases lx <;> cases ly <;> cases fresh <;>
    cases fire <;> decide

/-- The analogous final native leader exclusion for a surviving
responder grant. -/
theorem grantDrainTerminalResponderGrantForcesFollower
    (rx gx ry gy lx ly fresh : Bool) (fire : GrantDrainFire)
    (h :
      (grantDrainTokenRow rx gx ry gy lx ly fresh fire).2.grant =
        true) : ly = false := by
  revert h
  cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases lx <;> cases ly <;> cases fresh <;>
    cases fire <;> decide

/-- A request-free source has no way to receive a request in
the canonical row; the adversarial fresh request is responder-only. -/
theorem grantDrainTerminalUnrequestedSourceRow
    (gx ry gy lx ly fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow false gx ry gy lx ly fresh fire).1.req =
      false := by
  cases gx <;> cases ry <;> cases gy <;>
    cases lx <;> cases ly <;> cases fresh <;>
    cases fire <;> decide

/-- Moving a responder identity to the source is possible only
on the non-FIRE, unheld, final-follower branch. This theorem is
about the exact source-owner selector, not a hypothetical transport. -/
theorem grantDrainTerminalYSourceMoveBits
    (ry gy lx ly : Bool) (fire : GrantDrainFire)
    (row : TokPair × TokPair)
    (h : grantDrainLedgerYSource ry gy lx ly fire row =
      some false) :
    ry = false ∧ gy = true ∧ lx = false ∧ ly = false ∧
      fire = .none ∧ row.1.grant = true ∧ row.2.grant = false := by
  cases ry <;> cases gy <;> cases lx <;> cases ly <;>
    cases fire <;>
    cases hx : row.1.grant <;> cases hy : row.2.grant <;>
    simp [grantDrainLedgerYSource, hx, hy] at h ⊢ <;>
    revert h <;> decide

/-- If the source already holds a grant and an unheld Y-grant
coalesces there on a non-FIRE row, its source request survives. -/
theorem grantDrainTerminalCoalescedHeldSourceRow
    (fresh : Bool) :
    (grantDrainTokenRow true true false true false false
      fresh .none).1.req = true := by
  cases fresh <;> decide

/-- Pure four-mark algebra: the join of a persistent strong mark
with two nonterminal observations remains exactly strong. -/
theorem grantDrainTerminalStrongJoinBelow
    (a b : GrantDrainMark)
    (ha : a ≠ .terminal) (hb : b ≠ .terminal) :
    grantDrainMarkJoin .strong
      (grantDrainMarkJoin .strong (grantDrainMarkJoin a b)) =
        .strong := by
  cases a <;> cases b <;>
    simp [grantDrainMarkJoin, grantDrainMarkRank] at *

/-- The old observation of an unrequested strongly protected
follower is strong, even if its persistent ghost mark is terminal. -/
theorem grantDrainTerminalFollowerOldObservation
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hHost : label.host = some g)
    (hRequest : s.request g = false)
    (hFollower : (s.native g).l = false)
    (hLock : grantDrainLedgerStrongLock ring s g = true) :
    grantDrainLedgerObservedMark ring s label.host = .strong := by
  rw [hHost]
  simp [grantDrainLedgerObservedMark, hRequest, hFollower, hLock]

/-- Every surviving ledger host is either the old site or the
selected source. This is exact for X-stay, Y-stay, Y-move, and
untouched sites, independently of the persistent mark. -/
theorem grantDrainTerminalSuccessorHostRange
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (s : GrantDrainState n Scratch)
    (e g j : Fin n)
    (h :
      grantDrainLedgerHost ring fresh s e (some g) = some j) :
    j = g ∨ j = e := by
  by_cases hX : g = e
  · subst g
    cases hb : (s.grant e &&
        (grantDrainLedgerRow ring fresh s e).1.grant) with
    | false =>
        have hv :
            grantDrainLedgerHost ring fresh s e (some e) =
              none := by
          simp [grantDrainLedgerHost, hb]
        rw [hv] at h
        cases h
    | true =>
        have hv :
            grantDrainLedgerHost ring fresh s e (some e) =
              some e := by
          simp [grantDrainLedgerHost, hb]
        have he : e = j := Option.some.inj (hv.symm.trans h)
        exact Or.inl he.symm
  · by_cases hY : g = ring.rightNeighbor e
    · subst g
      have hne : ring.rightNeighbor e ≠ e :=
        grantDrainMarksNeighborDistinct (by omega : 3 ≤ n) ring e
      cases hs : grantDrainLedgerYSource
          (s.request (ring.rightNeighbor e))
          (s.grant (ring.rightNeighbor e))
          (grantDrainNativeNext ring s e e).l
          (grantDrainNativeNext ring s e
            (ring.rightNeighbor e)).l
          (grantDrainSelect ring s e)
          (grantDrainLedgerRow ring fresh s e) with
      | none =>
          have hv :
              grantDrainLedgerHost ring fresh s e
                (some (ring.rightNeighbor e)) = none := by
            simp only [grantDrainLedgerHost,
              if_neg hne, if_pos rfl, hs, if_true]
          rw [hv] at h
          cases h
      | some stay =>
          cases stay with
          | false =>
              have hv :
                  grantDrainLedgerHost ring fresh s e
                    (some (ring.rightNeighbor e)) = some e := by
                simp only [grantDrainLedgerHost,
                  if_neg hne, if_pos rfl, hs, if_true]
              have he : e = j :=
                Option.some.inj (hv.symm.trans h)
              exact Or.inr he.symm
          | true =>
              have hv :
                  grantDrainLedgerHost ring fresh s e
                    (some (ring.rightNeighbor e)) =
                      some (ring.rightNeighbor e) := by
                simp only [grantDrainLedgerHost,
                  if_neg hne, if_pos rfl, hs, if_true]
              have he : ring.rightNeighbor e = j :=
                Option.some.inj (hv.symm.trans h)
              exact Or.inl he.symm
    · have he : some g = some j := by
        simpa [grantDrainLedgerHost, hX, hY] using h
      exact Or.inl (Option.some.inj he).symm

end L3


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Corner exclusion.
The full strong-to-terminal LockBudget theorem remains open.
No extra physical-leaf hypothesis is assumed.
-/

/-- A strongly protected source at distance one is precisely the
left endpoint of the nominated incoming edge. The literal source
token row then sinks the responder grant, retiring its identity.
This rules out the putative held-terminal quota 1 -> 0 survivor. -/
theorem grantDrainStrongTerminalUnitHitRetires
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hOldStrong : label.mark = .strong)
    (hDistance :
      grantDrainStrongProtectedDistance ring s (some g) = 1)
    (hHit :
      grantDrainLedgerNominatedHit ring s e label.host = true) :
    (grantDrainLedgerStep ring fresh update s e label).host =
      none := by
  obtain ⟨hOldGrant, hOldCase⟩ := hInv g hOldHost
  rw [hOldStrong] at hOldCase
  obtain ⟨hOldRequest, hOldFollower, hOldLock, _⟩ :=
    hOldCase
  have hIncoming : ring.rightNeighbor e = g := by
    simpa [grantDrainLedgerNominatedHit, hOldHost, hOldRequest]
      using hHit
  obtain ⟨p, hNearest, _, _⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring s g hP hOldFollower hOldLock
  have hDistanceArc :=
    grantDrainMarksProtectedDistanceOfArc
      ring s p g hNearest
  have hOffsetOne : PPL.cyclicOffset ring p g = 1 := by
    rw [hDistanceArc] at hDistance
    exact hDistance
  have hNeighbor : ring.rightNeighbor p = g :=
    grantDrainMarksHostAtOffsetOne ring p g hOffsetOne
  have hLeftEdge :=
    grantDrainWeakIncomingHostLeftNeighbor
      ring hn e g hIncoming
  have hLeftProtected :=
    grantDrainWeakIncomingHostLeftNeighbor
      ring hn p g hNeighbor
  have he : e = p := hLeftEdge.symm.trans hLeftProtected
  rw [he]
  exact grantDrainMarksProtectedAdjacentHostRetired
    ring fresh update s p g label hNeighbor hOldHost
    hNearest.2.1 hOldFollower hOldGrant

/-- A nominated incoming hit cannot leave a strong identity alive
with old protected distance one. The old distance is positive for
every live host, so a surviving nominated hit starts at distance
at least two. In particular its strong LockBudget contains at
least two units, enough to leave positive quota after one hit. -/
theorem grantDrainStrongTerminalSurvivorHitDistance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hOldStrong : label.mark = .strong)
    (hHit :
      grantDrainLedgerNominatedHit ring s e label.host = true)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    2 ≤ grantDrainStrongProtectedDistance ring s (some g) := by
  have hPositive :=
    grantDrainStrongProtectedDistance_some_pos ring s g
  have hNotOne :
      grantDrainStrongProtectedDistance ring s (some g) ≠ 1 := by
    intro hDistance
    have hRetired :=
      grantDrainStrongTerminalUnitHitRetires
        ring hn fresh update s e label g
        hP hInv hOldHost hOldStrong hDistance hHit
    rw [hRetired] at hNewHost
    cases hNewHost
  omega

/-- The old strong budget pays the nominated decrement of any
surviving hit without exhausting the remaining counter. This is
pure old-state arithmetic plus the literal protected-source sink. -/
theorem grantDrainStrongTerminalSurvivorHitQuotaPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hOldStrong : label.mark = .strong)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    0 < label.remaining -
      (if grantDrainLedgerNominatedHit ring s e label.host
       then 1 else 0) := by
  obtain ⟨_, hOldCase⟩ := hInv g hOldHost
  rw [hOldStrong] at hOldCase
  obtain ⟨_, _, _, hBudget⟩ := hOldCase
  have hPositive :=
    grantDrainStrongProtectedDistance_some_pos ring s g
  cases hHit : grantDrainLedgerNominatedHit ring s e label.host with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
      omega
  | true =>
      have hDistance :=
        grantDrainStrongTerminalSurvivorHitDistance
          ring hn fresh update s e label g j
          hP hInv hOldHost hOldStrong hHit hNewHost
      simp only [↓reduceIte]
      omega

end L3


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Unmarked rising-mark partial closures on the LITERAL source
and ledger step.

The entire marked-to-cap arithmetic is proved without any native
assumption. An observed-mark/cap seed is then transported from the
existing initial LockBudget theorem, with identity irrelevant to
LockBudget. Finally two unconditional source-observation outcome cases
are discharged: a first post-step observation and a post-step held or
leader terminal status. This does NOT assert the universal
grantDrainLockBudgetUnmarkedRiseHolds: promotions caused only by an
OLD observation or coalescence need additional physical transport.
-/

/-- When the OLD persistent mark is unmarked, every surviving ledger
identity has EXACTLY its new cap. There is no nominated-hit decrement,
independently of native fields, requests, FIRE, and coalescence. -/
theorem grantDrainUnmarkedSuccessorRemainingIsCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (j : Fin n)
    (hUnmarked : label.mark = .unmarked)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    (grantDrainLedgerStep ring fresh update s e label).remaining =
      grantDrainLedgerQuotaCap n
        (grantDrainLedgerStep ring fresh update s e label).mark
        (grantDrainLedgerHeld
          (grantDrainStep ring fresh update s e) (some j)) := by
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host = some j :=
    hNewHost
  change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring fresh s e label.host)
      (grantDrainLedgerMarkNext ring fresh update s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e label.host)) =
    grantDrainLedgerQuotaCap n
      (grantDrainLedgerMarkNext ring fresh update s e label)
      (grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e) (some j))
  rw [hRawHost]
  simp [grantDrainLedgerRemainingNext, hUnmarked]

/-- An actual physical grant whose mark is exactly its own native /
token observation, with precisely the observation's quota cap,
satisfies LockBudget. This is a renaming of the initial-seed
invariant: the identity coordinate is not used in LockBudget or in
ledger-host transport. It applies at arbitrary source cuts. -/
theorem grantDrainLockBudgetObservedCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n) (j : Fin n)
    (hHost : label.host = some j)
    (hGrant : s.grant j = true)
    (hMark :
      label.mark = grantDrainLedgerObservedMark ring s (some j))
    (hRemaining :
      label.remaining =
        grantDrainLedgerQuotaCap n
          (grantDrainLedgerObservedMark ring s (some j))
          (grantDrainLedgerHeld s (some j))) :
    LockBudget ring fresh update s label := by
  have hSeed :
      LockBudget ring fresh update s
        { (grantDrainLedgerInitial ring s j) with
          identity := label.identity } := by
    exact grantDrainLockBudgetInitial ring hn fresh update s j
  have hSame :
      { (grantDrainLedgerInitial ring s j) with
        identity := label.identity } = label := by
    cases label with
    | mk identity host mark remaining =>
        change host = some j at hHost
        change mark =
          grantDrainLedgerObservedMark ring s (some j) at hMark
        change remaining =
          grantDrainLedgerQuotaCap n
            (grantDrainLedgerObservedMark ring s (some j))
            (grantDrainLedgerHeld s (some j)) at hRemaining
        cases hHost
        cases hMark
        cases hRemaining
        simp [grantDrainLedgerInitial, hGrant]
  rw [hSame] at hSeed
  exact hSeed

/-- A genuinely fresh detection is sufficient for the complete
unmarked-to-post-observation LockBudget step, for ANY actual FIRE,
movement, or local request. There is no assumed physical certificate.
The two hypotheses are OLD/COALESCE mark observations, not an
assertion about the POST host or its geometry. -/
theorem grantDrainLockBudgetUnmarkedFreshObservationHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hUnmarked : label.mark = .unmarked)
    (hOldObserved :
      grantDrainLedgerObservedMark ring s label.host =
        .unmarked)
    (hCoalesce :
      grantDrainLedgerCoalesceMark ring s e label.host
        (grantDrainLedgerHost ring fresh s e label.host) =
          .unmarked) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  intro j hNewHost
  have hNewGrant :
      (grantDrainStep ring fresh update s e).grant j = true :=
    grantDrainLockBudgetSuccessorGrant
      ring hn fresh update s e label hInv j hNewHost
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host = some j :=
    hNewHost
  have hNewMark :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        grantDrainLedgerObservedMark ring
          (grantDrainStep ring fresh update s e) (some j) := by
    change grantDrainLedgerMarkNext ring fresh update s e label =
      grantDrainLedgerObservedMark ring
        (grantDrainStep ring fresh update s e) (some j)
    unfold grantDrainLedgerMarkNext
    rw [hUnmarked, hOldObserved, hCoalesce, hRawHost]
    cases hObserved :
        grantDrainLedgerObservedMark ring
          (grantDrainStep ring fresh update s e) (some j) <;>
      rfl
  have hNewQuota :
      (grantDrainLedgerStep ring fresh update s e label).remaining =
        grantDrainLedgerQuotaCap n
          (grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e) (some j))
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e) (some j)) := by
    rw [grantDrainUnmarkedSuccessorRemainingIsCap
      ring fresh update s e label j hUnmarked hNewHost,
      hNewMark]
  exact grantDrainLockBudgetObservedCap
    ring hn fresh update
    (grantDrainStep ring fresh update s e)
    (grantDrainLedgerStep ring fresh update s e label) j
    hNewHost hNewGrant hNewMark hNewQuota j hNewHost

/-- A surviving unmarked label whose actual post host has either
a request (HOLD) or a native leader is fully terminal and budgeted.
The observer necessarily makes the persistent mark terminal, so
neither an old observation nor a coalesced observation can obstruct
the post-step terminal LockBudget. The held retirement obligation
comes from the literal token row via ObservedCap. -/
theorem grantDrainLockBudgetUnmarkedPostTerminalStatusHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (j : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hUnmarked : label.mark = .unmarked)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hPostStatus :
      (grantDrainStep ring fresh update s e).request j = true ∨
      ((grantDrainStep ring fresh update s e).native j).l = true) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  have hNewGrant :
      (grantDrainStep ring fresh update s e).grant j = true :=
    grantDrainLockBudgetSuccessorGrant
      ring hn fresh update s e label hInv j hNewHost
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host = some j :=
    hNewHost
  have hPostObserved :
      grantDrainLedgerObservedMark ring
        (grantDrainStep ring fresh update s e) (some j) =
          .terminal := by
    cases hPostStatus with
    | inl hr =>
        simp [grantDrainLedgerObservedMark, hr, hNewGrant]
    | inr hl =>
        cases hr :
            (grantDrainStep ring fresh update s e).request j with
        | true =>
            simp [grantDrainLedgerObservedMark, hr, hNewGrant]
        | false =>
            simp [grantDrainLedgerObservedMark, hr, hl]
  have hNewMark :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .terminal := by
    change grantDrainLedgerMarkNext ring fresh update s e label =
      .terminal
    unfold grantDrainLedgerMarkNext
    rw [hRawHost, hPostObserved]
    simp only [grantDrainMarkJoin_terminal_right]
  have hNewQuota :
      (grantDrainLedgerStep ring fresh update s e label).remaining =
        grantDrainLedgerQuotaCap n
          (grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e) (some j))
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e) (some j)) := by
    calc
      (grantDrainLedgerStep ring fresh update s e label).remaining =
          grantDrainLedgerQuotaCap n
            (grantDrainLedgerStep ring fresh update s e label).mark
            (grantDrainLedgerHeld
              (grantDrainStep ring fresh update s e) (some j)) :=
        grantDrainUnmarkedSuccessorRemainingIsCap
          ring fresh update s e label j hUnmarked hNewHost
      _ = grantDrainLedgerQuotaCap n
            (grantDrainLedgerObservedMark ring
              (grantDrainStep ring fresh update s e) (some j))
            (grantDrainLedgerHeld
              (grantDrainStep ring fresh update s e) (some j)) := by
        rw [hNewMark, hPostObserved]
  exact grantDrainLockBudgetObservedCap
    ring hn fresh update
    (grantDrainStep ring fresh update s e)
    (grantDrainLedgerStep ring fresh update s e label) j
    hNewHost hNewGrant
    (hNewMark.trans hPostObserved.symm) hNewQuota

end L3


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Terminal native-leader death, literal canonical source and ledger
step.

An unrequested responder grant cannot remain at the responder. If its
identity survives it moves to the initiator under the non-FIRE Y-source
row. The old initiator must be a peaceful LIVE follower. The protected
nearest-leader/zero-signal prefix behind that initiator is untouched:
the killed responder cannot be the protected root, because the literal
E death equation requires its old signal to be one or its old shield
to be false. The post initiator is therefore strongly locked.
-/

/-- No unrequested OLD responder grant can remain at Y after the
literal two-site token step, including any FIRE and fresh request. -/
theorem grantDrainTerminalLeaderUnheldResponderGrantLeaves
    (rx gx lx ly fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow rx gx false true lx ly fresh fire).2.grant =
      false := by
  cases rx <;> cases gx <;> cases lx <;> cases ly <;>
    cases fresh <;> cases fire <;>
    simp [grantDrainTokenRow] <;> decide

/-- Complete actual native/token certificate after death of an
unrequested old terminal leader hosted at the responder. No post-step
physical premise is assumed. In particular j must be the initiator,
and the new lock is inherited from the peaceful OLD LIVE killer's
strictly preceding shielded zero corridor. -/
theorem grantDrainTerminalLeaderDeathPhysicalHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (j : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost :
      label.host = some (ring.rightNeighbor e))
    (hTerminal : label.mark = .terminal)
    (hOldRequest :
      s.request (ring.rightNeighbor e) = false)
    (hOldLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    (grantDrainStep ring fresh update s e).grant j = true ∧
    (grantDrainStep ring fresh update s e).request j = false ∧
    ((grantDrainStep ring fresh update s e).native j).l = false ∧
    grantDrainLedgerStrongLock ring
      (grantDrainStep ring fresh update s e) j = true := by
  have hDifferent : ring.rightNeighbor e ≠ e :=
    grantDrainMarksNeighborDistinct (by omega : 3 ≤ n) ring e
  have hOldGrant :
      s.grant (ring.rightNeighbor e) = true :=
    (hInv (ring.rightNeighbor e) hOldHost).1
  have hResponderRow :
      (grantDrainLedgerRow ring fresh s e).2.grant = false := by
    unfold grantDrainLedgerRow
    rw [hOldRequest, hOldGrant]
    exact grantDrainTerminalLeaderUnheldResponderGrantLeaves
      (s.request e) (s.grant e)
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
      (fresh s e) (grantDrainSelect ring s e)
  have hResponderGrantGone :
      (grantDrainStep ring fresh update s e).grant
        (ring.rightNeighbor e) = false := by
    rw [grantDrainWeakStepGrantAtResponder
      ring fresh update s e hDifferent]
    exact hResponderRow
  have hCannotStay :
      (grantDrainLedgerStep ring fresh update s e label).host ≠
        some (ring.rightNeighbor e) := by
    intro hStay
    have hStillGrant :
        (grantDrainStep ring fresh update s e).grant
          (ring.rightNeighbor e) = true :=
      grantDrainLockBudgetSuccessorGrant
        ring hn fresh update s e label hInv
        (ring.rightNeighbor e) hStay
    rw [hResponderGrantGone] at hStillGrant
    cases hStillGrant
  have hMoved :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some e := by
    rcases GrantDrainEntrance.grantDrainEntranceResponderHostCases
        ring (by omega : 2 ≤ n) fresh update s e label
        hOldHost with hGone | hStay | hMove
    · rw [hGone] at hNewHost
      cases hNewHost
    · exact False.elim (hCannotStay hStay)
    · exact hMove
  have hj : e = j :=
    Option.some.inj (hMoved.symm.trans hNewHost)
  subst j
  have hRawMoved :
      grantDrainLedgerHost ring fresh s e
        (some (ring.rightNeighbor e)) = some e := by
    have hRaw :
        grantDrainLedgerHost ring fresh s e label.host =
          some e := hMoved
    rw [hOldHost] at hRaw
    exact hRaw
  have hSourceMoved :
      grantDrainLedgerYSource
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring s e e).l
        (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
        (grantDrainSelect ring s e)
        (grantDrainLedgerRow ring fresh s e) = some false := by
    cases hs : grantDrainLedgerYSource
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring s e e).l
        (grantDrainNativeNext ring s e
          (ring.rightNeighbor e)).l
        (grantDrainSelect ring s e)
        (grantDrainLedgerRow ring fresh s e) with
    | none =>
        have hImpossible : (none : Option (Fin n)) = some e := by
          simpa [grantDrainLedgerHost, hDifferent, hs] using hRawMoved
        cases hImpossible
    | some stays =>
        cases stays with
        | false => rfl
        | true =>
            have hImpossible :
                (some (ring.rightNeighbor e) : Option (Fin n)) =
                  some e := by
              simpa [grantDrainLedgerHost, hDifferent, hs]
                using hRawMoved
            exact False.elim
              (hDifferent (Option.some.inj hImpossible))
  obtain ⟨_, _, hFinalX, _, hNoFire, _, _⟩ :=
    grantDrainTerminalYSourceMoveBits
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
      (grantDrainSelect ring s e)
      (grantDrainLedgerRow ring fresh s e) hSourceMoved
  have hOldELeaderFalse : (s.native e).l = false := by
    have hELeft :
        (nativeE ring s.native e e).l = false := by
      simpa [grantDrainNativeNext, hNoFire] using hFinalX
    rw [grantDrainMarksNativeESource,
      grantDrainMarksOutgoingSourceLeaderNative] at hELeft
    exact hELeft
  have hNewVictimFollower :=
    grantDrainTerminalLeaderResponderSurvivorHasDied
      ring hn fresh update s e e label hOldHost hMoved
  have hEDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false := by
    change (grantDrainNativeNext ring s e
      (ring.rightNeighbor e)).l = false at hNewVictimFollower
    simpa [grantDrainNativeNext, hNoFire] using hNewVictimFollower
  have hLive : LiveBullet s.native e :=
    grantDrainWeakDeathFollowerMustBeLive
      ring hn s.native e hOldELeaderFalse hOldLeader hEDeath
  have hSourceStrong :
      grantDrainLedgerStrongLock ring s e = true :=
    GrantDrainEntrance.grantDrainEntranceLiveStrongLock
      ring s e hP hLive hOldELeaderFalse
  obtain ⟨p, hOldNearest, hOldZero, hOldShield⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring s e hP hOldELeaderFalse hSourceStrong
  have hOldRootZero : (s.native p).sg = false := by
    have hz := hOldZero 0 hOldNearest.1
    rw [grantDrainWeakDeathShiftRightZero ring p] at hz
    exact hz
  have hPairDeath :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.l = false := by
    simpa [nativeE, hDifferent] using hEDeath
  have hVictimOpen :
      (s.native (ring.rightNeighbor e)).sg = true ∨
      (s.native (ring.rightNeighbor e)).sh = false :=
    ((GrantDrainEntrance.grantDrainEntranceLiteralELeaderDeathCases
      (s.native e) (s.native (ring.rightNeighbor e))
      hOldLeader).mp hPairDeath).2
  have hNotRoot : ring.rightNeighbor e ≠ p := by
    intro hEq
    have hVictimShield :
        (s.native (ring.rightNeighbor e)).sh = true := by
      rw [hEq]
      exact hOldShield
    have hVictimZero :
        (s.native (ring.rightNeighbor e)).sg = false := by
      rw [hEq]
      exact hOldRootZero
    cases hVictimOpen with
    | inl hSignal =>
        rw [hVictimZero] at hSignal
        cases hSignal
    | inr hShield =>
        rw [hVictimShield] at hShield
        cases hShield
  have hAway :
      ∀ k : Nat, k < PPL.cyclicOffset ring p e →
        PPL.shiftRight ring p k ≠ e ∧
        PPL.shiftRight ring p k ≠ ring.rightNeighbor e :=
    grantDrainMarksOutgoingHostArcAway
      (by omega : 3 ≤ n) ring p e hNotRoot
  have hFrame :
      ∀ k : Nat, k < PPL.cyclicOffset ring p e →
        (grantDrainStep ring fresh update s e).native
          (PPL.shiftRight ring p k) =
        s.native (PPL.shiftRight ring p k) := by
    intro k hk
    exact grantDrainMarksNativeOutsidePairFrame
      ring s e (PPL.shiftRight ring p k)
      (hAway k hk).1 (hAway k hk).2
  have hRootFrame :
      (grantDrainStep ring fresh update s e).native p =
        s.native p := by
    have hf := hFrame 0 hOldNearest.1
    simpa only [grantDrainWeakDeathShiftRightZero ring p] using hf
  have hNewNearest :
      GrantDrainMarksNearestArc ring
        (grantDrainStep ring fresh update s e).native p e := by
    refine ⟨hOldNearest.1, ?_, ?_⟩
    · rw [hRootFrame]
      exact hOldNearest.2.1
    · intro k hk hlt
      rw [hFrame k hlt]
      exact hOldNearest.2.2 k hk hlt
  have hNewZero :
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainStep ring fresh update s e).native p e := by
    intro k hk
    rw [hFrame k hk]
    exact hOldZero k hk
  have hNewShield :
      ((grantDrainStep ring fresh update s e).native p).sh =
        true := by
    rw [hRootFrame]
    exact hOldShield
  have hStrong :
      grantDrainLedgerStrongLock ring
        (grantDrainStep ring fresh update s e) e = true :=
    grantDrainMarksOffsetArcStrongLock
      ring (grantDrainStep ring fresh update s e)
      p e hNewNearest hNewZero hNewShield
  have hELeftBullet :
      (nativeE ring s.native e e).b = (0 : Fin 3) :=
    GrantDrainEntrance.grantDrainEntranceNativeESourceBulletZero
      ring s.native e
  have hELeftFollower :
      (nativeE ring s.native e e).l = false := by
    simpa [grantDrainNativeNext, hNoFire] using hFinalX
  have hEligible :
      grantDrainEligible (nativeE ring s.native e) e = true := by
    simp [grantDrainEligible, hELeftBullet, hELeftFollower]
  have hOldXRequest : s.request e = false := by
    cases hr : s.request e with
    | false => rfl
    | true =>
        cases hg : s.grant e with
        | true =>
            have hFireLeft : grantDrainSelect ring s e =
                .leftLocal := by
              simp [grantDrainSelect, hr, hg, hEligible]
            rw [hFireLeft] at hNoFire
            cases hNoFire
        | false =>
            have hFireCross : grantDrainSelect ring s e =
                .cross := by
              simp [grantDrainSelect, hr, hg,
                hOldRequest, hOldGrant, hEligible]
            rw [hFireCross] at hNoFire
            cases hNoFire
  have hRowRequest :
      (grantDrainLedgerRow ring fresh s e).1.req = false := by
    unfold grantDrainLedgerRow
    rw [hOldXRequest]
    exact grantDrainTerminalUnrequestedSourceRow
      (s.grant e) (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
      (fresh s e) (grantDrainSelect ring s e)
  have hNewRequest :
      (grantDrainStep ring fresh update s e).request e = false := by
    change
      (if e = e then (grantDrainLedgerRow ring fresh s e).1.req
       else if e = ring.rightNeighbor e then
         (grantDrainLedgerRow ring fresh s e).2.req
       else s.request e) = false
    simp [hRowRequest]
  have hNewGrant :
      (grantDrainStep ring fresh update s e).grant e = true :=
    grantDrainLockBudgetSuccessorGrant
      ring hn fresh update s e label hInv e hMoved
  have hNewFollower :
      ((grantDrainStep ring fresh update s e).native e).l =
        false := hFinalX
  exact ⟨hNewGrant, hNewRequest, hNewFollower, hStrong⟩

/-- The responder half of a terminal native-leader LockBudget step:
retirement is vacuous; a surviving identity has its physical
strong-lock certificate from grantDrainTerminalLeaderDeathPhysicalHolds,
then receives its old n-budget from the death-of-physical lemma. -/
theorem grantDrainLockBudgetTerminalLeaderResponderHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hTerminal : label.mark = .terminal)
    (hRequest : s.request g = false)
    (hLeader : (s.native g).l = true)
    (hAtResponder : g = ring.rightNeighbor e) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  cases hh :
      (grantDrainLedgerStep ring fresh update s e label).host with
  | none =>
      intro j hj
      rw [hh] at hj
      cases hj
  | some j =>
      have hYHost :
          label.host = some (ring.rightNeighbor e) := by
        rw [← hAtResponder]
        exact hHost
      have hYRequest :
          s.request (ring.rightNeighbor e) = false := by
        rw [← hAtResponder]
        exact hRequest
      have hYLeader :
          (s.native (ring.rightNeighbor e)).l = true := by
        rw [← hAtResponder]
        exact hLeader
      obtain ⟨hGrant, hPostRequest, hFollower, hLock⟩ :=
        grantDrainTerminalLeaderDeathPhysicalHolds
          ring hn fresh update s e label j
          hP hInv hYHost hTerminal hYRequest hYLeader hh
      exact grantDrainLockBudgetTerminalLeaderDeathOfPhysical
        ring hn fresh update s e label g j
        hP hInv hHost hTerminal hRequest hLeader hh
        hGrant hPostRequest hFollower hLock

/-- Full terminal/native-leader branch, every edge, combining
the outgoing and away cases with the proved responder-death
physical corridor. No assumed leaf and no replacement transition. -/
theorem grantDrainLockBudgetTerminalLeaderHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hHost : label.host = some g)
    (hTerminal : label.mark = .terminal)
    (hRequest : s.request g = false)
    (hLeader : (s.native g).l = true) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  by_cases hAtSource : g = e
  · subst g
    exact grantDrainLockBudgetTerminalLeaderOutgoingHolds
      ring hn fresh update s e label
      hP hInv hHost hTerminal hRequest hLeader
  · by_cases hAtResponder : g = ring.rightNeighbor e
    · exact grantDrainLockBudgetTerminalLeaderResponderHolds
        ring hn fresh update s e g label
        hP hInv hHost hTerminal hRequest hLeader hAtResponder
    · exact grantDrainLockBudgetTerminalLeaderAwayHolds
        ring hn fresh update s e label g
        hInv hHost hTerminal hRequest hLeader
        hAtSource hAtResponder

end L3


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
The literal
strong-to-terminal LockBudget cell.

A live strong identity cannot enter the native-leader terminal
branch, because the token row sinks grants at new native leaders.
A coalescence-only terminal promotion forces an OLD held source
and the Y-to-X move keeps the source request. Thus every live
strong-to-terminal successor is physically held. The existing
strong survivor hit/quota lemma pays for its one-hit terminal cap.
-/

/-- A request-free native follower cannot have terminal as its
current literal observed mark, regardless of its grant, strong
lock, or weak lock. -/
theorem grantDrainStrongTerminalUnrequestedFollowerObservation
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (j : Fin n)
    (hRequest : s.request j = false)
    (hFollower : (s.native j).l = false) :
    grantDrainLedgerObservedMark ring s (some j) ≠ .terminal := by
  cases hs : grantDrainLedgerStrongLock ring s j <;>
    cases hw : grantDrainLedgerWeakLock ring s j <;>
    simp [grantDrainLedgerObservedMark,
      hRequest, hFollower, hs, hw]

/-- With both persistent and old observed marks strong, a terminal
join whose POST observation is not terminal must have arisen from
the OLD coalescing-source observation. -/
theorem grantDrainStrongTerminalJoinRequiresCoalescence
    (coalesced observed : GrantDrainMark)
    (hObserved : observed ≠ .terminal)
    (hJoin :
      grantDrainMarkJoin .strong
        (grantDrainMarkJoin .strong
          (grantDrainMarkJoin coalesced observed)) = .terminal) :
    coalesced = .terminal := by
  cases coalesced <;> cases observed <;>
    simp [grantDrainMarkJoin, grantDrainMarkRank] at *

/-- A responder-hosted identity can arrive at the old initiator
only when the literal Y-source classification is some false.
The other two Y-source outcomes cannot produce a live host at X. -/
theorem grantDrainStrongTerminalResponderMoveDetected
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hOldHost : label.host = some (ring.rightNeighbor e))
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some e) :
    grantDrainLedgerYSource
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l
      (grantDrainSelect ring s e)
      (grantDrainLedgerRow ring fresh s e) = some false := by
  have hRaw :
      grantDrainLedgerHost ring fresh s e
        (some (ring.rightNeighbor e)) = some e := by
    change grantDrainLedgerHost ring fresh s e label.host =
      some e at hNewHost
    rw [hOldHost] at hNewHost
    exact hNewHost
  have hDifferent : ring.rightNeighbor e ≠ e :=
    grantDrainMarksNeighborDistinct (by omega : 3 ≤ n) ring e
  cases hs : grantDrainLedgerYSource
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l
      (grantDrainSelect ring s e)
      (grantDrainLedgerRow ring fresh s e) with
  | none =>
      have hEval :
          grantDrainLedgerHost ring fresh s e
            (some (ring.rightNeighbor e)) = none := by
        simp only [grantDrainLedgerHost,
          if_neg hDifferent, if_pos rfl, hs, if_true]
      rw [hEval] at hRaw
      cases hRaw
  | some stay =>
      cases stay with
      | false => rfl
      | true =>
          have hEval :
              grantDrainLedgerHost ring fresh s e
                (some (ring.rightNeighbor e)) =
                  some (ring.rightNeighbor e) := by
            simp only [grantDrainLedgerHost,
              if_neg hDifferent, if_pos rfl, hs, if_true]
          have hEq : ring.rightNeighbor e = e :=
            Option.some.inj (hEval.symm.trans hRaw)
          exact False.elim (hDifferent hEq)

/-- On an old unrequested follower identity, a terminal OLD-X
coalescence observation can arise only by moving Y to a held X.
The moving-row conditions imply no FIRE and final followers;
an old leader at X would survive native E and forbid this move.
The literal token row therefore retains X's old request. -/
theorem grantDrainStrongTerminalCoalescencePostHeld
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hOldHost : label.host = some g)
    (hOldRequest : s.request g = false)
    (hOldGrant : s.grant g = true)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hCoalesced :
      grantDrainLedgerCoalesceMark ring s e label.host
        (grantDrainLedgerHost ring fresh s e label.host) =
          .terminal) :
    (grantDrainStep ring fresh update s e).request j = true := by
  have hCondition :
      label.host = some (ring.rightNeighbor e) ∧
        grantDrainLedgerHost ring fresh s e label.host = some e ∧
        s.grant e = true := by
    by_cases hc :
        label.host = some (ring.rightNeighbor e) ∧
          grantDrainLedgerHost ring fresh s e label.host =
            some e ∧ s.grant e = true
    · exact hc
    · have hNo :
          grantDrainLedgerCoalesceMark ring s e label.host
            (grantDrainLedgerHost ring fresh s e label.host) =
              .unmarked := by
        simp [grantDrainLedgerCoalesceMark, hc]
      rw [hNo] at hCoalesced
      cases hCoalesced
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host = some j :=
    hNewHost
  have hj : j = e :=
    Option.some.inj (hRawHost.symm.trans hCondition.2.1)
  have hg : g = ring.rightNeighbor e :=
    Option.some.inj (hOldHost.symm.trans hCondition.1)
  have hYRequest :
      s.request (ring.rightNeighbor e) = false := by
    rw [← hg]
    exact hOldRequest
  have hYGrant :
      s.grant (ring.rightNeighbor e) = true := by
    rw [← hg]
    exact hOldGrant
  have hAtSource :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some e :=
    hNewHost.trans (congrArg some hj)
  have hMove :=
    grantDrainStrongTerminalResponderMoveDetected
      ring hn fresh update s e label hCondition.1 hAtSource
  obtain ⟨_, _, hFinalX, hFinalY, hFire, _, _⟩ :=
    grantDrainTerminalYSourceMoveBits
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l
      (grantDrainSelect ring s e)
      (grantDrainLedgerRow ring fresh s e) hMove
  have hOldSourceFollower : (s.native e).l = false := by
    cases hl : (s.native e).l with
    | false => rfl
    | true =>
        have hOldLeaderPersists :
            (grantDrainNativeNext ring s e e).l = true :=
          grantDrainMarksOutgoingLeaderNext ring s e hl
        rw [hFinalX] at hOldLeaderPersists
        cases hOldLeaderPersists
  have hCoalescedObserved :
      grantDrainLedgerCoalesceMark ring s e label.host
        (grantDrainLedgerHost ring fresh s e label.host) =
          grantDrainLedgerObservedMark ring s (some e) := by
    unfold grantDrainLedgerCoalesceMark
    simp only [if_pos hCondition]
  have hOldSourceObserved :
      grantDrainLedgerObservedMark ring s (some e) =
        .terminal :=
    hCoalescedObserved.symm.trans hCoalesced
  have hOldSourceRequest : s.request e = true := by
    cases hr : s.request e with
    | true => rfl
    | false =>
        have hImpossible :=
          grantDrainStrongTerminalUnrequestedFollowerObservation
            ring s e hr hOldSourceFollower
        exact False.elim (hImpossible hOldSourceObserved)
  have hRowRequest :
      (grantDrainLedgerRow ring fresh s e).1.req = true := by
    unfold grantDrainLedgerRow
    rw [hOldSourceRequest, hCondition.2.2,
      hYRequest, hYGrant, hFinalX, hFinalY, hFire]
    exact grantDrainTerminalCoalescedHeldSourceRow (fresh s e)
  have hPostSourceRequest :
      (grantDrainStep ring fresh update s e).request e =
        true := by
    change
      (if e = e then (grantDrainLedgerRow ring fresh s e).1.req
       else if e = ring.rightNeighbor e then
         (grantDrainLedgerRow ring fresh s e).2.req
       else s.request e) = true
    simp [hRowRequest]
  exact (congrArg
    (fun z : Fin n =>
      (grantDrainStep ring fresh update s e).request z)
    hj).trans hPostSourceRequest

/-- Every survivor of an OLD follower-hosted identity is physically
a follower. At either endpoint the literal grant row excludes a
final leader. Away from the pair, source native bits are framed.
This does not require its persistent mark to stay strong. -/
theorem grantDrainStrongTerminalSurvivorFollower
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hOldHost : label.host = some g)
    (hOldGrant : s.grant g = true)
    (hOldFollower : (s.native g).l = false)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j) :
    ((grantDrainStep ring fresh update s e).native j).l =
      false := by
  have hNewGrant :=
    grantDrainWeakSurvivingHostGrant
      ring hn fresh update s e label g j
      hOldHost hOldGrant hNewHost
  have hRawHost :
      grantDrainLedgerHost ring fresh s e (some g) = some j := by
    have hh := hNewHost
    change grantDrainLedgerHost ring fresh s e label.host =
      some j at hh
    rw [hOldHost] at hh
    exact hh
  by_cases hX : j = e
  · have hRowGrant :
        (grantDrainLedgerRow ring fresh s e).1.grant =
          true := by
      have hh := hNewGrant
      rw [hX] at hh
      rw [grantDrainWeakStepGrantAtSource
        ring fresh update s e] at hh
      exact hh
    have hLiteralGrant :
        (grantDrainTokenRow
          (s.request e) (s.grant e)
          (s.request (ring.rightNeighbor e))
          (s.grant (ring.rightNeighbor e))
          (grantDrainNativeNext ring s e e).l
          (grantDrainNativeNext ring s e
            (ring.rightNeighbor e)).l
          (fresh s e) (grantDrainSelect ring s e)).1.grant =
            true := by
      simpa only [grantDrainLedgerRow] using hRowGrant
    rw [hX]
    change (grantDrainNativeNext ring s e e).l = false
    exact grantDrainTerminalSourceGrantForcesFollower
      (s.request e) (s.grant e)
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l
      (fresh s e) (grantDrainSelect ring s e) hLiteralGrant
  · by_cases hY : j = ring.rightNeighbor e
    · have hDifferent : ring.rightNeighbor e ≠ e :=
        grantDrainMarksNeighborDistinct
          (by omega : 3 ≤ n) ring e
      have hRowGrant :
          (grantDrainLedgerRow ring fresh s e).2.grant =
            true := by
        have hh := hNewGrant
        rw [hY] at hh
        rw [grantDrainWeakStepGrantAtResponder
          ring fresh update s e hDifferent] at hh
        exact hh
      have hLiteralGrant :
          (grantDrainTokenRow
            (s.request e) (s.grant e)
            (s.request (ring.rightNeighbor e))
            (s.grant (ring.rightNeighbor e))
            (grantDrainNativeNext ring s e e).l
            (grantDrainNativeNext ring s e
              (ring.rightNeighbor e)).l
            (fresh s e) (grantDrainSelect ring s e)).2.grant =
              true := by
        simpa only [grantDrainLedgerRow] using hRowGrant
      rw [hY]
      change
        (grantDrainNativeNext ring s e
          (ring.rightNeighbor e)).l = false
      exact grantDrainTerminalResponderGrantForcesFollower
        (s.request e) (s.grant e)
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring s e e).l
        (grantDrainNativeNext ring s e
          (ring.rightNeighbor e)).l
        (fresh s e) (grantDrainSelect ring s e) hLiteralGrant
    · have hRange :=
        grantDrainTerminalSuccessorHostRange
          ring hn fresh s e g j hRawHost
      have hJG : j = g := by
        cases hRange with
        | inl hh => exact hh
        | inr hh => exact False.elim (hX hh)
      have hNotSource : g ≠ e := by
        intro hh
        exact hX (hJG.trans hh)
      have hNotResponder : g ≠ ring.rightNeighbor e := by
        intro hh
        exact hY (hJG.trans hh)
      rw [hJG]
      change (grantDrainNativeNext ring s e g).l = false
      rw [grantDrainMarksNativeOutsidePairFrame
        ring s e g hNotSource hNotResponder]
      exact hOldFollower

/-- The complete post-host classification for a live old-strong
identity whose persistent mark rises to terminal: its successor
must be requested (and, by physical ancestry, grant-bearing).
The native-leader alternative is ruled out by literal token sinks;
a pure coalescence promotion is an old held-X/Y-to-X move. -/
theorem grantDrainStrongTerminalSurvivorRequested
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hOldStrong : label.mark = .strong)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hNewTerminal :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .terminal) :
    (grantDrainStep ring fresh update s e).request j = true := by
  obtain ⟨hOldGrant, hOldCase⟩ := hInv g hOldHost
  rw [hOldStrong] at hOldCase
  obtain ⟨hOldRequest, hOldFollower, hOldLock, _⟩ :=
    hOldCase
  have hOldObserved :=
    grantDrainTerminalFollowerOldObservation
      ring s label g hOldHost hOldRequest hOldFollower hOldLock
  have hNewFollower :=
    grantDrainStrongTerminalSurvivorFollower
      ring hn fresh update s e label g j
      hOldHost hOldGrant hOldFollower hNewHost
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host = some j :=
    hNewHost
  cases hRequest :
      (grantDrainStep ring fresh update s e).request j with
  | true => rfl
  | false =>
      have hPostObservedNotTerminal :
          grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e) (some j) ≠
              .terminal :=
        grantDrainStrongTerminalUnrequestedFollowerObservation
          ring (grantDrainStep ring fresh update s e) j
          hRequest hNewFollower
      have hJoin :
          grantDrainMarkJoin .strong
            (grantDrainMarkJoin .strong
              (grantDrainMarkJoin
                (grantDrainLedgerCoalesceMark ring s e
                  label.host (some j))
                (grantDrainLedgerObservedMark ring
                  (grantDrainStep ring fresh update s e)
                  (some j)))) = .terminal := by
        have hh :
            grantDrainLedgerMarkNext ring fresh update s e label =
              .terminal := hNewTerminal
        unfold grantDrainLedgerMarkNext at hh
        rw [hOldStrong, hOldObserved, hRawHost] at hh
        exact hh
      have hCoalescedAtJ :
          grantDrainLedgerCoalesceMark ring s e
            label.host (some j) = .terminal :=
        grantDrainStrongTerminalJoinRequiresCoalescence
          (grantDrainLedgerCoalesceMark ring s e
            label.host (some j))
          (grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e) (some j))
          hPostObservedNotTerminal hJoin
      have hCoalesced :
          grantDrainLedgerCoalesceMark ring s e label.host
            (grantDrainLedgerHost ring fresh s e label.host) =
              .terminal := by
        rw [hRawHost]
        exact hCoalescedAtJ
      have hPostRequest :=
        grantDrainStrongTerminalCoalescencePostHeld
          ring hn fresh update s e label g j
          hOldHost hOldRequest hOldGrant hNewHost hCoalesced
      rw [hRequest] at hPostRequest
      cases hPostRequest

/-- The unconditional old-strong/new-terminal LockBudget cell
on the literal source and ledger steps. Every surviving target
is post-held, the strong survivor quota is positive after its
nominated debit, and the next outgoing nomination retires it. -/
theorem grantDrainLockBudgetStrongToTerminalHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hOldStrong : label.mark = .strong)
    (hNewTerminal :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .terminal) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  cases hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host with
  | none =>
      intro j hj
      rw [hNewHost] at hj
      cases hj
  | some j =>
      have hNewGrant :=
        grantDrainLockBudgetSuccessorGrant
          ring hn fresh update s e label hInv j hNewHost
      have hNewRequest :=
        grantDrainStrongTerminalSurvivorRequested
          ring hn fresh update s e label g j
          hInv hOldHost hOldStrong hNewHost hNewTerminal
      have hRawHost :
          grantDrainLedgerHost ring fresh s e label.host =
            some j := hNewHost
      have hRawMark :
          grantDrainLedgerMarkNext ring fresh update s e label =
            .terminal := hNewTerminal
      have hNewHeld :
          grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e) (some j) =
              true := by
        simp [grantDrainLedgerHeld, hNewRequest, hNewGrant]
      have hOldQuotaPositive :
          0 < label.remaining -
            (if grantDrainLedgerNominatedHit ring s e label.host
             then 1 else 0) :=
        grantDrainStrongTerminalSurvivorHitQuotaPositive
          ring hn fresh update s e label g j
          hP hInv hOldHost hOldStrong hNewHost
      have hNextRemaining :
          (grantDrainLedgerStep ring fresh update s e label).remaining =
            min
              (label.remaining -
                (if grantDrainLedgerNominatedHit ring s e label.host
                 then 1 else 0))
              (min 1 n) := by
        change grantDrainLedgerRemainingNext n label
          (grantDrainLedgerHost ring fresh s e label.host)
          (grantDrainLedgerMarkNext ring fresh update s e label)
          (grantDrainLedgerNominatedHit ring s e label.host)
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerHost ring fresh s e label.host)) =
          min
            (label.remaining -
              (if grantDrainLedgerNominatedHit ring s e label.host
               then 1 else 0))
            (min 1 n)
        rw [hRawHost, hRawMark, hNewHeld]
        simp [grantDrainLedgerRemainingNext, hOldStrong,
          grantDrainLedgerQuotaCap]
      have hNextQuotaPositive :
          0 <
            (grantDrainLedgerStep ring fresh update s e label).remaining := by
        rw [hNextRemaining]
        have hCapOne : 1 ≤ min 1 n :=
          Nat.le_min.mpr ⟨Nat.le_refl 1, (by omega : 1 ≤ n)⟩
        have hMinimum :
            1 ≤ min
              (label.remaining -
                (if grantDrainLedgerNominatedHit ring s e label.host
                 then 1 else 0))
              (min 1 n) :=
          Nat.le_min.mpr
            ⟨Nat.succ_le_of_lt hOldQuotaPositive, hCapOne⟩
        omega
      intro k hk
      have hjk : j = k :=
        Option.some.inj (hNewHost.symm.trans hk)
      subst k
      refine ⟨hNewGrant, ?_⟩
      rw [hNewTerminal]
      simp only [hNewRequest, ↓reduceIte]
      exact ⟨hNextQuotaPositive,
        grantDrainLockBudgetHeldRetiresOnNomination
          ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label)
          j hNewHost hNewRequest hNewGrant⟩

end L3


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Source-level terminal FOLLOWER LockBudget closure.
No auxiliary transition:
the shadow label below has exactly the same host update and
nominated hit as the real label. It is used only to invoke the
already proved strong physical corridor geometry when the actual
persistent mark is terminal.
-/

private def grantDrainTerminalFollowerShadow {n : Nat}
    (label : GrantDrainLedgerLabel n) : GrantDrainLedgerLabel n :=
  { label with mark := .strong }

/-- Every actual grant at the selected source is on a final native
follower. A source leader is a terminal sink in the literal token row. -/
theorem grantDrainTerminalFollowerSourceGrantAtFollower
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hGrant :
      (grantDrainStep ring fresh update s e).grant e = true) :
    ((grantDrainStep ring fresh update s e).native e).l = false := by
  have hRow :
      (grantDrainLedgerRow ring fresh s e).1.grant = true := by
    rw [← grantDrainWeakStepGrantAtSource ring fresh update s e]
    exact hGrant
  have hLiteral :
      (grantDrainTokenRow
        (s.request e) (s.grant e)
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring s e e).l
        (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
        (fresh s e) (grantDrainSelect ring s e)).1.grant =
          true := by
    simpa only [grantDrainLedgerRow] using hRow
  change (grantDrainNativeNext ring s e e).l = false
  exact grantDrainTerminalSourceGrantForcesFollower
    (s.request e) (s.grant e)
    (s.request (ring.rightNeighbor e))
    (s.grant (ring.rightNeighbor e))
    (grantDrainNativeNext ring s e e).l
    (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
    (fresh s e) (grantDrainSelect ring s e) hLiteral

/-- A surviving old follower identity cannot be physically hosted
on a NEW native leader. This covers source, responder, and sites
outside the selected pair, with no assumption on its new mark. -/
theorem grantDrainTerminalFollowerSuccessorFollower
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hOldHost : label.host = some g)
    (hOldFollower : (s.native g).l = false)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hNewGrant :
      (grantDrainStep ring fresh update s e).grant j = true) :
    ((grantDrainStep ring fresh update s e).native j).l =
      false := by
  have hRaw :
      grantDrainLedgerHost ring fresh s e (some g) = some j := by
    have hh :
        grantDrainLedgerHost ring fresh s e label.host = some j :=
      hNewHost
    rw [hOldHost] at hh
    exact hh
  rcases grantDrainTerminalSuccessorHostRange
      ring hn fresh s e g j hRaw with hStay | hMove
  · subst j
    by_cases hAtSource : g = e
    · subst g
      exact grantDrainTerminalFollowerSourceGrantAtFollower
        ring fresh update s e hNewGrant
    · by_cases hAtResponder : g = ring.rightNeighbor e
      · subst g
        exact grantDrainTerminalLeaderResponderSurvivorHasDied
          ring hn fresh update s e
          (ring.rightNeighbor e) label hOldHost hNewHost
      · change (grantDrainNativeNext ring s e g).l = false
        rw [grantDrainMarksNativeOutsidePairFrame
          ring s e g hAtSource hAtResponder]
        exact hOldFollower
  · subst j
    exact grantDrainTerminalFollowerSourceGrantAtFollower
      ring fresh update s e hNewGrant

/-- A nominated incoming edge with a SURVIVING unrequested locked
follower has an old protected distance of at least two. Distance
one would make the selected source the preceding leader, which
cannot itself be a surviving grant's new follower host. -/
theorem grantDrainTerminalFollowerNominatedDistanceTwo
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hP : PPlus ring s.native)
    (hOldHost : label.host = some g)
    (hOldRequest : s.request g = false)
    (hOldGrant : s.grant g = true)
    (hOldFollower : (s.native g).l = false)
    (hOldLock : grantDrainLedgerStrongLock ring s g = true)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hHit :
      grantDrainLedgerNominatedHit ring s e label.host = true) :
    2 ≤ grantDrainStrongProtectedDistance ring s (some g) := by
  have hHitAtG :
      grantDrainLedgerNominatedHit ring s e (some g) = true := by
    rw [← hOldHost]
    exact hHit
  have hEdge : ring.rightNeighbor e = g := by
    simpa [grantDrainLedgerNominatedHit, hOldRequest]
      using hHitAtG
  have hYHost :
      label.host = some (ring.rightNeighbor e) := by
    rw [hEdge]
    exact hOldHost
  have hYRequest :
      s.request (ring.rightNeighbor e) = false := by
    rw [hEdge]
    exact hOldRequest
  have hYGrant :
      s.grant (ring.rightNeighbor e) = true := by
    rw [hEdge]
    exact hOldGrant
  have hLive :
      (grantDrainLedgerStep ring fresh update s e label).host ≠
        none := by
    rw [hNewHost]
    simp
  have hMoving :=
    grantDrainMarksIncomingFollowerSurvivorMoves
      (by omega : 3 ≤ n) ring fresh update s e label
      hYHost hYRequest hYGrant hLive
  have hOldSourceFollower : (s.native e).l = false := by
    have hNative :
        (nativeE ring s.native e e).l = false := by
      simpa [grantDrainNativeNext, hMoving.1] using hMoving.2.1
    rw [grantDrainMarksNativeESource,
      grantDrainMarksOutgoingSourceLeaderNative] at hNative
    exact hNative
  obtain ⟨p, hNearest, _, _⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring s g hP hOldFollower hOldLock
  have hAtLeastTwo :=
    (grantDrainMarksIncomingFollowerPrefixFrame
      (by omega : 3 ≤ n) ring s p g e
      (PPL.cyclicOffset ring p g) rfl hEdge hNearest
      hOldSourceFollower).1
  rw [grantDrainMarksProtectedDistanceOfArc ring s p g hNearest]
  exact hAtLeastTwo

/-- An unrequested physical follower is never observed as terminal.
The two nonterminal locks may hold or fail independently. -/
theorem grantDrainTerminalFollowerObservationBelowTerminal
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (j : Fin n)
    (hRequest : s.request j = false)
    (hFollower : (s.native j).l = false) :
    grantDrainLedgerObservedMark ring s (some j) ≠ .terminal := by
  cases hs : grantDrainLedgerStrongLock ring s j with
  | true =>
      simp [grantDrainLedgerObservedMark,
        hRequest, hFollower, hs]
  | false =>
      cases hw : grantDrainLedgerWeakLock ring s j with
      | true =>
          simp [grantDrainLedgerObservedMark,
            hRequest, hFollower, hs, hw]
      | false =>
          simp [grantDrainLedgerObservedMark,
            hRequest, hFollower, hs, hw]

/-- A coalescence into the old source cannot contribute a TERMINAL
old-source observation if the actual new host is unrequested.
An old native leader cannot be a moving Y-source target. An OLD
held X grant, on the only possible non-FIRE Y-to-X transport row,
retains its request at X. Both exclusions use literal physical rows. -/
theorem grantDrainTerminalFollowerCoalesceBelowTerminal
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hOldHost : label.host = some g)
    (hOldRequest : s.request g = false)
    (hOldGrant : s.grant g = true)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hNewRequest :
      (grantDrainStep ring fresh update s e).request j = false) :
    grantDrainLedgerCoalesceMark ring s e label.host
      (grantDrainLedgerHost ring fresh s e label.host) ≠
        .terminal := by
  by_cases hc :
      label.host = some (ring.rightNeighbor e) ∧
      grantDrainLedgerHost ring fresh s e label.host = some e ∧
      s.grant e = true
  · have hOldSite : g = ring.rightNeighbor e :=
      Option.some.inj (hOldHost.symm.trans hc.1)
    have hYRequest :
        s.request (ring.rightNeighbor e) = false := by
      rw [← hOldSite]
      exact hOldRequest
    have hYGrant :
        s.grant (ring.rightNeighbor e) = true := by
      rw [← hOldSite]
      exact hOldGrant
    have hRawHost :
        grantDrainLedgerHost ring fresh s e label.host = some j :=
      hNewHost
    have hj : j = e :=
      Option.some.inj (hRawHost.symm.trans hc.2.1)
    subst j
    have hLive :
        (grantDrainLedgerStep ring fresh update s e label).host ≠
          none := by
      rw [hNewHost]
      simp
    have hMoving :=
      grantDrainMarksIncomingFollowerSurvivorMoves
        (by omega : 3 ≤ n) ring fresh update s e label
        hc.1 hYRequest hYGrant hLive
    have hOldSourceFollower : (s.native e).l = false := by
      have hNative :
          (nativeE ring s.native e e).l = false := by
        simpa [grantDrainNativeNext, hMoving.1] using hMoving.2.1
      rw [grantDrainMarksNativeESource,
        grantDrainMarksOutgoingSourceLeaderNative] at hNative
      exact hNative
    have hOldSourceRequest : s.request e = false := by
      cases hr : s.request e with
      | false => rfl
      | true =>
          have hRowReq :
              (grantDrainLedgerRow ring fresh s e).1.req = true := by
            unfold grantDrainLedgerRow
            rw [hr, hc.2.2, hYRequest, hYGrant,
              hMoving.2.1, hMoving.2.2.1, hMoving.1]
            exact grantDrainTerminalCoalescedHeldSourceRow (fresh s e)
          have hPostRequest :
              (grantDrainStep ring fresh update s e).request e =
                true := by
            change (if e = e then
              (grantDrainLedgerRow ring fresh s e).1.req
            else if e = ring.rightNeighbor e then
              (grantDrainLedgerRow ring fresh s e).2.req
            else s.request e) = true
            simp [hRowReq]
          rw [hPostRequest] at hNewRequest
          cases hNewRequest
    have hOldObserved :=
      grantDrainTerminalFollowerObservationBelowTerminal
        ring s e hOldSourceRequest hOldSourceFollower
    change
      (if label.host = some (ring.rightNeighbor e) ∧
          grantDrainLedgerHost ring fresh s e label.host = some e ∧
          s.grant e = true then
        grantDrainLedgerObservedMark ring s (some e)
       else .unmarked) ≠ .terminal
    rw [if_pos hc]
    exact hOldObserved
  · simp [grantDrainLedgerCoalesceMark, hc]

/-- The shadow LABEL remains strong whenever the real terminal
identity survives at an unrequested follower. The original strong
physical corridor is reused without changing the source state.
The only possible competing terminal coalescence is excluded by
the literal source-row lemma immediately above. -/
theorem grantDrainTerminalFollowerShadowStrongNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hOldHost : label.host = some g)
    (hOldRequest : s.request g = false)
    (hOldGrant : s.grant g = true)
    (hOldFollower : (s.native g).l = false)
    (hOldLock : grantDrainLedgerStrongLock ring s g = true)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hNewRequest :
      (grantDrainStep ring fresh update s e).request j = false)
    (hNewFollower :
      ((grantDrainStep ring fresh update s e).native j).l =
        false) :
    (grantDrainLedgerStep ring fresh update s e
      (grantDrainTerminalFollowerShadow label)).mark =
        .strong := by
  have hOldObserved :
      grantDrainLedgerObservedMark ring s label.host =
        .strong := by
    rw [hOldHost]
    simp [grantDrainLedgerObservedMark,
      hOldRequest, hOldFollower, hOldLock]
  have hNoCoalesceTerminal :=
    grantDrainTerminalFollowerCoalesceBelowTerminal
      ring hn fresh update s e label g j
      hOldHost hOldRequest hOldGrant hNewHost hNewRequest
  have hNoPostTerminal :=
    grantDrainTerminalFollowerObservationBelowTerminal
      ring (grantDrainStep ring fresh update s e) j
      hNewRequest hNewFollower
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host = some j :=
    hNewHost
  change grantDrainMarkJoin .strong
      (grantDrainMarkJoin
        (grantDrainLedgerObservedMark ring s label.host)
        (grantDrainMarkJoin
          (grantDrainLedgerCoalesceMark ring s e label.host
            (grantDrainLedgerHost ring fresh s e label.host))
          (grantDrainLedgerObservedMark ring
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerHost ring fresh s e label.host)))) =
      .strong
  rw [hOldObserved, hRawHost]
  rw [hRawHost] at hNoCoalesceTerminal
  exact grantDrainTerminalStrongJoinBelow _ _
    hNoCoalesceTerminal hNoPostTerminal

/-- Source-derived strong physical lock and exact nominated-hit
distance drift for a terminal-marked unrequested follower that
survives at another unrequested follower. This specializes the
strong corridor geometry to a shadow mark, while retaining
the actual host and nominated-hit definition. -/
theorem grantDrainTerminalFollowerUnheldStrongProgress
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g j : Fin n)
    (hP : PPlus ring s.native)
    (hOldHost : label.host = some g)
    (hOldRequest : s.request g = false)
    (hOldGrant : s.grant g = true)
    (hOldFollower : (s.native g).l = false)
    (hOldLock : grantDrainLedgerStrongLock ring s g = true)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hNewRequest :
      (grantDrainStep ring fresh update s e).request j = false)
    (hNewFollower :
      ((grantDrainStep ring fresh update s e).native j).l =
        false) :
    grantDrainLedgerStrongLock ring
      (grantDrainStep ring fresh update s e) j = true ∧
    (if grantDrainLedgerNominatedHit ring s e label.host then
      grantDrainStrongProtectedDistance ring
        (grantDrainStep ring fresh update s e) (some j) + 1 ≤
        grantDrainStrongProtectedDistance ring s (some g)
     else
      grantDrainStrongProtectedDistance ring
        (grantDrainStep ring fresh update s e) (some j) ≤
        grantDrainStrongProtectedDistance ring s (some g)) := by
  have hOldPhysical :
      GrantDrainStrongPhysical ring s
        (grantDrainTerminalFollowerShadow label) := by
    refine ⟨g, ?_, rfl, hOldGrant, hOldRequest,
      hOldFollower, hOldLock⟩
    simpa [grantDrainTerminalFollowerShadow] using hOldHost
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host = some j :=
    hNewHost
  have hShadowHost :
      (grantDrainLedgerStep ring fresh update s e
        (grantDrainTerminalFollowerShadow label)).host =
          some j := by
    change grantDrainLedgerHost ring fresh s e label.host = some j
    exact hRawHost
  have hShadowLive :
      (grantDrainLedgerStep ring fresh update s e
        (grantDrainTerminalFollowerShadow label)).host ≠
          none := by
    rw [hShadowHost]
    simp
  have hShadowMark :=
    grantDrainTerminalFollowerShadowStrongNext
      ring hn fresh update s e label g j
      hOldHost hOldRequest hOldGrant hOldFollower hOldLock
      hNewHost hNewRequest hNewFollower
  have hGeometry :
      GrantDrainStrongCorridorGeometry ring fresh update :=
    grantDrainStrongCorridorGeometry_of_arc_coverage
      ring fresh update
      (grantDrainMarksStrongArcCoverageOfThree
        (by omega : 3 ≤ n) ring fresh update)
      (grantDrainMarksStrongPhysicalClosureOfThree
        (by omega : 3 ≤ n) ring fresh update)
  have hResult :=
    hGeometry s e (grantDrainTerminalFollowerShadow label)
      hP hOldPhysical hShadowLive hShadowMark
  have hProgress :
      if grantDrainLedgerNominatedHit ring s e label.host then
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e) (some j) + 1 ≤
        grantDrainStrongProtectedDistance ring s (some g)
      else
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e) (some j) ≤
        grantDrainStrongProtectedDistance ring s (some g) := by
    have hRaw := hResult.2
    change
      (if grantDrainLedgerNominatedHit ring s e label.host then
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerHost ring fresh s e label.host) + 1 ≤
        grantDrainStrongProtectedDistance ring s label.host
       else
        grantDrainStrongProtectedDistance ring
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerHost ring fresh s e label.host) ≤
        grantDrainStrongProtectedDistance ring s label.host)
      at hRaw
    rw [hRawHost, hOldHost] at hRaw
    rw [hOldHost]
    exact hRaw
  obtain ⟨k, hkHost, _, _, _, _, hkLock⟩ := hResult.1
  have hk : k = j :=
    Option.some.inj (hkHost.symm.trans hShadowHost)
  subst k
  exact ⟨hkLock, hProgress⟩

/-- Full old TERMINAL, unrequested FOLLOWER row of the literal
grantDrainStep/grantDrainLedgerStep. In the HELD branch the old
nominated hit can spend one only when the old protected distance
is at least two. In the unheld branch the shadow strong geometry
pays the same hit and gives the real post lock. The terminal mark
itself remains persistent throughout. -/
theorem grantDrainLockBudgetTerminalFollowerHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hTerminal : label.mark = .terminal)
    (hOldRequest : s.request g = false)
    (hOldFollower : (s.native g).l = false) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  obtain ⟨hOldGrant, hOldCase⟩ := hInv g hOldHost
  rw [hTerminal] at hOldCase
  have hOldStrong :
      grantDrainLedgerStrongLock ring s g = true ∧
      grantDrainStrongProtectedDistance ring s (some g) ≤
        label.remaining := by
    simpa only [hOldRequest, Bool.false_eq_true, ↓reduceIte,
      hOldFollower] using hOldCase
  have hOldLock := hOldStrong.1
  have hOldBudget := hOldStrong.2
  have hMarkNext :=
    grantDrainDeathTerminalMarkPersists
      ring fresh update s e label hTerminal
  have hRawMark :
      grantDrainLedgerMarkNext ring fresh update s e label =
        .terminal := hMarkNext
  intro j hj
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host = some j := hj
  have hNewGrant :=
    grantDrainLockBudgetSuccessorGrant
      ring hn fresh update s e label hInv j hj
  have hNewFollower :=
    grantDrainTerminalFollowerSuccessorFollower
      ring hn fresh update s e label g j
      hOldHost hOldFollower hj hNewGrant
  refine ⟨hNewGrant, ?_⟩
  rw [hMarkNext]
  cases hReq : (grantDrainStep ring fresh update s e).request j with
  | true =>
      have hSpentPositive :
          0 < label.remaining -
            (if grantDrainLedgerNominatedHit ring s e label.host
               then 1 else 0) := by
        have hOldPositive :=
          grantDrainStrongProtectedDistance_some_pos ring s g
        cases hh :
            grantDrainLedgerNominatedHit ring s e label.host with
        | false =>
            simp only [hh, Bool.false_eq_true, ↓reduceIte,
              Nat.sub_zero]
            omega
        | true =>
            have hTwo :=
              grantDrainTerminalFollowerNominatedDistanceTwo
                ring hn fresh update s e label g j
                hP hOldHost hOldRequest hOldGrant
                hOldFollower hOldLock hj hh
            simp only [hh, ↓reduceIte]
            omega
      have hPostHeld :
          grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e) (some j) =
              true := by
        simp [grantDrainLedgerHeld, hReq, hNewGrant]
      have hRemaining :
          (grantDrainLedgerStep ring fresh update s e label).remaining =
            min
              (label.remaining -
                (if grantDrainLedgerNominatedHit ring s e label.host
                   then 1 else 0))
              (min 1 n) := by
        change grantDrainLedgerRemainingNext n label
          (grantDrainLedgerHost ring fresh s e label.host)
          (grantDrainLedgerMarkNext ring fresh update s e label)
          (grantDrainLedgerNominatedHit ring s e label.host)
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerHost ring fresh s e label.host)) = _
        rw [hRawHost, hRawMark, hPostHeld]
        simp [grantDrainLedgerRemainingNext,
          hTerminal, grantDrainLedgerQuotaCap]
      have hOne : min 1 n = 1 :=
        Nat.min_eq_left (by omega : 1 ≤ n)
      have hOnePaid :
          1 ≤ label.remaining -
            (if grantDrainLedgerNominatedHit ring s e label.host
               then 1 else 0) := by omega
      have hRemainPositive :
          0 <
            (grantDrainLedgerStep ring fresh update s e label).remaining := by
        rw [hRemaining, hOne,
          Nat.min_eq_right hOnePaid]
        omega
      simp only [hReq, ↓reduceIte]
      exact ⟨hRemainPositive,
        grantDrainLockBudgetHeldRetiresOnNomination
          ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label)
          j hj hReq hNewGrant⟩
  | false =>
      have hPostHeld :
          grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e) (some j) =
              false := by
        simp [grantDrainLedgerHeld, hReq]
      have hRemaining :
          (grantDrainLedgerStep ring fresh update s e label).remaining =
            min
              (label.remaining -
                (if grantDrainLedgerNominatedHit ring s e label.host
                   then 1 else 0)) n := by
        change grantDrainLedgerRemainingNext n label
          (grantDrainLedgerHost ring fresh s e label.host)
          (grantDrainLedgerMarkNext ring fresh update s e label)
          (grantDrainLedgerNominatedHit ring s e label.host)
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerHost ring fresh s e label.host)) = _
        rw [hRawHost, hRawMark, hPostHeld]
        simp [grantDrainLedgerRemainingNext,
          hTerminal, grantDrainLedgerQuotaCap]
      obtain ⟨hNewLock, hProgress⟩ :=
        grantDrainTerminalFollowerUnheldStrongProgress
          ring hn fresh update s e label g j
          hP hOldHost hOldRequest hOldGrant
          hOldFollower hOldLock hj hReq hNewFollower
      have hNewBudget :
          grantDrainStrongProtectedDistance ring
            (grantDrainStep ring fresh update s e) (some j) ≤
            (grantDrainLedgerStep ring fresh update s e label).remaining := by
        rw [hRemaining]
        exact grantDrainStrongBudgetAlgebra
          n (grantDrainStrongProtectedDistance ring s (some g))
          (grantDrainStrongProtectedDistance ring
            (grantDrainStep ring fresh update s e) (some j))
          label.remaining
          (grantDrainLedgerNominatedHit ring s e label.host)
          hOldBudget
          (grantDrainStrongProtectedDistance_le_n
            ring (grantDrainStep ring fresh update s e) (some j))
          hProgress
      simp only [hReq, Bool.false_eq_true, ↓reduceIte,
        hNewFollower]
      exact ⟨hNewLock, hNewBudget⟩

end L3


namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Source-level LockBudget case assembly.
The shadow seeds below are proof-only copies, not physical updates.
-/

private theorem grantDrainUnmarkedOldJoinAbsorb
    (a b c : GrantDrainMark) :
    grantDrainMarkJoin .unmarked
      (grantDrainMarkJoin a (grantDrainMarkJoin b c)) =
    grantDrainMarkJoin a
      (grantDrainMarkJoin a (grantDrainMarkJoin b c)) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem grantDrainUnmarkedCoalesceJoinSwap
    (a c : GrantDrainMark) :
    grantDrainMarkJoin .unmarked
      (grantDrainMarkJoin .unmarked (grantDrainMarkJoin a c)) =
    grantDrainMarkJoin a
      (grantDrainMarkJoin a (grantDrainMarkJoin .unmarked c)) := by
  cases a <;> cases c <;> rfl

private theorem grantDrainFourMarkJoinBelowTerminal
    (a b c d : GrantDrainMark)
    (ha : a ≠ .terminal) (hb : b ≠ .terminal)
    (hc : c ≠ .terminal) (hd : d ≠ .terminal) :
    grantDrainMarkJoin a
      (grantDrainMarkJoin b (grantDrainMarkJoin c d)) ≠
        .terminal := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [grantDrainMarkJoin, grantDrainMarkRank] at *

/-- A bigger remaining counter preserves every LockBudget case.
The terminal-held future-retirement clause uses ONLY the common host,
not the identity, mark history or the remaining counter. -/
theorem grantDrainLockBudgetRaiseQuota
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (small large : GrantDrainLedgerLabel n)
    (hHost : small.host = large.host)
    (hMark : small.mark = large.mark)
    (hQuota : small.remaining ≤ large.remaining)
    (hBudget : LockBudget ring fresh update s small) :
    LockBudget ring fresh update s large := by
  intro j hj
  have hs : small.host = some j := hHost.trans hj
  obtain ⟨hGrant, hCase⟩ := hBudget j hs
  refine ⟨hGrant, ?_⟩
  rw [← hMark]
  cases hm : small.mark with
  | unmarked =>
      trivial
  | weak =>
      rw [hm] at hCase
      obtain ⟨hRequest, hFollower, hLock, hDistance⟩ := hCase
      exact ⟨hRequest, hFollower, hLock, by omega⟩
  | strong =>
      rw [hm] at hCase
      obtain ⟨hRequest, hFollower, hLock, hDistance⟩ := hCase
      exact ⟨hRequest, hFollower, hLock, by omega⟩
  | terminal =>
      rw [hm] at hCase
      cases hr : s.request j with
      | true =>
          simp only [hr, ↓reduceIte] at hCase ⊢
          obtain ⟨hPositive, hRetire⟩ := hCase
          constructor
          · omega
          · intro edge hHit
            have hHitSmall :
                grantDrainLedgerNominatedHit ring s edge
                  small.host = true := by
              rw [hHost]
              exact hHit
            have hGone := hRetire edge hHitSmall
            change grantDrainLedgerHost ring fresh s edge
              small.host = none at hGone
            change grantDrainLedgerHost ring fresh s edge
              large.host = none
            rw [← hHost]
            exact hGone
      | false =>
          cases hl : (s.native j).l with
          | true =>
              simp only [hr, Bool.false_eq_true, ↓reduceIte,
                hl] at hCase ⊢
              omega
          | false =>
              simp only [hr, Bool.false_eq_true, ↓reduceIte,
                hl] at hCase ⊢
              obtain ⟨hLock, hDistance⟩ := hCase
              exact ⟨hLock, by omega⟩

/-- At a fixed surviving host, the source-unmarked next counter is
its exact cap. Any other label with the SAME new host/mark has quota
at most that cap, independently of its old marked quota. -/
theorem grantDrainUnmarkedShadowTransfer
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (real shadow : GrantDrainLedgerLabel n) (j : Fin n)
    (hUnmarked : real.mark = .unmarked)
    (hRealHost :
      (grantDrainLedgerStep ring fresh update s e real).host =
        some j)
    (hShadowHost :
      (grantDrainLedgerStep ring fresh update s e shadow).host =
        some j)
    (hNextMark :
      (grantDrainLedgerStep ring fresh update s e shadow).mark =
      (grantDrainLedgerStep ring fresh update s e real).mark)
    (hShadowBudget :
      LockBudget ring fresh update
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e shadow)) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e real) := by
  have hShadowRaw :
      grantDrainLedgerHost ring fresh s e shadow.host = some j :=
    hShadowHost
  have hShadowCap :
      (grantDrainLedgerStep ring fresh update s e shadow).remaining ≤
        grantDrainLedgerQuotaCap n
          (grantDrainLedgerStep ring fresh update s e shadow).mark
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e) (some j)) := by
    have hBound := grantDrainLedgerRemainingNext_le_cap
      n shadow
      (grantDrainLedgerHost ring fresh s e shadow.host)
      (grantDrainLedgerMarkNext ring fresh update s e shadow)
      (grantDrainLedgerNominatedHit ring s e shadow.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e shadow.host))
    change
      (grantDrainLedgerStep ring fresh update s e shadow).remaining ≤
        grantDrainLedgerQuotaCap n
          (grantDrainLedgerStep ring fresh update s e shadow).mark
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerHost ring fresh s e shadow.host))
      at hBound
    rw [hShadowRaw] at hBound
    exact hBound
  have hRealCap :=
    grantDrainUnmarkedSuccessorRemainingIsCap
      ring fresh update s e real j hUnmarked hRealHost
  have hQuota :
      (grantDrainLedgerStep ring fresh update s e shadow).remaining ≤
      (grantDrainLedgerStep ring fresh update s e real).remaining := by
    rw [hRealCap, ← hNextMark]
    exact hShadowCap
  exact grantDrainLockBudgetRaiseQuota
    ring fresh update (grantDrainStep ring fresh update s e)
    (grantDrainLedgerStep ring fresh update s e shadow)
    (grantDrainLedgerStep ring fresh update s e real)
    (hShadowHost.trans hRealHost.symm)
    hNextMark hQuota hShadowBudget

/-- Seed a physical grant with its ACTUAL old observed mark and cap.
If that mark is already non-unmarked, the available row theorems
preserve LockBudget at any surviving, unrequested follower host.
For weak/strong seeds, a terminal coalescence is excluded explicitly
by a separate literal-row hypothesis; all other geometry is derived
from the weak/strong/terminal step theorems. -/
theorem grantDrainObservedSeedUnheldStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g j : Fin n)
    (shadow : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s shadow)
    (hHost : shadow.host = some g)
    (hOldObserved :
      shadow.mark = grantDrainLedgerObservedMark ring s shadow.host)
    (hMarked : shadow.mark ≠ .unmarked)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e shadow).host =
        some j)
    (hNewRequest :
      (grantDrainStep ring fresh update s e).request j = false)
    (hNewFollower :
      ((grantDrainStep ring fresh update s e).native j).l = false)
    (hCoalesce :
      shadow.mark ≠ .terminal →
      grantDrainLedgerCoalesceMark ring s e shadow.host
        (grantDrainLedgerHost ring fresh s e shadow.host) ≠
          .terminal) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e shadow) := by
  have hNewPostObserved :
      grantDrainLedgerObservedMark ring
        (grantDrainStep ring fresh update s e) (some j) ≠
          .terminal :=
    grantDrainTerminalFollowerObservationBelowTerminal
      ring (grantDrainStep ring fresh update s e)
      j hNewRequest hNewFollower
  have hRawHost :
      grantDrainLedgerHost ring fresh s e shadow.host = some j :=
    hNewHost
  cases hm : shadow.mark with
  | unmarked =>
      exact False.elim (hMarked hm)
  | weak =>
      have hNotTerminal : shadow.mark ≠ .terminal := by
        rw [hm]
        decide
      have hNewNotTerminal :
          (grantDrainLedgerStep ring fresh update s e shadow).mark ≠
            .terminal := by
        change grantDrainMarkJoin shadow.mark
          (grantDrainMarkJoin
            (grantDrainLedgerObservedMark ring s shadow.host)
            (grantDrainMarkJoin
              (grantDrainLedgerCoalesceMark ring s e shadow.host
                (grantDrainLedgerHost ring fresh s e shadow.host))
              (grantDrainLedgerObservedMark ring
                (grantDrainStep ring fresh update s e)
                (grantDrainLedgerHost ring fresh s e shadow.host)))) ≠
                  .terminal
        rw [← hOldObserved, hRawHost]
        exact grantDrainFourMarkJoinBelowTerminal _ _ _ _
          hNotTerminal hNotTerminal
          (by have h := hCoalesce hNotTerminal; rw [hRawHost] at h; exact h)
          hNewPostObserved
      cases hnmark :
          (grantDrainLedgerStep ring fresh update s e shadow).mark with
      | unmarked =>
          have hMono :=
            grantDrainLedgerStep_mark_monotone ring fresh update s e shadow
          rw [hm, hnmark] at hMono
          simp [grantDrainMarkRank] at hMono
      | weak =>
          exact grantDrainLockBudgetWeakStableNext
            ring hn fresh update s e shadow g
            hP hInv hHost hm hnmark
      | strong =>
          exact grantDrainLockBudgetWeakToStrongHolds
            ring hn fresh update s e shadow g
            hP hInv hHost hm hnmark
      | terminal =>
          exact False.elim (hNewNotTerminal hnmark)
  | strong =>
      have hNotTerminal : shadow.mark ≠ .terminal := by
        rw [hm]
        decide
      have hNewNotTerminal :
          (grantDrainLedgerStep ring fresh update s e shadow).mark ≠
            .terminal := by
        change grantDrainMarkJoin shadow.mark
          (grantDrainMarkJoin
            (grantDrainLedgerObservedMark ring s shadow.host)
            (grantDrainMarkJoin
              (grantDrainLedgerCoalesceMark ring s e shadow.host
                (grantDrainLedgerHost ring fresh s e shadow.host))
              (grantDrainLedgerObservedMark ring
                (grantDrainStep ring fresh update s e)
                (grantDrainLedgerHost ring fresh s e shadow.host)))) ≠
                  .terminal
        rw [← hOldObserved, hRawHost]
        exact grantDrainFourMarkJoinBelowTerminal _ _ _ _
          hNotTerminal hNotTerminal
          (by have h := hCoalesce hNotTerminal; rw [hRawHost] at h; exact h)
          hNewPostObserved
      cases hnmark :
          (grantDrainLedgerStep ring fresh update s e shadow).mark with
      | unmarked =>
          have hMono :=
            grantDrainLedgerStep_mark_monotone ring fresh update s e shadow
          rw [hm, hnmark] at hMono
          simp [grantDrainMarkRank] at hMono
      | weak =>
          have hMono :=
            grantDrainLedgerStep_mark_monotone ring fresh update s e shadow
          rw [hm, hnmark] at hMono
          simp [grantDrainMarkRank] at hMono
      | strong =>
          exact grantDrainLockBudgetStrongStableNext
            ring hn fresh update s e shadow g
            hP hInv hHost hm hnmark
      | terminal =>
          exact False.elim (hNewNotTerminal hnmark)
  | terminal =>
      have hOldTerm : shadow.mark = .terminal := hm
      have hCase := (hInv g hHost).2
      rw [hm] at hCase
      cases hr : s.request g with
      | true =>
          exact grantDrainLockBudgetTerminalHeldHolds
            ring hn fresh update s e shadow g
            hInv hHost hOldTerm hr
      | false =>
          cases hl : (s.native g).l with
          | true =>
              exact grantDrainLockBudgetTerminalLeaderHolds
                ring hn fresh update s e g shadow
                hP hInv hHost hOldTerm hr hl
          | false =>
              exact grantDrainLockBudgetTerminalFollowerHolds
                ring hn fresh update s e shadow g
                hP hInv hHost hOldTerm hr hl

/-- A marked old observation is itself a legitimate cap-seeded
physical identity. Its next mark and host are the SAME as those of
the originally unmarked identity. In an unrequested post follower,
the coalescence cannot secretly be terminal unless the old observed
identity was terminal already; the available marked rows
then give the shadow's entire LockBudget. -/
theorem grantDrainUnmarkedOldObservedOrigin
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g j : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hUnmarked : label.mark = .unmarked)
    (hOldObservedNotUnmarked :
      grantDrainLedgerObservedMark ring s label.host ≠
        .unmarked)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hNewRequest :
      (grantDrainStep ring fresh update s e).request j = false)
    (hNewFollower :
      ((grantDrainStep ring fresh update s e).native j).l =
        false) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  have hOldGrant := (hInv g hOldHost).1
  have hSeedHost :
      (grantDrainLedgerInitial ring s g).host = some g := by
    simp [grantDrainLedgerInitial, hOldGrant]
  have hSeedMark :
      (grantDrainLedgerInitial ring s g).mark =
        grantDrainLedgerObservedMark ring s (some g) := by
    simp [grantDrainLedgerInitial, hOldGrant]
  have hSeedObserved :
      (grantDrainLedgerInitial ring s g).mark =
        grantDrainLedgerObservedMark ring s
          (grantDrainLedgerInitial ring s g).host := by
    rw [hSeedHost]
    exact hSeedMark
  have hSeedMarked :
      (grantDrainLedgerInitial ring s g).mark ≠
        .unmarked := by
    rw [hSeedMark]
    rw [hOldHost] at hOldObservedNotUnmarked
    exact hOldObservedNotUnmarked
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host =
        some j := hNewHost
  have hShadowHost :
      (grantDrainLedgerStep ring fresh update s e
        (grantDrainLedgerInitial ring s g)).host = some j := by
    change grantDrainLedgerHost ring fresh s e
      (grantDrainLedgerInitial ring s g).host = some j
    rw [hSeedHost]
    have hRealRaw := hRawHost
    rw [hOldHost] at hRealRaw
    exact hRealRaw
  have hSameMark :
      (grantDrainLedgerStep ring fresh update s e
        (grantDrainLedgerInitial ring s g)).mark =
      (grantDrainLedgerStep ring fresh update s e label).mark := by
    change grantDrainLedgerMarkNext ring fresh update s e
      (grantDrainLedgerInitial ring s g) =
      grantDrainLedgerMarkNext ring fresh update s e label
    unfold grantDrainLedgerMarkNext
    rw [hSeedMark, hSeedHost, hOldHost, hUnmarked]
    simp only [grantDrainUnmarkedOldJoinAbsorb]
  have hSeedBudget :
      LockBudget ring fresh update s
        (grantDrainLedgerInitial ring s g) :=
    grantDrainLockBudgetInitial ring hn fresh update s g
  have hCoalesceNonterminal :
      (grantDrainLedgerInitial ring s g).mark ≠ .terminal →
      grantDrainLedgerCoalesceMark ring s e
        (grantDrainLedgerInitial ring s g).host
        (grantDrainLedgerHost ring fresh s e
          (grantDrainLedgerInitial ring s g).host) ≠
          .terminal := by
    intro hm
    have hOldRequest : s.request g = false := by
      cases hr : s.request g with
      | false => rfl
      | true =>
          have hTerminal :
              (grantDrainLedgerInitial ring s g).mark =
                .terminal := by
            rw [hSeedMark]
            simp [grantDrainLedgerObservedMark, hr, hOldGrant]
          exact False.elim (hm hTerminal)
    have hNot :=
      grantDrainTerminalFollowerCoalesceBelowTerminal
        ring hn fresh update s e label g j
        hOldHost hOldRequest hOldGrant hNewHost hNewRequest
    rw [hSeedHost, ← hOldHost]
    exact hNot
  have hShadowBudget :=
    grantDrainObservedSeedUnheldStep
      ring hn fresh update s e g j
      (grantDrainLedgerInitial ring s g)
      hP hSeedBudget hSeedHost hSeedObserved hSeedMarked
      hShadowHost hNewRequest hNewFollower hCoalesceNonterminal
  exact grantDrainUnmarkedShadowTransfer
    ring fresh update s e label
    (grantDrainLedgerInitial ring s g) j hUnmarked
    hNewHost hShadowHost hSameMark hShadowBudget

/-- A nontrivial coalescence with an initially unmarked Y identity
uses the OLD physical grant at X as a cap-seeded shadow. Unlike a
hypothetical coalescing ghost, the OLD X grant physically survives:
YSource really moved to X and the literal source row retains grant X.
The X shadow is never itself classified as a Y->X coalescence. -/
theorem grantDrainUnmarkedCoalesceOrigin
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g j : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hUnmarked : label.mark = .unmarked)
    (hOldObserved :
      grantDrainLedgerObservedMark ring s label.host =
        .unmarked)
    (hCoalesced :
      grantDrainLedgerCoalesceMark ring s e label.host
        (grantDrainLedgerHost ring fresh s e label.host) ≠
          .unmarked)
    (hNewHost :
      (grantDrainLedgerStep ring fresh update s e label).host =
        some j)
    (hNewRequest :
      (grantDrainStep ring fresh update s e).request j = false)
    (hNewFollower :
      ((grantDrainStep ring fresh update s e).native j).l =
        false) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  have hCondition :
      label.host = some (ring.rightNeighbor e) ∧
      grantDrainLedgerHost ring fresh s e label.host = some e ∧
      s.grant e = true := by
    by_cases hc :
        label.host = some (ring.rightNeighbor e) ∧
        grantDrainLedgerHost ring fresh s e label.host = some e ∧
        s.grant e = true
    · exact hc
    · have hUnmarkedCoalesce :
          grantDrainLedgerCoalesceMark ring s e label.host
            (grantDrainLedgerHost ring fresh s e label.host) =
              .unmarked := by
        simp [grantDrainLedgerCoalesceMark, hc]
      exact False.elim (hCoalesced hUnmarkedCoalesce)
  have hRawHost :
      grantDrainLedgerHost ring fresh s e label.host =
        some j := hNewHost
  have hJ : j = e :=
    Option.some.inj (hRawHost.symm.trans hCondition.2.1)
  subst j
  have hNewGrant :
      (grantDrainStep ring fresh update s e).grant e = true :=
    grantDrainLockBudgetSuccessorGrant
      ring hn fresh update s e label hInv e hNewHost
  have hRowGrant :
      (grantDrainLedgerRow ring fresh s e).1.grant = true := by
    rw [← grantDrainWeakStepGrantAtSource ring fresh update s e]
    exact hNewGrant
  have hSeedHost :
      (grantDrainLedgerInitial ring s e).host = some e := by
    simp [grantDrainLedgerInitial, hCondition.2.2]
  have hSeedMark :
      (grantDrainLedgerInitial ring s e).mark =
        grantDrainLedgerObservedMark ring s (some e) := by
    simp [grantDrainLedgerInitial, hCondition.2.2]
  have hSeedObserved :
      (grantDrainLedgerInitial ring s e).mark =
        grantDrainLedgerObservedMark ring s
          (grantDrainLedgerInitial ring s e).host := by
    rw [hSeedHost]
    exact hSeedMark
  have hSeedNontrivial :
      (grantDrainLedgerInitial ring s e).mark ≠
        .unmarked := by
    rw [hSeedMark]
    have hObs :
        grantDrainLedgerCoalesceMark ring s e label.host
          (grantDrainLedgerHost ring fresh s e label.host) =
          grantDrainLedgerObservedMark ring s (some e) := by
      unfold grantDrainLedgerCoalesceMark
      simp only [if_pos hCondition]
    rw [hObs] at hCoalesced
    exact hCoalesced
  have hShadowHost :
      (grantDrainLedgerStep ring fresh update s e
        (grantDrainLedgerInitial ring s e)).host = some e := by
    change grantDrainLedgerHost ring fresh s e
      (grantDrainLedgerInitial ring s e).host = some e
    rw [hSeedHost]
    simp [grantDrainLedgerHost, hCondition.2.2, hRowGrant]
  have hDifferent : e ≠ ring.rightNeighbor e :=
    Ne.symm (grantDrainMarksNeighborDistinct
      (by omega : 3 ≤ n) ring e)
  have hShadowCoalesce :
      grantDrainLedgerCoalesceMark ring s e
        (grantDrainLedgerInitial ring s e).host
        (grantDrainLedgerHost ring fresh s e
          (grantDrainLedgerInitial ring s e).host) =
          .unmarked := by
    rw [hSeedHost]
    simp [grantDrainLedgerCoalesceMark, hDifferent]
  have hRealCoalesce :
      grantDrainLedgerCoalesceMark ring s e label.host
        (grantDrainLedgerHost ring fresh s e label.host) =
          grantDrainLedgerObservedMark ring s (some e) := by
    unfold grantDrainLedgerCoalesceMark
    simp only [if_pos hCondition]
  have hSameMark :
      (grantDrainLedgerStep ring fresh update s e
        (grantDrainLedgerInitial ring s e)).mark =
      (grantDrainLedgerStep ring fresh update s e label).mark := by
    change grantDrainLedgerMarkNext ring fresh update s e
      (grantDrainLedgerInitial ring s e) =
      grantDrainLedgerMarkNext ring fresh update s e label
    unfold grantDrainLedgerMarkNext
    rw [hUnmarked, hOldObserved, hRealCoalesce,
      hShadowCoalesce, hSeedMark,
      (show grantDrainLedgerHost ring fresh s e
        (grantDrainLedgerInitial ring s e).host = some e from hShadowHost),
      hRawHost, hSeedHost]
    simp only [grantDrainUnmarkedCoalesceJoinSwap]
  have hSeedBudget :
      LockBudget ring fresh update s
        (grantDrainLedgerInitial ring s e) :=
    grantDrainLockBudgetInitial ring hn fresh update s e
  have hCoalesceNotTerminal :
      (grantDrainLedgerInitial ring s e).mark ≠ .terminal →
      grantDrainLedgerCoalesceMark ring s e
        (grantDrainLedgerInitial ring s e).host
        (grantDrainLedgerHost ring fresh s e
          (grantDrainLedgerInitial ring s e).host) ≠
          .terminal := by
    intro _
    rw [hShadowCoalesce]
    decide
  have hShadowBudget :=
    grantDrainObservedSeedUnheldStep
      ring hn fresh update s e e e
      (grantDrainLedgerInitial ring s e)
      hP hSeedBudget hSeedHost hSeedObserved hSeedNontrivial
      hShadowHost hNewRequest hNewFollower hCoalesceNotTerminal
  exact grantDrainUnmarkedShadowTransfer
    ring fresh update s e label
    (grantDrainLedgerInitial ring s e) e hUnmarked
    hNewHost hShadowHost hSameMark hShadowBudget

/-- The full source-level unmarked rise, without an assumed physical
certificate. Direct terminal observations and fresh post observations
use the existing seeds; older observed marks and coalescing-X
marks use cap-seeded physical shadows, transported to the original
unmarked identity by the literal min-cap inequality. -/
theorem grantDrainLockBudgetUnmarkedRiseHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hUnmarked : label.mark = .unmarked) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  cases hjHost :
      (grantDrainLedgerStep ring fresh update s e label).host with
  | none =>
      intro j hj
      rw [hjHost] at hj
      cases hj
  | some j =>
      have hGrant :=
        grantDrainLockBudgetSuccessorGrant
          ring hn fresh update s e label hInv j hjHost
      cases hr : (grantDrainStep ring fresh update s e).request j with
      | true =>
          exact grantDrainLockBudgetUnmarkedPostTerminalStatusHolds
            ring hn fresh update s e label j
            hP hInv hUnmarked hjHost (Or.inl hr)
      | false =>
          cases hl :
              ((grantDrainStep ring fresh update s e).native j).l with
          | true =>
              exact grantDrainLockBudgetUnmarkedPostTerminalStatusHolds
                ring hn fresh update s e label j
                hP hInv hUnmarked hjHost (Or.inr hl)
          | false =>
              by_cases hOldObserved :
                  grantDrainLedgerObservedMark ring s label.host =
                    .unmarked
              · by_cases hCoalesced :
                    grantDrainLedgerCoalesceMark ring s e label.host
                      (grantDrainLedgerHost ring fresh s e label.host) =
                      .unmarked
                · exact grantDrainLockBudgetUnmarkedFreshObservationHolds
                    ring hn fresh update s e label
                    hP hInv hUnmarked hOldObserved hCoalesced
                · exact grantDrainUnmarkedCoalesceOrigin
                    ring hn fresh update s e g j label
                    hP hInv hOldHost hUnmarked hOldObserved
                    hCoalesced hjHost hr hl
              · exact grantDrainUnmarkedOldObservedOrigin
                  ring hn fresh update s e g j label
                  hP hInv hOldHost hUnmarked
                  hOldObserved hjHost hr hl

/-- The weak-to-terminal case is also needed for the universal
four-mark case split. A surviving initially weak identity can become
terminal only by acquiring a physically held post host: its old
observation is weak, its newly coalesced terminal observation would
require an old held X whose request survives, and an unrequested
follower has no terminal post observation. Its old weak reserve
(d+n) pays at most one nominated debit and leaves the one-hit cap. -/
theorem grantDrainLockBudgetWeakToTerminalHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) (g : Fin n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label)
    (hOldHost : label.host = some g)
    (hWeak : label.mark = .weak)
    (hNewTerminal :
      (grantDrainLedgerStep ring fresh update s e label).mark =
        .terminal) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  cases hjHost :
      (grantDrainLedgerStep ring fresh update s e label).host with
  | none =>
      intro j hj
      rw [hjHost] at hj
      cases hj
  | some j =>
      obtain ⟨hOldGrant, hOldCase⟩ := hInv g hOldHost
      rw [hWeak] at hOldCase
      obtain ⟨hOldReq, hOldFollower, hOldLock,
        hOldBudget⟩ := hOldCase
      have hOldStrongFalse :
          grantDrainLedgerStrongLock ring s g = false := by
        cases hs :
            (s.native (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))).sh with
        | false =>
            simp [grantDrainLedgerStrongLock, hs]
        | true =>
            simp [grantDrainLedgerWeakLock, hs] at hOldLock
      have hOldObservation :
          grantDrainLedgerObservedMark ring s label.host =
            .weak := by
        rw [hOldHost]
        simp [grantDrainLedgerObservedMark,
          hOldReq, hOldFollower, hOldStrongFalse, hOldLock]
      have hNewGrant :=
        grantDrainLockBudgetSuccessorGrant
          ring hn fresh update s e label hInv j hjHost
      have hNewFollower :=
        grantDrainStrongTerminalSurvivorFollower
          ring hn fresh update s e label g j
          hOldHost hOldGrant hOldFollower hjHost
      have hRawHost :
          grantDrainLedgerHost ring fresh s e label.host = some j :=
        hjHost
      have hNewRequest :
          (grantDrainStep ring fresh update s e).request j =
            true := by
        cases hr :
            (grantDrainStep ring fresh update s e).request j with
        | true => rfl
        | false =>
            have hPostNotTerminal :=
              grantDrainTerminalFollowerObservationBelowTerminal
                ring (grantDrainStep ring fresh update s e)
                j hr hNewFollower
            have hCoalesceNotTerminal :=
              grantDrainTerminalFollowerCoalesceBelowTerminal
                ring hn fresh update s e label g j
                hOldHost hOldReq hOldGrant hjHost hr
            have hNotTerminal :
                (grantDrainLedgerStep ring fresh update s e label).mark ≠
                  .terminal := by
              change grantDrainLedgerMarkNext ring fresh update s e label ≠
                .terminal
              unfold grantDrainLedgerMarkNext
              rw [hWeak, hOldObservation, hRawHost]
              rw [hRawHost] at hCoalesceNotTerminal
              exact grantDrainFourMarkJoinBelowTerminal _ _ _ _
                (by decide) (by decide)
                hCoalesceNotTerminal hPostNotTerminal
            exact False.elim (hNotTerminal hNewTerminal)
      have hRawMark :
          grantDrainLedgerMarkNext ring fresh update s e label =
            .terminal := hNewTerminal
      have hPostHeld :
          grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e) (some j) =
              true := by
        simp [grantDrainLedgerHeld, hNewRequest, hNewGrant]
      have hRemaining :
          (grantDrainLedgerStep ring fresh update s e label).remaining =
            min
              (label.remaining -
                (if grantDrainLedgerNominatedHit ring s e label.host
                 then 1 else 0))
              (min 1 n) := by
        change grantDrainLedgerRemainingNext n label
          (grantDrainLedgerHost ring fresh s e label.host)
          (grantDrainLedgerMarkNext ring fresh update s e label)
          (grantDrainLedgerNominatedHit ring s e label.host)
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update s e)
            (grantDrainLedgerHost ring fresh s e label.host)) = _
        rw [hRawHost, hRawMark, hPostHeld]
        simp [grantDrainLedgerRemainingNext,
          hWeak, grantDrainLedgerQuotaCap]
      have hOldDistancePositive :=
        grantDrainStrongProtectedDistance_some_pos ring s g
      have hSpentPositive :
          0 < label.remaining -
            (if grantDrainLedgerNominatedHit ring s e label.host
              then 1 else 0) := by
        cases hh : grantDrainLedgerNominatedHit ring s e label.host with
        | false =>
            simp only [hh, Bool.false_eq_true, ↓reduceIte,
              Nat.sub_zero]
            omega
        | true =>
            simp only [hh, ↓reduceIte]
            omega
      have hNextPositive :
          0 <
            (grantDrainLedgerStep ring fresh update s e label).remaining := by
        rw [hRemaining]
        have hCapOne : 1 ≤ min 1 n :=
          Nat.le_min.mpr ⟨Nat.le_refl 1, (by omega : 1 ≤ n)⟩
        have hBound :
            1 ≤ min
              (label.remaining -
                (if grantDrainLedgerNominatedHit ring s e label.host
                 then 1 else 0))
              (min 1 n) :=
          Nat.le_min.mpr
            ⟨Nat.succ_le_of_lt hSpentPositive, hCapOne⟩
        omega
      intro k hk
      have heq : j = k :=
        Option.some.inj (hjHost.symm.trans hk)
      subst k
      refine ⟨hNewGrant, ?_⟩
      rw [hNewTerminal]
      simp only [hNewRequest, ↓reduceIte]
      exact ⟨hNextPositive,
        grantDrainLockBudgetHeldRetiresOnNomination
          ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label)
          j hjHost hNewRequest hNewGrant⟩

/-- Complete canonical one-edge LockBudget invariant, using the
verified physical/counter rows for every old observation and every
new mark. No user-supplied leaf, no additional protocol assumption. -/
theorem grantDrainLockBudgetStepHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hInv : LockBudget ring fresh update s label) :
    LockBudget ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label) := by
  cases hHost : label.host with
  | none =>
      exact grantDrainLockBudgetRetiredStep
        ring fresh update s e label hHost
  | some g =>
      cases hOldMark : label.mark with
      | unmarked =>
          exact grantDrainLockBudgetUnmarkedRiseHolds
            ring hn fresh update s e label g
            hP hInv hHost hOldMark
      | weak =>
          cases hNewMark :
              (grantDrainLedgerStep ring fresh update s e label).mark with
          | unmarked =>
              have hDecrease :
                  grantDrainMarkRank
                    (grantDrainLedgerStep ring fresh update s e label).mark <
                  grantDrainMarkRank label.mark := by
                rw [hOldMark, hNewMark]
                simp [grantDrainMarkRank]
              exact False.elim
                (grantDrainLockBudgetDecreasingMarkImpossible
                  ring fresh update s e label hDecrease)
          | weak =>
              exact grantDrainLockBudgetWeakStableNext
                ring hn fresh update s e label g
                hP hInv hHost hOldMark hNewMark
          | strong =>
              exact grantDrainLockBudgetWeakToStrongHolds
                ring hn fresh update s e label g
                hP hInv hHost hOldMark hNewMark
          | terminal =>
              exact grantDrainLockBudgetWeakToTerminalHolds
                ring hn fresh update s e label g
                hP hInv hHost hOldMark hNewMark
      | strong =>
          cases hNewMark :
              (grantDrainLedgerStep ring fresh update s e label).mark with
          | unmarked =>
              have hDecrease :
                  grantDrainMarkRank
                    (grantDrainLedgerStep ring fresh update s e label).mark <
                  grantDrainMarkRank label.mark := by
                rw [hOldMark, hNewMark]
                simp [grantDrainMarkRank]
              exact False.elim
                (grantDrainLockBudgetDecreasingMarkImpossible
                  ring fresh update s e label hDecrease)
          | weak =>
              have hDecrease :
                  grantDrainMarkRank
                    (grantDrainLedgerStep ring fresh update s e label).mark <
                  grantDrainMarkRank label.mark := by
                rw [hOldMark, hNewMark]
                simp [grantDrainMarkRank]
              exact False.elim
                (grantDrainLockBudgetDecreasingMarkImpossible
                  ring fresh update s e label hDecrease)
          | strong =>
              exact grantDrainLockBudgetStrongStableNext
                ring hn fresh update s e label g
                hP hInv hHost hOldMark hNewMark
          | terminal =>
              exact grantDrainLockBudgetStrongToTerminalHolds
                ring hn fresh update s e label g
                hP hInv hHost hOldMark hNewMark
      | terminal =>
          have hOldGrant := (hInv g hHost).1
          cases hRequest : s.request g with
          | true =>
              exact grantDrainLockBudgetTerminalHeldHolds
                ring hn fresh update s e label g
                hInv hHost hOldMark hRequest
          | false =>
              cases hLeader : (s.native g).l with
              | true =>
                  exact grantDrainLockBudgetTerminalLeaderHolds
                    ring hn fresh update s e g label
                    hP hInv hHost hOldMark hRequest hLeader
              | false =>
                  exact grantDrainLockBudgetTerminalFollowerHolds
                    ring hn fresh update s e label g
                    hP hInv hHost hOldMark hRequest hLeader

/-- The canonical n-labelled no-new-grant reference has a
globally positive remaining quota at every live, marked ghost
descended from an initial physical grant, for every scheduler word. -/
theorem grantDrainLedgerNoExhaustionHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s0 : GrantDrainState n Scratch) :
    GrantDrainLedgerNoExhaustion ring fresh update s0 := by
  exact grantDrainNoExhaustionOfLockBudgetStep
    ring hn fresh update s0
    (fun s e label hP hInv =>
      grantDrainLockBudgetStepHolds
        ring hn fresh update s e label hP hInv)

end L3


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Dependency audit:

R8d / zeta:
* grantDrainEntranceNominatedQuota gives the
  pathwise < n outgoing-bullet quota while the paired grant remains
  unmarked. The finite-family tail is subsequently converted by
  grantDrainEntranceFirstStageCost into
    ∀ T, costNumerator (grantDrainEntranceNext ring fresh update)
      GrantDrainEntranceDone (grantDrainEntranceInitial ring s) T
      ≤ n ^ T * (4 * n ^ 2).
  This already needs only PPlus, not LedgerNoExhaustion. The
  disjunction defining GrantDrainEntranceDone is:
  all old bad-LIVE bullet identities retired OR all surviving
  grant identities marked.

R8e / unclean DUMMY:
* GrantDrainEntranceNoBadLive and
  GrantDrainEntranceZeroTrailFamily = I are
  separate factors of GrantDrainEntranceIntermediateZ.
* grantDrainDummyInitialFaithful and
  grantDrainDummyEmptyCoverImpliesI are proved.
* Precise FIRST missing universal transition premise:
    ∀ (s : GrantDrainState n Scratch) (e : Fin n),
      PPlus ring s.native →
      GrantDrainEntranceNoBadLive ring s →
      GrantDrainDummyEdgeOrigin ring fresh update s e
  Sufficient but stronger missing premise:
    ∀ (s : GrantDrainState n Scratch) (e : Fin n),
      PPlus ring s.native →
      GrantDrainEntranceNoBadLive ring s →
      GrantDrainDummyCleanGeometry ring fresh update s e
  The conditional bridges are
  grantDrainDummyEdgeOriginOfCleanGeometry,
  grantDrainDummyWordFaithfulOfCleanGeometry,
  and grantDrainDummyEdgeWordFaithfulOfOrigins.
  In addition, a nominated-hit/finite-family clock for retiring
  initially unclean DUMMY identities is NOT yet present. Thus
  no numerical first-hit-to-I theorem has been established.

D.5 / clean-sector:
* grantDrainEntranceR8eIntermediateWordClosed,
  grantDrainEntranceR8ePotentialNonincreaseProved,
  grantDrainEntranceR8ePotentialNominatedDropProved,
  grantDrainEntranceR8ePotentialSharpCapProved, and
  grantDrainEntranceR8eCleanSectorCostSharp give
    ∀ s, GrantDrainEntranceIntermediateZ ring s →
      ∀ T, costNumerator (grantDrainCanonicalModel ...).step
        (fun x => C_native ring x.native) s T
        ≤ n ^ T * (n * (n - 2)).
  grantDrainEntranceR8eCleanCostOfNoBadAndI is the
  explicit two-factor corollary.
* The earlier R8d Done cut does NOT imply I, even if a physical
  grant remains: the literal five-site counterexample below
  strengthens grantDrainR8eFirstNoBadCutRefuted.
  Neither the assumed LedgerNoExhaustion nor NoBadLive itself
  supplies the missing DUMMY sector clock.

D.6 / warm:
* grantDrainWarmRank is NOT nonincreasing on
  all steps; grantDrainWarmRank_not_globally_nonincreasing
  is a proved literal counterexample.
* grantDrainWarmLabelStep and grantDrainChargedWarmRank
  define a proof-only compensated potential.
  grantDrainWarmQuota_nonincrease_of_paid_increment and
  grantDrainWarmQuota_strict_of_paid_increment prove ONLY
  the Nat inequalities from the explicit paid-increment conditions
    w' ≤ w + (b - b') + (d - d')
  and, on a nominee,
    w' + 1 ≤ w + (b - b') + (d - d').
  The corresponding physical source-step inequalities, the
  nominated-progress edge and a uniform initial warm-charge cap
  remain open. No D.6 hitting-time stage bound exists to compose.

NoExhaustion:
* GrantDrainLedgerNoExhaustion is defined in GrantDrainMarks.
  Its precise active implication is:
    PPlus ring s0.native →
      ∀ i edges, s0.grant i = true →
        (grantDrainLedgerRun ...).2.host ≠ none →
        (grantDrainLedgerRun ...).2.mark ≠ .unmarked →
        0 < (grantDrainLedgerRun ...).2.remaining.
  The user grants grantDrainLedgerNoExhaustionHolds at every PPlus
  initial state. It enters only when the R8d Done right branch
  leaves still-live marked grant identities; it does not yield
  the DUMMY origin/clock or D.6 paid-increment law.

Composition and BANK:
* UniformFirstHit.expectedHittingTimeAtMost_iff_cost converts
  every-horizon source costNumerator bounds to literal expectation.
  The two stage clocks are converted below.
* The remaining unproved stage entry and stage-duration
  statements prevent an unconditional all-horizon grant-free
  numerator inequality and hence GrantDrainSharedBound.
  The source model is the literal grantDrainCanonicalModel.
* BankGrantDrainRefinement is a Prop
  describing post-InheritedAuthorityExtinct physical correspondence.
  No source GrantDrainSharedBound or consequent BANK expectation
  transfer theorem is claimed here.

The scalar paper ceiling grantDrainCeiling = ceil(109*n*n/3)
is shown below to be STRICTLY below 37*n^2 for n >= 5, but a
numerical comparison cannot replace the absent stage laws.
-/

/-- Literal expected time for the first/zeta
stage, not merely its finite-horizon numerator inequality. -/
theorem grantDrainEntranceFirstStageExpectedTime
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (grantDrainEntranceNext ring fresh update)
      GrantDrainEntranceDone
      (grantDrainEntranceInitial ring s)
      ((4 * n ^ 2 : Nat) : Rat) := by
  exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (grantDrainEntranceNext ring fresh update)
    GrantDrainEntranceDone
    (by omega : 0 < n)
    (grantDrainEntranceInitial ring s)
    (4 * n ^ 2)).2
    (grantDrainEntranceFirstStageCost
      ring hn fresh update s hPB)

/-- Literal expected time from the ACTUAL closed NoBadLive-and-I
cut to native clean sectors, including the almost-sure clause. -/
theorem grantDrainEntranceCleanSectorExpectedTime
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hCut : GrantDrainEntranceIntermediateZ ring s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (grantDrainCanonicalModel ring hn fresh update).step
      (fun x : GrantDrainState n Scratch => C_native ring x.native)
      s ((n * (n - 2) : Nat) : Rat) := by
  exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (grantDrainCanonicalModel ring hn fresh update).step
    (fun x : GrantDrainState n Scratch => C_native ring x.native)
    (by omega : 0 < n) s (n * (n - 2))).2
    (grantDrainEntranceR8eCleanSectorCostSharp
      ring hn fresh update s hCut)

/-- The moved-clean-DUMMY clause of GrantDrainDummyCleanGeometry,
for BOTH source-leader and source-follower cases, and every FIRE.
No PPlus, NoBadLive, or external geometry hypothesis is required. -/
theorem grantDrainDummyMovingCleanHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hDummy : (s.native e).b = (1 : Fin 3))
    (hYFollower : (s.native (ring.rightNeighbor e)).l = false)
    (hYEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native e) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  cases hLeader : (s.native e).l with
  | false =>
      exact grantDrainDummyMovedFollowerSourceClean
        ring hn fresh update s e
        hLeader hDummy hYFollower hYEmpty hOldClean
  | true =>
      exact grantDrainDummyMovedLeaderSourceClean
        ring hn fresh update s e
        hLeader hDummy hOldClean hYFollower hYEmpty

/-- The paper's integral ceiling really is strictly below
37*n^2 at every ring size in the R8 range. All large
products are turned into an opaque Nat before omega. -/
theorem grantDrainR8PaperCeilingBelowThirtySeven
    (n : Nat) (hn : 5 ≤ n) :
    grantDrainCeiling n < 37 * n ^ 2 := by
  have hProduct : 5 * n ≤ n * n :=
    Nat.mul_le_mul_right n hn
  have hAtLeastTwo : 2 ≤ n * n := by omega
  unfold grantDrainCeiling
  rw [Nat.pow_two]
  generalize hSquare : n * n = q at *
  omega

/-- Same n=5 PPlus native array as the existing R8e obstruction,
but now a real unrequested GRANT survives at site 4:
site 0=(leader,true; bullet 0; shield false; signal false),
sites 1,2=(follower; DUMMY 1; shield false; signal false),
sites 3,4=(follower; bullet 0; shield false; signal false);
all requests false. Scheduler word is empty. -/
private def grantDrainR8eUncleanWithGrant : GrantDrainState 5 Unit :=
  { grantDrainR8eUncleanCutState with
    grant := fun i => i.val == 4 }

/-- The first R8d Done cut may have no BAD LIVE and an actual
outstanding physical grant, yet lack I. This is a literal
nonempty-grant obstruction to jumping directly from R8d to D.5. -/
theorem grantDrainR8DoneWithGrantNotIntermediate :
    PPlus grantDrainR8eUncleanCutRing
      grantDrainR8eUncleanWithGrant.native ∧
    GrantDrainEntranceDone
      (grantDrainEntranceInitial grantDrainR8eUncleanCutRing
        grantDrainR8eUncleanWithGrant) ∧
    GrantDrainEntranceNoBadLive grantDrainR8eUncleanCutRing
      grantDrainR8eUncleanWithGrant ∧
    ¬ I grantDrainR8eUncleanCutRing
      grantDrainR8eUncleanWithGrant.native ∧
    ¬ GrantFree grantDrainR8eUncleanWithGrant := by
  have hNoBad :
      GrantDrainEntranceNoBadLive grantDrainR8eUncleanCutRing
        grantDrainR8eUncleanWithGrant :=
    grantDrainR8eUncleanCutNoBad
  have hDone :
      GrantDrainEntranceDone
        (grantDrainEntranceInitial grantDrainR8eUncleanCutRing
          grantDrainR8eUncleanWithGrant) := by
    left
    intro id
    change grantDrainEntranceBulletInitial
      grantDrainR8eUncleanCutRing
      grantDrainR8eUncleanWithGrant id = none
    unfold grantDrainEntranceBulletInitial
    simp [hNoBad id]
  refine ⟨grantDrainR8eUncleanCutProtected,
    hDone, hNoBad, grantDrainR8eUncleanCutNotI, ?_⟩
  intro hFree
  have hGrant :
      grantDrainR8eUncleanWithGrant.grant (4 : Fin 5) =
        true := by
    rfl
  have hEmpty := hFree (4 : Fin 5)
  rw [hGrant] at hEmpty
  cases hEmpty

/-- Formal universal refutation of the invalid R8d-to-D.5
shortcut, even when the starting state has a live GRANT. -/
theorem grantDrainR8DoneNoBadGrantDoesNotImplyI :
    ¬ ∀ s : GrantDrainState 5 Unit,
      PPlus grantDrainR8eUncleanCutRing s.native →
      GrantDrainEntranceDone
        (grantDrainEntranceInitial grantDrainR8eUncleanCutRing s) →
      GrantDrainEntranceNoBadLive grantDrainR8eUncleanCutRing s →
      ¬ GrantFree s →
      I grantDrainR8eUncleanCutRing s.native := by
  intro hImp
  obtain ⟨hPB, hDone, hNoBad, hNotI, hGrant⟩ :=
    grantDrainR8DoneWithGrantNotIntermediate
  exact hNotI
    (hImp grantDrainR8eUncleanWithGrant
      hPB hDone hNoBad hGrant)


/-- The two already-established numerical stage ceilings, 4*n^2
for R8d and n*(n-2) for D.5, use strictly less than 37*n^2
in total. This is NOT a bound for the intervening DUMMY stage
or for the final warm stage; those terms remain to be proved. -/
theorem grantDrainR8ProvedStageCoefficientsBelowThirtySeven
    (n : Nat) (hn : 5 ≤ n) :
    4 * n ^ 2 + n * (n - 2) < 37 * n ^ 2 := by
  have hMultiplier :
      n * (n - 2) ≤ n * n :=
    Nat.mul_le_mul_left n (Nat.sub_le n 2)
  have hPositive : 0 < n * n :=
    Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n)
  rw [Nat.pow_two]
  generalize hSquare : n * n = q at *
  omega


/-- Markov tail on the genuine R8d source stage: the number of
surviving T-words is bounded without a fabricated stopping law. -/
theorem grantDrainEntranceFirstStageSurvivalTail
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native) (T : Nat) :
    T * UniformFirstHit.survivalNumerator
      (grantDrainEntranceNext ring fresh update)
      GrantDrainEntranceDone (grantDrainEntranceInitial ring s) T ≤
      n ^ T * (4 * n ^ 2) := by
  exact Nat.le_trans
    (UniformFirstHit.survival_mul_le_cost
      (grantDrainEntranceNext ring fresh update)
      GrantDrainEntranceDone (grantDrainEntranceInitial ring s) T)
    (grantDrainEntranceFirstStageCost
      ring hn fresh update s hPB T)

/-- Corresponding exact survival-tail bound after the NoBadLive/I
cut for the genuine D.5 clean-sector stage. -/
theorem grantDrainEntranceCleanSectorSurvivalTail
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hCut : GrantDrainEntranceIntermediateZ ring s)
    (T : Nat) :
    T * UniformFirstHit.survivalNumerator
      (grantDrainCanonicalModel ring hn fresh update).step
      (fun x : GrantDrainState n Scratch => C_native ring x.native)
      s T ≤ n ^ T * (n * (n - 2)) := by
  exact Nat.le_trans
    (UniformFirstHit.survival_mul_le_cost
      (grantDrainCanonicalModel ring hn fresh update).step
      (fun x : GrantDrainState n Scratch => C_native ring x.native)
      s T)
    (grantDrainEntranceR8eCleanSectorCostSharp
      ring hn fresh update s hCut T)


/-- From the LEFT disjunct of the actual R8d Done cut, the canonical
physical source word has no paper-bad LIVE anywhere. This uses
the immutable-bullet ancestry and exact physical projection;
it does NOT claim that the native I factor already holds. -/
theorem grantDrainR8FirstDoneLeftPhysicalNoBad
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (word : List (Fin n))
    (hPB : PPlus ring s.native)
    (hLeft :
      ∀ id : Fin n,
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring s) word).bulletHosts id =
          none) :
    GrantDrainEntranceNoBadLive ring
      (grantDrainEntrancePhysicalWord ring fresh update s word) := by
  have hFaithful :=
    grantDrainEntranceInitialFaithfulRun
      ring hn fresh update s word hPB
  have hNoBad :=
    (grantDrainEntranceNoBulletIffNoBad ring
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word) hFaithful).mp hLeft
  have hProjection :
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).physical =
      grantDrainEntrancePhysicalWord ring fresh update s word := by
    simpa [grantDrainEntranceInitial] using
      (grantDrainEntrancePhysicalWordProjection
        ring fresh update word (grantDrainEntranceInitial ring s))
  change GrantDrainEntranceNoBadLive ring
    (grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring s) word).physical at hNoBad
  rw [hProjection] at hNoBad
  exact hNoBad


/-- Exact comparison of the immutable entrance grant identity with
the SAME physical state's literal GrantDrainLedgerRun, for every
scheduler word. This is a source-label projection, not a BANK
simulation or a new stochastic assumption. -/
theorem grantDrainEntranceGrantLedgerProjection
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (x : GrantDrainEntranceState n Scratch) (i : Fin n),
      (grantDrainLedgerRun ring fresh update x.physical
        (x.grantLabels i) word).2 =
      (grantDrainEntranceRun ring fresh update x word).grantLabels i := by
  intro word
  induction word with
  | nil =>
      intro x i
      rfl
  | cons e rest ih =>
      intro x i
      change
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update x.physical e)
          (grantDrainLedgerStep ring fresh update x.physical e
            (x.grantLabels i)) rest).2 =
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update x e) rest).grantLabels i
      exact ih (grantDrainEntranceNext ring fresh update x e) i

/-- The RIGHT R8d Done disjunct is quantitatively meaningful
under exactly the user-authorized LedgerNoExhaustion premise:
every initially real GRANT identity still alive at that cut
has strictly positive remaining quota. No such premise is used
in the LEFT NoBadLive branch or in FirstStageCost. -/
theorem grantDrainR8FirstDoneRightMarkedQuotaPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (word : List (Fin n))
    (hPB : PPlus ring s.native)
    (hNoExhaustion : GrantDrainLedgerNoExhaustion ring fresh update s)
    (hRight :
      ∀ i : Fin n,
        ((grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring s) word).grantLabels i).host ≠
          none →
        ((grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring s) word).grantLabels i).mark ≠
          .unmarked)
    (i : Fin n) (hGrant : s.grant i = true)
    (hLive :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).grantLabels i).host ≠
          none) :
    0 < ((grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring s) word).grantLabels i).remaining := by
  have hProjection :
      (grantDrainLedgerRun ring fresh update s
        (grantDrainLedgerInitial ring s i) word).2 =
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).grantLabels i := by
    simpa [grantDrainEntranceInitial] using
      (grantDrainEntranceGrantLedgerProjection
        ring fresh update word (grantDrainEntranceInitial ring s) i)
  have hLiveRaw :
      (grantDrainLedgerRun ring fresh update s
        (grantDrainLedgerInitial ring s i) word).2.host ≠ none := by
    rw [hProjection]
    exact hLive
  have hMarkedRaw :
      (grantDrainLedgerRun ring fresh update s
        (grantDrainLedgerInitial ring s i) word).2.mark ≠
          .unmarked := by
    rw [hProjection]
    exact hRight i hLive
  have hQuota :=
    hNoExhaustion hPB i word hGrant hLiveRaw hMarkedRaw
  rw [hProjection] at hQuota
  exact hQuota


/-- Exact R8d first-stage branching on the ORIGINAL scheduler word.
The left outcome is physical NoBadLive. The right outcome is the
positive persistent-mark quota for every surviving initial grant,
using only the explicitly authorized LedgerNoExhaustion premise.
Neither branch implies I or the warm paid-increment law. -/
theorem grantDrainR8DonePhysicalOrMarkedBudget
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (word : List (Fin n))
    (hPB : PPlus ring s.native)
    (hNoExhaustion : GrantDrainLedgerNoExhaustion ring fresh update s)
    (hDone :
      GrantDrainEntranceDone
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring s) word)) :
    GrantDrainEntranceNoBadLive ring
      (grantDrainEntrancePhysicalWord ring fresh update s word) ∨
    (∀ i : Fin n, s.grant i = true →
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).grantLabels i).host ≠
          none →
      0 < ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).grantLabels i).remaining) := by
  cases hDone with
  | inl hLeft =>
      exact Or.inl
        (grantDrainR8FirstDoneLeftPhysicalNoBad
          ring hn fresh update s word hPB hLeft)
  | inr hRight =>
      right
      intro i hGrant hLive
      exact grantDrainR8FirstDoneRightMarkedQuotaPositive
        ring fresh update s word hPB hNoExhaustion
        hRight i hGrant hLive

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
DUMMY clean geometry, E/FIRE case table (literal source row).

A. Stationary old clean DUMMY at b != e:
  A0 b old leader, b outside pair:
     grantDrainDummyStationaryLeaderAwayClean.
  A1 b old leader, b=Y, Y survives:
     grantDrainDummyStationarySurvivingResponderClean.
  A2 b=Y, old leader dies and old DUMMY remains:
     grantDrainDummyResidentLeaderDeathClean below (E death,
     new follower, B=1; F1 impossible; F0/F2 or no-FIRE).
  A3 b old follower, old Y leader dies from follower LIVE:
     if b in Y sector, StationaryFatalFollowerVictimClean,
     with exact select none/F0,F2/F1 branches.
     If b in another sector, untouched-sector frame is required.
  A4 b old follower, Y old follower:
     stationary quiet no-transfer, otherwise split FIRE and
     source-SG/nonfatal transfer; nonfatal stationary F0 remains
     to be assembled.
  A5 b old follower, Y old leader survives or dies without
     a LIVE follower killer: requires the corresponding sector frame.

B. Moved clean DUMMY from X into empty follower Y:
  source leader: MovedLeaderSourceClean;
  source follower: MovedFollowerSourceClean.
  Both are assembled by grantDrainDummyMovingCleanHolds.

C. Ready OLD leader at responder Y:
  Y survives leader: ReadySurvivingLeaderClean.
  Y dies, old X leader: grantDrainDummySourceLeaderDeathClean
     below (literal E row, no FIRE).
  Y dies, old X follower LIVE: ReadyFollowerLiveClean
     (none / F0 / F2; F1 impossible).
  The ready case does not have an incoming F1 birth at Y because
  the E row already gives B=1 there.

Only the fully proved rows below are declared as theorems. The
unresolved general stationary follower case A4/A5 is NOT assumed.
-/

/-- An OLD leader source has post-E signal zero whenever its OLD
leader responder dies. The literal E row clears a ready source
before OR-ing its newly dead responder, including an old LIVE
emission and all shield/bullet cases. -/
theorem grantDrainDummyLeaderDeathSourceSignalZero
    (x y : CertNative)
    (hXLeader : x.l = true)
    (hYLeader : y.l = true)
    (hDeath : (certLiteralEPair x y).2.l = false) :
    (certLiteralEPair x y).1.sg = false := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  change xl = true at hXLeader
  change yl = true at hYLeader
  subst xl
  subst yl
  rcases grantDrainEntranceLocalFinThreeCases xb with rfl | rfl | rfl <;>
    rcases grantDrainEntranceLocalFinThreeCases yb with rfl | rfl | rfl <;>
    cases xsh <;> cases xsg <;> cases ysh <;> cases ysg <;>
    simp [certLiteralEPair, certFinThree] at *

/-- A responder with a post-E DUMMY cannot fire F1, so a final
follower at that responder was already a follower after native E.
This is the exact implication needed when an old leader dies. -/
theorem grantDrainDummyPostFollowerImpliesEDeath
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hEDummy :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3))
    (hFinalFollower :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = false) :
    (nativeE ring s.native e (ring.rightNeighbor e)).l =
      false := by
  have hDifferent : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hEDummy]
  have hNoFOne :
      grantDrainSelect ring s e ≠ .rightLocal :=
    grantDrainEntranceResponderIneligibleNoRightFire
      ring s e hIneligible
  change (grantDrainNativeNext ring s e
    (ring.rightNeighbor e)).l = false at hFinalFollower
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hFinalFollower
  | leftLocal =>
      simpa [grantDrainNativeNext, hf,
        canonicalBirth, hDifferent] using hFinalFollower
  | rightLocal =>
      exact False.elim (hNoFOne hf)
  | cross =>
      simpa [grantDrainNativeNext, hf,
        canonicalBirth, hDifferent] using hFinalFollower

/-- OLD leader X, OLD leader Y: if native E kills Y, leaves its
DUMMY and signal zero, the literal selector is no-FIRE.
Consequently Y is a clean follower immediately after zero-signal,
empty-bullet leader X. This covers ready-Y and resident-quiet-Y
sources without assuming a post-step geometric certificate. -/
theorem grantDrainDummySourceLeaderDeathClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hXLeader : (s.native e).l = true)
    (hYLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hYDeath :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = false)
    (hYDummy :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).b = (1 : Fin 3))
    (hYZero :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).sg = false) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hDifferent : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hESourceLeader :
      (nativeE ring s.native e e).l = true := by
    rw [grantDrainMarksNativeESource,
      grantDrainMarksOutgoingSourceLeaderNative]
    exact hXLeader
  have hESourceEmpty :
      (nativeE ring s.native e e).b = (0 : Fin 3) :=
    grantDrainEntranceNativeESourceBulletZero
      ring s.native e
  have hPairDeath :
      (certLiteralEPair
        (s.native e)
        (s.native (ring.rightNeighbor e))).2.l = false := by
    simpa [nativeE, hDifferent] using hYDeath
  have hESourceZero :
      (nativeE ring s.native e e).sg = false := by
    rw [grantDrainMarksNativeESource]
    exact grantDrainDummyLeaderDeathSourceSignalZero
      (s.native e) (s.native (ring.rightNeighbor e))
      hXLeader hYLeader hPairDeath
  have hXIneligible :
      grantDrainEligible (nativeE ring s.native e) e =
        false := by
    simp [grantDrainEligible, hESourceLeader]
  have hYIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hYDummy]
  have hNoFire : grantDrainSelect ring s e = .none := by
    simp [grantDrainSelect, hXIneligible, hYIneligible]
  have hPhysical :
      (grantDrainStep ring fresh update s e).native =
        nativeE ring s.native e := by
    change grantDrainNativeNext ring s e =
      nativeE ring s.native e
    simp [grantDrainNativeNext, hNoFire]
  rw [hPhysical]
  exact grantDrainDummyAdjacentFollowerClean
    ring hn (nativeE ring s.native e) e
    hESourceLeader hESourceEmpty hESourceZero
    hYDeath hYDummy hYZero

/-- OLD follower LIVE X killing OLD leader Y: the deleted Y is
an empty-bullet, signal-zero follower after E, while X's initial
LIVE is clean under PPlus + NoBadLive. In a no-FIRE successor,
the new Y's clean sector comes from the old clean LIVE at X.
For F0/F2, born X is the immediately preceding clean leader.
F1 is excluded by the real E DUMMY at Y. -/
theorem grantDrainDummySourceFollowerDeathClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hXFollower : (s.native e).l = false)
    (hYLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hYDeath :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = false)
    (hYDummy :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).b = (1 : Fin 3))
    (hYZero :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).sg = false) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hDifferent : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hLive : LiveBullet s.native e :=
    L3.grantDrainWeakDeathFollowerMustBeLive
      ring hn s.native e hXFollower hYLeader hYDeath
  have hXZero : (s.native e).sg = false :=
    L3.grantDrainDeathLiveOwnSignalZero
      ring s e hP hLive
  have hOldClean :
      GrantDrainEntranceBulletCleanAt ring s.native e :=
    grantDrainDummyLiveCleanOfNoBad
      ring s.native hP hNoBad e hLive
  have hOldCleanCore := hOldClean
  obtain ⟨_, p, hOldSector, _, hOldTrail⟩ := hOldClean
  have hRootZero : (s.native p).sg = false := by
    have hz := hOldTrail
      (⟨0, (show 0 < n by omega)⟩ : Fin n) (Nat.zero_le _)
    simpa [grantDrainWeakDeathShiftRightZero] using hz
  have hRootShield : (s.native p).sh = true := by
    have hPeace := hP.2 e hLive
    unfold PPL.PeacefulCore at hPeace
    rw [hOldSector.2] at hPeace
    have hh := hPeace.1
    rw [grantDrainEntranceLeftOffset ring p e] at hh
    exact hh
  have hPairDeath :
      (certLiteralEPair
        (s.native e)
        (s.native (ring.rightNeighbor e))).2.l = false := by
    simpa [nativeE, hDifferent] using hYDeath
  have hOpen :
      (s.native (ring.rightNeighbor e)).sg = true ∨
      (s.native (ring.rightNeighbor e)).sh = false :=
    ((grantDrainEntranceLiteralELeaderDeathCases
      (s.native e) (s.native (ring.rightNeighbor e))
      hYLeader).mp hPairDeath).2
  have hNotRoot : p ≠ ring.rightNeighbor e := by
    intro hEq
    have hYZeroOld :
        (s.native (ring.rightNeighbor e)).sg = false := by
      rw [← hEq]
      exact hRootZero
    have hYShield :
        (s.native (ring.rightNeighbor e)).sh = true := by
      rw [← hEq]
      exact hRootShield
    cases hOpen with
    | inl hYReady =>
        rw [hYZeroOld] at hYReady
        cases hYReady
    | inr hYUnshield =>
        rw [hYShield] at hYUnshield
        cases hYUnshield
  have hESourceEmpty :
      (nativeE ring s.native e e).b = (0 : Fin 3) :=
    grantDrainEntranceNativeESourceBulletZero ring s.native e
  have hYBullet :
      HasBullet (nativeE ring s.native e)
        (ring.rightNeighbor e) := by
    unfold HasBullet
    rw [hYDummy]
    exact (by decide : (1 : Fin 3) ≠ (0 : Fin 3))
  have hZeroBackward :
      ∀ i : Fin n, (s.native i).sg = false →
        (nativeE ring s.native e i).sg = false := by
    intro i hOldZero
    exact grantDrainDummyDeathEZeroBackward
      ring hn s.native e i hYLeader hYDeath
      hXZero hOldZero
  have hNoFireClean :
      GrantDrainEntranceBulletCleanAt ring
        (nativeE ring s.native e)
        (ring.rightNeighbor e) :=
    grantDrainDummyCleanFollowerSuccessorCore
      ring s.native (nativeE ring s.native e) e p
      hXFollower hNotRoot hOldSector hOldCleanCore
      (fun i hi =>
        grantDrainDummyNativeELeaderAwayResponder
          ring s.native e i hi)
      hESourceEmpty hYDeath hYBullet hYZero hZeroBackward
      (fun i hi hBullet =>
        grantDrainDummyNativeEBulletBackwardExceptResponder
          ring s.native e i hESourceEmpty hi hBullet)
  have hBirthClean :
      GrantDrainEntranceBulletCleanAt ring
        (canonicalBirth (nativeE ring s.native e) e)
        (ring.rightNeighbor e) := by
    exact grantDrainDummyAdjacentFollowerClean
      ring hn (canonicalBirth (nativeE ring s.native e) e) e
      (by simp [canonicalBirth, firedNative])
      (by simp [canonicalBirth, firedNative])
      (by simp [canonicalBirth, firedNative])
      (by simpa [canonicalBirth, hDifferent] using hYDeath)
      (by simpa [canonicalBirth, hDifferent] using hYDummy)
      (by simpa [canonicalBirth, hDifferent] using hYZero)
  have hYIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hYDummy]
  have hNoFOne :
      grantDrainSelect ring s e ≠ .rightLocal :=
    grantDrainEntranceResponderIneligibleNoRightFire
      ring s e hYIneligible
  change GrantDrainEntranceBulletCleanAt ring
    (grantDrainNativeNext ring s e) (ring.rightNeighbor e)
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hNoFireClean
  | leftLocal =>
      simpa [grantDrainNativeNext, hf] using hBirthClean
  | rightLocal =>
      exact False.elim (hNoFOne hf)
  | cross =>
      simpa [grantDrainNativeNext, hf] using hBirthClean

/-- The ready-responder clause of CleanGeometry: a final follower
DUMMY at the OLD ready leader is clean. OLD leader-source death
is handled by the literal source-leader E row above; OLD follower
source is necessarily a LIVE and uses the all-FIRE row. -/
theorem grantDrainDummyReadyResponderCleanHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hReady : GrantDrainDummyReadyResponder ring s e)
    (hNewFollower :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = false)
    (hNewDummy :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b = (1 : Fin 3)) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hYLeader := hReady.1
  have hYReady := hReady.2
  have hEDummy :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) :=
    grantDrainEntranceNativeEReadyVictimBulletDummy
      ring (by omega : 2 ≤ n) s.native e hYLeader hYReady
  have hEZero :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        false :=
    (grantDrainEntranceNativeELeaderBulletAfter
      ring (by omega : 2 ≤ n) s.native e hYLeader).2
  have hEDeath :=
    grantDrainDummyPostFollowerImpliesEDeath
      ring hn fresh update s e hEDummy hNewFollower
  cases hOldXLeader : (s.native e).l with
  | true =>
      exact grantDrainDummySourceLeaderDeathClean
        ring hn fresh update s e hOldXLeader hYLeader
        hEDeath hEDummy hEZero
  | false =>
      exact grantDrainDummySourceFollowerDeathClean
        ring hn fresh update s e hP hNoBad
        hOldXLeader hYLeader hEDeath hEDummy hEZero

/-- An OLD clean leader-hosted DUMMY at the responder can be
retained as a NEW follower DUMMY after its leader dies.
Cleanliness is inherited from the old LIVE killer's sector,
or from an immediately preceding leader at the initiator. -/
theorem grantDrainDummyResidentLeaderDeathCleanHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hYLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hYDummy :
      (s.native (ring.rightNeighbor e)).b = (1 : Fin 3))
    (hYClean :
      GrantDrainEntranceBulletCleanAt ring s.native
        (ring.rightNeighbor e))
    (hYNewFollower :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = false) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hYQuiet :
      (s.native (ring.rightNeighbor e)).sg = false :=
    grantDrainDummyCleanOwnSignalZero
      ring s.native (ring.rightNeighbor e) hYClean
  have hEYDummy :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) := by
    exact (grantDrainEntranceNativeEQuietVictimBulletRetained
      ring (by omega : 2 ≤ n) s.native e
      hYLeader hYQuiet).trans hYDummy
  have hEYZero :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        false :=
    (grantDrainEntranceNativeELeaderBulletAfter
      ring (by omega : 2 ≤ n) s.native e hYLeader).2
  have hEDeath :=
    grantDrainDummyPostFollowerImpliesEDeath
      ring hn fresh update s e hEYDummy hYNewFollower
  cases hXL : (s.native e).l with
  | true =>
      exact grantDrainDummySourceLeaderDeathClean
        ring hn fresh update s e hXL hYLeader
        hEDeath hEYDummy hEYZero
  | false =>
      exact grantDrainDummySourceFollowerDeathClean
        ring hn fresh update s e hP hNoBad
        hXL hYLeader hEDeath hEYDummy hEYZero

/-- The old leader-hosted stationary clause is now completely
covered: an off-pair leader is framed; a responder that survives
is a clean zero-signal leader; if the responder dies, the retained
DUMMY is a clean follower by the new actual E/FIRE row. -/
theorem grantDrainDummyStationaryLeaderCleanHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hLeader : (s.native b).l = true)
    (hDummy : (s.native b).b = (1 : Fin 3))
    (hClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hNotE : b ≠ e) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  by_cases hAtY : b = ring.rightNeighbor e
  · subst b
    cases hNewLeader :
        ((grantDrainStep ring fresh update s e).native
          (ring.rightNeighbor e)).l with
    | true =>
        exact grantDrainDummyStationarySurvivingResponderClean
          ring hn fresh update s e
          hLeader hDummy hClean hNewLeader
    | false =>
        exact grantDrainDummyResidentLeaderDeathCleanHolds
          ring hn fresh update s e hP hNoBad
          hLeader hDummy hClean hNewLeader
  · exact grantDrainDummyStationaryLeaderAwayClean
      ring hn fresh update s e b
      hLeader hDummy hClean hNotE hAtY

/-- Fully discharged second geometric clause, with no PPlus or
NoBadLive premise: a clean source DUMMY entering an old empty
follower responder stays clean under every native E/FIRE outcome. -/
theorem grantDrainDummyCleanGeometryMovedHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    (s.native e).b = (1 : Fin 3) →
    (s.native (ring.rightNeighbor e)).l = false →
    (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) →
    GrantDrainEntranceBulletCleanAt ring s.native e →
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  intro hd hy hz hc
  exact grantDrainDummyMovingCleanHolds
    ring hn fresh update s e hd hy hz hc

/-- The source of the incoming edge e -> Y lies one step before Y
in the old leader sector. Thus an OLD clean follower DUMMY at Y
forces the source's signal zero, even when the source is a leader.
This uses the inclusive old clean signal trail, not an assumed
source-quiet hypothesis. -/
theorem grantDrainDummyCleanResponderSourceZero
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hYFollower : (N (ring.rightNeighbor e)).l = false)
    (hYClean : GrantDrainEntranceBulletCleanAt ring N
      (ring.rightNeighbor e)) :
    (N e).sg = false := by
  obtain ⟨_, p, hSector, _, hTrail⟩ := hYClean
  have hNearest :=
    grantDrainDummyFollowerSectorNearestArc ring N p
      (ring.rightNeighbor e) hYFollower hSector
  have hPos : 1 ≤ PPL.cyclicOffset ring p
      (ring.rightNeighbor e) :=
    Nat.succ_le_of_lt hNearest.1
  have hBound :=
    grantDrainEntranceArcOffsetLt ring p (ring.rightNeighbor e)
  have hNeighbor :
      ring.rightNeighbor e = PPL.shiftRight ring e 1 := by
    apply Fin.ext
    rfl
  have hLeft :
      PPL.shiftLeft ring (ring.rightNeighbor e) 1 = e := by
    rw [hNeighbor]
    have hCancel :=
      grantDrainMarksArcShiftLeftRight ring e 1 1
        (by omega : 1 ≤ 1) (by omega : 1 < n)
    simpa [grantDrainWeakDeathShiftRightZero] using hCancel
  have hSite :
      e = PPL.shiftRight ring p
        (PPL.cyclicOffset ring p (ring.rightNeighbor e) - 1) := by
    have hs := grantDrainMarksArcLeftHostSite
      ring p (ring.rightNeighbor e)
      (PPL.cyclicOffset ring p (ring.rightNeighbor e))
      rfl hPos
    rw [hLeft] at hs
    exact hs
  have hOldZero :
      (N (PPL.shiftRight ring p
        (PPL.cyclicOffset ring p (ring.rightNeighbor e) - 1))).sg =
          false := by
    exact hTrail
      (⟨PPL.cyclicOffset ring p (ring.rightNeighbor e) - 1,
        (show PPL.cyclicOffset ring p (ring.rightNeighbor e) - 1 < n by omega)⟩ :
          Fin n)
      (show PPL.cyclicOffset ring p (ring.rightNeighbor e) - 1 ≤
        PPL.cyclicOffset ring p (ring.rightNeighbor e) by omega)
  rw [hSite] 
  exact hOldZero

/-- OLD responder Y is itself a clean follower DUMMY. Native E
preserves its nonempty bullet and zero signal, while its old
predecessor has zero signal by CleanAt. The literal no-FIRE branch
uses the stationary quiet-row theorem; F0/F2 births the
new nearest protected leader immediately before Y; F1 is blocked
by Y's nonempty post-E DUMMY. -/
theorem grantDrainDummyStationaryResponderFollowerCleanHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hYFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hYDummy :
      (s.native (ring.rightNeighbor e)).b = (1 : Fin 3))
    (hYClean : GrantDrainEntranceBulletCleanAt ring s.native
      (ring.rightNeighbor e)) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  have hDifferent : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hXQuiet :=
    grantDrainDummyCleanResponderSourceZero
      ring hn s.native e hYFollower hYClean
  have hYQuiet :=
    grantDrainDummyCleanOwnSignalZero
      ring s.native (ring.rightNeighbor e) hYClean
  have hYNotEmpty :
      (s.native (ring.rightNeighbor e)).b ≠
        (0 : Fin 3) := by
    rw [hYDummy]
    decide
  have hPair :=
    grantDrainDummyQuietFollowerNoTransferPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hXQuiet hYFollower hYQuiet (Or.inr hYNotEmpty)
  have hEYL :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false := by
    simpa [nativeE, hDifferent] using hPair.2.1.trans hYFollower
  have hEYB :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) := by
    have hEq :
        (certLiteralEPair
          (s.native e) (s.native (ring.rightNeighbor e))).2.b =
            (1 : Fin 3) :=
      hPair.2.2.2.1.trans hYDummy
    simpa [nativeE, hDifferent] using hEq
  have hEYS :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        false := by
    simpa [nativeE, hDifferent] using hPair.2.2.2.2.2
  have hYIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hEYB]
  have hNoFOne :
      grantDrainSelect ring s e ≠ .rightLocal :=
    grantDrainEntranceResponderIneligibleNoRightFire
      ring s e hYIneligible
  have hBirth :
      GrantDrainEntranceBulletCleanAt ring
        (canonicalBirth (nativeE ring s.native e) e)
        (ring.rightNeighbor e) := by
    exact grantDrainDummyAdjacentFollowerClean
      ring hn (canonicalBirth (nativeE ring s.native e) e) e
      (by simp [canonicalBirth, firedNative])
      (by simp [canonicalBirth, firedNative])
      (by simp [canonicalBirth, firedNative])
      (by simpa [canonicalBirth, hDifferent] using hEYL)
      (by simpa [canonicalBirth, hDifferent] using hEYB)
      (by simpa [canonicalBirth, hDifferent] using hEYS)
  cases hf : grantDrainSelect ring s e with
  | none =>
      exact grantDrainDummyStationaryQuietFollowerNoTransferClean
        ring hn fresh update s e (ring.rightNeighbor e)
        hDifferent hYClean hXQuiet hYFollower hYQuiet
        (Or.inr hYNotEmpty) hf
  | leftLocal =>
      change GrantDrainEntranceBulletCleanAt ring
        (grantDrainNativeNext ring s e) (ring.rightNeighbor e)
      simpa [grantDrainNativeNext, hf] using hBirth
  | rightLocal =>
      exact False.elim (hNoFOne hf)
  | cross =>
      change GrantDrainEntranceBulletCleanAt ring
        (grantDrainNativeNext ring s e) (ring.rightNeighbor e)
      simpa [grantDrainNativeNext, hf] using hBirth

/-- A clean follower has an EMPTY-BULLET preceding leader in
its own old sector. Thus the old clean DUMMY cannot coexist
with a resident leader DUMMY at that sector's root. -/
theorem grantDrainDummyCleanFollowerRootEmpty
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (p b : Fin n)
    (hFollower : (N b).l = false)
    (hSector : leaderSector ring N p b)
    (hClean : GrantDrainEntranceBulletCleanAt ring N b) :
    (N p).b = (0 : Fin 3) := by
  have hNearest :=
    grantDrainDummyFollowerSectorNearestArc
      ring N p b hFollower hSector
  have hEmpty :=
    grantDrainDummyCleanPrefixEmpty
      ring N p b hNearest hSector hClean 0 hNearest.1
  simpa [grantDrainWeakDeathShiftRightZero] using hEmpty

/-- The OLD ready leader Y cannot be the first leader of any
different clean follower DUMMY b in its sector: the clean zero
trail includes that ready leader itself. This eliminates the
only competing new DUMMY at Y in the stationary-clean case. -/
theorem grantDrainDummyReadyRootNotCleanFollower
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e b : Fin n)
    (hReady : GrantDrainDummyReadyResponder ring s e)
    (hSector :
      leaderSector ring s.native (ring.rightNeighbor e) b)
    (hClean : GrantDrainEntranceBulletCleanAt ring s.native b) :
    False := by
  have hTrail :=
    grantDrainDummyCleanTrailAtNearest
      ring s.native (ring.rightNeighbor e) b hClean hSector
  have hRootZero :
      (s.native (ring.rightNeighbor e)).sg = false := by
    have hz := hTrail
      (⟨0, (show 0 < n by omega)⟩ : Fin n) (Nat.zero_le _)
    simpa [grantDrainWeakDeathShiftRightZero] using hz
  have hReadySignal := hReady.2
  rw [hRootZero] at hReadySignal
  cases hReadySignal

/-- The resident responder DUMMY case is now complete, whether
the old responder was itself a leader or a follower. Its old
cleanliness rules out the ready flag when needed, and the actual
literal step preserves the clean DUMMY at the same host. -/
theorem grantDrainDummyStationaryResponderCleanHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hYDummy :
      (s.native (ring.rightNeighbor e)).b = (1 : Fin 3))
    (hYClean : GrantDrainEntranceBulletCleanAt
      ring s.native (ring.rightNeighbor e)) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) := by
  cases hl : (s.native (ring.rightNeighbor e)).l with
  | true =>
      exact grantDrainDummyStationaryLeaderCleanHolds
        ring hn fresh update s e (ring.rightNeighbor e)
        hP hNoBad hl hYDummy hYClean
        (grantDrainEntranceRightNeighborDistinct
          ring (by omega : 2 ≤ n) e)
  | false =>
      exact grantDrainDummyStationaryResponderFollowerCleanHolds
        ring hn fresh update s e hl hYDummy hYClean

/-- Exactly the moving and ready-responder conjuncts of the
original GrantDrainDummyCleanGeometry are fully discharged at
every PPlus / NoBadLive source cut. The stationary off-pair
follower clause is not made an implicit assumption. -/
theorem grantDrainDummyCleanGeometryMovingReadyHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) :
    ((s.native e).b = (1 : Fin 3) →
      (s.native (ring.rightNeighbor e)).l = false →
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) →
      GrantDrainEntranceBulletCleanAt ring s.native e →
      GrantDrainEntranceBulletCleanAt ring
        (grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)) ∧
    (GrantDrainDummyReadyResponder ring s e →
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = false →
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b = (1 : Fin 3) →
      GrantDrainEntranceBulletCleanAt ring
        (grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)) := by
  constructor
  · exact grantDrainDummyCleanGeometryMovedHolds
      ring hn fresh update s e
  · intro hReady hFollower hDummy
    exact grantDrainDummyReadyResponderCleanHolds
      ring hn fresh update s e hP hNoBad
      hReady hFollower hDummy

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainDummyLeaderDeathSourceSignalZero
#print axioms L3.GrantDrainEntrance.grantDrainDummyPostFollowerImpliesEDeath
#print axioms L3.GrantDrainEntrance.grantDrainDummySourceLeaderDeathClean
#print axioms L3.GrantDrainEntrance.grantDrainDummySourceFollowerDeathClean
#print axioms L3.GrantDrainEntrance.grantDrainDummyReadyResponderCleanHolds
#print axioms L3.GrantDrainEntrance.grantDrainDummyResidentLeaderDeathCleanHolds
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryLeaderCleanHolds
#print axioms L3.GrantDrainEntrance.grantDrainDummyCleanGeometryMovedHolds
#print axioms L3.GrantDrainEntrance.grantDrainDummyCleanResponderSourceZero
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryResponderFollowerCleanHolds
#print axioms L3.GrantDrainEntrance.grantDrainDummyCleanFollowerRootEmpty
#print axioms L3.GrantDrainEntrance.grantDrainDummyReadyRootNotCleanFollower
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryResponderCleanHolds
#print axioms L3.GrantDrainEntrance.grantDrainDummyCleanGeometryMovingReadyHolds

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- Local copy of the private GrantDrainMarks offset lemma. -/
theorem grantDrainEntranceArcOffsetShiftRight
    {n : Nat} (ring : DirectedRing n)
    (p : Fin n) (d : Nat) (hd : d < n) :
    PPL.cyclicOffset ring p (PPL.shiftRight ring p d) = d := by
  change (((p.val + d) % n + n - p.val) % n) = d
  by_cases hs : p.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have he : p.val + d + n - p.val = n + d := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hd]
  · have hge : n ≤ p.val + d := by omega
    have hlt : p.val + d - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have he : p.val + d - n + n - p.val = d := by omega
    rw [he, Nat.mod_eq_of_lt hd]


/-!
Source-level nearest-sector separation.
The stationary old clean follower DUMMY b has nearest old leader p,
strict prefix [p,b), and no old bullet or signal on this prefix.
The selected edge e -> y has three geometric positions:
  OUTSIDE: neither e nor y in [p,b): whole certificate framed.
  INTERIOR: e,y both in [p,b): E is exactly inert; none keeps the
    old certificate, and FIRE at e or y births a nearer empty leader.
  ROOT-INCOMING: y=p and e immediately precedes p: p can survive
    or be killed; its geometry must be spliced with the old e sector.
The following lemmas close the first two classes on the literal
native E/FIRE step, without a strong post-step assumption.
-/

/-- A clean stationary follower needs only its old nearest-source
prefix and host to be physically framed; it does not need the
entire ring's native leader array to be unchanged. -/
theorem grantDrainDummyFollowerCleanOfPrefixFrame
    {n : Nat}
    (ring : DirectedRing n)
    (N M : Fin n → CertNative) (p b : Fin n)
    (hOldFollower : (N b).l = false)
    (hOldSector : leaderSector ring N p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring N b)
    (hHostFrame : M b = N b)
    (hPrefixFrame :
      ∀ k : Nat, k < PPL.cyclicOffset ring p b →
        M (PPL.shiftRight ring p k) =
          N (PPL.shiftRight ring p k)) :
    GrantDrainEntranceBulletCleanAt ring M b := by
  have hOldNearest :=
    grantDrainDummyFollowerSectorNearestArc
      ring N p b hOldFollower hOldSector
  have hOldTrail :=
    grantDrainDummyCleanTrailAtNearest
      ring N p b hOldClean hOldSector
  have hOldEmpty :=
    grantDrainDummyCleanPrefixEmpty
      ring N p b hOldNearest hOldSector hOldClean
  have hNewBullet : HasBullet M b := by
    change (M b).b ≠ (0 : Fin 3)
    rw [hHostFrame]
    exact hOldClean.1
  have hNewFollower : (M b).l = false := by
    rw [hHostFrame]
    exact hOldFollower
  have hOldOwnZero : (N b).sg = false := by
    have hAt := hOldTrail
      (⟨PPL.cyclicOffset ring p b,
        (show PPL.cyclicOffset ring p b < n by
          exact grantDrainEntranceArcOffsetLt ring p b)⟩ : Fin n)
      (Nat.le_refl _)
    rw [grantDrainMarksArcShiftRightOffset ring p b] at hAt
    exact hAt
  have hNewOwnZero : (M b).sg = false := by
    rw [hHostFrame]
    exact hOldOwnZero
  have hNewNearest :
      GrantDrainMarksNearestArc ring M p b := by
    refine ⟨hOldNearest.1, ?_, ?_⟩
    · have hRoot := hPrefixFrame 0 hOldNearest.1
      rw [grantDrainWeakDeathShiftRightZero ring p] at hRoot
      rw [hRoot]
      exact hOldNearest.2.1
    · intro k hk hlt
      rw [hPrefixFrame k hlt]
      exact hOldNearest.2.2 k hk hlt
  have hNewZero :
      GrantDrainMarksZeroOffsetArc ring M p b := by
    intro k hk
    rw [hPrefixFrame k hk]
    exact hOldTrail
      (⟨k, (show k < n by
        exact Nat.lt_trans hk
          (grantDrainEntranceArcOffsetLt ring p b))⟩ : Fin n)
      (Nat.le_of_lt hk)
  have hNewEmpty :
      ∀ k : Nat, k < PPL.cyclicOffset ring p b →
        (M (PPL.shiftRight ring p k)).b = (0 : Fin 3) := by
    intro k hk
    rw [hPrefixFrame k hk]
    exact hOldEmpty k hk
  exact grantDrainDummyCleanFromNearestZeroNoBefore
    ring M p b hNewBullet hNewFollower
    hNewNearest hNewZero hNewOwnZero hNewEmpty

/-- If both selected sites lie outside the complete old prefix
and the old DUMMY host is not selected, native E and all possible
canonical FIRE overlays frame the relevant records. -/
theorem grantDrainDummyStationaryFollowerOutsideArcClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hOldFollower : (s.native b).l = false)
    (hOldSector : leaderSector ring s.native p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hNotE : b ≠ e)
    (hNotY : b ≠ ring.rightNeighbor e)
    (hOutside :
      ∀ k : Nat, k < PPL.cyclicOffset ring p b →
        PPL.shiftRight ring p k ≠ e ∧
        PPL.shiftRight ring p k ≠ ring.rightNeighbor e) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hHostFrame :
      (grantDrainStep ring fresh update s e).native b =
        s.native b :=
    grantDrainMarksNativeOutsidePairFrame
      ring s e b hNotE hNotY
  have hPrefixFrame :
      ∀ k : Nat, k < PPL.cyclicOffset ring p b →
        (grantDrainStep ring fresh update s e).native
          (PPL.shiftRight ring p k) =
        s.native (PPL.shiftRight ring p k) := by
    intro k hk
    exact grantDrainMarksNativeOutsidePairFrame
      ring s e (PPL.shiftRight ring p k)
      (hOutside k hk).1 (hOutside k hk).2
  exact grantDrainDummyFollowerCleanOfPrefixFrame
    ring s.native
    (grantDrainStep ring fresh update s e).native
    p b hOldFollower hOldSector hOldClean
    hHostFrame hPrefixFrame

/-- When both selected endpoints have empty bullets and zero
signals, and Y is a follower, the literal native E pair does
not change either complete native record. X may be a leader. -/
theorem grantDrainDummyEmptyQuietFollowerPairFixed
    (x y : CertNative)
    (hXEmpty : x.b = (0 : Fin 3))
    (hXZero : x.sg = false)
    (hYFollower : y.l = false)
    (hYEmpty : y.b = (0 : Fin 3))
    (hYZero : y.sg = false) :
    certLiteralEPair x y = (x, y) := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  change xb = (0 : Fin 3) at hXEmpty
  change xsg = false at hXZero
  change yl = false at hYFollower
  change yb = (0 : Fin 3) at hYEmpty
  change ysg = false at hYZero
  subst xb
  subst xsg
  subst yl
  subst yb
  subst ysg
  cases xl <;> cases xsh <;> cases ysh <;>
    simp [certLiteralEPair, certFinThree]

/-- Under that OLD empty/quiet selected pair, native E frames
the ENTIRE ring, not merely the old clean sector. The only
remaining physical modifications are the optional FIRE birth
at source or responder. -/
theorem grantDrainDummyEmptyQuietFollowerNativeEFixed
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hXEmpty : (N e).b = (0 : Fin 3))
    (hXZero : (N e).sg = false)
    (hYFollower : (N (ring.rightNeighbor e)).l = false)
    (hYEmpty : (N (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hYZero : (N (ring.rightNeighbor e)).sg = false) :
    nativeE ring N e = N := by
  have hPair :=
    grantDrainDummyEmptyQuietFollowerPairFixed
      (N e) (N (ring.rightNeighbor e))
      hXEmpty hXZero hYFollower hYEmpty hYZero
  have hDifferent : e ≠ ring.rightNeighbor e :=
    Ne.symm (grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e)
  funext i
  by_cases hi : i = e
  · subst i
    simp [nativeE, hPair]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp [nativeE, Ne.symm hDifferent, hPair]
    · simp [nativeE, hi, hj]

/-- Birth at ANY source z in the strict old clean prefix cuts
off the earlier root and leaves b clean: the newly born leader
has zero signal and no bullet, while all following old prefix
sites were empty/quiet and no closer leader is present. -/
theorem grantDrainDummyCleanBirthInsideOldPrefix
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (p b z : Fin n) (j : Nat)
    (hOldFollower : (N b).l = false)
    (hOldSector : leaderSector ring N p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring N b)
    (hSite : z = PPL.shiftRight ring p j)
    (hInside : j < PPL.cyclicOffset ring p b) :
    GrantDrainEntranceBulletCleanAt
      ring (canonicalBirth N z) b := by
  have hOldNearest :=
    grantDrainDummyFollowerSectorNearestArc
      ring N p b hOldFollower hOldSector
  have hOldTrail :=
    grantDrainDummyCleanTrailAtNearest
      ring N p b hOldClean hOldSector
  have hOldZero :
      GrantDrainMarksZeroOffsetArc ring N p b := by
    intro k hk
    exact hOldTrail
      (⟨k, (show k < n by
        exact Nat.lt_trans hk
          (grantDrainEntranceArcOffsetLt ring p b))⟩ : Fin n)
      (Nat.le_of_lt hk)
  have hOldEmpty :=
    grantDrainDummyCleanPrefixEmpty
      ring N p b hOldNearest hOldSector hOldClean
  obtain ⟨hNewNearest, hNewZero, _⟩ :=
    grantDrainWeakDeathProtectedArcBirth
      ring N p b z j hOldNearest hOldZero hSite hInside
  have hJBound : j < n :=
    Nat.lt_trans hInside (grantDrainEntranceArcOffsetLt ring p b)
  have hZNotB : b ≠ z := by
    intro heq
    have hoff := congrArg (PPL.cyclicOffset ring p) heq
    rw [hSite, grantDrainEntranceArcOffsetShiftRight
      ring p j hJBound] at hoff
    omega
  have hHostFrame : canonicalBirth N z b = N b :=
    grantDrainEntranceCanonicalBirthFrame N z b hZNotB
  have hNewBullet : HasBullet (canonicalBirth N z) b := by
    change (canonicalBirth N z b).b ≠ (0 : Fin 3)
    rw [hHostFrame]
    exact hOldClean.1
  have hNewFollower : (canonicalBirth N z b).l = false := by
    rw [hHostFrame]
    exact hOldFollower
  have hOldOwnZero : (N b).sg = false := by
    have hz := hOldTrail
      (⟨PPL.cyclicOffset ring p b,
        (show PPL.cyclicOffset ring p b < n by
          exact grantDrainEntranceArcOffsetLt ring p b)⟩ : Fin n)
      (Nat.le_refl _)
    rw [grantDrainMarksArcShiftRightOffset ring p b] at hz
    exact hz
  have hNewOwnZero :
      (canonicalBirth N z b).sg = false := by
    rw [hHostFrame]
    exact hOldOwnZero
  have hOffset :
      PPL.cyclicOffset ring z b =
        PPL.cyclicOffset ring p b - j := by
    rw [hSite]
    exact grantDrainMarksArcOffsetSubtract
      ring p b j (Nat.le_of_lt hInside)
  have hNewEmpty :
      ∀ k : Nat, k < PPL.cyclicOffset ring z b →
        (canonicalBirth N z
          (PPL.shiftRight ring z k)).b = (0 : Fin 3) := by
    intro k hk
    by_cases hkZero : k = 0
    · subst k
      rw [grantDrainWeakDeathShiftRightZero ring z]
      exact (grantDrainEntranceCanonicalBirthAtSite N z).2.1
    · have hPositive : 0 < k := by omega
      have hCombined : j + k < PPL.cyclicOffset ring p b := by
        rw [hOffset] at hk
        omega
      have hCombinedN : j + k < n :=
        Nat.lt_trans hCombined
          (grantDrainEntranceArcOffsetLt ring p b)
      have hNoSame :
          PPL.shiftRight ring p (j + k) ≠ z := by
        rw [hSite]
        exact grantDrainWeakDeathShiftRightNe
          ring p (j + k) j hCombinedN hJBound
          (by omega : j + k ≠ j)
      have hIndex :
          PPL.shiftRight ring z k =
            PPL.shiftRight ring p (j + k) := by
        rw [hSite]
        exact grantDrainWeakDeathShiftRightAdd ring p j k
      rw [hIndex]
      rw [grantDrainEntranceCanonicalBirthFrame
        N z (PPL.shiftRight ring p (j + k)) hNoSame]
      exact hOldEmpty (j + k) hCombined
  exact grantDrainDummyCleanFromNearestZeroNoBefore
    ring (canonicalBirth N z) z b
    hNewBullet hNewFollower hNewNearest hNewZero
    hNewOwnZero hNewEmpty

/-- Both endpoints strictly inside a clean follower DUMMY's old
prefix are empty and quiet. The literal E row is inert, and every
allowed FIRE outcome (F0/F2 at X or F1 at Y) is a clean nearer
root birth strictly before b. -/
theorem grantDrainDummyStationaryFollowerInteriorClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n) (t : Nat)
    (hOldFollower : (s.native b).l = false)
    (hOldSector : leaderSector ring s.native p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hSourceSite : e = PPL.shiftRight ring p t)
    (hTargetSite :
      ring.rightNeighbor e = PPL.shiftRight ring p (t + 1))
    (hSourceInside : t < PPL.cyclicOffset ring p b)
    (hTargetInside : t + 1 < PPL.cyclicOffset ring p b) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hOldNearest :=
    grantDrainDummyFollowerSectorNearestArc
      ring s.native p b hOldFollower hOldSector
  have hEmpty :=
    grantDrainDummyCleanPrefixEmpty
      ring s.native p b hOldNearest hOldSector hOldClean
  have hTrail :=
    grantDrainDummyCleanTrailAtNearest
      ring s.native p b hOldClean hOldSector
  have hOldXEmpty : (s.native e).b = (0 : Fin 3) := by
    rw [hSourceSite]
    exact hEmpty t hSourceInside
  have hOldYEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) := by
    rw [hTargetSite]
    exact hEmpty (t + 1) hTargetInside
  have hOldXZero : (s.native e).sg = false := by
    rw [hSourceSite]
    exact hTrail
      (⟨t, (show t < n by
        exact Nat.lt_trans hSourceInside
          (grantDrainEntranceArcOffsetLt ring p b))⟩ : Fin n)
      (Nat.le_of_lt hSourceInside)
  have hOldYZero :
      (s.native (ring.rightNeighbor e)).sg = false := by
    rw [hTargetSite]
    exact hTrail
      (⟨t + 1, (show t + 1 < n by
        exact Nat.lt_trans hTargetInside
          (grantDrainEntranceArcOffsetLt ring p b))⟩ : Fin n)
      (Nat.le_of_lt hTargetInside)
  have hOldYFollower :
      (s.native (ring.rightNeighbor e)).l = false := by
    rw [hTargetSite]
    exact hOldNearest.2.2 (t + 1)
      (by omega : 0 < t + 1) hTargetInside
  have hNativeE :
      nativeE ring s.native e = s.native :=
    grantDrainDummyEmptyQuietFollowerNativeEFixed
      ring hn s.native e hOldXEmpty hOldXZero
      hOldYFollower hOldYEmpty hOldYZero
  have hBirthX :
      GrantDrainEntranceBulletCleanAt ring
        (canonicalBirth s.native e) b :=
    grantDrainDummyCleanBirthInsideOldPrefix
      ring s.native p b e t hOldFollower
      hOldSector hOldClean hSourceSite hSourceInside
  have hBirthY :
      GrantDrainEntranceBulletCleanAt ring
        (canonicalBirth s.native (ring.rightNeighbor e)) b :=
    grantDrainDummyCleanBirthInsideOldPrefix
      ring s.native p b (ring.rightNeighbor e) (t + 1)
      hOldFollower hOldSector hOldClean hTargetSite hTargetInside
  change GrantDrainEntranceBulletCleanAt ring
    (grantDrainNativeNext ring s e) b
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf, hNativeE] using hOldClean
  | leftLocal =>
      simpa [grantDrainNativeNext, hf, hNativeE] using hBirthX
  | rightLocal =>
      simpa [grantDrainNativeNext, hf, hNativeE] using hBirthY
  | cross =>
      simpa [grantDrainNativeNext, hf, hNativeE] using hBirthX

/-- All stationary clean follower cases EXCEPT the incoming edge to
their OLD protected root p. For p != rightNeighbor e, either both
pair sites are interior to the bullet-free old prefix or neither
is. The former has exact inert E and all-FIRE closer-birth closure;
the latter frames the full old clean sector. -/
theorem grantDrainDummyStationaryFollowerAwayFromRootClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hOldFollower : (s.native b).l = false)
    (hOldSector : leaderSector ring s.native p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hNotSource : b ≠ e)
    (hNotResponder : b ≠ ring.rightNeighbor e)
    (hNotRootIncoming : p ≠ ring.rightNeighbor e) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hOffsetStep :=
    grantDrainDummySourceSuccessorOffset
      ring e p hNotRootIncoming
  have hDistanceLt :=
    grantDrainEntranceArcOffsetLt ring p b
  have hOldNearest :=
    grantDrainDummyFollowerSectorNearestArc
      ring s.native p b hOldFollower hOldSector
  by_cases hInside :
      PPL.cyclicOffset ring p e < PPL.cyclicOffset ring p b
  · have hStepBound :
        PPL.cyclicOffset ring p e + 1 <
          PPL.cyclicOffset ring p b := by
      have hAtY :
          ring.rightNeighbor e =
            PPL.shiftRight ring p
              (PPL.cyclicOffset ring p e + 1) := by
        calc
          ring.rightNeighbor e =
              PPL.shiftRight ring p
                (PPL.cyclicOffset ring p (ring.rightNeighbor e)) :=
            (grantDrainMarksArcShiftRightOffset
              ring p (ring.rightNeighbor e)).symm
          _ = PPL.shiftRight ring p
                (PPL.cyclicOffset ring p e + 1) := by
              rw [hOffsetStep]
      have hCannotEqual :
          PPL.cyclicOffset ring p e + 1 ≠
            PPL.cyclicOffset ring p b := by
        intro hEqual
        have hSite :
            ring.rightNeighbor e = b := by
          rw [hEqual, grantDrainMarksArcShiftRightOffset ring p b]
            at hAtY
          exact hAtY
        exact hNotResponder hSite.symm
      omega
    have hXSite :
        e = PPL.shiftRight ring p
          (PPL.cyclicOffset ring p e) :=
      (grantDrainMarksArcShiftRightOffset ring p e).symm
    have hYSite :
        ring.rightNeighbor e = PPL.shiftRight ring p
          (PPL.cyclicOffset ring p e + 1) := by
      calc
        ring.rightNeighbor e =
            PPL.shiftRight ring p
              (PPL.cyclicOffset ring p (ring.rightNeighbor e)) :=
          (grantDrainMarksArcShiftRightOffset
            ring p (ring.rightNeighbor e)).symm
        _ = PPL.shiftRight ring p
              (PPL.cyclicOffset ring p e + 1) := by
          rw [hOffsetStep]
    exact grantDrainDummyStationaryFollowerInteriorClean
      ring hn fresh update s e p b
      (PPL.cyclicOffset ring p e)
      hOldFollower hOldSector hOldClean
      hXSite hYSite hInside hStepBound
  · have hOutside :
        ∀ k : Nat, k < PPL.cyclicOffset ring p b →
          PPL.shiftRight ring p k ≠ e ∧
          PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
      intro k hk
      have hkN : k < n :=
        Nat.lt_trans hk hDistanceLt
      constructor
      · intro he
        have hOffset := congrArg (PPL.cyclicOffset ring p) he
        rw [grantDrainWeakDeathOffsetShiftRight ring p k hkN]
          at hOffset
        omega
      · intro hy
        have hOffset := congrArg (PPL.cyclicOffset ring p) hy
        rw [grantDrainWeakDeathOffsetShiftRight ring p k hkN,
          hOffsetStep] at hOffset
        omega
    exact grantDrainDummyStationaryFollowerOutsideArcClean
      ring hn fresh update s e p b hOldFollower
      hOldSector hOldClean hNotSource hNotResponder hOutside

/-- A birth or a native E rewrite AT the OLD nearest leader is
harmless to a stationary clean follower as long as the root stays
empty, quiet and a leader. The entire strict suffix of the old
prefix is framed; the old root's other native fields may change. -/
theorem grantDrainDummyFollowerCleanOfRootTailFrame
    {n : Nat}
    (ring : DirectedRing n)
    (N M : Fin n → CertNative) (p b : Fin n)
    (hOldFollower : (N b).l = false)
    (hOldSector : leaderSector ring N p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring N b)
    (hHostFrame : M b = N b)
    (hRootLeader : (M p).l = true)
    (hRootEmpty : (M p).b = (0 : Fin 3))
    (hRootZero : (M p).sg = false)
    (hTailFrame :
      ∀ k : Nat, 0 < k →
        k < PPL.cyclicOffset ring p b →
        M (PPL.shiftRight ring p k) =
          N (PPL.shiftRight ring p k)) :
    GrantDrainEntranceBulletCleanAt ring M b := by
  have hOldNearest :=
    grantDrainDummyFollowerSectorNearestArc
      ring N p b hOldFollower hOldSector
  have hOldTrail :=
    grantDrainDummyCleanTrailAtNearest
      ring N p b hOldClean hOldSector
  have hOldEmpty :=
    grantDrainDummyCleanPrefixEmpty
      ring N p b hOldNearest hOldSector hOldClean
  have hOwnZero : (M b).sg = false := by
    rw [hHostFrame]
    have hh := hOldTrail
      (⟨PPL.cyclicOffset ring p b,
        (show PPL.cyclicOffset ring p b < n by
          exact grantDrainEntranceArcOffsetLt ring p b)⟩ : Fin n)
      (Nat.le_refl _)
    rw [grantDrainMarksArcShiftRightOffset ring p b] at hh
    exact hh
  have hBullet : HasBullet M b := by
    change (M b).b ≠ (0 : Fin 3)
    rw [hHostFrame]
    exact hOldClean.1
  have hFollower : (M b).l = false := by
    rw [hHostFrame]
    exact hOldFollower
  have hNewNearest :
      GrantDrainMarksNearestArc ring M p b := by
    refine ⟨hOldNearest.1, hRootLeader, ?_⟩
    intro k hk hlt
    rw [hTailFrame k hk hlt]
    exact hOldNearest.2.2 k hk hlt
  have hNewZero :
      GrantDrainMarksZeroOffsetArc ring M p b := by
    intro k hk
    by_cases hkZero : k = 0
    · subst k
      rw [grantDrainWeakDeathShiftRightZero ring p]
      exact hRootZero
    · have hkPositive : 0 < k := by omega
      rw [hTailFrame k hkPositive hk]
      exact hOldTrail
        (⟨k, (show k < n by
          exact Nat.lt_trans hk
            (grantDrainEntranceArcOffsetLt ring p b))⟩ : Fin n)
        (Nat.le_of_lt hk)
  have hNewEmpty :
      ∀ k : Nat, k < PPL.cyclicOffset ring p b →
        (M (PPL.shiftRight ring p k)).b = (0 : Fin 3) := by
    intro k hk
    by_cases hkZero : k = 0
    · subst k
      rw [grantDrainWeakDeathShiftRightZero ring p]
      exact hRootEmpty
    · rw [hTailFrame k (by omega : 0 < k) hk]
      exact hOldEmpty k hk
  exact grantDrainDummyCleanFromNearestZeroNoBefore
    ring M p b hBullet hFollower hNewNearest
    hNewZero hOwnZero hNewEmpty

/-- On the edge entering the protected old nearest root p, the
old clean follower host b and every STRICTLY later prefix site
are unaffected, including all four actual FIRE choices. -/
theorem grantDrainDummyIncomingRootTailFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p b : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (hOldFollower : (s.native b).l = false)
    (hOldSector : leaderSector ring s.native p b)
    (hNotSource : b ≠ e) :
    (grantDrainStep ring fresh update s e).native b =
      s.native b ∧
    (∀ k : Nat, 0 < k →
      k < PPL.cyclicOffset ring p b →
      (grantDrainStep ring fresh update s e).native
        (PPL.shiftRight ring p k) =
      s.native (PPL.shiftRight ring p k)) := by
  have hbNotRoot : b ≠ p := by
    intro hb
    rw [hb, hOldSector.1] at hOldFollower
    cases hOldFollower
  have hHostFrame :
      (grantDrainStep ring fresh update s e).native b =
        s.native b := by
    exact grantDrainMarksNativeOutsidePairFrame
      ring s e b hNotSource
      (by rw [hIncoming]; exact hbNotRoot)
  refine ⟨hHostFrame, ?_⟩
  intro k hk hklt
  change grantDrainNativeNext ring s e
    (PPL.shiftRight ring p k) =
      s.native (PPL.shiftRight ring p k)
  exact grantDrainMarksIncomingSourceInteriorFrame
    (by omega : 3 ≤ n) ring s p b e
    hIncoming k hk hklt

/-- The old quiet empty leader root p either remains a leader
or is re-born as a leader. In both cases its final bullet is
empty and its signal is zero. The old clean sector's interior
is untouched, so any such final leader continues to protect
the stationary clean follower DUMMY at b. -/
theorem grantDrainDummyStationaryIncomingRootSurvivingClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (hOldFollower : (s.native b).l = false)
    (hOldSector : leaderSector ring s.native p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hNotSource : b ≠ e)
    (hNewRootLeader :
      ((grantDrainStep ring fresh update s e).native p).l =
        true) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hOldPLeader : (s.native p).l = true := hOldSector.1
  have hOldPZero : (s.native p).sg = false := by
    have hTrail :=
      grantDrainDummyCleanTrailAtNearest
        ring s.native p b hOldClean hOldSector
    have hZero := hTrail
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      (Nat.zero_le _)
    simpa [grantDrainWeakDeathShiftRightZero ring p] using hZero
  have hOldPEmpty : (s.native p).b = (0 : Fin 3) :=
    grantDrainDummyCleanFollowerRootEmpty
      ring s.native p b hOldFollower hOldSector hOldClean
  have hEYBullet :
      (nativeE ring s.native e p).b = (0 : Fin 3) := by
    have hRow :=
      grantDrainEntranceNativeEQuietVictimBulletRetained
        ring (by omega : 2 ≤ n) s.native e
        (by rw [hIncoming]; exact hOldPLeader)
        (by rw [hIncoming]; exact hOldPZero)
    rw [hIncoming] at hRow
    exact hRow.trans hOldPEmpty
  have hPostEmpty :
      ((grantDrainStep ring fresh update s e).native p).b =
        (0 : Fin 3) := by
    change (grantDrainNativeNext ring s e p).b =
      (0 : Fin 3)
    have hDifferent : e ≠ p := by
      rw [← hIncoming]
      exact Ne.symm (grantDrainEntranceRightNeighborDistinct
        ring (by omega : 2 ≤ n) e)
    cases hf : grantDrainSelect ring s e with
    | none =>
        simpa [grantDrainNativeNext, hf] using hEYBullet
    | leftLocal =>
        simpa [grantDrainNativeNext, hf,
          canonicalBirth, Ne.symm hDifferent] using hEYBullet
    | rightLocal =>
        simp [grantDrainNativeNext, hf, canonicalBirth, firedNative, hIncoming]
    | cross =>
        simpa [grantDrainNativeNext, hf,
          canonicalBirth, Ne.symm hDifferent] using hEYBullet
  have hPostZero :
      ((grantDrainStep ring fresh update s e).native p).sg =
        false := by
    rw [← hIncoming]
    exact grantDrainDummyOldLeaderResponderSignalZero
      ring hn fresh update s e
      (by rw [hIncoming]; exact hOldPLeader)
  obtain ⟨hFrameB, hTail⟩ :=
    grantDrainDummyIncomingRootTailFrame
      ring hn fresh update s e p b
      hIncoming hOldFollower hOldSector hNotSource
  exact grantDrainDummyFollowerCleanOfRootTailFrame
    ring s.native
    (grantDrainStep ring fresh update s e).native
    p b hOldFollower hOldSector hOldClean
    hFrameB hNewRootLeader hPostEmpty hPostZero hTail

/-- The only canonical birth that can affect the responder's
leader bit is F1, and it makes that bit TRUE. Therefore a final
follower at Y was already a follower after native E. -/
theorem grantDrainDummyFinalResponderFollowerWasPostE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFinalFollower :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = false) :
    (nativeE ring s.native e (ring.rightNeighbor e)).l =
      false := by
  have hDifferent : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  change
    (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l =
      false at hFinalFollower
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hFinalFollower
  | leftLocal =>
      simpa [grantDrainNativeNext, hf,
        canonicalBirth, hDifferent] using hFinalFollower
  | rightLocal =>
      have hContr : true = false := by
        simpa [grantDrainNativeNext, hf,
          canonicalBirth, firedNative] using hFinalFollower
      cases hContr
  | cross =>
      simpa [grantDrainNativeNext, hf,
        canonicalBirth, hDifferent] using hFinalFollower

/-- Extending an old clean root-to-host sector ONE place
counterclockwise is safe when its old leader p is killed and
becomes an empty zero-signal follower, and the preceding
site e becomes an empty quiet leader. The new bullet-free
prefix has length oldDistance + 1. No PPlus or I hypothesis
is needed for this local geometric construction. -/
theorem grantDrainDummyCleanOfPredecessorLeaderExtension
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (N M : Fin n → CertNative)
    (e p b : Fin n)
    (hEdge : ring.rightNeighbor e = p)
    (hOldFollower : (N b).l = false)
    (hOldSector : leaderSector ring N p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring N b)
    (hNotSource : b ≠ e)
    (hHostFrame : M b = N b)
    (hNewRootLeader : (M e).l = true)
    (hNewRootEmpty : (M e).b = (0 : Fin 3))
    (hNewRootZero : (M e).sg = false)
    (hOldRootDead : (M p).l = false)
    (hOldRootEmpty : (M p).b = (0 : Fin 3))
    (hOldRootZero : (M p).sg = false)
    (hTailFrame :
      ∀ k : Nat, 0 < k →
        k < PPL.cyclicOffset ring p b →
        M (PPL.shiftRight ring p k) =
          N (PPL.shiftRight ring p k)) :
    GrantDrainEntranceBulletCleanAt ring M b := by
  have hOldNearest :=
    grantDrainDummyFollowerSectorNearestArc
      ring N p b hOldFollower hOldSector
  have hOldTrail :=
    grantDrainDummyCleanTrailAtNearest
      ring N p b hOldClean hOldSector
  have hOldEmpty :=
    grantDrainDummyCleanPrefixEmpty
      ring N p b hOldNearest hOldSector hOldClean
  have hOldDistBound :=
    grantDrainEntranceArcOffsetLt ring p b
  have hStepSite :
      PPL.shiftRight ring e
        (PPL.cyclicOffset ring p b + 1) =
          PPL.shiftRight ring p
            (PPL.cyclicOffset ring p b) := by
    rw [grantDrainWeakDeathRightShiftSucc
      ring e (PPL.cyclicOffset ring p b), hEdge]
  have hSiteB :
      b = PPL.shiftRight ring e
        (PPL.cyclicOffset ring p b + 1) := by
    calc
      b = PPL.shiftRight ring p
            (PPL.cyclicOffset ring p b) :=
        (grantDrainMarksArcShiftRightOffset ring p b).symm
      _ = PPL.shiftRight ring e
            (PPL.cyclicOffset ring p b + 1) := hStepSite.symm
  have hNewDistBound :
      PPL.cyclicOffset ring p b + 1 < n := by
    by_cases hLt : PPL.cyclicOffset ring p b + 1 < n
    · exact hLt
    · have hEq : PPL.cyclicOffset ring p b + 1 = n := by
        omega
      have hBEqualsE : b = e := by
        rw [hEq, grantDrainMarksFullRotation ring e] at hSiteB
        exact hSiteB
      exact False.elim (hNotSource hBEqualsE)
  have hNewDistance :
      PPL.cyclicOffset ring e b =
        PPL.cyclicOffset ring p b + 1 := by
    calc
      PPL.cyclicOffset ring e b =
          PPL.cyclicOffset ring e
            (PPL.shiftRight ring e
              (PPL.cyclicOffset ring p b + 1)) :=
        congrArg (PPL.cyclicOffset ring e) hSiteB
      _ = PPL.cyclicOffset ring p b + 1 :=
        grantDrainWeakDeathOffsetShiftRight
          ring e (PPL.cyclicOffset ring p b + 1) hNewDistBound
  have hShift :
      ∀ k : Nat, 1 ≤ k →
        PPL.shiftRight ring e k =
          PPL.shiftRight ring p (k - 1) := by
    intro k hk
    have hDecompose : k = k - 1 + 1 := by omega
    calc
      PPL.shiftRight ring e k =
          PPL.shiftRight ring e (k - 1 + 1) :=
        congrArg (PPL.shiftRight ring e) hDecompose
      _ = PPL.shiftRight ring (ring.rightNeighbor e) (k - 1) :=
        grantDrainWeakDeathRightShiftSucc ring e (k - 1)
      _ = PPL.shiftRight ring p (k - 1) := by rw [hEdge]
  have hNewBullet : HasBullet M b := by
    change (M b).b ≠ (0 : Fin 3)
    rw [hHostFrame]
    exact hOldClean.1
  have hNewFollower : (M b).l = false := by
    rw [hHostFrame]
    exact hOldFollower
  have hNewOwnZero : (M b).sg = false := by
    rw [hHostFrame]
    have hOldOwn := hOldTrail
      (⟨PPL.cyclicOffset ring p b,
        (show PPL.cyclicOffset ring p b < n by
          exact hOldDistBound)⟩ : Fin n)
      (Nat.le_refl _)
    rw [grantDrainMarksArcShiftRightOffset ring p b] at hOldOwn
    exact hOldOwn
  have hNewNearest :
      GrantDrainMarksNearestArc ring M e b := by
    refine ⟨?_, hNewRootLeader, ?_⟩
    · rw [hNewDistance]
      omega
    · intro k hk hklt
      have hkRange : k - 1 < PPL.cyclicOffset ring p b := by
        rw [hNewDistance] at hklt
        omega
      rw [hShift k (by omega : 1 ≤ k)]
      by_cases hkAtRoot : k = 1
      · subst k
        simpa [grantDrainWeakDeathShiftRightZero ring p]
          using hOldRootDead
      · have hkInterior : 0 < k - 1 := by omega
        rw [hTailFrame (k - 1) hkInterior hkRange]
        exact hOldNearest.2.2 (k - 1) hkInterior hkRange
  have hNewZero :
      GrantDrainMarksZeroOffsetArc ring M e b := by
    intro k hk
    by_cases hkAtE : k = 0
    · subst k
      rw [grantDrainWeakDeathShiftRightZero ring e]
      exact hNewRootZero
    · have hkPos : 1 ≤ k := by omega
      have hkRange : k - 1 < PPL.cyclicOffset ring p b := by
        rw [hNewDistance] at hk
        omega
      rw [hShift k hkPos]
      by_cases hkAtP : k = 1
      · subst k
        simpa [grantDrainWeakDeathShiftRightZero ring p]
          using hOldRootZero
      · have hkInterior : 0 < k - 1 := by omega
        rw [hTailFrame (k - 1) hkInterior hkRange]
        exact hOldTrail
          (⟨k - 1, (show k - 1 < n by
            exact Nat.lt_trans hkRange hOldDistBound)⟩ : Fin n)
          (Nat.le_of_lt hkRange)
  have hNewEmpty :
      ∀ k : Nat, k < PPL.cyclicOffset ring e b →
        (M (PPL.shiftRight ring e k)).b =
          (0 : Fin 3) := by
    intro k hk
    by_cases hkAtE : k = 0
    · subst k
      rw [grantDrainWeakDeathShiftRightZero ring e]
      exact hNewRootEmpty
    · have hkPos : 1 ≤ k := by omega
      have hkRange : k - 1 < PPL.cyclicOffset ring p b := by
        rw [hNewDistance] at hk
        omega
      rw [hShift k hkPos]
      by_cases hkAtP : k = 1
      · subst k
        simpa [grantDrainWeakDeathShiftRightZero ring p]
          using hOldRootEmpty
      · have hkInterior : 0 < k - 1 := by omega
        rw [hTailFrame (k - 1) hkInterior hkRange]
        exact hOldEmpty (k - 1) hkRange
  exact grantDrainDummyCleanFromNearestZeroNoBefore
    ring M e b hNewBullet hNewFollower
    hNewNearest hNewZero hNewOwnZero hNewEmpty

/-- If an OLD leader at the initiator kills the old quiet,
empty-bullet nearest root at the responder, and the responder
is still a follower after the literal step, no FIRE can occur:
F0/F2 are source-ineligible and F1 would restore a leader at Y.
The initiator is the new nearest empty, quiet leader of b. -/
theorem grantDrainDummyStationaryIncomingRootLeaderDeathClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p b : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (hOldSourceLeader : (s.native e).l = true)
    (hOldFollower : (s.native b).l = false)
    (hOldSector : leaderSector ring s.native p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hNotSource : b ≠ e)
    (hPostRootFollower :
      ((grantDrainStep ring fresh update s e).native p).l =
        false) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hOldPLeader : (s.native p).l = true := hOldSector.1
  have hOldPZero : (s.native p).sg = false := by
    have hTrail :=
      grantDrainDummyCleanTrailAtNearest
        ring s.native p b hOldClean hOldSector
    have hz := hTrail
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      (Nat.zero_le _)
    simpa [grantDrainWeakDeathShiftRightZero ring p] using hz
  have hOldPEmpty : (s.native p).b = (0 : Fin 3) :=
    grantDrainDummyCleanFollowerRootEmpty
      ring s.native p b hOldFollower hOldSector hOldClean
  have hEDeath : (nativeE ring s.native e p).l =
      false := by
    rw [← hIncoming]
    exact grantDrainDummyFinalResponderFollowerWasPostE
      ring hn fresh update s e
      (by rw [hIncoming]; exact hPostRootFollower)
  have hELeader :
      (nativeE ring s.native e e).l = true := by
    rw [grantDrainMarksNativeESource,
      grantDrainMarksOutgoingSourceLeaderNative]
    exact hOldSourceLeader
  have hYEmpty :
      (nativeE ring s.native e p).b = (0 : Fin 3) := by
    have hh :=
      grantDrainEntranceNativeEQuietVictimBulletRetained
        ring (by omega : 2 ≤ n) s.native e
        (by rw [hIncoming]; exact hOldPLeader)
        (by rw [hIncoming]; exact hOldPZero)
    rw [hIncoming] at hh
    exact hh.trans hOldPEmpty
  have hYZero :
      (nativeE ring s.native e p).sg = false := by
    have hh := (grantDrainEntranceNativeELeaderBulletAfter
      ring (by omega : 2 ≤ n) s.native e
      (by rw [hIncoming]; exact hOldPLeader)).2
    rw [hIncoming] at hh
    exact hh
  have hXEmpty :
      (nativeE ring s.native e e).b = (0 : Fin 3) :=
    grantDrainEntranceNativeESourceBulletZero ring s.native e
  have hDifferent : e ≠ p := by
    rw [← hIncoming]
    exact Ne.symm (grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e)
  have hPairDeath :
      (certLiteralEPair
        (s.native e) (s.native (ring.rightNeighbor e))).2.l =
          false := by
    have hh := hEDeath
    rw [← hIncoming] at hh
    have hDistinctY : ring.rightNeighbor e ≠ e :=
      grantDrainEntranceRightNeighborDistinct
        ring (by omega : 2 ≤ n) e
    simpa [nativeE, hDistinctY] using hh
  have hXZero :
      (nativeE ring s.native e e).sg = false := by
    rw [grantDrainMarksNativeESource]
    exact grantDrainDummyLeaderDeathSourceSignalZero
      (s.native e) (s.native (ring.rightNeighbor e))
      hOldSourceLeader
      (by rw [hIncoming]; exact hOldPLeader)
      hPairDeath
  have hSelector :=
    grantDrainMarksOutgoingLeaderSelector
      ring s e hOldSourceLeader
  have hNoFire : grantDrainSelect ring s e = .none := by
    cases hSelector with
    | inl hh =>
        exact hh
    | inr hh =>
        have hImpossible :
            ((grantDrainStep ring fresh update s e).native p).l =
              true := by
          change (grantDrainNativeNext ring s e p).l = true
          rw [← hIncoming]
          simp [grantDrainNativeNext, hh, canonicalBirth, firedNative]
        rw [hPostRootFollower] at hImpossible
        cases hImpossible
  have hPhysical :
      (grantDrainStep ring fresh update s e).native =
        nativeE ring s.native e := by
    change grantDrainNativeNext ring s e =
      nativeE ring s.native e
    simp [grantDrainNativeNext, hNoFire]
  have hPostEHostFrame :
      (nativeE ring s.native e) b = s.native b := by
    have hbNeP : b ≠ p := by
      intro hb
      rw [hb, hOldPLeader] at hOldFollower
      cases hOldFollower
    exact grantDrainEntranceNativeEFrame
      ring s.native e b hNotSource
      (by rw [hIncoming]; exact hbNeP)
  have hPostETail :
      ∀ k : Nat, 0 < k →
        k < PPL.cyclicOffset ring p b →
        nativeE ring s.native e
          (PPL.shiftRight ring p k) =
        s.native (PPL.shiftRight ring p k) := by
    intro k hk hklt
    exact grantDrainWeakDeathRightInteriorEFrame
      ring hn s e p b hIncoming k hk hklt
  rw [hPhysical]
  exact grantDrainDummyCleanOfPredecessorLeaderExtension
    ring hn s.native (nativeE ring s.native e)
    e p b hIncoming hOldFollower hOldSector hOldClean
    hNotSource hPostEHostFrame
    hELeader hXEmpty hXZero hEDeath hYEmpty hYZero
    hPostETail

/-- When the old nearest clean root p dies on e -> p and the
old initiator was a follower, the literal death row forces an
OLD LIVE at e. PPlus and NoBadLive give that LIVE's original
clean preceding sector; the fatal-victim all-FIRE row
splices it with the clean old p..b sector. -/
theorem grantDrainDummyStationaryIncomingRootFollowerDeathClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hIncoming : ring.rightNeighbor e = p)
    (hOldSourceFollower : (s.native e).l = false)
    (hOldFollower : (s.native b).l = false)
    (hOldDummy : (s.native b).b = (1 : Fin 3))
    (hOldSector : leaderSector ring s.native p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hNotSource : b ≠ e)
    (hNewRootFollower :
      ((grantDrainStep ring fresh update s e).native p).l =
        false) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hEDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false := by
    exact grantDrainDummyFinalResponderFollowerWasPostE
      ring hn fresh update s e
      (by rw [hIncoming]; exact hNewRootFollower)
  have hOldLeader :
      (s.native (ring.rightNeighbor e)).l = true := by
    rw [hIncoming]
    exact hOldSector.1
  have hLive : LiveBullet s.native e :=
    grantDrainWeakDeathFollowerMustBeLive
      ring hn s.native e
      hOldSourceFollower hOldLeader hEDeath
  have hCleanE :
      GrantDrainEntranceBulletCleanAt ring s.native e :=
    grantDrainDummyLiveCleanOfNoBad
      ring s.native hP hNoBad e hLive
  obtain ⟨_, q, hSectorE, _, _⟩ := hCleanE
  have hSectorB :
      leaderSector ring s.native (ring.rightNeighbor e) b := by
    rw [hIncoming]
    exact hOldSector
  exact grantDrainDummyStationaryFatalFollowerVictimClean
    ring hn fresh update s e q b
    hP hNoBad hOldSourceFollower hOldLeader hEDeath
    hOldFollower hNotSource hOldDummy hOldClean
    hSectorE hSectorB

/-- Complete incoming-to-old-root edge, with no assumed
post-sector geometry. A surviving or re-born responder leader
preserves the old root and suffix; if the responder dies, an OLD
leader initiator becomes the adjacent predecessor root, whereas
an OLD follower initiator is a PPlus/NoBadLive clean LIVE killer. -/
theorem grantDrainDummyStationaryFollowerIncomingRootClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hIncoming : ring.rightNeighbor e = p)
    (hOldFollower : (s.native b).l = false)
    (hOldDummy : (s.native b).b = (1 : Fin 3))
    (hOldSector : leaderSector ring s.native p b)
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hNotSource : b ≠ e) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  cases hNewP : ((grantDrainStep ring fresh update s e).native p).l with
  | true =>
      exact grantDrainDummyStationaryIncomingRootSurvivingClean
        ring hn fresh update s e p b hIncoming
        hOldFollower hOldSector hOldClean hNotSource hNewP
  | false =>
      cases hOldX : (s.native e).l with
      | true =>
          exact grantDrainDummyStationaryIncomingRootLeaderDeathClean
            ring hn fresh update s e p b
            hIncoming hOldX hOldFollower hOldSector
            hOldClean hNotSource hNewP
      | false =>
          exact grantDrainDummyStationaryIncomingRootFollowerDeathClean
            ring hn fresh update s e p b
            hP hNoBad hIncoming hOldX
            hOldFollower hOldDummy hOldSector hOldClean
            hNotSource hNewP

/-- All remaining stationary old clean follower DUMMY identities
away from both interacting sites remain clean. Their OLD nearest
root p either is the selected responder (the incoming-root
classification) or is not (interior-pair or completely framed).
Every FIRE is handled by a real native birth or the
fatal-follower victim row. -/
theorem grantDrainDummyStationaryFollowerOffPairCleanHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e b : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hOldFollower : (s.native b).l = false)
    (hOldDummy : (s.native b).b = (1 : Fin 3))
    (hOldClean : GrantDrainEntranceBulletCleanAt ring s.native b)
    (hNotSource : b ≠ e)
    (hNotResponder : b ≠ ring.rightNeighbor e) :
    GrantDrainEntranceBulletCleanAt ring
      (grantDrainStep ring fresh update s e).native b := by
  have hOldCert := hOldClean
  obtain ⟨_, p, hOldSector, _, _⟩ := hOldCert
  by_cases hAtRoot : p = ring.rightNeighbor e
  · exact grantDrainDummyStationaryFollowerIncomingRootClean
      ring hn fresh update s e p b hP hNoBad
      hAtRoot.symm hOldFollower hOldDummy
      hOldSector hOldClean hNotSource
  · exact grantDrainDummyStationaryFollowerAwayFromRootClean
      ring hn fresh update s e p b
      hOldFollower hOldSector hOldClean hNotSource
      hNotResponder hAtRoot

/-- Source-level complete clean-DUMMY geometry at EVERY literal
E+FIRE edge under PPlus and absence of paper-bad LIVE. The
stationary follower case is closed by strict nearest-sector
partition; the previously moving and ready responder
clauses are reused unchanged. -/
theorem grantDrainDummyCleanGeometryHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) :
    GrantDrainDummyCleanGeometry ring fresh update s e := by
  have hMovingReady :=
    grantDrainDummyCleanGeometryMovingReadyHolds
      ring hn fresh update s e hP hNoBad
  refine ⟨?_, hMovingReady.1, hMovingReady.2⟩
  intro b hNotSource hNotReady hOldDummy hOldClean
  by_cases hAtResponder : b = ring.rightNeighbor e
  · subst b
    exact grantDrainDummyStationaryResponderCleanHolds
      ring hn fresh update s e hP hNoBad
      hOldDummy hOldClean
  · cases hOldLeader : (s.native b).l with
    | true =>
        exact grantDrainDummyStationaryLeaderCleanHolds
          ring hn fresh update s e b hP hNoBad
          hOldLeader hOldDummy hOldClean hNotSource
    | false =>
        exact grantDrainDummyStationaryFollowerOffPairCleanHolds
          ring hn fresh update s e b hP hNoBad
          hOldLeader hOldDummy hOldClean
          hNotSource hAtResponder

/-- The genuine universal DUMMY-edge origin now follows from
the complete clean geometry for this very same literal
grantDrainStep, with no hypothetical transition or leaf. -/
theorem grantDrainDummyEdgeOriginHolds
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) :
    GrantDrainDummyEdgeOrigin ring fresh update s e := by
  exact grantDrainDummyEdgeOriginOfCleanGeometry
    ring hn fresh update s e
    (grantDrainDummyCleanGeometryHolds
      ring hn fresh update s e hP hNoBad)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainDummyFollowerCleanOfPrefixFrame
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryFollowerOutsideArcClean
#print axioms L3.GrantDrainEntrance.grantDrainDummyEmptyQuietFollowerPairFixed
#print axioms L3.GrantDrainEntrance.grantDrainDummyEmptyQuietFollowerNativeEFixed
#print axioms L3.GrantDrainEntrance.grantDrainDummyCleanBirthInsideOldPrefix
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryFollowerInteriorClean
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryFollowerAwayFromRootClean
#print axioms L3.GrantDrainEntrance.grantDrainDummyFollowerCleanOfRootTailFrame
#print axioms L3.GrantDrainEntrance.grantDrainDummyIncomingRootTailFrame
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryIncomingRootSurvivingClean
#print axioms L3.GrantDrainEntrance.grantDrainDummyFinalResponderFollowerWasPostE
#print axioms L3.GrantDrainEntrance.grantDrainDummyCleanOfPredecessorLeaderExtension
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryIncomingRootLeaderDeathClean
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryIncomingRootFollowerDeathClean
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryFollowerIncomingRootClean
#print axioms L3.GrantDrainEntrance.grantDrainDummyStationaryFollowerOffPairCleanHolds
#print axioms L3.GrantDrainEntrance.grantDrainDummyCleanGeometryHolds
#print axioms L3.GrantDrainEntrance.grantDrainDummyEdgeOriginHolds

namespace L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-!
Literal scan frame.
No Mathlib or Batteries. The first-hit inverse and the List
congruence lemmas below use the actual core List.range', find?
and takeWhile definitions.

The d=n branch is essential: the old list may have no leader
at any positive distance, so getD n is its fallback. In that
case the entire range 1..n is framed. When d<n, the first
hit is preserved by its prefix through d.
-/

/-- The exact consecutive list scanned by the native D.6 source
and inclusive left-bullet functions. -/
private theorem grantDrainWarmScanRange
    (length : Nat) :
    (List.range length).map (fun k : Nat => k + 1) =
      List.range' 1 length := by
  have hFun : (fun k : Nat => k + 1) =
      (fun k : Nat => 1 + k) := by
    funext k
    omega
  rw [hFun]
  exact (List.range'_eq_map_range
    (s := 1) (n := length)).symm

/-- List.find? is unchanged by equal predicate values throughout
a consecutive finite range. In the d=n fallback branch all of
those values are within the framed distance. -/
private theorem grantDrainWarmRangeFindCongr
    (f h : Nat → Bool) :
    ∀ length start,
      (∀ k : Nat, start ≤ k → k < start + length →
        f k = h k) →
      (List.range' start length).find? f =
        (List.range' start length).find? h := by
  intro length
  induction length with
  | zero =>
      intro start _
      rfl
  | succ length ih =>
      intro start hAgree
      have hHead : f start = h start :=
        hAgree start (Nat.le_refl _) (by omega)
      have hTail :
          (List.range' (start + 1) length).find? f =
            (List.range' (start + 1) length).find? h := by
        apply ih (start + 1)
        intro k hk hkl
        exact hAgree k (by omega) (by omega)
      simp [List.range'_succ, List.find?_cons, hHead, hTail]

/-- If the first successful search result over a consecutive range
is d, d lies in that range, succeeds, and every smaller entry
fails. This is a direct induction, without Nat.find. -/
private theorem grantDrainWarmRangeFindConverse
    (f : Nat → Bool) :
    ∀ length start d,
      (List.range' start length).find? f = some d →
      start ≤ d ∧ d < start + length ∧ f d = true ∧
        (∀ k : Nat, start ≤ k → k < d →
          f k = false) := by
  intro length
  induction length with
  | zero =>
      intro start d h
      simp [List.range'] at h
  | succ length ih =>
      intro start d h
      cases hf : f start with
      | true =>
          have hd : d = start := by
            have hh : some start = some d := by
              simpa [List.range'_succ, List.find?_cons,
                hf] using h
            exact (Option.some.inj hh).symm
          subst d
          refine ⟨by omega, by omega, hf, ?_⟩
          intro k hk hkd
          omega
      | false =>
          have ht :
              (List.range' (start + 1) length).find? f =
                some d := by
            simpa [List.range'_succ, List.find?_cons,
              hf] using h
          obtain ⟨hlo, hhi, hval, hbefore⟩ :=
            ih (start + 1) d ht
          refine ⟨by omega, by omega, hval, ?_⟩
          intro k hk hkd
          by_cases heq : k = start
          · rw [heq]
            exact hf
          · exact hbefore k (by omega) hkd

/-- A generic core List.takeWhile congruence, including the
first false entry, proved without deciding any nonclosed data. -/
private theorem grantDrainWarmTakeWhileCongr
    {A : Type} (xs : List A) (f h : A → Bool)
    (hAgree : ∀ x : A, x ∈ xs → f x = h x) :
    xs.takeWhile f = xs.takeWhile h := by
  revert hAgree
  induction xs with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro hAgree
      have hHead : f x = h x :=
        hAgree x (by simp)
      have hTail :
          xs.takeWhile f = xs.takeWhile h := by
        apply ih
        intro y hy
        exact hAgree y (by simp [hy])
      cases hf : f x with
      | true =>
          have hh : h x = true := hHead.symm.trans hf
          simp [List.takeWhile, hf, hh, hTail]
      | false =>
          have hh : h x = false := hHead.symm.trans hf
          simp [List.takeWhile, hf, hh]

/-- Complete first-leader scan frame, without any rootedness
assumption. The no-hit fallback d=n is handled independently. -/
theorem grantDrainWarmLeaderScanFrame
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (hFrame : ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring N g →
      M (PPL.shiftLeft ring g k) =
        N (PPL.shiftLeft ring g k)) :
    grantDrainLeftLeaderDistance ring M g =
      grantDrainLeftLeaderDistance ring N g := by
  cases hFind :
      (List.range' 1 n).find?
        (fun k => (N (PPL.shiftLeft ring g k)).l) with
  | none =>
      have hOld :
          grantDrainLeftLeaderDistance ring N g = n := by
        change
          (((List.range n).map (fun k : Nat => k + 1)).find?
            (fun k => (N (PPL.shiftLeft ring g k)).l)).getD n =
              n
        rw [grantDrainWarmScanRange, hFind]
        rfl
      have hFindFrame :
          (List.range' 1 n).find?
              (fun k => (M (PPL.shiftLeft ring g k)).l) =
          (List.range' 1 n).find?
              (fun k => (N (PPL.shiftLeft ring g k)).l) := by
        apply grantDrainWarmRangeFindCongr
        intro k hk hkn
        have hInside :
            k ≤ grantDrainLeftLeaderDistance ring N g := by
          rw [hOld]
          omega
        exact congrArg CertNative.l (hFrame k hInside)
      rw [hOld]
      change
        (((List.range n).map (fun k : Nat => k + 1)).find?
          (fun k => (M (PPL.shiftLeft ring g k)).l)).getD n =
            n
      rw [grantDrainWarmScanRange, hFindFrame, hFind]
      rfl
  | some d =>
      have hOld :
          grantDrainLeftLeaderDistance ring N g = d := by
        change
          (((List.range n).map (fun k : Nat => k + 1)).find?
            (fun k => (N (PPL.shiftLeft ring g k)).l)).getD n =
              d
        rw [grantDrainWarmScanRange, hFind]
        rfl
      obtain ⟨hpos, hbound, hAt, hBefore⟩ :=
        grantDrainWarmRangeFindConverse
          (fun k => (N (PPL.shiftLeft ring g k)).l)
          n 1 d hFind
      rw [hOld]
      apply grantDrainMarksScanFirstSource
        ring M g d hpos (by omega)
      · have hdFrame :
            M (PPL.shiftLeft ring g d) =
              N (PPL.shiftLeft ring g d) :=
          hFrame d (by rw [hOld]; exact Nat.le_refl _)
        rw [hdFrame]
        exact hAt
      · intro k hk hkd
        have hkFrame :
            M (PPL.shiftLeft ring g k) =
              N (PPL.shiftLeft ring g k) :=
          hFrame k (by rw [hOld]; omega)
        rw [hkFrame]
        exact hBefore k hk hkd

/-- Exact inclusive 1..d left-bullet scan frame, using the
consecutive-range List.find? congruence above. -/
theorem grantDrainWarmBulletScanFrame
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (d : Nat)
    (hFrame : ∀ k : Nat, 1 ≤ k → k ≤ d →
      M (PPL.shiftLeft ring g k) =
        N (PPL.shiftLeft ring g k)) :
    grantDrainLeftBulletDistance ring M g d =
      grantDrainLeftBulletDistance ring N g d := by
  change
    (((List.range d).map (fun k : Nat => k + 1)).find?
      (fun k => (M (PPL.shiftLeft ring g k)).b.val != 0)) =
    (((List.range d).map (fun k : Nat => k + 1)).find?
      (fun k => (N (PPL.shiftLeft ring g k)).b.val != 0))
  simp only [grantDrainWarmScanRange]
  apply grantDrainWarmRangeFindCongr
  intro k hk hkd
  have hSite := hFrame k hk (by omega)
  rw [hSite]

/-- Exact 0..d-1 terminal signal-run frame, including the
takeWhile stopping site. -/
theorem grantDrainWarmTerminalScanFrame
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (d : Nat)
    (hFrame : ∀ k : Nat, k < d →
      M (PPL.shiftLeft ring g k) =
        N (PPL.shiftLeft ring g k)) :
    grantDrainTerminalRun ring M g d =
      grantDrainTerminalRun ring N g d := by
  unfold grantDrainTerminalRun
  have hTake :
      (List.range d).takeWhile
          (fun k => (M (PPL.shiftLeft ring g k)).sg) =
      (List.range d).takeWhile
          (fun k => (N (PPL.shiftLeft ring g k)).sg) := by
    apply grantDrainWarmTakeWhileCongr
    intro k hk
    have hlt : k < d := List.mem_range.mp hk
    exact congrArg CertNative.sg (hFrame k hlt)
  rw [hTake]

/-- All four observers together. The actual d is
obtained from the old state, and we frame the native records
through that distance, including the preceding leader and the
site g. No positivity or root hypothesis is needed. -/
theorem grantDrainWarmFullScanFrame
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (hFrame : ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring N g →
      M (PPL.shiftLeft ring g k) =
        N (PPL.shiftLeft ring g k)) :
    grantDrainLeftLeaderDistance ring M g =
        grantDrainLeftLeaderDistance ring N g ∧
    grantDrainTerminalRun ring M g
        (grantDrainLeftLeaderDistance ring N g) =
      grantDrainTerminalRun ring N g
        (grantDrainLeftLeaderDistance ring N g) ∧
    grantDrainLeftBulletDistance ring M g
        (grantDrainLeftLeaderDistance ring N g) =
      grantDrainLeftBulletDistance ring N g
        (grantDrainLeftLeaderDistance ring N g) ∧
    grantDrainWarmRank ring M g =
      grantDrainWarmRank ring N g := by
  have hd :=
    grantDrainWarmLeaderScanFrame ring N M g hFrame
  have hf :
      grantDrainTerminalRun ring M g
        (grantDrainLeftLeaderDistance ring N g) =
      grantDrainTerminalRun ring N g
        (grantDrainLeftLeaderDistance ring N g) :=
    grantDrainWarmTerminalScanFrame ring N M g
      (grantDrainLeftLeaderDistance ring N g)
      (by intro k hk; exact hFrame k (by omega))
  have hp :
      grantDrainLeftBulletDistance ring M g
        (grantDrainLeftLeaderDistance ring N g) =
      grantDrainLeftBulletDistance ring N g
        (grantDrainLeftLeaderDistance ring N g) :=
    grantDrainWarmBulletScanFrame ring N M g
      (grantDrainLeftLeaderDistance ring N g)
      (by intro k hk hle; exact hFrame k hle)
  have hReady :
      (M (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring N g))).sg =
      (N (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring N g))).sg :=
    congrArg CertNative.sg
      (hFrame _ (Nat.le_refl _))
  refine ⟨hd, hf, hp, ?_⟩
  simp only [grantDrainWarmRank, hd, hf, hp, hReady]

/-- An unconditional literal source-step consequence.
If every position of the OLD scan arc, from g to its first
leader inclusive, lies outside the selected pair, nativeE and
every canonical birth leave its records unchanged. No extra
no-birth assumption is needed because FIRE is pair-local. -/
theorem grantDrainWarmOutsidePairScanFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n)
    (hOutside : ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g k ≠ e ∧
      PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g =
      grantDrainWarmRank ring s.native g := by
  exact (grantDrainWarmFullScanFrame ring s.native
    (grantDrainStep ring fresh update s e).native g
    (by
      intro k hk
      change grantDrainNativeNext ring s e
        (PPL.shiftLeft ring g k) =
          s.native (PPL.shiftLeft ring g k)
      exact grantDrainMarksNativeOutsidePairFrame
        ring s e (PPL.shiftLeft ring g k)
        (hOutside k hk).1 (hOutside k hk).2)).2.2.2

end L3.GrantDrainEntrance
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeaderScanFrame
#print axioms L3.GrantDrainEntrance.grantDrainWarmBulletScanFrame
#print axioms L3.GrantDrainEntrance.grantDrainWarmTerminalScanFrame
#print axioms L3.GrantDrainEntrance.grantDrainWarmFullScanFrame
#print axioms L3.GrantDrainEntrance.grantDrainWarmOutsidePairScanFrame

namespace L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-!
One-label row.

These lemmas use the literal edge carrier, not an assumed origin
or a surrogate step. They prove the fixed-target, single-edge
distance decrease and the OLD-leader collision barrier.

They do NOT prove a wordwise < n nominated-hit quota. Iterating
the inequality requires proving that a surviving label's *current*
nearest clockwise leader cannot be lost before a closer birth changes
the nominated target. No such dynamic-target invariant is supplied
or assumed below.
-/

/-- An outgoing label cannot remain alive upon meeting a site
which was already a leader before the selected edge. -/
theorem grantDrainDummyOutgoingLeaderBlocked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n)) (e id : Fin n)
    (hHost : host id = some e)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true) :
    grantDrainDummyEdgeNextHost ring fresh update s host e id =
      none := by
  classical
  have hNoMove :
      ¬ GrantDrainDummyMovingUnclean ring fresh update s e := by
    intro hMove
    have hImpossible : true = false :=
      hLeader.symm.trans hMove.1
    cases hImpossible
  simp [grantDrainDummyEdgeNextHost, hHost, hNoMove]

/-- Complete one-label survivor displacement, including the
off-source stationary branch and the on-source outgoing branch.
There is no assumption on PPlus, NoBadLive or any future state. -/
theorem grantDrainDummyEdgeSurvivorDisplacement
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n))
    (e id b b' : Fin n)
    (hOld : host id = some b)
    (hNew :
      grantDrainDummyEdgeNextHost ring fresh update s host e id =
        some b') :
    (b' = b ∧ e ≠ b) ∨
      (b = e ∧ b' = ring.rightNeighbor e) := by
  classical
  by_cases hAt : b = e
  · have hAtSource : host id = some e :=
      hOld.trans (congrArg some hAt)
    rcases grantDrainDummyEdgeOutgoing
        ring fresh update s host e id hAtSource with hGone | hMoved
    · rw [hNew] at hGone
      cases hGone
    · exact Or.inr
        ⟨hAt, Option.some.inj (hNew.symm.trans hMoved)⟩
  · have hStep :
        grantDrainDummyEdgeNextHost ring fresh update s host e id =
          none ∨
        grantDrainDummyEdgeNextHost ring fresh update s host e id =
          some b := by
      by_cases hReady :
          b = ring.rightNeighbor e ∧
            GrantDrainDummyReadyResponder ring s e
      · left
        have hne : ring.rightNeighbor e ≠ e :=
          fun h => hAt (hReady.1.trans h)
        simp [grantDrainDummyEdgeNextHost, hOld, hAt, hReady, hne]
      · by_cases hUnclean :
          GrantDrainEntranceUncleanDummyAt ring
            (grantDrainStep ring fresh update s e).native b
        · right
          simp [grantDrainDummyEdgeNextHost,
            hOld, hAt, hReady, hUnclean]
        · left
          simp [grantDrainDummyEdgeNextHost,
            hOld, hAt, hReady, hUnclean]
    rcases hStep with hGone | hStay
    · rw [hNew] at hGone
      cases hGone
    · exact Or.inl
        ⟨Option.some.inj (hNew.symm.trans hStay),
          (fun he => hAt he.symm)⟩

/-- Nonzero clockwise distance to a different target. The
zero-offset case is discharged by the exact existing shift inverse. -/
theorem grantDrainDummyOffsetPositiveAwayFromTarget
    {n : Nat} (ring : DirectedRing n)
    (b t : Fin n) (hDifferent : b ≠ t) :
    0 < PPL.cyclicOffset ring b t := by
  by_cases hZero : PPL.cyclicOffset ring b t = 0
  · have hSite := grantDrainMarksArcShiftRightOffset ring b t
    rw [hZero] at hSite
    have hShift : PPL.shiftRight ring b 0 = b := by
      apply Fin.ext
      change (b.val + 0) % n = b.val
      simp [Nat.mod_eq_of_lt b.isLt]
    rw [hShift] at hSite
    exact False.elim (hDifferent hSite)
  · omega

/-- The actual single-edge one-label rank inequality. A surviving
outgoing hit consumes exactly one clockwise unit toward ANY fixed
distinct target; another edge cannot increase that fixed-target rank.
This is a local row, not a dynamic-nearest-leader word induction. -/
theorem grantDrainDummyOneLabelFixedTargetStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n))
    (e id b b' t : Fin n)
    (hOld : host id = some b)
    (hNew :
      grantDrainDummyEdgeNextHost ring fresh update s host e id =
        some b')
    (hDifferent : b ≠ t) :
    PPL.cyclicOffset ring b' t +
        (if e = b then 1 else 0) ≤
      PPL.cyclicOffset ring b t := by
  rcases grantDrainDummyEdgeSurvivorDisplacement
      ring fresh update s host e id b b' hOld hNew with
    ⟨hStay, hOff⟩ | ⟨hAt, hMove⟩
  · rw [hStay]
    simp [hOff]
  · have hPos :=
      grantDrainDummyOffsetPositiveAwayFromTarget
        ring b t hDifferent
    have hShift :
        PPL.shiftRight ring b 1 = ring.rightNeighbor b := by
      apply Fin.ext
      rfl
    have hDrop :
        PPL.cyclicOffset ring (ring.rightNeighbor b) t =
          PPL.cyclicOffset ring b t - 1 := by
      rw [← hShift]
      exact grantDrainMarksArcOffsetSubtract
        ring b t 1 (by omega)
    subst e
    rw [hMove, hDrop]
    simp only [ite_true]
    omega

/-- A surviving label cannot acquire an OLD leader as its host
if its previous host was different. This includes the adjacent
collision, which is retired by the literal carrier. -/
theorem grantDrainDummySurvivorAvoidsOldLeader
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n))
    (e id b b' t : Fin n)
    (hOld : host id = some b)
    (hNew :
      grantDrainDummyEdgeNextHost ring fresh update s host e id =
        some b')
    (hDifferent : b ≠ t)
    (hLeader : (s.native t).l = true) :
    b' ≠ t := by
  intro hSame
  rcases grantDrainDummyEdgeSurvivorDisplacement
      ring fresh update s host e id b b' hOld hNew with
    ⟨hStay, _⟩ | ⟨hAt, hMove⟩
  · exact hDifferent (hStay.symm.trans hSame)
  · have hAtResponder : t = ring.rightNeighbor e :=
      hSame.symm.trans hMove
    have hLeaderResponder :
        (s.native (ring.rightNeighbor e)).l = true := by
      rw [← hAtResponder]
      exact hLeader
    have hAtSource : host id = some e :=
      hOld.trans (congrArg some hAt)
    have hGone := grantDrainDummyOutgoingLeaderBlocked
      ring fresh update s host e id hAtSource hLeaderResponder
    rw [hGone] at hNew
    cases hNew

/-- In the nominated case the fixed-target rank drops strictly.
The target is any distinct site, not a presumed immortal leader. -/
theorem grantDrainDummyOneLabelNominatedStrictDrop
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n))
    (e id b' t : Fin n)
    (hOld : host id = some e)
    (hNew :
      grantDrainDummyEdgeNextHost ring fresh update s host e id =
        some b')
    (hDifferent : e ≠ t) :
    PPL.cyclicOffset ring b' t <
      PPL.cyclicOffset ring e t := by
  have hBound :=
    grantDrainDummyOneLabelFixedTargetStep
      ring fresh update s host e id e b' t
      hOld hNew hDifferent
  have hOne :
      PPL.cyclicOffset ring b' t + 1 ≤
        PPL.cyclicOffset ring e t := by
    simpa only [ite_true] using hBound
  omega

end L3.GrantDrainEntrance
#print axioms L3.GrantDrainEntrance.grantDrainDummyOutgoingLeaderBlocked
#print axioms L3.GrantDrainEntrance.grantDrainDummyEdgeSurvivorDisplacement
#print axioms L3.GrantDrainEntrance.grantDrainDummyOffsetPositiveAwayFromTarget
#print axioms L3.GrantDrainEntrance.grantDrainDummyOneLabelFixedTargetStep
#print axioms L3.GrantDrainEntrance.grantDrainDummySurvivorAvoidsOldLeader
#print axioms L3.GrantDrainEntrance.grantDrainDummyOneLabelNominatedStrictDrop

namespace L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-! Two literal source rows and closed five-site regressions.
    These are NOT the universal physical-increment theorem. -/

/-- Case (ii) native E row. An empty follower source copies an
    empty signal-one follower responder's signal, without a bullet. -/
theorem grantDrainWarmIncomingEmptyFollowerPair
    (x y : CertNative)
    (hxl : x.l = false) (hxb : x.b = (0 : Fin 3))
    (hyl : y.l = false) (hyb : y.b = (0 : Fin 3))
    (hys : y.sg = true) :
    (certLiteralEPair x y).1.sg = true ∧
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.b = (0 : Fin 3) := by
  simp [certLiteralEPair, hxl, hxb, hyl, hyb, hys, certFinThree]

/-- Case (iv) native E row, with the preceding leader as SOURCE.
    This is different from the ready-RESPONDER dummy row.
    The new LIVE travels immediately from source to empty responder. -/
theorem grantDrainWarmReadyLeaderSourcePair
    (x y : CertNative)
    (hxl : x.l = true) (hxs : x.sg = true)
    (hyl : y.l = false) (hyb : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.b = (2 : Fin 3) := by
  simp [certLiteralEPair, hxl, hxs, hyl, hyb, certFinThree]

/-! The same n=5 clean initial state witnesses both requested edge
    positions; it has a single ready leader at 0, signal-one empty
    followers at 1..4, and an unheld grant at 3. -/

private def grantDrainWarmPairCaseRing : DirectedRing 5 :=
  ⟨by decide⟩

private def grantDrainWarmPairCaseNative (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (0 : Fin 3), sh := true, sg := true }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := true }

private def grantDrainWarmPairCaseInitial : GrantDrainState 5 Unit :=
  { native := grantDrainWarmPairCaseNative
    request := fun _ => false
    grant := fun i => i.val == 3
    scratch := ()
    history := [] }

private def grantDrainWarmPairCaseLabel : GrantDrainWarmLabel 5 :=
  { identity := (3 : Fin 5)
    host := some (3 : Fin 5)
    warm := true
    birthsLeft := 5
    exceptionalLeft := true }

theorem grantDrainWarmPairCaseClean :
    PPlus grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native ∧
    C_native grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native := by
  constructor
  · decide
  · decide

theorem grantDrainWarmPairCaseNoBad :
    GrantDrainEntranceNoBadLive
      grantDrainWarmPairCaseRing grantDrainWarmPairCaseInitial := by
  have hZero :
      ∀ i : Fin 5,
        (grantDrainWarmPairCaseInitial.native i).b =
          (0 : Fin 3) := by
    decide
  intro b hBad
  have hLive :
      LiveBullet grantDrainWarmPairCaseInitial.native b := hBad.1
  change (grantDrainWarmPairCaseInitial.native b).b =
    (2 : Fin 3) at hLive
  rw [hZero b] at hLive
  cases hLive

private def grantDrainWarmPairCaseIncoming : GrantDrainState 5 Unit :=
  grantDrainStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWarmPairCaseInitial (2 : Fin 5)

private def grantDrainWarmPairCaseIncomingLabel : GrantDrainWarmLabel 5 :=
  grantDrainWarmLabelStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWarmPairCaseInitial (2 : Fin 5)
    grantDrainWarmPairCaseLabel

/-- Case (ii), e=2, y=g=3. The unheld tracked grant really moves
    to e=2 and remains warm. The literal D.6 rank decreases 4→3.
    This finite regression is not the arbitrary-n theorem. -/
theorem grantDrainWarmIncomingHostFiveTrace :
    grantDrainWarmAt grantDrainWarmPairCaseInitial (3 : Fin 5) =
        true ∧
    grantDrainWarmPairCaseInitial.grant (3 : Fin 5) = true ∧
    grantDrainSelect grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial (2 : Fin 5) = .none ∧
    grantDrainWarmPairCaseIncomingLabel.host =
      some (2 : Fin 5) ∧
    grantDrainWarmPairCaseIncomingLabel.warm = true ∧
    grantDrainWarmAt grantDrainWarmPairCaseIncoming (2 : Fin 5) =
      true ∧
    grantDrainWarmPairCaseIncoming.grant (2 : Fin 5) = true ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native (3 : Fin 5) = 4 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseIncoming.native (2 : Fin 5) = 3 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseIncoming.native (2 : Fin 5) ≤
      grantDrainWarmRank grantDrainWarmPairCaseRing
        grantDrainWarmPairCaseInitial.native (3 : Fin 5) +
      (if grantDrainSelect grantDrainWarmPairCaseRing
          grantDrainWarmPairCaseInitial (2 : Fin 5) = .none
       then 0 else 1) +
      (if grantDrainExceptionalDeath grantDrainWarmPairCaseRing
          grantDrainWarmPairCaseInitial (2 : Fin 5) (3 : Fin 5)
       then 2 * (5 - 2) else 0) := by
  decide

private def grantDrainWarmPairCaseLeader : GrantDrainState 5 Unit :=
  grantDrainStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWarmPairCaseInitial (0 : Fin 5)

private def grantDrainWarmPairCaseLeaderLabel : GrantDrainWarmLabel 5 :=
  grantDrainWarmLabelStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWarmPairCaseInitial (0 : Fin 5)
    grantDrainWarmPairCaseLabel

/-- Case (iv), e=0=preceding leader, y=1 strictly inside the arc
    to g=3. Literal E emits a LIVE and immediately moves it to 1,
    not retaining a bullet at 0. The surviving warm host has W=2,
    not W=3 as the proposed source-leader substitution claims.
    The desired charged increment bound nevertheless holds here. -/
theorem grantDrainWarmPrecedingLeaderFiveTrace :
    grantDrainLeftLeaderDistance grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native (3 : Fin 5) = 3 ∧
    PPL.shiftLeft grantDrainWarmPairCaseRing
      (3 : Fin 5) 3 = (0 : Fin 5) ∧
    grantDrainSelect grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial (0 : Fin 5) = .none ∧
    (grantDrainWarmPairCaseLeader.native (0 : Fin 5)).b =
      (0 : Fin 3) ∧
    (grantDrainWarmPairCaseLeader.native (1 : Fin 5)).b =
      (2 : Fin 3) ∧
    grantDrainWarmPairCaseLeaderLabel.host = some (3 : Fin 5) ∧
    grantDrainWarmPairCaseLeaderLabel.warm = true ∧
    grantDrainWarmPairCaseLeader.grant (3 : Fin 5) = true ∧
    grantDrainWarmAt grantDrainWarmPairCaseLeader (3 : Fin 5) =
      true ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native (3 : Fin 5) = 4 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) = 2 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) ≤
      grantDrainWarmRank grantDrainWarmPairCaseRing
        grantDrainWarmPairCaseInitial.native (3 : Fin 5) +
      (if grantDrainSelect grantDrainWarmPairCaseRing
          grantDrainWarmPairCaseInitial (0 : Fin 5) = .none
       then 0 else 1) +
      (if grantDrainExceptionalDeath grantDrainWarmPairCaseRing
          grantDrainWarmPairCaseInitial (0 : Fin 5) (3 : Fin 5)
       then 2 * (5 - 2) else 0) := by
  decide

end L3.GrantDrainEntrance
#print axioms L3.GrantDrainEntrance.grantDrainWarmIncomingEmptyFollowerPair
#print axioms L3.GrantDrainEntrance.grantDrainWarmReadyLeaderSourcePair
#print axioms L3.GrantDrainEntrance.grantDrainWarmPairCaseClean
#print axioms L3.GrantDrainEntrance.grantDrainWarmPairCaseNoBad
#print axioms L3.GrantDrainEntrance.grantDrainWarmIncomingHostFiveTrace
#print axioms L3.GrantDrainEntrance.grantDrainWarmPrecedingLeaderFiveTrace

namespace L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-!
Physical target-survival row.

The sectorLength endpoint is the first clockwise leader STRICTLY
after a site of that sector, with the unique-leader wrap case d=n.
For a surviving unclean DUMMY identity this old endpoint itself
cannot be deleted on the selected E+FIRE step. The proof uses the
already-proved NoBadLive exclusion, not an assumed trajectory leaf.

This does not yet identify the NEW first clockwise leader after a
birth, and does not claim the wordwise fewer-than-n hit quota.
-/

/-- The old clockwise target is the right endpoint of the unique
old sector containing b. For the unique-leader sector, d=n and
the endpoint is the root itself after one full clockwise turn. -/
def GrantDrainDummyClockwiseSectorTarget
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (b t : Fin n) : Prop :=
  ∃ (p : Fin n) (d : Fin (n + 1)) (a : Fin n),
    sectorLength ring N p d ∧
    a.val < d.val ∧
    b = PPL.shiftRight ring p a.val ∧
    t = PPL.shiftRight ring p d.val

/-- Every site of a rooted native state has a first strictly
clockwise leader, including the complete-turn case. -/
theorem grantDrainDummyClockwiseSectorTargetExists
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hPB : PPlus ring N) (b : Fin n) :
    ∃ t : Fin n,
      GrantDrainDummyClockwiseSectorTarget ring N b t := by
  obtain ⟨p, d, a, hSector, hInside, hAt⟩ :=
    grantDrainEntranceSectorCoverOfRoot ring N hPB.1 b
  exact ⟨PPL.shiftRight ring p d.val,
    p, d, a, hSector, hInside, hAt, rfl⟩

/-- Birth can never turn an E-surviving leader into a follower. -/
theorem grantDrainDummyBirthFollowerWasFollower
    {n : Nat} (N : Fin n → CertNative)
    (z i : Fin n)
    (hNew : ((canonicalBirth N z) i).l = false) :
    (N i).l = false := by
  by_cases hi : i = z
  · subst i
    simp [canonicalBirth, firedNative] at hNew
  · simpa [canonicalBirth, hi] using hNew

/-- A follower after the actual canonical E+FIRE step was already
a follower after native E, irrespective of which FIRE was selected. -/
theorem grantDrainDummyPostFollowerWasNativeEFollower
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e i : Fin n)
    (hNew :
      ((grantDrainStep ring fresh update s e).native i).l = false) :
    (nativeE ring s.native e i).l = false := by
  change (grantDrainNativeNext ring s e i).l = false at hNew
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hNew
  | leftLocal =>
      apply grantDrainDummyBirthFollowerWasFollower
        (nativeE ring s.native e) e i
      simpa [grantDrainNativeNext, hf] using hNew
  | rightLocal =>
      apply grantDrainDummyBirthFollowerWasFollower
        (nativeE ring s.native e) (ring.rightNeighbor e) i
      simpa [grantDrainNativeNext, hf] using hNew
  | cross =>
      apply grantDrainDummyBirthFollowerWasFollower
        (nativeE ring s.native e) e i
      simpa [grantDrainNativeNext, hf] using hNew

/-- The left predecessor of a sector's next-leader endpoint is its
last interior position. Unlike a short-arc lemma, this includes
the d=n wraparound case. -/
theorem grantDrainDummySectorEndpointPredecessor
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (p : Fin n) (d : Fin (n + 1))
    (hPositive : 0 < d.val) :
    PPL.shiftLeft ring (PPL.shiftRight ring p d.val) 1 =
      PPL.shiftRight ring p (d.val - 1) := by
  by_cases hShort : d.val < n
  · exact grantDrainMarksArcShiftLeftRight
      ring p d.val 1 (by omega : 1 ≤ d.val) hShort
  · have hFull : d.val = n := by
      have hBound : d.val < n + 1 := d.isLt
      omega
    rw [hFull, grantDrainMarksFullRotation ring p]
    apply Fin.ext
    change (p.val + n - 1 % n) % n =
      (p.val + (n - 1)) % n
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
    have hNumerator :
        p.val + n - 1 = p.val + (n - 1) := by omega
    rw [hNumerator]

/-- An OLD target leader of a surviving unclean identity is never
deleted by the ACTUAL E+FIRE edge. If the target were the responder
and died, its predecessor would be either the labelled source
(retirement on its outgoing edge) or an OLD follower LIVE after the
label in the very same sector (forbidden by NoBadLive).

This is stronger than simply ruling out old-target death before
a closer birth, but does not itself classify the new nearest target. -/
theorem grantDrainDummyUncleanOldTargetLeaderSurvives
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n))
    (e id b b' t : Fin n)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hBad : GrantDrainEntranceUncleanDummyAt ring s.native b)
    (hHost : host id = some b)
    (hNew :
      grantDrainDummyEdgeNextHost ring fresh update s host e id =
        some b')
    (hTarget :
      GrantDrainDummyClockwiseSectorTarget ring s.native b t) :
    ((grantDrainStep ring fresh update s e).native t).l = true := by
  obtain ⟨p, d, a, hSector, hInside, hAt, hEndpoint⟩ := hTarget
  have hOldLeader : (s.native t).l = true := by
    rw [hEndpoint]
    exact hSector.2.2.1
  cases hFinal :
      ((grantDrainStep ring fresh update s e).native t).l with
  | true =>
      rfl
  | false =>
      have hEDeath :
          (nativeE ring s.native e t).l = false :=
        grantDrainDummyPostFollowerWasNativeEFollower
          ring fresh update s e t hFinal
      by_cases hAtResponder : t = ring.rightNeighbor e
      · have hOldY :
            (s.native (ring.rightNeighbor e)).l = true := by
          rw [← hAtResponder]
          exact hOldLeader
        have hEDeathY :
            (nativeE ring s.native e
              (ring.rightNeighbor e)).l = false := by
          rw [← hAtResponder]
          exact hEDeath
        have hInverse :
            PPL.shiftLeft ring (ring.rightNeighbor e) 1 = e := by
          have hCancel := grantDrainMarksArcShiftLeftRight
            ring e 1 1 (by omega : 1 ≤ 1) (by omega : 1 < n)
          change
            PPL.shiftLeft ring (ring.rightNeighbor e) 1 =
              PPL.shiftRight ring e (1 - 1) at hCancel
          simpa [PPL.shiftRight, Nat.mod_eq_of_lt e.isLt]
            using hCancel
        have hPredecessor :
            e = PPL.shiftRight ring p (d.val - 1) := by
          calc
            e = PPL.shiftLeft ring (ring.rightNeighbor e) 1 :=
              hInverse.symm
            _ = PPL.shiftLeft ring t 1 := by rw [hAtResponder]
            _ = PPL.shiftLeft ring
                  (PPL.shiftRight ring p d.val) 1 := by rw [hEndpoint]
            _ = PPL.shiftRight ring p (d.val - 1) :=
              grantDrainDummySectorEndpointPredecessor
                ring hn p d hSector.1
        by_cases hLast : a.val = d.val - 1
        · have hSource : b = e := by
            calc
              b = PPL.shiftRight ring p a.val := hAt
              _ = PPL.shiftRight ring p (d.val - 1) := by rw [hLast]
              _ = e := hPredecessor.symm
          have hHostSource : host id = some e :=
            hHost.trans (congrArg some hSource)
          have hGone := grantDrainDummyOutgoingLeaderBlocked
            ring fresh update s host e id hHostSource hOldY
          rw [hGone] at hNew
          cases hNew
        · have hEarlier : a.val < d.val - 1 := by omega
          have hPredecessorPositive : 0 < d.val - 1 := by omega
          have hPredecessorBound : d.val - 1 < n := by
            have hd : d.val < n + 1 := d.isLt
            omega
          have hSourceFollower : (s.native e).l = false := by
            rw [hPredecessor]
            exact hSector.2.2.2
              (⟨d.val - 1, hPredecessorBound⟩ : Fin n)
              hPredecessorPositive (by (try dsimp only); omega)
          have hSourceSector : leaderSector ring s.native p e := by
            rw [hPredecessor]
            exact grantDrainDummySectorNearest
              ring s.native p d hSector
              (⟨d.val - 1, hPredecessorBound⟩ : Fin n)
              (by (try dsimp only); omega)
          have hBulletSector : leaderSector ring s.native p b := by
            rw [hAt]
            exact grantDrainDummySectorNearest
              ring s.native p d hSector a hInside
          have hEarlierOffset :
              PPL.cyclicOffset ring p b <
                PPL.cyclicOffset ring p e := by
            have hbOffset :
                PPL.cyclicOffset ring p b = a.val := by
              rw [hAt]
              exact grantDrainDummyRightOffset ring p a.val a.isLt
            have heOffset :
                PPL.cyclicOffset ring p e = d.val - 1 := by
              rw [hPredecessor]
              exact grantDrainDummyRightOffset
                ring p (d.val - 1) hPredecessorBound
            rw [hbOffset, heOffset]
            exact hEarlier
          exact False.elim
            (grantDrainDummyFatalFollowerNoEarlierBullet
              ring hn s.native e p b
              hSourceFollower hOldY hEDeathY hNoBad
              hSourceSector hBulletSector
              (grantDrainDummyBadHasBullet ring s.native b hBad)
              hEarlierOffset)
      · have hOldELeader :
            (nativeE ring s.native e t).l = true := by
          rw [grantDrainDummyNativeELeaderAwayResponder
            ring s.native e t hAtResponder]
          exact hOldLeader
        rw [hOldELeader] at hEDeath
        cases hEDeath

/-- For every protected NoBadLive state and every surviving
initially unclean label, a real old nearest-clockwise target exists
and is still a leader after the selected canonical source step. -/
theorem grantDrainDummyUncleanOldTargetWitnessSurvives
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n))
    (e id b b' : Fin n)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hBad : GrantDrainEntranceUncleanDummyAt ring s.native b)
    (hHost : host id = some b)
    (hNew :
      grantDrainDummyEdgeNextHost ring fresh update s host e id =
        some b') :
    ∃ t : Fin n,
      GrantDrainDummyClockwiseSectorTarget ring s.native b t ∧
      ((grantDrainStep ring fresh update s e).native t).l = true := by
  obtain ⟨t, hTarget⟩ :=
    grantDrainDummyClockwiseSectorTargetExists
      ring s.native hPB b
  exact ⟨t, hTarget,
    grantDrainDummyUncleanOldTargetLeaderSurvives
      ring hn fresh update s host e id b b' t
      hNoBad hBad hHost hNew hTarget⟩

/-- Every newly created leader lies at one of the serviced sites.
Together with old-target survival, this isolates the only possible
cause of a closer new clockwise target: a canonical birth. -/
theorem grantDrainDummyNewLeaderOnlyAtSelectedPair
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e i : Fin n)
    (hOldFollower : (s.native i).l = false)
    (hNewLeader :
      ((grantDrainStep ring fresh update s e).native i).l = true) :
    i = e ∨ i = ring.rightNeighbor e := by
  by_cases hx : i = e
  · exact Or.inl hx
  · by_cases hy : i = ring.rightNeighbor e
    · exact Or.inr hy
    · have hFrame :
          (grantDrainStep ring fresh update s e).native i =
            s.native i := by
        change grantDrainNativeNext ring s e i = s.native i
        exact grantDrainMarksNativeOutsidePairFrame ring s e i hx hy
      rw [hFrame, hOldFollower] at hNewLeader
      cases hNewLeader

end L3.GrantDrainEntrance
#print axioms L3.GrantDrainEntrance.grantDrainDummyClockwiseSectorTargetExists
#print axioms L3.GrantDrainEntrance.grantDrainDummyBirthFollowerWasFollower
#print axioms L3.GrantDrainEntrance.grantDrainDummyPostFollowerWasNativeEFollower
#print axioms L3.GrantDrainEntrance.grantDrainDummySectorEndpointPredecessor
#print axioms L3.GrantDrainEntrance.grantDrainDummyUncleanOldTargetLeaderSurvives
#print axioms L3.GrantDrainEntrance.grantDrainDummyUncleanOldTargetWitnessSurvives
#print axioms L3.GrantDrainEntrance.grantDrainDummyNewLeaderOnlyAtSelectedPair

namespace L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-! Exact one-state D.6 finite-scan characterization. -/

/-- Converse to the already first-hit converse, without Nat.find. -/
private theorem grantDrainWarmRangeFirstHit
    (test : Nat → Bool) :
    ∀ length start p,
      start ≤ p → p < start + length →
      test p = true →
      (∀ k, start ≤ k → k < p → test k = false) →
      (List.range' start length).find? test = some p := by
  intro length
  induction length with
  | zero =>
      intro start p _ hlt _ _
      omega
  | succ length ih =>
      intro start p hlo hhi hhit hbefore
      by_cases heq : start = p
      · subst p
        simp [List.range'_succ, List.find?, hhit]
      · have hfirst : test start = false :=
          hbefore start (Nat.le_refl _) (by omega)
        have htail :
            (List.range' (start + 1) length).find? test = some p :=
          ih (start + 1) p (by omega) (by omega) hhit
            (fun k hk hkp => hbefore k (by omega) hkp)
        simpa [List.range'_succ, List.find?, hfirst] using htail

/-- Scan list of positive consecutive distances 1,...,length. -/
private theorem grantDrainWarmPositiveRange (length : Nat) :
    (List.range length).map (fun k : Nat => k + 1) =
      List.range' 1 length := by
  exact grantDrainWarmScanRange length

/-- For a first leader strictly before a full circuit, the actual
    getD fallback cannot be active. Both directions are unconditional
    on C_native, PPlus, or any physical step. -/
theorem grantDrainWarmLeaderFirstCharacterization
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) (d : Nat)
    (hpos : 1 ≤ d) (hshort : d < n) :
    grantDrainLeftLeaderDistance ring N g = d ↔
      (N (PPL.shiftLeft ring g d)).l = true ∧
      (∀ k : Nat, 1 ≤ k → k < d →
        (N (PPL.shiftLeft ring g k)).l = false) := by
  have hScan :
      grantDrainLeftLeaderDistance ring N g =
        ((List.range' 1 n).find?
          (fun k => (N (PPL.shiftLeft ring g k)).l)).getD n := by
    unfold grantDrainLeftLeaderDistance
    rw [grantDrainWarmPositiveRange]
  constructor
  · intro h
    cases hf : (List.range' 1 n).find?
        (fun k => (N (PPL.shiftLeft ring g k)).l) with
    | none =>
        have hEq : n = d := by
          simpa [hScan, hf] using h
        omega
    | some p =>
        have hp : p = d := by
          simpa [hScan, hf] using h
        subst p
        obtain ⟨_, _, hhit, hbefore⟩ :=
          grantDrainWarmRangeFindConverse
            (fun k => (N (PPL.shiftLeft ring g k)).l)
            n 1 d hf
        exact ⟨hhit, hbefore⟩
  · rintro ⟨hhit, hbefore⟩
    exact grantDrainMarksScanFirstSource
      ring N g d hpos (by omega) hhit hbefore

/-- The CORRECT fallback characterization: only distances strictly
    less than n must miss. A leader at the nth scanned position
    (the starting site g itself) also yields distance n. -/
theorem grantDrainWarmLeaderFullCharacterization
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) :
    grantDrainLeftLeaderDistance ring N g = n ↔
      ∀ k : Nat, 1 ≤ k → k < n →
        (N (PPL.shiftLeft ring g k)).l = false := by
  have hScan :
      grantDrainLeftLeaderDistance ring N g =
        ((List.range' 1 n).find?
          (fun k => (N (PPL.shiftLeft ring g k)).l)).getD n := by
    unfold grantDrainLeftLeaderDistance
    rw [grantDrainWarmPositiveRange]
  constructor
  · intro h k hk hkn
    cases hf : (List.range' 1 n).find?
        (fun j => (N (PPL.shiftLeft ring g j)).l) with
    | none =>
        have hm : k ∈ List.range' 1 n := by
          apply (List.mem_range').2
          refine ⟨k - 1, by omega, ?_⟩
          omega
        simpa using (List.find?_eq_none.mp hf) k hm
    | some p =>
        have hp : p = n := by
          simpa [hScan, hf] using h
        obtain ⟨_, _, _, hbefore⟩ :=
          grantDrainWarmRangeFindConverse
            (fun j => (N (PPL.shiftLeft ring g j)).l)
            n 1 p hf
        exact hbefore k hk (by omega)
  · intro hNo
    cases hf : (List.range' 1 n).find?
        (fun k => (N (PPL.shiftLeft ring g k)).l) with
    | none =>
        simpa [hScan, hf]
    | some p =>
        obtain ⟨hpos, hbound, hhit, _⟩ :=
          grantDrainWarmRangeFindConverse
            (fun k => (N (PPL.shiftLeft ring g k)).l)
            n 1 p hf
        have hp : p = n := by
          by_cases hs : p < n
          · have hfalse := hNo p hpos hs
            rw [hfalse] at hhit
            cases hhit
          · omega
        simpa [hScan, hf, hp]

/-- The inclusive 1..d bullet scan has p as its first nonzero value.
    The endpoint p=d is included, not discarded. -/
theorem grantDrainWarmBulletSomeCharacterization
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) (d p : Nat) :
    grantDrainLeftBulletDistance ring N g d = some p ↔
      1 ≤ p ∧ p ≤ d ∧
      (N (PPL.shiftLeft ring g p)).b.val ≠ 0 ∧
      (∀ k : Nat, 1 ≤ k → k < p →
        (N (PPL.shiftLeft ring g k)).b.val = 0) := by
  have hScan :
      grantDrainLeftBulletDistance ring N g d =
        (List.range' 1 d).find?
          (fun k => (N (PPL.shiftLeft ring g k)).b.val != 0) := by
    unfold grantDrainLeftBulletDistance
    rw [grantDrainWarmPositiveRange]
  constructor
  · intro h
    have hf :
        (List.range' 1 d).find?
          (fun k => (N (PPL.shiftLeft ring g k)).b.val != 0) =
          some p := by
      rw [← hScan]
      exact h
    obtain ⟨hpos, hbound, hhit, hbefore⟩ :=
      grantDrainWarmRangeFindConverse
        (fun k => (N (PPL.shiftLeft ring g k)).b.val != 0)
        d 1 p hf
    refine ⟨hpos, by omega, ?_, ?_⟩
    · simpa using hhit
    · intro k hk hkp
      have hz := hbefore k hk hkp
      simpa using hz
  · rintro ⟨hpos, hbound, hhit, hbefore⟩
    rw [hScan]
    apply grantDrainWarmRangeFirstHit
      (fun k => (N (PPL.shiftLeft ring g k)).b.val != 0)
      d 1 p hpos (by omega)
    · simpa using hhit
    · intro k hk hkp
      simpa [hbefore k hk hkp]

/-- No hit on the INCLUSIVE range 1..d is equivalent to the
    physical bullet field being zero at each scanned position. -/
theorem grantDrainWarmBulletNoneCharacterization
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) (d : Nat) :
    grantDrainLeftBulletDistance ring N g d = none ↔
      ∀ k : Nat, 1 ≤ k → k ≤ d →
        (N (PPL.shiftLeft ring g k)).b.val = 0 := by
  have hScan :
      grantDrainLeftBulletDistance ring N g d =
        (List.range' 1 d).find?
          (fun k => (N (PPL.shiftLeft ring g k)).b.val != 0) := by
    unfold grantDrainLeftBulletDistance
    rw [grantDrainWarmPositiveRange]
  constructor
  · intro h k hk hkd
    have hm : k ∈ List.range' 1 d := by
      apply (List.mem_range').2
      refine ⟨k - 1, by omega, ?_⟩
      omega
    have hz := (List.find?_eq_none.mp
      (hScan.symm.trans h)) k hm
    simpa using hz
  · intro hNo
    rw [hScan]
    apply List.find?_eq_none.mpr
    intro k hk
    obtain ⟨j, hj, heq⟩ := (List.mem_range').1 hk
    have hpos : 1 ≤ k := by omega
    have hbound : k ≤ d := by omega
    simpa [hNo k hpos hbound]

/-- The length of a takeWhile on a consecutive range is precisely
    its true prefix, stopped either by the first false item or
    by exhaustion. This is a core List induction, not Nat.find. -/
private theorem grantDrainWarmTakeWhileCount
    (test : Nat → Bool) :
    ∀ length start count,
      ((List.range' start length).takeWhile test).length = count ↔
        count ≤ length ∧
        (∀ k : Nat, start ≤ k → k < start + count →
          test k = true) ∧
        (count = length ∨ test (start + count) = false) := by
  intro length
  induction length with
  | zero =>
      intro start count
      constructor
      · intro h
        have hz : count = 0 := by
          simp [List.range', List.takeWhile] at h
          omega
        subst count
        refine ⟨by omega, ?_, Or.inl rfl⟩
        intro k hk hlt
        omega
      · rintro ⟨hbound, _, _⟩
        have hz : count = 0 := by omega
        subst count
        simp [List.range', List.takeWhile]
  | succ length ih =>
      intro start count
      cases ht : test start with
      | false =>
          have hHead :
              ((List.range' start (length + 1)).takeWhile test).length =
                0 := by
            simp [List.range'_succ, List.takeWhile, ht]
          constructor
          · intro h
            rw [hHead] at h
            have hz : count = 0 := by omega
            subst count
            refine ⟨by omega, ?_, Or.inr ?_⟩
            · intro k hk hlt
              omega
            · simpa using ht
          · rintro ⟨hbound, hprefix, _⟩
            have hz : count = 0 := by
              by_cases hc : count = 0
              · exact hc
              · have hpos : 0 < count := by omega
                have hwrong := hprefix start (Nat.le_refl _) (by omega)
                rw [ht] at hwrong
                cases hwrong
            rw [hz]
            exact hHead
      | true =>
          have hHead :
              ((List.range' start (length + 1)).takeWhile test).length =
                ((List.range' (start + 1) length).takeWhile test).length + 1 := by
            simp [List.range'_succ, List.takeWhile, ht]
          constructor
          · intro h
            rw [hHead] at h
            have hpos : 1 ≤ count := by omega
            have htail :
                ((List.range' (start + 1) length).takeWhile test).length =
                  count - 1 := by omega
            obtain ⟨hbound, hprefix, hstop⟩ :=
              (ih (start + 1) (count - 1)).mp htail
            refine ⟨by omega, ?_, ?_⟩
            · intro k hk hlt
              by_cases he : k = start
              · simpa [he] using ht
              · exact hprefix k (by omega) (by omega)
            · rcases hstop with hfull | hfalse
              · left
                omega
              · right
                have hidx : start + 1 + (count - 1) =
                    start + count := by omega
                rw [hidx] at hfalse
                exact hfalse
          · rintro ⟨hbound, hprefix, hstop⟩
            have hpos : 1 ≤ count := by
              by_cases hc : count = 0
              · subst count
                rcases hstop with heq | hf
                · omega
                · have hwrong : test start = false := by
                    simpa using hf
                  rw [ht] at hwrong
                  cases hwrong
              · omega
            have htail :
                ((List.range' (start + 1) length).takeWhile test).length =
                  count - 1 := by
              apply (ih (start + 1) (count - 1)).mpr
              refine ⟨by omega, ?_, ?_⟩
              · intro k hk hlt
                exact hprefix k (by omega) (by omega)
              · rcases hstop with hfull | hfalse
                · left
                  omega
                · right
                  have hidx : start + 1 + (count - 1) =
                      start + count := by omega
                  rw [hidx]
                  exact hfalse
            rw [hHead, htail]
            omega

private theorem grantDrainWarmZeroRange (length : Nat) :
    List.range length = List.range' 0 length := by
  simpa using (List.range'_eq_map_range
    (s := 0) (n := length)).symm

/-- A zero-distance left shift is the original site. -/
theorem grantDrainWarmShiftLeftZero
    {n : Nat} (ring : DirectedRing n) (g : Fin n) :
    PPL.shiftLeft ring g 0 = g := by
  apply Fin.ext
  change (g.val + n - 0 % n) % n = g.val
  simp [Nat.mod_eq_of_lt g.isLt]

/-- A signal-one host has at least one true entry in its
    nonempty terminal scan, including distance zero. -/
private theorem grantDrainWarmTerminalPositive
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n)
    (d : Nat) (hd : 1 ≤ d) (hsg : (N g).sg = true) :
    1 ≤ ((List.range d).takeWhile
      (fun k => (N (PPL.shiftLeft ring g k)).sg)).length := by
  have hsize : d = (d - 1) + 1 := by omega
  have hList : List.range d = 0 :: List.range' 1 (d - 1) := by
    calc
      List.range d = List.range' 0 d :=
        grantDrainWarmZeroRange d
      _ = List.range' 0 ((d - 1) + 1) := by rw [← hsize]
      _ = 0 :: List.range' 1 (d - 1) := by
        simp [List.range'_succ]
  rw [hList]
  simp [List.takeWhile, grantDrainWarmShiftLeftZero, hsg]

/-- Exact characterization of terminal 1-run length, with f<d,
    all signal-one sites 0..f inclusive, and an actual stopping
    signal unless the scan has exhausted its bound. -/
theorem grantDrainWarmTerminalCharacterization
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) (d f : Nat)
    (hd : 1 ≤ d) (hsg : (N g).sg = true) :
    grantDrainTerminalRun ring N g d = f ↔
      f < d ∧
      (∀ k : Nat, k ≤ f →
        (N (PPL.shiftLeft ring g k)).sg = true) ∧
      (f + 1 = d ∨
        (N (PPL.shiftLeft ring g (f + 1))).sg = false) := by
  have hPos :=
    grantDrainWarmTerminalPositive ring N g d hd hsg
  have hCore :
      ((List.range d).takeWhile
        (fun k => (N (PPL.shiftLeft ring g k)).sg)).length =
          f + 1 ↔
      f + 1 ≤ d ∧
      (∀ k : Nat, k < f + 1 →
        (N (PPL.shiftLeft ring g k)).sg = true) ∧
      (f + 1 = d ∨
        (N (PPL.shiftLeft ring g (f + 1))).sg = false) := by
    rw [grantDrainWarmZeroRange]
    simpa using
      (grantDrainWarmTakeWhileCount
        (fun k => (N (PPL.shiftLeft ring g k)).sg) d 0 (f + 1))
  constructor
  · intro h
    have hlen :
        ((List.range d).takeWhile
          (fun k => (N (PPL.shiftLeft ring g k)).sg)).length =
            f + 1 := by
      unfold grantDrainTerminalRun at h
      omega
    obtain ⟨hbound, hprefix, hstop⟩ := hCore.mp hlen
    refine ⟨by omega, ?_, hstop⟩
    intro k hk
    exact hprefix k (by omega)
  · rintro ⟨hbound, hprefix, hstop⟩
    have hlen :
        ((List.range d).takeWhile
          (fun k => (N (PPL.shiftLeft ring g k)).sg)).length =
            f + 1 :=
      hCore.mpr ⟨by omega,
        (fun k hk => hprefix k (by omega)), hstop⟩
    unfold grantDrainTerminalRun
    rw [hlen]
    omega

/-- One-step counterclockwise composition, including arbitrary k
    and all wrap positions. The ring size n>=2 avoids 1%n=0. -/
theorem grantDrainWarmShiftLeftOneAdd
    {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (g : Fin n) (k : Nat) :
    PPL.shiftLeft ring (PPL.shiftLeft ring g 1) k =
      PPL.shiftLeft ring g (k + 1) := by
  apply Fin.ext
  have hone : 1 % n = 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hmod : (k + 1) % n = ((k % n) + 1) % n := by
    rw [Nat.add_mod, hone]
  have hkbound : k % n < n := Nat.mod_lt _ ring.hn
  change
    (((g.val + n - 1 % n) % n + n - k % n) % n) =
      ((g.val + n - (k + 1) % n) % n)
  rw [hone, hmod]
  have hsub :
      (g.val + n - 1) % n + n - k % n =
        (g.val + n - 1) % n + (n - k % n) := by omega
  rw [hsub, Nat.mod_add_mod]
  by_cases hshort : k % n + 1 < n
  · rw [Nat.mod_eq_of_lt hshort]
    have hcalc :
        (g.val + n - 1) + (n - k % n) =
          n + (g.val + n - (k % n + 1)) := by omega
    rw [hcalc, Nat.add_mod_left]
  · have heq : k % n + 1 = n := by omega
    rw [heq, Nat.mod_self]
    have hcalc :
        (g.val + n - 1) + (n - k % n) = g.val + n := by omega
    rw [hcalc, Nat.sub_zero]

/-- Successor followed by one left shift is identity, exactly
    the existing incoming-host geometry lemma. -/
theorem grantDrainWarmRightNeighborLeftOne
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (e : Fin n) :
    PPL.shiftLeft ring (ring.rightNeighbor e) 1 = e := by
  exact grantDrainWeakIncomingHostLeftNeighbor
    ring hn e (ring.rightNeighbor e) rfl

/-- The valid leader-scan rebase: if the first old leader lies
    at distance 2..n-1, moving the observer one step left gives
    exactly d-1. This needs no hypothesis on the NEW physical state. -/
theorem grantDrainWarmLeaderRebase
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (N : Fin n → CertNative)
    (g : Fin n) (d : Nat)
    (hmin : 2 ≤ d) (hmax : d < n)
    (hold : grantDrainLeftLeaderDistance ring N g = d) :
    grantDrainLeftLeaderDistance ring N
        (PPL.shiftLeft ring g 1) = d - 1 := by
  obtain ⟨hhit, hbefore⟩ :=
    (grantDrainWarmLeaderFirstCharacterization
      ring N g d (by omega) hmax).mp hold
  apply (grantDrainWarmLeaderFirstCharacterization
    ring N (PPL.shiftLeft ring g 1)
    (d - 1) (by omega) (by omega)).mpr
  constructor
  · rw [grantDrainWarmShiftLeftOneAdd ring (by omega) g (d - 1)]
    have heq : d - 1 + 1 = d := by omega
    rw [heq]
    exact hhit
  · intro k hk hkd
    rw [grantDrainWarmShiftLeftOneAdd ring (by omega) g k]
    exact hbefore (k + 1) (by omega) (by omega)

/-- If the OLD left bullet is at p>=2, it stays included
    in the rebased scan and has exact new distance p-1. -/
theorem grantDrainWarmBulletRebaseSome
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (N : Fin n → CertNative)
    (g : Fin n) (d p : Nat)
    (hd : 2 ≤ d) (hp : 2 ≤ p) (hpd : p ≤ d)
    (hold : grantDrainLeftBulletDistance ring N g d = some p) :
    grantDrainLeftBulletDistance ring N
      (PPL.shiftLeft ring g 1) (d - 1) = some (p - 1) := by
  obtain ⟨_, _, hhit, hbefore⟩ :=
    (grantDrainWarmBulletSomeCharacterization
      ring N g d p).mp hold
  apply (grantDrainWarmBulletSomeCharacterization
    ring N (PPL.shiftLeft ring g 1) (d - 1) (p - 1)).mpr
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [grantDrainWarmShiftLeftOneAdd ring (by omega) g (p - 1)]
    have heq : p - 1 + 1 = p := by omega
    rw [heq]
    exact hhit
  · intro k hk hkp
    rw [grantDrainWarmShiftLeftOneAdd ring (by omega) g k]
    exact hbefore (k + 1) (by omega) (by omega)

/-- An empty entire OLD inclusive bullet scan stays empty when
    its first position is removed by the new observer. -/
theorem grantDrainWarmBulletRebaseNone
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (N : Fin n → CertNative)
    (g : Fin n) (d : Nat) (hd : 1 ≤ d)
    (hold : grantDrainLeftBulletDistance ring N g d = none) :
    grantDrainLeftBulletDistance ring N
      (PPL.shiftLeft ring g 1) (d - 1) = none := by
  have hbefore :=
    (grantDrainWarmBulletNoneCharacterization ring N g d).mp hold
  apply (grantDrainWarmBulletNoneCharacterization
    ring N (PPL.shiftLeft ring g 1) (d - 1)).mpr
  intro k hk hkd
  rw [grantDrainWarmShiftLeftOneAdd ring (by omega) g k]
  exact hbefore (k + 1) (by omega) (by omega)

/-- An empty first signal at a nonempty scan forces f=0. -/
private theorem grantDrainWarmTerminalHeadFalse
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n)
    (d : Nat) (hd : 1 ≤ d)
    (hfalse : (N g).sg = false) :
    grantDrainTerminalRun ring N g d = 0 := by
  have hsize : d = (d - 1) + 1 := by omega
  have hList : List.range d = 0 :: List.range' 1 (d - 1) := by
    calc
      List.range d = List.range' 0 d :=
        grantDrainWarmZeroRange d
      _ = List.range' 0 ((d - 1) + 1) := by rw [← hsize]
      _ = 0 :: List.range' 1 (d - 1) := by
        simp [List.range'_succ]
  unfold grantDrainTerminalRun
  rw [hList]
  simp [List.takeWhile, grantDrainWarmShiftLeftZero, hfalse]

/-- For an old signal-one host and d>=2, f rebases exactly by
    subtraction of one, including the f=0 stopping boundary. -/
theorem grantDrainWarmTerminalRebase
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (N : Fin n → CertNative)
    (g : Fin n) (d f : Nat)
    (hd : 2 ≤ d) (hsg : (N g).sg = true)
    (hold : grantDrainTerminalRun ring N g d = f) :
    grantDrainTerminalRun ring N
      (PPL.shiftLeft ring g 1) (d - 1) = f - 1 := by
  obtain ⟨hbound, hprefix, hstop⟩ :=
    (grantDrainWarmTerminalCharacterization
      ring N g d f (by omega) hsg).mp hold
  cases f with
  | zero =>
      have hfalse :
          (N (PPL.shiftLeft ring g 1)).sg = false := by
        rcases hstop with hfull | hval
        · omega
        · exact hval
      exact grantDrainWarmTerminalHeadFalse
        ring N (PPL.shiftLeft ring g 1) (d - 1)
        (by omega) hfalse
  | succ f =>
      have hnewsig :
          (N (PPL.shiftLeft ring g 1)).sg = true :=
        hprefix 1 (by omega)
      have hnew :
          grantDrainTerminalRun ring N
            (PPL.shiftLeft ring g 1) (d - 1) = f := by
        apply (grantDrainWarmTerminalCharacterization
          ring N (PPL.shiftLeft ring g 1) (d - 1) f
          (by omega) hnewsig).mpr
        refine ⟨by omega, ?_, ?_⟩
        · intro k hk
          rw [grantDrainWarmShiftLeftOneAdd ring (by omega) g k]
          exact hprefix (k + 1) (by omega)
        · rcases hstop with hfull | hfalse
          · left
            omega
          · right
            rw [grantDrainWarmShiftLeftOneAdd ring (by omega) g (f + 1)]
            have heq : f + 1 + 1 = Nat.succ f + 1 := by omega
            rw [heq]
            exact hfalse
      simpa using hnew

/-! Small CLOSED counterexamples to the two unqualified claims
    of the question; no protocol transition or arbitrary leaf. -/

private def grantDrainWarmScanCounterRing : DirectedRing 5 :=
  ⟨by decide⟩

private def grantDrainWarmScanSelfLeader (i : Fin 5) : CertNative :=
  if i.val == 0 then firedNative
  else { l := false, b := (0 : Fin 3),
         sh := false, sg := false }

/-- c1 as originally worded is false. The ONLY leader is g=0,
    which is reached at distance n=5. The raw scan returns 5,
    although the tested nth position is a leader. -/
theorem grantDrainWarmFullScanNotNoLeaderWitness :
    grantDrainLeftLeaderDistance grantDrainWarmScanCounterRing
      grantDrainWarmScanSelfLeader (0 : Fin 5) = 5 ∧
    (grantDrainWarmScanSelfLeader
      (PPL.shiftLeft grantDrainWarmScanCounterRing
        (0 : Fin 5) 5)).l = true := by
  unfold grantDrainLeftLeaderDistance grantDrainWarmScanSelfLeader
  decide

private def grantDrainWarmScanNoLeader (_ : Fin 5) : CertNative :=
  { l := false, b := (0 : Fin 3), sh := false, sg := false }

/-- c5 as stated is false without a successful preceding-leader
    scan: a leaderless 5-ring has d=5 BOTH before and after
    moving the observer, instead of decreasing to d-1=4. -/
theorem grantDrainWarmLeaderlessRebaseWitness :
    (grantDrainWarmScanNoLeader
      (PPL.shiftLeft grantDrainWarmScanCounterRing
        (0 : Fin 5) 1)).l = false ∧
    grantDrainLeftLeaderDistance grantDrainWarmScanCounterRing
      grantDrainWarmScanNoLeader (0 : Fin 5) = 5 ∧
    grantDrainLeftLeaderDistance grantDrainWarmScanCounterRing
      grantDrainWarmScanNoLeader
        (PPL.shiftLeft grantDrainWarmScanCounterRing
          (0 : Fin 5) 1) = 5 ∧
    ¬ grantDrainLeftLeaderDistance grantDrainWarmScanCounterRing
        grantDrainWarmScanNoLeader
          (PPL.shiftLeft grantDrainWarmScanCounterRing
            (0 : Fin 5) 1) =
      grantDrainLeftLeaderDistance grantDrainWarmScanCounterRing
        grantDrainWarmScanNoLeader (0 : Fin 5) - 1 := by
  unfold grantDrainLeftLeaderDistance grantDrainWarmScanNoLeader
  decide

private def grantDrainWarmScanAdjacentBullet (i : Fin 5) : CertNative :=
  if i.val == 4 then
    { l := false, b := (1 : Fin 3), sh := false, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

/-- c5's unconditional p->p-1 is also false at p=1:
    the old bullet at the newly chosen host is not scanned from
    that host, since bullet distances start at 1 rather than 0. -/
theorem grantDrainWarmAdjacentBulletRebaseWitness :
    grantDrainLeftBulletDistance grantDrainWarmScanCounterRing
      grantDrainWarmScanAdjacentBullet (0 : Fin 5) 3 = some 1 ∧
    grantDrainLeftBulletDistance grantDrainWarmScanCounterRing
      grantDrainWarmScanAdjacentBullet
        (PPL.shiftLeft grantDrainWarmScanCounterRing
          (0 : Fin 5) 1) 2 = none := by
  unfold grantDrainLeftBulletDistance grantDrainWarmScanAdjacentBullet
  decide

end L3.GrantDrainEntrance
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeaderFirstCharacterization
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeaderFullCharacterization
#print axioms L3.GrantDrainEntrance.grantDrainWarmBulletSomeCharacterization
#print axioms L3.GrantDrainEntrance.grantDrainWarmBulletNoneCharacterization
#print axioms L3.GrantDrainEntrance.grantDrainWarmShiftLeftZero
#print axioms L3.GrantDrainEntrance.grantDrainWarmTerminalCharacterization
#print axioms L3.GrantDrainEntrance.grantDrainWarmShiftLeftOneAdd
#print axioms L3.GrantDrainEntrance.grantDrainWarmRightNeighborLeftOne
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeaderRebase
#print axioms L3.GrantDrainEntrance.grantDrainWarmBulletRebaseSome
#print axioms L3.GrantDrainEntrance.grantDrainWarmBulletRebaseNone
#print axioms L3.GrantDrainEntrance.grantDrainWarmTerminalRebase
#print axioms L3.GrantDrainEntrance.grantDrainWarmFullScanNotNoLeaderWitness
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeaderlessRebaseWitness
#print axioms L3.GrantDrainEntrance.grantDrainWarmAdjacentBulletRebaseWitness

namespace L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-! D.6 formalization.
    These are actual local rows, a physical no-birth signal-copy row,
    pure-birth subrows, and an incoming-observer rebase.  They do NOT
    assert the unproved all-event physical increment theorem. -/

/-- Turning additional Bool entries true cannot shorten takeWhile. -/
private theorem grantDrainWarmTakeWhileLengthMono
    {A : Type} (xs : List A) (a b : A → Bool)
    (h : ∀ x : A, x ∈ xs → a x = true → b x = true) :
    (xs.takeWhile a).length ≤ (xs.takeWhile b).length := by
  revert h
  induction xs with
  | nil =>
      intro _
      simp [List.takeWhile]
  | cons x xs ih =>
      intro h
      cases hx : a x with
      | false =>
          simp [List.takeWhile, hx]
      | true =>
          have hb : b x = true := h x (by simp) hx
          have ht :
              (xs.takeWhile a).length ≤
                (xs.takeWhile b).length := by
            apply ih
            intro y hy hfy
            exact h y (by simp [hy]) hfy
          simpa [List.takeWhile, hx, hb] using
            Nat.succ_le_succ ht

/-- Fixed-pointer signal expansion: leaders and bullets are fixed,
    the signal at the preceding leader is fixed, and signal ones
    cannot disappear.  This proves W cannot increase.  The premises
    are field-level facts, not the desired rank inequality. -/
theorem grantDrainWarmSignalExpansionRank
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (hL : ∀ i : Fin n, (M i).l = (N i).l)
    (hB : ∀ i : Fin n, (M i).b = (N i).b)
    (hEnd :
      (M (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring N g))).sg =
      (N (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring N g))).sg)
    (hSg : ∀ i : Fin n, (N i).sg = true →
      (M i).sg = true) :
    grantDrainWarmRank ring M g ≤ grantDrainWarmRank ring N g := by
  have hd :
      grantDrainLeftLeaderDistance ring M g =
        grantDrainLeftLeaderDistance ring N g := by
    simp [grantDrainLeftLeaderDistance, hL]
  have hp (d : Nat) :
      grantDrainLeftBulletDistance ring M g d =
        grantDrainLeftBulletDistance ring N g d := by
    simp [grantDrainLeftBulletDistance, hB]
  have hf (d : Nat) :
      grantDrainTerminalRun ring N g d ≤
        grantDrainTerminalRun ring M g d := by
    unfold grantDrainTerminalRun
    have hlen :=
      grantDrainWarmTakeWhileLengthMono
        (List.range d)
        (fun k => (N (PPL.shiftLeft ring g k)).sg)
        (fun k => (M (PPL.shiftLeft ring g k)).sg)
        (by
          intro k _ hk
          exact hSg (PPL.shiftLeft ring g k) hk)
    omega
  have hrun :=
    hf (grantDrainLeftLeaderDistance ring N g)
  simp only [grantDrainWarmRank, hd, hp, hEnd]
  cases hb :
      grantDrainLeftBulletDistance ring N g
        (grantDrainLeftLeaderDistance ring N g) with
  | none =>
      cases hs :
          (N (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring N g))).sg with
      | false =>
          simp [hb, hs] <;> omega
      | true =>
          simp [hb, hs] <;> omega
  | some p =>
      simp [hb] <;> omega

/-- Literal empty-follower/empty-follower E pair: the only native
    change is the OR-copy of the responder signal into the source. -/
theorem grantDrainWarmEmptyFollowerSignalCopyPair
    (x y : CertNative)
    (hxl : x.l = false) (hxb : x.b = (0 : Fin 3))
    (hyl : y.l = false) (hyb : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.l = x.l ∧
    (certLiteralEPair x y).1.b = x.b ∧
    (certLiteralEPair x y).1.sg = (x.sg || y.sg) ∧
    (certLiteralEPair x y).2 = y := by
  simp [certLiteralEPair, hxl, hxb, hyl, hyb, certFinThree]
  cases y
  simp_all

/-- Lift that exact local pair into global nativeE field facts.
    In particular, neither a bullet nor a leader is changed and
    every old signal one survives. -/
theorem grantDrainWarmEmptyFollowerSignalCopyNativeE
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (hxl : (N e).l = false)
    (hxb : (N e).b = (0 : Fin 3))
    (hyl : (N (ring.rightNeighbor e)).l = false)
    (hyb : (N (ring.rightNeighbor e)).b = (0 : Fin 3)) :
    ∀ i : Fin n,
      (nativeE ring N e i).l = (N i).l ∧
      (nativeE ring N e i).b = (N i).b ∧
      ((N i).sg = true → (nativeE ring N e i).sg = true) ∧
      ((N i).l = true →
        (nativeE ring N e i).sg = (N i).sg) := by
  intro i
  have hPair :=
    grantDrainWarmEmptyFollowerSignalCopyPair
      (N e) (N (ring.rightNeighbor e)) hxl hxb hyl hyb
  by_cases he : i = e
  · subst i
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [nativeE] using hPair.1
    · simpa [nativeE] using hPair.2.1
    · intro hsg
      have htrue :
          (certLiteralEPair (N e)
            (N (ring.rightNeighbor e))).1.sg = true := by
        rw [hPair.2.2.1, hsg]
        simp
      simpa [nativeE] using htrue
    · intro hl
      rw [hxl] at hl
      cases hl
  · by_cases hy : i = ring.rightNeighbor e
    · subst i
      simp [nativeE, he, hPair.2.2.2]
    · simp [nativeE, he, hy]

/-- Complete physical no-FIRE signal-copy row at a fixed observer.
    The endpoint-leader premise is the genuine rooted-sector scan
    fact required to keep the preceding leader signal unchanged. -/
theorem grantDrainWarmSignalCopyPhysicalNoBirth
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hxl : (s.native e).l = false)
    (hxb : (s.native e).b = (0 : Fin 3))
    (hyl : (s.native (ring.rightNeighbor e)).l = false)
    (hyb : (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none)
    (hLeader :
      (s.native (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))).l = true) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g ≤
      grantDrainWarmRank ring s.native g := by
  have hFields :=
    grantDrainWarmEmptyFollowerSignalCopyNativeE
      ring s.native e hxl hxb hyl hyb
  have hL :
      ∀ i : Fin n,
        (nativeE ring s.native e i).l = (s.native i).l := by
    intro i
    exact (hFields i).1
  have hB :
      ∀ i : Fin n,
        (nativeE ring s.native e i).b = (s.native i).b := by
    intro i
    exact (hFields i).2.1
  have hSg :
      ∀ i : Fin n, (s.native i).sg = true →
        (nativeE ring s.native e i).sg = true := by
    intro i hi
    exact (hFields i).2.2.1 hi
  have hEnd :
      (nativeE ring s.native e
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))).sg =
      (s.native (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))).sg :=
    (hFields (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).2.2.2
        hLeader
  have hRank :=
    grantDrainWarmSignalExpansionRank
      ring s.native (nativeE ring s.native e) g
      hL hB hEnd hSg
  change
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g
  have hNative :
      grantDrainNativeNext ring s e =
        nativeE ring s.native e := by
    simp [grantDrainNativeNext, hNone]
  rw [hNative]
  exact hRank

/-- A nonzero left bullet moves from an empty-follower source to
    its empty-follower responder, clearing the responder signal. -/
theorem grantDrainWarmLeftBulletMovePair
    (x y : CertNative)
    (hxl : x.l = false) (hxb : x.b ≠ (0 : Fin 3))
    (hyl : y.l = false) (hyb : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.b = x.b ∧
    (certLiteralEPair x y).2.sg = false := by
  have hbnon : x.b.val ≠ 0 := by
    intro hv
    apply hxb
    apply Fin.ext
    exact hv
  have hbpos : 0 < x.b.val := by omega
  have hfin : certFinThree x.b.val = x.b := by
    unfold certFinThree
    split
    · apply Fin.ext
      rfl
    · have hv := x.b.isLt
      omega
  have hzero : certFinThree 0 = (0 : Fin 3) := rfl
  simp [certLiteralEPair, hxl, hyl, hyb, hbpos, hfin, hzero]

/-- Ready front as RESPONDER: it dummy-fires before the incoming
    live bullet kills it, and its dummy remains on the old front. -/
theorem grantDrainWarmReadyResponderDeathPair
    (x y : CertNative)
    (hxl : x.l = false) (hxb : x.b = (2 : Fin 3))
    (hyl : y.l = true) (hys : y.sg = true) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.b = (1 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, hxl, hxb, hyl, hys, certFinThree]

/-- Unready unshielded front as RESPONDER: the live killer is
    consumed, the leader disappears, and any old responder dummy
    remains at that site. -/
theorem grantDrainWarmUnreadyFrontDeathPair
    (x y : CertNative)
    (hxl : x.l = false) (hxb : x.b = (2 : Fin 3))
    (hyl : y.l = true) (hysh : y.sh = false)
    (hys : y.sg = false) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.b = y.b ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, hxl, hxb, hyl, hysh, hys,
    certFinThree]

/-- The arithmetic of the possible front-death merge:
    L' ≤ n-1 and L ≥ 1 bound the increase by 2(n-2).
    The native case split identifying this as the only positive
    death case is NOT established by this lemma. -/
theorem grantDrainWarmExceptionalMergeArithmetic
    (n oldDistance newDistance f : Nat)
    (hn : 2 ≤ n) (ho : 1 ≤ oldDistance)
    (hnew : newDistance ≤ n - 1) :
    2 * newDistance - f + 1 ≤
      (2 * oldDistance - f + 1) + 2 * (n - 2) := by
  omega

/-- Pure birth outside the actual inclusive observer scan is
    exactly rank-neutral, independently of the other sectors. -/
theorem grantDrainWarmBirthOutsideScan
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (hOutside : ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring N g →
      PPL.shiftLeft ring g k ≠ z) :
    grantDrainWarmRank ring (canonicalBirth N z) g =
      grantDrainWarmRank ring N g := by
  exact
    (grantDrainWarmFullScanFrame
      ring N (canonicalBirth N z) g
      (by
        intro k hk
        simp [canonicalBirth, hOutside k hk])).2.2.2

/-- Pure-birth arithmetic, ahead of the bullet with the new
    right neighbor already inside the terminal signal block. -/
theorem grantDrainWarmBirthAheadCoveredArithmetic
    (p f w : Nat) (hw : 1 ≤ w) (hwp : w < p) :
    w + 2 ≤ p + 2 * (p - (f + 1)) + 1 := by
  omega

/-- Pure-birth arithmetic, ahead of the bullet and outside the
    terminal signal block: the resulting rank cannot rise. -/
theorem grantDrainWarmBirthAheadGapArithmetic
    (p f w : Nat) (hwp : w < p) (hgap : f + 1 < w) :
    2 * w - f + 1 ≤ p + 2 * (p - (f + 1)) := by
  omega

/-- Pure-birth arithmetic without a left bullet. Both possible
    new-front branches are at most the old nonready-front value. -/
theorem grantDrainWarmBirthNoBulletArithmetic
    (d f w : Nat) (hwd : w < d) (hf : f < d) :
    (2 * w - f + 1 ≤ 2 * d - f + 1) ∧
    (w + 2 ≤ 2 * d - f + 1) := by
  constructor <;> omega

/-- Exact W rebase for an incoming move, in an unchanged native
    word.  A bullet at distance one would fall off the inclusive
    left scan and is excluded: that crossing instead ends warm.
    The old nearest leader is at distance 2..n-1. -/
theorem grantDrainWarmIncomingRebaseRank
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (g : Fin n) (d f : Nat)
    (hd : 2 ≤ d) (hshort : d < n)
    (hDistance : grantDrainLeftLeaderDistance ring N g = d)
    (hSignal : (N g).sg = true)
    (hTerminal : grantDrainTerminalRun ring N g d = f)
    (hNoAdjacentBullet :
      ∀ p : Nat, grantDrainLeftBulletDistance ring N g d =
        some p → 2 ≤ p) :
    grantDrainWarmRank ring N (PPL.shiftLeft ring g 1) + 1 ≤
      grantDrainWarmRank ring N g := by
  have hLeader :=
    grantDrainWarmLeaderRebase
      ring hn N g d hd hshort hDistance
  have hTerm :=
    grantDrainWarmTerminalRebase
      ring hn N g d f hd hSignal hTerminal
  have hfBound : f < d :=
    ((grantDrainWarmTerminalCharacterization
      ring N g d f (by omega) hSignal).mp hTerminal).1
  have hShift :
      PPL.shiftLeft ring (PPL.shiftLeft ring g 1) (d - 1) =
        PPL.shiftLeft ring g d := by
    rw [grantDrainWarmShiftLeftOneAdd ring (by omega) g (d - 1)]
    have heq : d - 1 + 1 = d := by omega
    rw [heq]
  cases hb : grantDrainLeftBulletDistance ring N g d with
  | none =>
      have hbNew :=
        grantDrainWarmBulletRebaseNone
          ring hn N g d (by omega) hb
      cases hs : (N (PPL.shiftLeft ring g d)).sg with
      | false =>
          simp [grantDrainWarmRank, hDistance, hLeader,
            hTerminal, hTerm, hb, hbNew, hShift, hs] <;>
            omega
      | true =>
          simp [grantDrainWarmRank, hDistance, hLeader,
            hTerminal, hTerm, hb, hbNew, hShift, hs] <;>
            omega
  | some p =>
      have hBounds :=
        (grantDrainWarmBulletSomeCharacterization
          ring N g d p).mp hb
      have hbNew :=
        grantDrainWarmBulletRebaseSome
          ring hn N g d p hd
          (hNoAdjacentBullet p hb) hBounds.2.1 hb
      simp [grantDrainWarmRank, hDistance, hLeader,
        hTerminal, hTerm, hb, hbNew] <;> omega

end L3.GrantDrainEntrance
#print axioms L3.GrantDrainEntrance.grantDrainWarmSignalExpansionRank
#print axioms L3.GrantDrainEntrance.grantDrainWarmEmptyFollowerSignalCopyPair
#print axioms L3.GrantDrainEntrance.grantDrainWarmEmptyFollowerSignalCopyNativeE
#print axioms L3.GrantDrainEntrance.grantDrainWarmSignalCopyPhysicalNoBirth
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeftBulletMovePair
#print axioms L3.GrantDrainEntrance.grantDrainWarmReadyResponderDeathPair
#print axioms L3.GrantDrainEntrance.grantDrainWarmUnreadyFrontDeathPair
#print axioms L3.GrantDrainEntrance.grantDrainWarmExceptionalMergeArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainWarmBirthOutsideScan
#print axioms L3.GrantDrainEntrance.grantDrainWarmBirthAheadCoveredArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainWarmBirthAheadGapArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainWarmBirthNoBulletArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainWarmIncomingRebaseRank

namespace L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-!
Sector-local interface and literal locality for SS closure.
The universal multi-leader
E/birth/death closure is NOT asserted here.
-/

/-- The three sector-local conjuncts of Native.C_native, without
the separately required rooted PPlus condition.  The range is
the clockwise half-open sector [p,p+d), including the bullet at p. -/
def GrantDrainSettledSector {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1)) : Prop :=
  (∀ (a b : Fin n), a.val < d.val → b.val < d.val →
    HasBullet N (PPL.shiftRight ring p a.val) →
    HasBullet N (PPL.shiftRight ring p b.val) → a = b) ∧
  (∀ a : Fin n, a.val < d.val →
    HasBullet N (PPL.shiftRight ring p a.val) →
    ∀ k : Fin n, k.val ≤ a.val →
      (N (PPL.shiftRight ring p k.val)).sg = false) ∧
  ((∃ h : Fin n, h.val < d.val ∧
      HasBullet N (PPL.shiftRight ring p h.val) ∧
      (∀ k : Fin n, k.val ≤ h.val →
        (N (PPL.shiftRight ring p k.val)).sg = false) ∧
      signalZeroStarOneStar ring N p (h.val + 1) d.val)
    ∨
    ((∀ h : Fin n, h.val < d.val →
        ¬ HasBullet N (PPL.shiftRight ring p h.val)) ∧
      signalZeroStarOneStar ring N p 1 d.val ∧
      ((N p).sg = true →
        ∀ k : Fin n, 1 ≤ k.val → k.val < d.val →
          (N (PPL.shiftRight ring p k.val)).sg = true)))

/-- C_native is *exactly* rooted PB plus the conjunction of the
sector-local SS obligations, with no extra token or NoBadLive guard.
This theorem does not assume that any sector is preserved. -/
theorem grantDrainC_native_iff_sectors
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) :
    C_native ring N ↔
      PPlus ring N ∧
      ∀ (p : Fin n) (d : Fin (n + 1)),
        sectorLength ring N p d →
          GrantDrainSettledSector ring N p d := by
  constructor
  · intro h
    refine ⟨h.1.1, ?_⟩
    intro p d hSector
    exact ⟨(h.1.2 p d hSector).1,
      (h.1.2 p d hSector).2,
      h.2 p d hSector⟩
  · rintro ⟨hP, hLocal⟩
    refine ⟨⟨hP, ?_⟩, ?_⟩
    · intro p d hSector
      exact ⟨(hLocal p d hSector).1,
        (hLocal p d hSector).2.1⟩
    · intro p d hSector
      exact (hLocal p d hSector).2.2

/-- The sector prefix 0*1* is preserved when the records agree
on every offset from 0 through an enclosing upper distance. -/
theorem grantDrainSectorSignalSuffixOfArc
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (lo hi : Nat)
    (hhi : hi ≤ d.val)
    (hArc : ∀ k : Nat, k ≤ d.val →
      M (PPL.shiftRight ring p k) =
        N (PPL.shiftRight ring p k))
    (hOld : signalZeroStarOneStar ring N p lo hi) :
    signalZeroStarOneStar ring M p lo hi := by
  unfold signalZeroStarOneStar at hOld ⊢
  obtain ⟨cut, hLo, hCut, hZero, hOne⟩ := hOld
  refine ⟨cut, hLo, hCut, ?_, ?_⟩
  · intro k hkLo hkCut
    rw [hArc k.val (by omega)]
    exact hZero k hkLo hkCut
  · intro k hkCut hkHi
    rw [hArc k.val (by omega)]
    exact hOne k hkCut hkHi

/-- If the old full sector arc, including its terminal leader,
is unchanged, its sectorLength witness is still valid. -/
theorem grantDrainSectorLengthOfArc
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (hArc : ∀ k : Nat, k ≤ d.val →
      M (PPL.shiftRight ring p k) =
        N (PPL.shiftRight ring p k))
    (hOld : sectorLength ring N p d) :
    sectorLength ring M p d := by
  have hRoot : M p = N p := by
    simpa only [grantDrainWeakDeathShiftRightZero] using
      (hArc 0 (Nat.zero_le d.val))
  unfold sectorLength at hOld ⊢
  obtain ⟨hPos, hP, hEnd, hInterior⟩ := hOld
  refine ⟨hPos, ?_, ?_, ?_⟩
  · rw [hRoot]
    exact hP
  · rw [hArc d.val (Nat.le_refl _)]
    exact hEnd
  · intro k hkPos hkShort
    rw [hArc k.val (by omega)]
    exact hInterior k hkPos hkShort

/-- Local SS itself is stable under equality on the inclusive
sector arc. This transports *all three* conjuncts (bullet
uniqueness, zero trail, and the two disjoint signal phases).
No unspecified E or birth preservation theorem is used. -/
theorem grantDrainSettledSectorOfArc
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (hArc : ∀ k : Nat, k ≤ d.val →
      M (PPL.shiftRight ring p k) =
        N (PPL.shiftRight ring p k))
    (hOld : GrantDrainSettledSector ring N p d) :
    GrantDrainSettledSector ring M p d := by
  obtain ⟨hUnique, hZero, hPhase⟩ := hOld
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb hAM hBM
    have hAN : HasBullet N (PPL.shiftRight ring p a.val) := by
      change (N (PPL.shiftRight ring p a.val)).b ≠ (0 : Fin 3)
      rw [← hArc a.val (by omega)]
      exact hAM
    have hBN : HasBullet N (PPL.shiftRight ring p b.val) := by
      change (N (PPL.shiftRight ring p b.val)).b ≠ (0 : Fin 3)
      rw [← hArc b.val (by omega)]
      exact hBM
    exact hUnique a b ha hb hAN hBN
  · intro a ha hAM k hk
    have hAN : HasBullet N (PPL.shiftRight ring p a.val) := by
      change (N (PPL.shiftRight ring p a.val)).b ≠ (0 : Fin 3)
      rw [← hArc a.val (by omega)]
      exact hAM
    rw [hArc k.val (by omega)]
    exact hZero a ha hAN k hk
  · rcases hPhase with hSome | hNone
    · left
      obtain ⟨h, hh, hBullet, hTrail, hSuffix⟩ := hSome
      refine ⟨h, hh, ?_, ?_, ?_⟩
      · change (M (PPL.shiftRight ring p h.val)).b ≠ (0 : Fin 3)
        rw [hArc h.val (by omega)]
        exact hBullet
      · intro k hk
        rw [hArc k.val (by omega)]
        exact hTrail k hk
      · exact grantDrainSectorSignalSuffixOfArc
          ring N M p d (h.val + 1) d.val
          (Nat.le_refl _) hArc hSuffix
    · right
      obtain ⟨hNoneBullet, hSuffix, hReady⟩ := hNone
      refine ⟨?_, ?_, ?_⟩
      · intro h hh hMB
        apply hNoneBullet h hh
        change (N (PPL.shiftRight ring p h.val)).b ≠ (0 : Fin 3)
        rw [← hArc h.val (by omega)]
        exact hMB
      · exact grantDrainSectorSignalSuffixOfArc
          ring N M p d 1 d.val (Nat.le_refl _) hArc hSuffix
      · intro hMReady k hkPos hkShort
        have hNReady : (N p).sg = true := by
          have hRoot : M p = N p := by
            simpa only [grantDrainWeakDeathShiftRightZero] using
              (hArc 0 (Nat.zero_le d.val))
          rw [← hRoot]
          exact hMReady
        rw [hArc k.val (by omega)]
        exact hReady hNReady k hkPos hkShort

/-- Physical locality, at any n and for every hostile fresh request:
E and any FIRE overlay can touch only e and its responder.
This is independent of PB, SS, and NoBadLive. -/
theorem grantDrainSettledNativeStepOutsidePair
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e i : Fin n)
    (hiX : i ≠ e)
    (hiY : i ≠ ring.rightNeighbor e) :
    (grantDrainStep ring fresh update s e).native i =
      s.native i := by
  change grantDrainNativeNext ring s e i = s.native i
  exact grantDrainMarksNativeOutsidePairFrame
    ring s e i hiX hiY

/-- The requested sector frame: any old sector whose FULL arc
(including the endpoint's leader field) avoids the selected pair
remains a sector and retains SS after the actual physical step.
This is stronger on boundary geometry than merely avoiding
the sector's half-open body; a touched terminal leader may die. -/
theorem grantDrainStepFramesUntouchedSettledSector
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p : Fin n)
    (d : Fin (n + 1))
    (hC : C_native ring s.native)
    (hSector : sectorLength ring s.native p d)
    (hAway : ∀ k : Nat, k ≤ d.val →
      PPL.shiftRight ring p k ≠ e ∧
      PPL.shiftRight ring p k ≠ ring.rightNeighbor e) :
    sectorLength ring
      (grantDrainStep ring fresh update s e).native p d ∧
    GrantDrainSettledSector ring
      (grantDrainStep ring fresh update s e).native p d := by
  have hArc :
      ∀ k : Nat, k ≤ d.val →
        (grantDrainStep ring fresh update s e).native
          (PPL.shiftRight ring p k) =
        s.native (PPL.shiftRight ring p k) := by
    intro k hk
    exact grantDrainSettledNativeStepOutsidePair
      ring fresh update s e (PPL.shiftRight ring p k)
      (hAway k hk).1 (hAway k hk).2
  have hOldLocal : GrantDrainSettledSector ring s.native p d :=
    ((grantDrainC_native_iff_sectors ring s.native).mp hC).2
      p d hSector
  exact ⟨grantDrainSectorLengthOfArc
      ring s.native (grantDrainStep ring fresh update s e).native
      p d hArc hSector,
    grantDrainSettledSectorOfArc
      ring s.native (grantDrainStep ring fresh update s e).native
      p d hArc hOldLocal⟩

/-- Pure birth at a site outside the inclusive old sector arc
cannot change either the sector endpoints or its SS word.
This includes either possible FIRE site from grantDrainNativeNext,
but it is not the missing *split* case. -/
theorem grantDrainCanonicalBirthFramesSettledSector
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z p : Fin n)
    (d : Fin (n + 1))
    (hSector : sectorLength ring N p d)
    (hLocal : GrantDrainSettledSector ring N p d)
    (hAway : ∀ k : Nat, k ≤ d.val →
      PPL.shiftRight ring p k ≠ z) :
    sectorLength ring (canonicalBirth N z) p d ∧
      GrantDrainSettledSector ring (canonicalBirth N z) p d := by
  have hArc :
      ∀ k : Nat, k ≤ d.val →
        canonicalBirth N z (PPL.shiftRight ring p k) =
          N (PPL.shiftRight ring p k) := by
    intro k hk
    simp [canonicalBirth, hAway k hk]
  exact ⟨grantDrainSectorLengthOfArc
      ring N (canonicalBirth N z) p d hArc hSector,
    grantDrainSettledSectorOfArc
      ring N (canonicalBirth N z) p d hArc hLocal⟩

/-- E-only case (a), fully settled for a single leader by the
existing singleton native normal-form theorem.
The universal multi-leader internal-edge case is NOT claimed. -/
theorem grantDrainStepSingletonNoBirthPreserves_C_native
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hOne : OneNativeLeader s.native)
    (hC : C_native ring s.native)
    (hNoFire : grantDrainSelect ring s e = .none) :
    C_native ring (grantDrainStep ring fresh update s e).native := by
  have hE :
      C_native ring (nativeE ring s.native e) :=
    (nativeE_preserves_singleton_C_native
      hn ring s.native e ⟨hOne, hC⟩).2
  change C_native ring (grantDrainNativeNext ring s e)
  simpa [grantDrainNativeNext, hNoFire] using hE

/-- Case (a), a completely literal (possibly multi-leader) E-only
quiet pair. Both endpoints are empty, the responder is a follower,
and both signals are zero. Thus E leaves the entire native state
unchanged, not merely the two selected sectors. -/
theorem grantDrainStepQuietNoBirthPreserves_C_native
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hxB : (s.native e).b = (0 : Fin 3))
    (hxS : (s.native e).sg = false)
    (hyL : (s.native (ring.rightNeighbor e)).l = false)
    (hyB : (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hyS : (s.native (ring.rightNeighbor e)).sg = false)
    (hNoFire : grantDrainSelect ring s e = .none) :
    C_native ring (grantDrainStep ring fresh update s e).native := by
  have hE : nativeE ring s.native e = s.native :=
    grantDrainDummyEmptyQuietFollowerNativeEFixed
      ring hn s.native e hxB hxS hyL hyB hyS
  change C_native ring (grantDrainNativeNext ring s e)
  simpa [grantDrainNativeNext, hNoFire, hE] using hC

end L3.GrantDrainEntrance
#print axioms L3.GrantDrainEntrance.grantDrainC_native_iff_sectors
#print axioms L3.GrantDrainEntrance.grantDrainSectorSignalSuffixOfArc
#print axioms L3.GrantDrainEntrance.grantDrainSectorLengthOfArc
#print axioms L3.GrantDrainEntrance.grantDrainSettledSectorOfArc
#print axioms L3.GrantDrainEntrance.grantDrainSettledNativeStepOutsidePair
#print axioms L3.GrantDrainEntrance.grantDrainStepFramesUntouchedSettledSector
#print axioms L3.GrantDrainEntrance.grantDrainCanonicalBirthFramesSettledSector
#print axioms L3.GrantDrainEntrance.grantDrainStepSingletonNoBirthPreserves_C_native
#print axioms L3.GrantDrainEntrance.grantDrainStepQuietNoBirthPreserves_C_native

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Literal obstruction.

The requested comparison expressed with PPL.cyclicOffset is FALSE
for a singleton leader-hosted unclean DUMMY. Its first STRICTLY
clockwise leader is the same leader after a full n-site circuit.
PPL.cyclicOffset b b is zero, not n. A remote canonical birth
makes the new first leader closer in the actual clockwise order,
but its raw cyclicOffset becomes POSITIVE rather than <= 0.

This refutes the requested first-target offset inequality as
stated; it does NOT refute the paper's strictly-positive
clockwise-distance argument or the eventual < n hit quota.
-/

/-- Five-site genuine rooted source. The only OLD leader is 0.
It owns an unclean DUMMY because its signal is one. The source
has no live bullets, hence satisfies both PPlus and NoBadLive.
A separate OLD request and grant at 2 enable an F0 birth. -/
private def grantDrainDummyWrapRing : DirectedRing 5 :=
  ⟨by decide⟩

private def grantDrainDummyWrapNative (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (1 : Fin 3), sh := true, sg := true }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

private def grantDrainDummyWrapBefore : GrantDrainState 5 Unit :=
  { native := grantDrainDummyWrapNative
    request := fun i => i.val == 2
    grant := fun i => i.val == 2
    scratch := ()
    history := [] }

private def grantDrainDummyWrapAfter : GrantDrainState 5 Unit :=
  grantDrainStep grantDrainDummyWrapRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainDummyWrapBefore (2 : Fin 5)

/-- Use precisely the physical initial immutable-label family, not
an invented host map. The source cohort contains label id 0. -/
private noncomputable def grantDrainDummyWrapHosts
    (id : Fin 5) : Option (Fin 5) :=
  (grantDrainEntranceDummyInitial grantDrainDummyWrapRing
    grantDrainDummyWrapBefore id).host

private theorem grantDrainDummyWrapInitialPremises :
    PPlus grantDrainDummyWrapRing
      grantDrainDummyWrapBefore.native ∧
    GrantDrainEntranceNoBadLive grantDrainDummyWrapRing
      grantDrainDummyWrapBefore ∧
    GrantDrainEntranceUncleanDummyAt grantDrainDummyWrapRing
      grantDrainDummyWrapBefore.native (0 : Fin 5) := by
  unfold PPlus P PeacefulBullet GrantDrainEntranceNoBadLive
    SharedPaperNonleftmostLiveExact
    GrantDrainEntranceUncleanDummyAt
    GrantDrainEntranceBulletCleanAt
  decide

private theorem grantDrainDummyWrapInitialHost :
    grantDrainDummyWrapHosts (0 : Fin 5) =
      some (0 : Fin 5) := by
  change
    (grantDrainEntranceDummyInitial grantDrainDummyWrapRing
      grantDrainDummyWrapBefore (0 : Fin 5)).host =
        some (0 : Fin 5)
  exact (grantDrainEntranceDummyInitialHostIff
    grantDrainDummyWrapRing grantDrainDummyWrapBefore
    (0 : Fin 5)).mpr grantDrainDummyWrapInitialPremises.2.2

private theorem grantDrainDummyWrapActualBirth :
    grantDrainSelect grantDrainDummyWrapRing
      grantDrainDummyWrapBefore (2 : Fin 5) = .leftLocal ∧
    (grantDrainDummyWrapBefore.native (2 : Fin 5)).l = false ∧
    (grantDrainDummyWrapAfter.native (2 : Fin 5)).l = true ∧
    (grantDrainDummyWrapAfter.native (0 : Fin 5)).l = true := by
  unfold grantDrainDummyWrapAfter grantDrainDummyWrapBefore
    grantDrainDummyWrapNative grantDrainDummyWrapRing
  decide

/-- OLD target 0 is the first strictly clockwise leader from
the OLD host 0, reached only after the five-site wraparound. -/
private theorem grantDrainDummyWrapOldTarget :
    GrantDrainDummyClockwiseSectorTarget grantDrainDummyWrapRing
      grantDrainDummyWrapBefore.native (0 : Fin 5) (0 : Fin 5) := by
  unfold GrantDrainDummyClockwiseSectorTarget sectorLength
  decide

/-- The F0 birth at 2 is now the first strictly clockwise leader
from the same physical host 0. -/
private theorem grantDrainDummyWrapNewTarget :
    GrantDrainDummyClockwiseSectorTarget grantDrainDummyWrapRing
      grantDrainDummyWrapAfter.native (0 : Fin 5) (2 : Fin 5) := by
  unfold GrantDrainDummyClockwiseSectorTarget sectorLength
  decide

private theorem grantDrainDummyWrapPostUnclean :
    GrantDrainEntranceUncleanDummyAt grantDrainDummyWrapRing
      grantDrainDummyWrapAfter.native (0 : Fin 5) := by
  unfold GrantDrainEntranceUncleanDummyAt
    GrantDrainEntranceBulletCleanAt
  decide

/-- The OLD id=0 label actually survives the selected e=2
service at the same host: neither endpoint is site 0 and the
old DUMMY remains unclean after the canonical F0 birth. -/
theorem grantDrainDummyWrapIdentitySurvives :
    grantDrainDummyEdgeNextHost grantDrainDummyWrapRing
      (fun _ _ => false) (fun _ _ => ())
      grantDrainDummyWrapBefore grantDrainDummyWrapHosts
      (2 : Fin 5) (0 : Fin 5) = some (0 : Fin 5) := by
  classical
  have hOld := grantDrainDummyWrapInitialHost
  have hNotSource : (0 : Fin 5) ≠ (2 : Fin 5) := by decide
  have hNotResponder :
      (0 : Fin 5) ≠ grantDrainDummyWrapRing.rightNeighbor
        (2 : Fin 5) := by decide
  have hNotReady :
      ¬ ((0 : Fin 5) =
        grantDrainDummyWrapRing.rightNeighbor (2 : Fin 5) ∧
        GrantDrainDummyReadyResponder grantDrainDummyWrapRing
          grantDrainDummyWrapBefore (2 : Fin 5)) := by
    intro h
    exact hNotResponder h.1
  unfold grantDrainDummyEdgeNextHost
  rw [hOld]
  simp only [if_neg hNotSource, if_neg hNotReady]
  exact if_pos grantDrainDummyWrapPostUnclean

/-- This is the exact failed inequality requested in (1).
The old endpoint survives and the new first endpoint is a birth,
but raw cyclicOffset changes 0 -> 2, not a nonincrease. -/
theorem grantDrainDummyWrapCyclicOffsetRises :
    PPL.cyclicOffset grantDrainDummyWrapRing
      (0 : Fin 5) (0 : Fin 5) = 0 ∧
    PPL.cyclicOffset grantDrainDummyWrapRing
      (0 : Fin 5) (2 : Fin 5) = 2 ∧
    ¬ PPL.cyclicOffset grantDrainDummyWrapRing
        (0 : Fin 5) (2 : Fin 5) ≤
      PPL.cyclicOffset grantDrainDummyWrapRing
        (0 : Fin 5) (0 : Fin 5) := by
  unfold grantDrainDummyWrapRing
  decide

/-- There is NO alternative post-step first-clockwise target
with the alleged PPL.cyclicOffset <= old offset. This excludes
a second-target loophole in the negative example. -/
theorem grantDrainDummyWrapNoBoundedNewTarget :
    ¬ ∃ t' : Fin 5,
      GrantDrainDummyClockwiseSectorTarget grantDrainDummyWrapRing
        grantDrainDummyWrapAfter.native (0 : Fin 5) t' ∧
      PPL.cyclicOffset grantDrainDummyWrapRing
        (0 : Fin 5) t' ≤
      PPL.cyclicOffset grantDrainDummyWrapRing
        (0 : Fin 5) (0 : Fin 5) := by
  unfold GrantDrainDummyClockwiseSectorTarget sectorLength
  decide

/-- The corrected numerical observer gives a full lap, n, to
the strictly next leader when the endpoint equals the host.
This repairs the wraparound arithmetic, but by itself is NOT
a one-step or wordwise physical theorem. -/
def grantDrainDummyPositiveClockwiseOffset {n : Nat}
    (ring : DirectedRing n) (b t : Fin n) : Nat :=
  if b = t then n else PPL.cyclicOffset ring b t

theorem grantDrainDummyPositiveClockwiseOffsetSelf
    {n : Nat} (ring : DirectedRing n) (b : Fin n) :
    grantDrainDummyPositiveClockwiseOffset ring b b = n := by
  simp [grantDrainDummyPositiveClockwiseOffset]

theorem grantDrainDummyPositiveClockwiseOffsetLe
    {n : Nat} (ring : DirectedRing n) (b t : Fin n) :
    grantDrainDummyPositiveClockwiseOffset ring b t ≤ n := by
  unfold grantDrainDummyPositiveClockwiseOffset
  split
  · omega
  · exact Nat.le_of_lt (grantDrainEntranceArcOffsetLt ring b t)

theorem grantDrainDummyPositiveClockwiseOffsetPos
    {n : Nat} (ring : DirectedRing n) (hn : 0 < n)
    (b t : Fin n) :
    0 < grantDrainDummyPositiveClockwiseOffset ring b t := by
  unfold grantDrainDummyPositiveClockwiseOffset
  split
  · exact hn
  · rename_i hDifferent
    exact grantDrainDummyOffsetPositiveAwayFromTarget
      ring b t hDifferent

/-- Under the corrected full-lap convention, the same literal
birth does decrease the distance from 5 to 2, as desired. -/
theorem grantDrainDummyWrapPositiveDistanceDrops :
    grantDrainDummyPositiveClockwiseOffset
        grantDrainDummyWrapRing (0 : Fin 5) (2 : Fin 5) <
      grantDrainDummyPositiveClockwiseOffset
        grantDrainDummyWrapRing (0 : Fin 5) (0 : Fin 5) := by
  unfold grantDrainDummyPositiveClockwiseOffset
    grantDrainDummyWrapRing
  decide

end L3.GrantDrainEntrance
#print axioms L3.GrantDrainEntrance.grantDrainDummyWrapIdentitySurvives
#print axioms L3.GrantDrainEntrance.grantDrainDummyWrapCyclicOffsetRises
#print axioms L3.GrantDrainEntrance.grantDrainDummyWrapNoBoundedNewTarget
#print axioms L3.GrantDrainEntrance.grantDrainDummyPositiveClockwiseOffsetSelf
#print axioms L3.GrantDrainEntrance.grantDrainDummyPositiveClockwiseOffsetLe
#print axioms L3.GrantDrainEntrance.grantDrainDummyPositiveClockwiseOffsetPos
#print axioms L3.GrantDrainEntrance.grantDrainDummyWrapPositiveDistanceDrops

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Native-field lifting on the actual grantDrainStep.
The remaining all-n scan-to-rank step is NOT claimed below. -/

private theorem grantDrainWarmPhysicalPairDistinct
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (e : Fin n) : ring.rightNeighbor e ≠ e := by
  intro he
  have hv := congrArg Fin.val he
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- A literal no-FIRE grant-drain step has the exact nativeE
configuration, for arbitrary hostile request and scratch updates. -/
theorem grantDrainWarmPhysicalNoBirthNative
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hNone : grantDrainSelect ring s e = .none) :
    (grantDrainStep ring fresh update s e).native =
      nativeE ring s.native e := by
  change grantDrainNativeNext ring s e = nativeE ring s.native e
  simp [grantDrainNativeNext, hNone]

/-- (1), literal PHYSICAL no-birth left-bullet transport: the
old source bullet clears, the responder inherits it, and the
responder's signal clears. Every other site is framed. -/
theorem grantDrainWarmLeftBulletMovePhysicalFields
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hXL : (s.native e).l = false)
    (hXB : (s.native e).b ≠ (0 : Fin 3))
    (hYL : (s.native (ring.rightNeighbor e)).l = false)
    (hYB : (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    ((grantDrainStep ring fresh update s e).native e).b =
        (0 : Fin 3) ∧
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).b = (s.native e).b ∧
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).sg = false ∧
    (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
      (grantDrainStep ring fresh update s e).native i =
        s.native i) := by
  have hNative := grantDrainWarmPhysicalNoBirthNative
    ring fresh update s e hNone
  have hPair := grantDrainWarmLeftBulletMovePair
    (s.native e) (s.native (ring.rightNeighbor e))
    hXL hXB hYL hYB
  have hNe := grantDrainWarmPhysicalPairDistinct ring hn e
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hNative]
    simpa [nativeE] using hPair.1
  · rw [hNative]
    simpa [nativeE, hNe] using hPair.2.1
  · rw [hNative]
    simpa [nativeE, hNe] using hPair.2.2
  · intro i hi hy
    change grantDrainNativeNext ring s e i = s.native i
    exact grantDrainMarksNativeOutsidePairFrame
      ring s e i hi hy

/-- An actual nonzero bullet at the pointer terminates its warm
status, independently of its token ownership. -/
theorem grantDrainWarmPhysicalBulletEndsWarm
    {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hBullet : (s.native g).b ≠ (0 : Fin 3)) :
    grantDrainWarmAt s g = false := by
  have hv : (s.native g).b.val ≠ 0 := by
    intro he
    apply hBullet
    apply Fin.ext
    exact he
  have hBool : ((s.native g).b.val == 0) = false := by
    cases hb : ((s.native g).b.val == 0) with
    | false =>
        rfl
    | true =>
        have he : (s.native g).b.val = 0 :=
          (beq_iff_eq).mp hb
        exact False.elim (hv he)
  simp [grantDrainWarmAt, hBool]

/-- (1), the p=1 boundary: when the bullet's responder is g,
the new physical bullet at g leaves the warm class. -/
theorem grantDrainWarmLeftBulletContactPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hEdge : ring.rightNeighbor e = g)
    (hXL : (s.native e).l = false)
    (hXB : (s.native e).b ≠ (0 : Fin 3))
    (hYL : (s.native g).l = false)
    (hYB : (s.native g).b = (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainWarmAt (grantDrainStep ring fresh update s e) g =
      false := by
  have hFields := grantDrainWarmLeftBulletMovePhysicalFields
    ring hn fresh update s e hXL hXB
    (by rw [hEdge]; exact hYL)
    (by rw [hEdge]; exact hYB) hNone
  have hNewBullet :
      ((grantDrainStep ring fresh update s e).native g).b =
        (s.native e).b := by
    rw [← hEdge]
    exact hFields.2.1
  apply grantDrainWarmPhysicalBulletEndsWarm
  rw [hNewBullet]
  exact hXB

/-- (2a), physical ready front as SOURCE. The fresh LIVE travels
to the empty first follower, rather than staying at its leader. -/
theorem grantDrainWarmReadyFrontSourcePhysicalFields
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hXL : (s.native e).l = true)
    (hXS : (s.native e).sg = true)
    (hYL : (s.native (ring.rightNeighbor e)).l = false)
    (hYB : (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    ((grantDrainStep ring fresh update s e).native e).b =
        (0 : Fin 3) ∧
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).b = (2 : Fin 3) ∧
    (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
      (grantDrainStep ring fresh update s e).native i =
        s.native i) := by
  have hNative := grantDrainWarmPhysicalNoBirthNative
    ring fresh update s e hNone
  have hPair := grantDrainWarmReadyLeaderSourcePair
    (s.native e) (s.native (ring.rightNeighbor e))
    hXL hXS hYL hYB
  have hNe := grantDrainWarmPhysicalPairDistinct ring hn e
  refine ⟨?_, ?_, ?_⟩
  · rw [hNative]
    simpa [nativeE] using hPair.1
  · rw [hNative]
    simpa [nativeE, hNe] using hPair.2
  · intro i hi hy
    change grantDrainNativeNext ring s e i = s.native i
    exact grantDrainMarksNativeOutsidePairFrame
      ring s e i hi hy

/-- (2a), an adjacent ready-front source fires directly into g,
ending the warm state. -/
theorem grantDrainWarmReadyFrontSourceContactPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hEdge : ring.rightNeighbor e = g)
    (hXL : (s.native e).l = true)
    (hXS : (s.native e).sg = true)
    (hYL : (s.native g).l = false)
    (hYB : (s.native g).b = (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainWarmAt (grantDrainStep ring fresh update s e) g =
      false := by
  have hFields := grantDrainWarmReadyFrontSourcePhysicalFields
    ring hn fresh update s e hXL hXS
    (by rw [hEdge]; exact hYL)
    (by rw [hEdge]; exact hYB) hNone
  have hNewBullet :
      ((grantDrainStep ring fresh update s e).native g).b =
        (2 : Fin 3) := by
    rw [← hEdge]
    exact hFields.2.1
  apply grantDrainWarmPhysicalBulletEndsWarm
  rw [hNewBullet]
  intro he
  cases he

/-- (2b), physical ready front as RESPONDER. The incoming LIVE
killer is consumed, the old leader dies, but the ready dummy
remains on the old front site; all other sites are framed. -/
theorem grantDrainWarmReadyFrontResponderPhysicalFields
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hXL : (s.native e).l = false)
    (hXB : (s.native e).b = (2 : Fin 3))
    (hYL : (s.native (ring.rightNeighbor e)).l = true)
    (hYS : (s.native (ring.rightNeighbor e)).sg = true)
    (hNone : grantDrainSelect ring s e = .none) :
    ((grantDrainStep ring fresh update s e).native e).b =
        (0 : Fin 3) ∧
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).l = false ∧
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).b = (1 : Fin 3) ∧
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).sg = false ∧
    (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
      (grantDrainStep ring fresh update s e).native i =
        s.native i) := by
  have hNative := grantDrainWarmPhysicalNoBirthNative
    ring fresh update s e hNone
  have hPair := grantDrainWarmReadyResponderDeathPair
    (s.native e) (s.native (ring.rightNeighbor e))
    hXL hXB hYL hYS
  have hNe := grantDrainWarmPhysicalPairDistinct ring hn e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hNative]
    simpa [nativeE] using hPair.1
  · rw [hNative]
    simpa [nativeE, hNe] using hPair.2.1
  · rw [hNative]
    simpa [nativeE, hNe] using hPair.2.2.1
  · rw [hNative]
    simpa [nativeE, hNe] using hPair.2.2.2
  · intro i hi hy
    change grantDrainNativeNext ring s e i = s.native i
    exact grantDrainMarksNativeOutsidePairFrame
      ring s e i hi hy

/-- Opaque-Nat rank arithmetic for a left bullet moving one
site toward g when the terminal run loses at most one site.
Proving that physical scan update is the remaining hard step. -/
theorem grantDrainWarmLeftBulletMoveRankArithmetic
    (p oldF newF : Nat)
    (hp : 2 ≤ p)
    (hSignal : oldF ≤ newF + 1) :
    (p - 1) + 2 * ((p - 1) - (newF + 1)) + 1 ≤
      p + 2 * (p - (oldF + 1)) := by
  omega

/-- Ready leader as source: the old full signal block and its
successor bullet give at least one rank unit of decrease. -/
theorem grantDrainWarmReadyFrontSourceRankArithmetic
    (d : Nat) (hd : 2 ≤ d) :
    (d - 1) + 2 * ((d - 1) - ((d - 2) + 1)) + 1 ≤
      1 + d := by
  omega

/-- Small, literal five-site left-bullet move from 1 to 2
with a fixed warm grant at 3. This is a regression, not an all-n
proof of the scan change. -/
private def grantDrainWarmLeftBulletFiveAfter :
    GrantDrainState 5 Unit :=
  grantDrainStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWarmPairCaseLeader (1 : Fin 5)

theorem grantDrainWarmLeftBulletFiveTrace :
    grantDrainSelect grantDrainWarmPairCaseRing
        grantDrainWarmPairCaseLeader (1 : Fin 5) = .none ∧
    (grantDrainWarmPairCaseLeader.native (1 : Fin 5)).l = false ∧
    (grantDrainWarmPairCaseLeader.native (1 : Fin 5)).b =
      (2 : Fin 3) ∧
    (grantDrainWarmPairCaseLeader.native (2 : Fin 5)).l = false ∧
    (grantDrainWarmPairCaseLeader.native (2 : Fin 5)).b =
      (0 : Fin 3) ∧
    (grantDrainWarmLeftBulletFiveAfter.native (1 : Fin 5)).b =
      (0 : Fin 3) ∧
    (grantDrainWarmLeftBulletFiveAfter.native (2 : Fin 5)).b =
      (2 : Fin 3) ∧
    (grantDrainWarmLeftBulletFiveAfter.native (2 : Fin 5)).sg =
      false ∧
    grantDrainWarmAt grantDrainWarmPairCaseLeader (3 : Fin 5) =
      true ∧
    grantDrainWarmAt grantDrainWarmLeftBulletFiveAfter (3 : Fin 5) =
      true ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) = 2 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmLeftBulletFiveAfter.native (3 : Fin 5) = 1 := by
  decide

/-- PPlus, C_native and NoBadLive of this small PRE-state are
derived from the existing one-leader clean seed and exact
native closure, not assumed as an unproved leaf. -/
theorem grantDrainWarmLeftBulletFiveProduction :
    PPlus grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native ∧
    C_native grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native ∧
    GrantDrainEntranceNoBadLive grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader := by
  have hClean := grantDrainWarmPairCaseClean
  have hNoBad := grantDrainWarmPairCaseNoBad
  have hPB : PPlus grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native :=
    grantDrainStep_preserves_PPlus
      (by decide : 3 ≤ 5)
      grantDrainWarmPairCaseRing
      (fun _ _ => false) (fun _ _ => ())
      grantDrainWarmPairCaseInitial (0 : Fin 5) hClean.1
  have hSingle :
      OneNativeLeader grantDrainWarmPairCaseInitial.native := by
    refine ⟨(0 : Fin 5), by decide, ?_⟩
    intro i hi
    revert hi
    revert i
    decide
  have hNone :
      grantDrainSelect grantDrainWarmPairCaseRing
        grantDrainWarmPairCaseInitial (0 : Fin 5) = .none := by
    decide
  have hNat := grantDrainWarmPhysicalNoBirthNative
    grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWarmPairCaseInitial (0 : Fin 5) hNone
  have hC := (nativeE_preserves_singleton_C_native
      (by decide : 5 ≤ 5)
      grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native (0 : Fin 5)
      ⟨hSingle, hClean.2⟩).2
  have hNatEq :
      grantDrainWarmPairCaseLeader.native =
        nativeE grantDrainWarmPairCaseRing
          grantDrainWarmPairCaseInitial.native (0 : Fin 5) := hNat
  rw [← hNatEq] at hC
  have hNoBadNew :=
    grantDrainEntrancePhysicalNoBadNext
      grantDrainWarmPairCaseRing (by decide : 5 ≤ 5)
      (fun _ _ => false) (fun _ _ => ())
      grantDrainWarmPairCaseInitial (0 : Fin 5)
      hClean.1 hNoBad
  exact ⟨hPB, hC, hNoBadNew⟩

/-- The concrete continuing left-bullet move pays zero FIRE and
zero exceptional-death charges; this verifies the exact requested
rank inequality on this closed physical trace. -/
theorem grantDrainWarmLeftBulletFiveCharged :
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmLeftBulletFiveAfter.native (3 : Fin 5) + 1 ≤
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) +
    (if grantDrainSelect grantDrainWarmPairCaseRing
        grantDrainWarmPairCaseLeader (1 : Fin 5) = .none
     then 0 else 1) +
    (if grantDrainExceptionalDeath grantDrainWarmPairCaseRing
        grantDrainWarmPairCaseLeader (1 : Fin 5) (3 : Fin 5)
     then 2 * (5 - 2) else 0) := by
  decide

/-- The already identified ready-front SOURCE example has a
strict charged decrease on its literal n=5 physical step. -/
theorem grantDrainWarmReadyFrontSourceFiveCharged :
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) + 1 ≤
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native (3 : Fin 5) +
    (if grantDrainSelect grantDrainWarmPairCaseRing
        grantDrainWarmPairCaseInitial (0 : Fin 5) = .none
     then 0 else 1) +
    (if grantDrainExceptionalDeath grantDrainWarmPairCaseRing
        grantDrainWarmPairCaseInitial (0 : Fin 5) (3 : Fin 5)
     then 2 * (5 - 2) else 0) := by
  decide

end L3.GrantDrainEntrance
#print axioms L3.GrantDrainEntrance.grantDrainWarmPhysicalNoBirthNative
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeftBulletMovePhysicalFields
#print axioms L3.GrantDrainEntrance.grantDrainWarmPhysicalBulletEndsWarm
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeftBulletContactPhysical
#print axioms L3.GrantDrainEntrance.grantDrainWarmReadyFrontSourcePhysicalFields
#print axioms L3.GrantDrainEntrance.grantDrainWarmReadyFrontSourceContactPhysical
#print axioms L3.GrantDrainEntrance.grantDrainWarmReadyFrontResponderPhysicalFields
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeftBulletMoveRankArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainWarmReadyFrontSourceRankArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeftBulletFiveTrace
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeftBulletFiveProduction
#print axioms L3.GrantDrainEntrance.grantDrainWarmLeftBulletFiveCharged
#print axioms L3.GrantDrainEntrance.grantDrainWarmReadyFrontSourceFiveCharged

namespace L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-!
D(b,t) is the already positive clockwise offset, assigning
distance n to the strict clockwise return to b itself. The single
ring-shift and sector-characterization lemmas below derive the actual
first-clockwise-leader comparison from sectorLength, rather than
assuming monotonicity of a dynamically selected target.

The wordwise quota concerns outgoing hits accumulated while an OLD
nonclean DUMMY identity STILL SURVIVES unclean at the end of the
word. Its last retiring/cleaning service is not counted as part of
a surviving prefix. This is the exact pathwise condition used in
the first-hit family tail argument.

The requested third cost type involving
  costNumerator (grantDrainEntranceNext ...) (fun x => I ring x.native) s T
is NOT well-typed with the existing definitions: grantDrainEntranceNext
accepts GrantDrainEntranceState, whereas I ring x.native expects a
GrantDrainState with a native field. The physical transition is
grantDrainStep, and the entrance ghost has x.physical.native.
The first-stage theorem controls GrantDrainEntranceDone for its
own ghost and does not automatically prove the DUMMY target I.
No unsupported cost theorem is asserted here.
-/

/-- The strictly-positive clockwise distance of a forward shift
by k in 1..n is k, even at k=n (returning to the origin). -/
theorem grantDrainDummyPositiveOffsetOfShift
    {n : Nat} (ring : DirectedRing n)
    (b t : Fin n) (k : Nat)
    (hk : 0 < k) (hkn : k ≤ n)
    (ht : PPL.shiftRight ring b k = t) :
    grantDrainDummyPositiveClockwiseOffset ring b t = k := by
  by_cases hsmall : k < n
  · have hOffset : PPL.cyclicOffset ring b t = k := by
      rw [← ht]
      exact grantDrainWeakDeathOffsetShiftRight ring b k hsmall
    have hDifferent : b ≠ t := by
      intro heq
      rw [← heq, grantDrainDummyArcOffsetSelf] at hOffset
      omega
    simp only [grantDrainDummyPositiveClockwiseOffset,
      if_neg hDifferent, hOffset]
  · have heq : k = n := by omega
    have hSame : b = t := by
      rw [heq, grantDrainMarksFullRotation ring b] at ht
      exact ht
    rw [← hSame]
    simp [grantDrainDummyPositiveClockwiseOffset, heq]

/-- A target specified by an actual native leader sector is at
precisely d-a positive clockwise sites from its host. This is
also correct for d=n and a=0, when the target equals the host. -/
theorem grantDrainDummySectorTargetDistance
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1)) (a : Fin n)
    (b t : Fin n)
    (hSector : sectorLength ring N p d)
    (ha : a.val < d.val)
    (hb : b = PPL.shiftRight ring p a.val)
    (ht : t = PPL.shiftRight ring p d.val) :
    grantDrainDummyPositiveClockwiseOffset ring b t =
      d.val - a.val := by
  have hSite :
      PPL.shiftRight ring b (d.val - a.val) = t := by
    rw [hb, grantDrainWeakDeathShiftRightAdd]
    have hSum : a.val + (d.val - a.val) = d.val := by omega
    rw [hSum]
    exact ht.symm
  have hPos : 0 < d.val - a.val := by omega
  have hBound : d.val - a.val ≤ n := by
    have hd := d.isLt
    omega
  exact grantDrainDummyPositiveOffsetOfShift
    ring b t (d.val - a.val) hPos hBound hSite

/-- A first strict clockwise leader minimizes the positive
distance among ALL leaders, including the host itself. The
proof uses the actual sector's leader-free interior. -/
theorem grantDrainDummyClockwiseTargetMin
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (b t q : Fin n)
    (hTarget : GrantDrainDummyClockwiseSectorTarget ring N b t)
    (hLeader : (N q).l = true) :
    grantDrainDummyPositiveClockwiseOffset ring b t ≤
      grantDrainDummyPositiveClockwiseOffset ring b q := by
  obtain ⟨p, d, a, hSector, ha, hAt, hEnd⟩ := hTarget
  have hDistance : grantDrainDummyPositiveClockwiseOffset ring b t =
      d.val - a.val :=
    grantDrainDummySectorTargetDistance ring N p d a b t
      hSector ha hAt hEnd
  by_cases hSame : q = b
  · subst q
    have hUpper :=
      grantDrainDummyPositiveClockwiseOffsetLe ring b t
    rw [grantDrainDummyPositiveClockwiseOffsetSelf]
    exact hUpper
  · have hDifferent : b ≠ q := Ne.symm hSame
    by_cases hBound :
        grantDrainDummyPositiveClockwiseOffset ring b t ≤
          grantDrainDummyPositiveClockwiseOffset ring b q
    · exact hBound
    · have hShort :
          grantDrainDummyPositiveClockwiseOffset ring b q <
            d.val - a.val := by
        rw [hDistance] at hBound
        omega
      have hPositive :
          0 < grantDrainDummyPositiveClockwiseOffset ring b q := by
        have hn : 0 < n := by
          have hh := b.isLt
          omega
        exact grantDrainDummyPositiveClockwiseOffsetPos ring
          hn b q
      have hIndexPositive :
          0 < a.val +
            grantDrainDummyPositiveClockwiseOffset ring b q := by
        omega
      have hIndexInside :
          a.val +
            grantDrainDummyPositiveClockwiseOffset ring b q <
              d.val := by
        omega
      have hIndexBound :
          a.val +
            grantDrainDummyPositiveClockwiseOffset ring b q < n := by
        have hd := d.isLt
        omega
      have hOffset :
          grantDrainDummyPositiveClockwiseOffset ring b q =
            PPL.cyclicOffset ring b q := by
        simp only [grantDrainDummyPositiveClockwiseOffset,
          if_neg hDifferent]
      have hSite :
          q = PPL.shiftRight ring b
            (grantDrainDummyPositiveClockwiseOffset ring b q) := by
        rw [hOffset]
        exact (grantDrainMarksArcShiftRightOffset ring b q).symm
      have hInterior : (N q).l = false := by
        have hCell := hSector.2.2.2
          (⟨a.val +
            grantDrainDummyPositiveClockwiseOffset ring b q,
            hIndexBound⟩ : Fin n)
          hIndexPositive hIndexInside
        have hq : q = PPL.shiftRight ring p
            (a.val + grantDrainDummyPositiveClockwiseOffset ring b q) := by
          calc q = PPL.shiftRight ring b
                (grantDrainDummyPositiveClockwiseOffset ring b q) := hSite
            _ = PPL.shiftRight ring (PPL.shiftRight ring p a.val)
                (grantDrainDummyPositiveClockwiseOffset ring b q) := by
              rw [← hAt]
            _ = _ := grantDrainWeakDeathShiftRightAdd ring p a.val _
        rw [hq]
        exact hCell
      rw [hLeader] at hInterior
      cases hInterior

/-- A full clockwise circuit from b has n edges; after one
outgoing move the remaining distance back to b is n-1.
This explicitly handles the old leader-hosted wrap case. -/
theorem grantDrainDummyOutgoingSelfDistance
    {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (b : Fin n) :
    grantDrainDummyPositiveClockwiseOffset ring
      (ring.rightNeighbor b) b + 1 = n := by
  have hRight :
      PPL.shiftRight ring b 1 = ring.rightNeighbor b := by
    apply Fin.ext
    rfl
  have hSite :
      PPL.shiftRight ring (ring.rightNeighbor b) (n - 1) = b := by
    rw [← hRight, grantDrainWeakDeathShiftRightAdd]
    have hSum : 1 + (n - 1) = n := by omega
    rw [hSum, grantDrainMarksFullRotation ring b]
  have hDistance :=
    grantDrainDummyPositiveOffsetOfShift ring
      (ring.rightNeighbor b) b (n - 1)
      (by omega : 0 < n - 1)
      (by omega : n - 1 ≤ n) hSite
  omega

/-- The actual OLD physical source and literal DUMMY carrier
satisfy the fixed-target inequality in POSITIVE distance.
The old target is an OLD leader, so a surviving label cannot
move into it and spuriously create a new n-lap distance. -/
theorem grantDrainDummyPositiveFixedTargetStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n))
    (e id b b' t : Fin n)
    (hOld : host id = some b)
    (hNew :
      grantDrainDummyEdgeNextHost ring fresh update s host e id =
        some b')
    (hLeader : (s.native t).l = true) :
    grantDrainDummyPositiveClockwiseOffset ring b' t +
      (if e = b then 1 else 0) ≤
        grantDrainDummyPositiveClockwiseOffset ring b t := by
  by_cases hDifferent : b ≠ t
  · have hNewDifferent : b' ≠ t :=
      grantDrainDummySurvivorAvoidsOldLeader
        ring fresh update s host e id b b' t
        hOld hNew hDifferent hLeader
    have hRaw :=
      grantDrainDummyOneLabelFixedTargetStep
        ring fresh update s host e id b b' t
        hOld hNew hDifferent
    simpa only [grantDrainDummyPositiveClockwiseOffset,
      if_neg hDifferent, if_neg hNewDifferent] using hRaw
  · have hSame : b = t := by
      exact Classical.not_not.mp hDifferent
    rcases grantDrainDummyEdgeSurvivorDisplacement
      ring fresh update s host e id b b' hOld hNew with
      ⟨hStay, hAway⟩ | ⟨hAt, hMove⟩
    · rw [hStay]
      have hOff : (if e = b then 1 else 0) = 0 :=
        if_neg hAway
      rw [hOff]
      omega
    · have hNom : e = b := hAt.symm
      have hMoveDistance :
          grantDrainDummyPositiveClockwiseOffset ring b' t + 1 = n := by
        rw [hMove, ← hAt, ← hSame]
        exact grantDrainDummyOutgoingSelfDistance
          ring (by omega : 2 ≤ n) b
      have hOldDistance :
          grantDrainDummyPositiveClockwiseOffset ring b t = n := by
        rw [hSame]
        exact grantDrainDummyPositiveClockwiseOffsetSelf ring t
      rw [if_pos hNom, hOldDistance]
      exact Nat.le_of_eq hMoveDistance

/-- This is the one-edge physical, dynamic-target comparison.
No hypothetical monotone-target premise: the OLD leader survives
by the existing NoBadLive theorem, the actual NEW target exists
by PPlus, and sector-first minimality gives the distance bound. -/
theorem grantDrainDummyUncleanTargetBound
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n))
    (e id b b' t t' : Fin n)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hBad : GrantDrainEntranceUncleanDummyAt ring s.native b)
    (hOld : host id = some b)
    (hNew :
      grantDrainDummyEdgeNextHost ring fresh update s host e id =
        some b')
    (hTarget : GrantDrainDummyClockwiseSectorTarget ring s.native b t)
    (hNextTarget : GrantDrainDummyClockwiseSectorTarget ring
      (grantDrainStep ring fresh update s e).native b' t') :
    grantDrainDummyPositiveClockwiseOffset ring b' t' +
      (if e = b then 1 else 0) ≤
        grantDrainDummyPositiveClockwiseOffset ring b t := by
  have hOldLeader : (s.native t).l = true := by
    obtain ⟨p, d, a, hSector, ha, hAt, hEnd⟩ := hTarget
    rw [hEnd]
    exact hSector.2.2.1
  have hNextLeader :
      ((grantDrainStep ring fresh update s e).native t).l = true :=
    grantDrainDummyUncleanOldTargetLeaderSurvives
      ring hn fresh update s host e id b b' t
      hNoBad hBad hOld hNew hTarget
  have hClosest :
      grantDrainDummyPositiveClockwiseOffset ring b' t' ≤
        grantDrainDummyPositiveClockwiseOffset ring b' t :=
    grantDrainDummyClockwiseTargetMin
      ring (grantDrainStep ring fresh update s e).native
      b' t' t hNextTarget hNextLeader
  have hFixed :=
    grantDrainDummyPositiveFixedTargetStep
      ring hn fresh update s host e id b b' t
      hOld hNew hOldLeader
  omega

/-- One-step theorem in the requested existential first-target
form: the new strictly clockwise first leader REALLY exists and
is no farther, with an additional unit drop on nomination. -/
theorem grantDrainDummyUncleanTargetSurvives
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (host : Fin n → Option (Fin n))
    (e id b b' t : Fin n)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hBad : GrantDrainEntranceUncleanDummyAt ring s.native b)
    (hOld : host id = some b)
    (hNew :
      grantDrainDummyEdgeNextHost ring fresh update s host e id =
        some b')
    (hTarget : GrantDrainDummyClockwiseSectorTarget ring s.native b t) :
    ∃ t' : Fin n,
      GrantDrainDummyClockwiseSectorTarget ring
        (grantDrainStep ring fresh update s e).native b' t' ∧
      grantDrainDummyPositiveClockwiseOffset ring b' t' +
        (if e = b then 1 else 0) ≤
          grantDrainDummyPositiveClockwiseOffset ring b t := by
  have hPBNext : PPlus ring
      (grantDrainStep ring fresh update s e).native :=
    grantDrainStep_preserves_PPlus
      (by omega : 3 ≤ n) ring fresh update s e hPB
  obtain ⟨t', hNextTarget⟩ :=
    grantDrainDummyClockwiseSectorTargetExists
      ring (grantDrainStep ring fresh update s e).native
      hPBNext b'
  exact ⟨t', hNextTarget,
    grantDrainDummyUncleanTargetBound
      ring hn fresh update s host e id b b' t t'
      hNoBad hBad hOld hNew hTarget hNextTarget⟩

/-- Genuine nominated-edge count for ONE immutable ghost label.
Only outgoing edges of its CURRENT host count, not edges of a
frozen entrance site. Ghost hosts evolve by the ACTUAL E+FIRE
step, and the function stops counting after retirement. -/
noncomputable def grantDrainDummyOutgoingHits
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (id : Fin n)
    (z : GrantDrainState n Scratch × (Fin n → Option (Fin n))) :
    List (Fin n) → Nat
  | [] => 0
  | e :: es =>
      (if z.2 id = some e then 1 else 0) +
        grantDrainDummyOutgoingHits ring fresh update id
          (grantDrainDummyEdgeWordStep ring fresh update z e) es

/-- PPlus is preserved along any literal physical/ghost word.
The ghost has no power to alter the physical native projection. -/
theorem grantDrainDummyEdgeWordPPlus
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (z : GrantDrainState n Scratch × (Fin n → Option (Fin n))),
      PPlus ring z.1.native →
      PPlus ring
        (word.foldl (grantDrainDummyEdgeWordStep
          ring fresh update) z).1.native := by
  intro word
  induction word with
  | nil =>
      intro z hPB
      exact hPB
  | cons e es ih =>
      intro z hPB
      have hNext : PPlus ring
          (grantDrainDummyEdgeWordStep
            ring fresh update z e).1.native := by
        change PPlus ring
          (grantDrainStep ring fresh update z.1 e).native
        exact grantDrainStep_preserves_PPlus
          (by omega : 3 ≤ n) ring fresh update z.1 e hPB
      change PPlus ring
        (es.foldl (grantDrainDummyEdgeWordStep ring fresh update)
          (grantDrainDummyEdgeWordStep ring fresh update z e)).1.native
      exact ih (grantDrainDummyEdgeWordStep ring fresh update z e) hNext

/-- Wordwise charging of every nominated outgoing hit to one
unit of the actual nearest-clockwise-leader distance. This
induction reselects the actual new target after every service;
no immutable-root or per-word ranking hypothesis is imported. -/
theorem grantDrainDummyUncleanWordConservation
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (z : GrantDrainState n Scratch × (Fin n → Option (Fin n)))
      (id b t b' t' : Fin n),
      PPlus ring z.1.native →
      GrantDrainEntranceNoBadLive ring z.1 →
      GrantDrainEntranceUncleanDummyAt ring z.1.native b →
      z.2 id = some b →
      GrantDrainDummyClockwiseSectorTarget ring z.1.native b t →
      (word.foldl (grantDrainDummyEdgeWordStep
        ring fresh update) z).2 id = some b' →
      GrantDrainDummyClockwiseSectorTarget ring
        (word.foldl (grantDrainDummyEdgeWordStep
          ring fresh update) z).1.native b' t' →
      grantDrainDummyOutgoingHits ring fresh update id z word +
        grantDrainDummyPositiveClockwiseOffset ring b' t' ≤
          grantDrainDummyPositiveClockwiseOffset ring b t := by
  intro word
  induction word with
  | nil =>
      intro z id b t b' t' hPB hNoBad hBad hOld hTarget
        hFinal hTargetFinal
      have hb : b = b' :=
        Option.some.inj (hOld.symm.trans hFinal)
      subst b'
      have hOldLeader : (z.1.native t).l = true := by
        obtain ⟨p, d, a, hSector, ha, hAt, hEnd⟩ := hTarget
        rw [hEnd]
        exact hSector.2.2.1
      have hClosest :=
        grantDrainDummyClockwiseTargetMin ring z.1.native
          b t' t hTargetFinal hOldLeader
      change 0 +
        grantDrainDummyPositiveClockwiseOffset ring b t' ≤
          grantDrainDummyPositiveClockwiseOffset ring b t
      omega
  | cons e es ih =>
      intro z id b t b' t' hPB hNoBad hBad hOld hTarget
        hFinal hTargetFinal
      change
        (es.foldl (grantDrainDummyEdgeWordStep ring fresh update)
          (grantDrainDummyEdgeWordStep ring fresh update z e)).2 id =
            some b' at hFinal
      change GrantDrainDummyClockwiseSectorTarget ring
        (es.foldl (grantDrainDummyEdgeWordStep ring fresh update)
          (grantDrainDummyEdgeWordStep ring fresh update z e)).1.native
          b' t' at hTargetFinal
      cases hNext :
          (grantDrainDummyEdgeWordStep
            ring fresh update z e).2 id with
      | none =>
          have hRetired :=
            grantDrainDummyEdgeWordRetired
              ring fresh update es
              (grantDrainDummyEdgeWordStep ring fresh update z e)
              id hNext
          rw [hRetired] at hFinal
          cases hFinal
      | some mid =>
          have hNextHost :
              grantDrainDummyEdgeNextHost ring fresh update
                z.1 z.2 e id = some mid := by
            exact hNext
          have hPBNext : PPlus ring
              (grantDrainDummyEdgeWordStep
                ring fresh update z e).1.native := by
            change PPlus ring
              (grantDrainStep ring fresh update z.1 e).native
            exact grantDrainStep_preserves_PPlus
              (by omega : 3 ≤ n) ring fresh update z.1 e hPB
          have hNoBadNext : GrantDrainEntranceNoBadLive ring
              (grantDrainDummyEdgeWordStep
                ring fresh update z e).1 := by
            change GrantDrainEntranceNoBadLive ring
              (grantDrainStep ring fresh update z.1 e)
            exact grantDrainEntrancePhysicalNoBadNext
              ring hn fresh update z.1 e hPB hNoBad
          have hBadNext : GrantDrainEntranceUncleanDummyAt ring
              (grantDrainDummyEdgeWordStep
                ring fresh update z e).1.native mid := by
            change GrantDrainEntranceUncleanDummyAt ring
              (grantDrainStep ring fresh update z.1 e).native mid
            exact grantDrainDummyEdgeHostSound
              ring fresh update z.1 z.2 e id mid hNextHost
          obtain ⟨u, hTargetMid⟩ :=
            grantDrainDummyClockwiseSectorTargetExists
              ring (grantDrainDummyEdgeWordStep
                ring fresh update z e).1.native hPBNext mid
          have hStepBound :
              grantDrainDummyPositiveClockwiseOffset ring mid u +
                (if e = b then 1 else 0) ≤
                  grantDrainDummyPositiveClockwiseOffset ring b t :=
            grantDrainDummyUncleanTargetBound
              ring hn fresh update z.1 z.2 e id b mid t u
              hNoBad hBad hOld hNextHost hTarget hTargetMid
          have hTailBound :=
            ih (grantDrainDummyEdgeWordStep
              ring fresh update z e)
              id mid u b' t' hPBNext hNoBadNext hBadNext
              hNext hTargetMid hFinal hTargetFinal
          have hHead :
              (if z.2 id = some e then 1 else 0) =
                (if e = b then 1 else 0) := by
            rw [hOld]
            by_cases he : e = b
            · subst e
              simp
            · have hbne : b ≠ e := fun h => he h.symm
              simp [he, hbne]
          change
            (if z.2 id = some e then 1 else 0) +
              grantDrainDummyOutgoingHits ring fresh update id
                (grantDrainDummyEdgeWordStep
                  ring fresh update z e) es +
              grantDrainDummyPositiveClockwiseOffset ring b' t' ≤
                grantDrainDummyPositiveClockwiseOffset ring b t
          rw [hHead]
          omega

/-- Per-label < n nominated outgoing-hit quota, from EVERY
protected NoBadLive Cartesian cut with an actually hosted
unclean DUMMY identity, along EVERY word on which that SAME
identity remains unclean. Neither roots nor grants are frozen. -/
theorem grantDrainDummyUncleanNominatedQuota
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch × (Fin n → Option (Fin n)))
    (word : List (Fin n)) (id b b' : Fin n)
    (hPB : PPlus ring z.1.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring z.1)
    (hBad : GrantDrainEntranceUncleanDummyAt ring z.1.native b)
    (hOld : z.2 id = some b)
    (hFinal :
      (word.foldl (grantDrainDummyEdgeWordStep
        ring fresh update) z).2 id = some b') :
    grantDrainDummyOutgoingHits ring fresh update id z word < n := by
  obtain ⟨t, hTarget⟩ :=
    grantDrainDummyClockwiseSectorTargetExists
      ring z.1.native hPB b
  have hPBFinal :=
    grantDrainDummyEdgeWordPPlus
      ring hn fresh update word z hPB
  obtain ⟨t', hTargetFinal⟩ :=
    grantDrainDummyClockwiseSectorTargetExists
      ring (word.foldl (grantDrainDummyEdgeWordStep
        ring fresh update) z).1.native hPBFinal b'
  have hConservation :=
    grantDrainDummyUncleanWordConservation
      ring hn fresh update word z id b t b' t'
      hPB hNoBad hBad hOld hTarget hFinal hTargetFinal
  have hPos :=
    grantDrainDummyPositiveClockwiseOffsetPos
      ring (by omega : 0 < n) b' t'
  have hCap :=
    grantDrainDummyPositiveClockwiseOffsetLe ring b t
  omega

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainDummyPositiveOffsetOfShift
#print axioms L3.GrantDrainEntrance.grantDrainDummySectorTargetDistance
#print axioms L3.GrantDrainEntrance.grantDrainDummyClockwiseTargetMin
#print axioms L3.GrantDrainEntrance.grantDrainDummyOutgoingSelfDistance
#print axioms L3.GrantDrainEntrance.grantDrainDummyPositiveFixedTargetStep
#print axioms L3.GrantDrainEntrance.grantDrainDummyUncleanTargetBound
#print axioms L3.GrantDrainEntrance.grantDrainDummyUncleanTargetSurvives
#print axioms L3.GrantDrainEntrance.grantDrainDummyEdgeWordPPlus
#print axioms L3.GrantDrainEntrance.grantDrainDummyUncleanWordConservation
#print axioms L3.GrantDrainEntrance.grantDrainDummyUncleanNominatedQuota

namespace L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-!
D6-PAIR-SCAN. These are pure observers, not physical-step lemmas.
The two unqualified clauses identified below are false even for
small clean native configurations. The corrected scan interfaces
are stated separately, without treating a scan conclusion as a
hypothesis.
-/

/-- If the two changed sites retain their leader flags, then the
entire leader scan is unchanged, including its distance-n fallback. -/
theorem grantDrainD6PairLeaderFlagsPreserved
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n) (k : Nat)
    (hAway : ∀ i : Fin n,
      i ≠ PPL.shiftLeft ring g (k + 1) →
      i ≠ PPL.shiftLeft ring g k →
      M i = N i)
    (hFar :
      (M (PPL.shiftLeft ring g (k + 1))).l =
        (N (PPL.shiftLeft ring g (k + 1))).l)
    (hNear :
      (M (PPL.shiftLeft ring g k)).l =
        (N (PPL.shiftLeft ring g k)).l) :
    grantDrainLeftLeaderDistance ring M g =
      grantDrainLeftLeaderDistance ring N g := by
  have hField : ∀ i : Fin n, (M i).l = (N i).l := by
    intro i
    by_cases hiFar : i = PPL.shiftLeft ring g (k + 1)
    · rw [hiFar]
      exact hFar
    · by_cases hiNear : i = PPL.shiftLeft ring g k
      · rw [hiNear]
        exact hNear
      · rw [hAway i hiFar hiNear]
  simp [grantDrainLeftLeaderDistance, hField]

/-- The candidate predicate is assembled from the old bullet
values outside the selected pair and the new values at the pair.
The ordered first hit of this predicate is their minimum. -/
def grantDrainD6PairBulletCandidate
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (k j : Nat) : Bool :=
  if j = k then
    (M (PPL.shiftLeft ring g k)).b.val != 0
  else if j = k + 1 then
    (M (PPL.shiftLeft ring g (k + 1))).b.val != 0
  else
    (N (PPL.shiftLeft ring g j)).b.val != 0

/-- P2 as an ordered-minimum formula for an inclusive scan.
Only the non-pair bullet projection is framed; neither signals
nor leader flags are constrained. -/
theorem grantDrainD6PairBulletCandidates
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (d k : Nat)
    (hOutside : ∀ j : Nat,
      1 ≤ j → j ≤ d → j ≠ k → j ≠ k + 1 →
      (M (PPL.shiftLeft ring g j)).b.val =
        (N (PPL.shiftLeft ring g j)).b.val) :
    grantDrainLeftBulletDistance ring M g d =
      (List.range' 1 d).find?
        (grantDrainD6PairBulletCandidate ring N M g k) := by
  unfold grantDrainLeftBulletDistance
  rw [grantDrainWarmScanRange]
  apply grantDrainWarmRangeFindCongr
  intro j hj hjd
  unfold grantDrainD6PairBulletCandidate
  by_cases hNear : j = k
  · subst j
    simp
  · by_cases hFar : j = k + 1
    · subst j
      simp [hNear]
    · have hBullet := hOutside j hj (by omega) hNear hFar
      simp [hNear, hFar, hBullet]

/-- A precise minimum characterization for the candidate scan:
p is selected iff it is a hit and every smaller positive offset
is absent. This includes the inclusive p=d endpoint. -/
theorem grantDrainD6PairBulletFirstCharacterization
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (d k p : Nat)
    (hOutside : ∀ j : Nat,
      1 ≤ j → j ≤ d → j ≠ k → j ≠ k + 1 →
      (M (PPL.shiftLeft ring g j)).b.val =
        (N (PPL.shiftLeft ring g j)).b.val) :
    grantDrainLeftBulletDistance ring M g d = some p ↔
      1 ≤ p ∧ p ≤ d ∧
      grantDrainD6PairBulletCandidate ring N M g k p = true ∧
      (∀ j : Nat, 1 ≤ j → j < p →
        grantDrainD6PairBulletCandidate ring N M g k j =
          false) := by
  rw [grantDrainD6PairBulletCandidates ring N M g d k hOutside]
  constructor
  · intro h
    obtain ⟨hLow, hHigh, hHit, hEarlier⟩ :=
      grantDrainWarmRangeFindConverse
        (grantDrainD6PairBulletCandidate ring N M g k)
        d 1 p h
    exact ⟨hLow, by omega, hHit, hEarlier⟩
  · rintro ⟨hLow, hHigh, hHit, hEarlier⟩
    exact grantDrainWarmRangeFirstHit
      (grantDrainD6PairBulletCandidate ring N M g k)
      d 1 p hLow (by omega) hHit hEarlier

/-- Correct P3 early-stop condition. The first false site at
offset f+1 must also lie strictly before the nearer changed
site k. Merely requiring f<k+1 is insufficient. -/
theorem grantDrainD6PairTerminalStopsBeforeNear
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (d k f : Nat)
    (hd : 1 ≤ d) (hWarm : (N g).sg = true)
    (hOld : grantDrainTerminalRun ring N g d = f)
    (hPrefix : ∀ j : Nat, j < k →
      M (PPL.shiftLeft ring g j) =
        N (PPL.shiftLeft ring g j))
    (hStopBefore : f + 1 < k) :
    grantDrainTerminalRun ring M g d = f := by
  obtain ⟨hBound, hTrue, hStop⟩ :=
    (grantDrainWarmTerminalCharacterization
      ring N g d f hd hWarm).mp hOld
  have hNewWarm : (M g).sg = true := by
    have hHead := hPrefix 0 (by omega)
    rw [grantDrainWarmShiftLeftZero] at hHead
    rw [hHead]
    exact hWarm
  apply (grantDrainWarmTerminalCharacterization
    ring M g d f hd hNewWarm).mpr
  refine ⟨hBound, ?_, ?_⟩
  · intro j hj
    rw [hPrefix j (by omega)]
    exact hTrue j hj
  · rcases hStop with hFull | hFalse
    · exact Or.inl hFull
    · right
      rw [hPrefix (f + 1) hStopBefore]
      exact hFalse

/-- P4 under the exact first-bullet and field-level frame facts.
A nearer old bullet would invalidate the asserted p-to-(p-1)
identity, hence the hypothesis is the old FIRST bullet, not just
an arbitrary old bullet at the farther site. -/
theorem grantDrainD6PairFirstBulletMoveRank
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (d k : Nat)
    (hk : 1 ≤ k) (hInside : k + 1 ≤ d)
    (hLeader : ∀ i : Fin n, (M i).l = (N i).l)
    (hSignal : ∀ i : Fin n, (M i).sg = (N i).sg)
    (hBulletPrefix : ∀ j : Nat, 1 ≤ j → j < k →
      (M (PPL.shiftLeft ring g j)).b.val =
        (N (PPL.shiftLeft ring g j)).b.val)
    (hDistance : grantDrainLeftLeaderDistance ring N g = d)
    (hOldFirst :
      grantDrainLeftBulletDistance ring N g d = some (k + 1))
    (hNewNear :
      (M (PPL.shiftLeft ring g k)).b.val ≠ 0)
    (hNewFarEmpty :
      (M (PPL.shiftLeft ring g (k + 1))).b.val = 0) :
    grantDrainLeftLeaderDistance ring M g = d ∧
    grantDrainLeftBulletDistance ring M g d = some k ∧
    grantDrainTerminalRun ring M g d =
      grantDrainTerminalRun ring N g d ∧
    grantDrainWarmRank ring M g + 1 ≤
      grantDrainWarmRank ring N g := by
  have hDistanceNew :
      grantDrainLeftLeaderDistance ring M g = d := by
    have hEqual :
        grantDrainLeftLeaderDistance ring M g =
          grantDrainLeftLeaderDistance ring N g := by
      simp [grantDrainLeftLeaderDistance, hLeader]
    exact hEqual.trans hDistance
  have hTerminal :
      grantDrainTerminalRun ring M g d =
        grantDrainTerminalRun ring N g d := by
    simp [grantDrainTerminalRun, hSignal]
  obtain ⟨_, _, _, hNoEarlier⟩ :=
    (grantDrainWarmBulletSomeCharacterization
      ring N g d (k + 1)).mp hOldFirst
  have hBulletNew :
      grantDrainLeftBulletDistance ring M g d = some k := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring M g d k).mpr
    refine ⟨hk, by omega, hNewNear, ?_⟩
    intro j hj hjk
    rw [hBulletPrefix j hj hjk]
    exact hNoEarlier j hj (by omega)
  have hArithmetic :=
    grantDrainWarmLeftBulletMoveRankArithmetic
      (k + 1)
      (grantDrainTerminalRun ring N g d)
      (grantDrainTerminalRun ring M g d)
      (by omega) (by rw [hTerminal]; omega)
  have hSubtract : k + 1 - 1 = k := by omega
  rw [hSubtract] at hArithmetic
  refine ⟨hDistanceNew, hBulletNew, hTerminal, ?_⟩
  calc
    grantDrainWarmRank ring M g + 1 =
        k + 2 * (k -
          (grantDrainTerminalRun ring M g d + 1)) + 1 := by
      simp [grantDrainWarmRank, hDistanceNew, hBulletNew]
    _ ≤ (k + 1) + 2 * ((k + 1) -
          (grantDrainTerminalRun ring N g d + 1)) := hArithmetic
    _ = grantDrainWarmRank ring N g := by
      simp [grantDrainWarmRank, hDistance, hOldFirst]

/-! Small closed counterexample to the original unqualified
far-site P1 branch and "does not reach u" P3 branch.
n=5, g=4, k=1, v=3, u=2. Both changed sites can become
leaders; the nearer one wins. Independently, changing sg at v
changes the terminal run even though its old f=1 is less than
the farther site's distance 2. No physical-step premise is used.
-/

private def grantDrainD6PairCounterRing : DirectedRing 5 :=
  ⟨by decide⟩

private def grantDrainD6PairCounterOld (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (0 : Fin 3), sh := true, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false,
      sg := (i.val == 3 || i.val == 4) }

private def grantDrainD6PairCounterNew (i : Fin 5) : CertNative :=
  if i.val == 0 || i.val == 2 || i.val == 3 then
    { l := true, b := (0 : Fin 3), sh := true, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false,
      sg := i.val == 4 }

/-- Only u=2 and v=3 may differ; the old/new states are rooted
and satisfy the full native SS condition as well. -/
theorem grantDrainD6PairCounterFrame :
    PPL.shiftLeft grantDrainD6PairCounterRing (4 : Fin 5) 2 =
      (2 : Fin 5) ∧
    PPL.shiftLeft grantDrainD6PairCounterRing (4 : Fin 5) 1 =
      (3 : Fin 5) ∧
    (∀ i : Fin 5,
      i ≠ (2 : Fin 5) → i ≠ (3 : Fin 5) →
      grantDrainD6PairCounterNew i =
        grantDrainD6PairCounterOld i) := by
  decide

theorem grantDrainD6PairCounterSettled :
    C_native grantDrainD6PairCounterRing
      grantDrainD6PairCounterOld ∧
    C_native grantDrainD6PairCounterRing
      grantDrainD6PairCounterNew := by
  decide

/-- P1 as phrased is false: the new leader at u=2 has distance
2<4, but the nearer changed site v=3 also becomes a leader, so
the new first distance is 1 rather than 2. -/
theorem grantDrainD6PairFarBirthNotFirstWitness :
    (grantDrainD6PairCounterOld (2 : Fin 5)).l = false ∧
    (grantDrainD6PairCounterNew (2 : Fin 5)).l = true ∧
    (grantDrainD6PairCounterOld (3 : Fin 5)).l = false ∧
    (grantDrainD6PairCounterNew (3 : Fin 5)).l = true ∧
    grantDrainLeftLeaderDistance grantDrainD6PairCounterRing
      grantDrainD6PairCounterOld (4 : Fin 5) = 4 ∧
    grantDrainLeftLeaderDistance grantDrainD6PairCounterRing
      grantDrainD6PairCounterNew (4 : Fin 5) = 1 ∧
    ¬ grantDrainLeftLeaderDistance grantDrainD6PairCounterRing
      grantDrainD6PairCounterNew (4 : Fin 5) = 2 := by
  decide

/-- P3 as phrased is false even on settled native states:
the old warm run f=1 does NOT reach u at distance 2, but
changing sg at v (distance 1) shortens that run to f=0. -/
theorem grantDrainD6PairTerminalNotFarWitness :
    (grantDrainD6PairCounterOld (4 : Fin 5)).sg = true ∧
    grantDrainTerminalRun grantDrainD6PairCounterRing
      grantDrainD6PairCounterOld (4 : Fin 5) 4 = 1 ∧
    grantDrainTerminalRun grantDrainD6PairCounterRing
      grantDrainD6PairCounterNew (4 : Fin 5) 4 = 0 ∧
    1 < (2 : Nat) ∧
    ¬ grantDrainTerminalRun grantDrainD6PairCounterRing
        grantDrainD6PairCounterNew (4 : Fin 5) 4 =
      grantDrainTerminalRun grantDrainD6PairCounterRing
        grantDrainD6PairCounterOld (4 : Fin 5) 4 := by
  decide

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6PairLeaderFlagsPreserved
#print axioms L3.GrantDrainEntrance.grantDrainD6PairBulletCandidates
#print axioms L3.GrantDrainEntrance.grantDrainD6PairBulletFirstCharacterization
#print axioms L3.GrantDrainEntrance.grantDrainD6PairTerminalStopsBeforeNear
#print axioms L3.GrantDrainEntrance.grantDrainD6PairFirstBulletMoveRank
#print axioms L3.GrantDrainEntrance.grantDrainD6PairCounterFrame
#print axioms L3.GrantDrainEntrance.grantDrainD6PairCounterSettled
#print axioms L3.GrantDrainEntrance.grantDrainD6PairFarBirthNotFirstWitness
#print axioms L3.GrantDrainEntrance.grantDrainD6PairTerminalNotFarWitness

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! Exact original-DUMMY ghost, no hypothetical physical map. -/

noncomputable def grantDrainDummyInitialUncleanHosts
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch) :
    Fin n → Option (Fin n) :=
  fun id => (grantDrainEntranceDummyInitial ring s id).host

def GrantDrainDummyUncleanRetired
    {n : Nat} {Scratch : Type}
    (z : GrantDrainState n Scratch × (Fin n → Option (Fin n))) : Prop :=
  ∀ id : Fin n, z.2 id = none

/-- The unused fallback after a label retires is needed only
to make the nominated edge total. It is never used on surviving
identity trajectories. -/
noncomputable def grantDrainDummyRetireChosen
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (id : Fin n)
    (z : GrantDrainState n Scratch × (Fin n → Option (Fin n))) :
    Fin n :=
  match z.2 id with
  | some host => host
  | none => ⟨0, ring.hn⟩

noncomputable def grantDrainDummyRetireChosenHits
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (id : Fin n) :
    (GrantDrainState n Scratch × (Fin n → Option (Fin n))) →
      List (Fin n) → Nat
  | _, [] => 0
  | z, e :: es =>
      (if e = grantDrainDummyRetireChosen ring id z then 1 else 0) +
        grantDrainDummyRetireChosenHits ring fresh update id
          (grantDrainDummyEdgeWordStep ring fresh update z e) es

/-- Survivors never passed through a retired state, so total
nominations agree with the true immutable-label outgoing hits. -/
theorem grantDrainDummyRetireChosenHitsOfSurvivor
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (id : Fin n) :
    ∀ (word : List (Fin n))
      (z : GrantDrainState n Scratch ×
        (Fin n → Option (Fin n))) (b : Fin n),
      (word.foldl (grantDrainDummyEdgeWordStep ring fresh update) z).2 id =
        some b →
      grantDrainDummyRetireChosenHits ring fresh update id z word =
        grantDrainDummyOutgoingHits ring fresh update id z word := by
  intro word
  induction word with
  | nil =>
      intro z b _
      rfl
  | cons e rest ih =>
      intro z b hFinal
      change
        (rest.foldl (grantDrainDummyEdgeWordStep ring fresh update)
          (grantDrainDummyEdgeWordStep ring fresh update z e)).2 id =
            some b at hFinal
      cases hOld : z.2 id with
      | none =>
          have hGone :
              (grantDrainDummyEdgeWordStep ring fresh update z e).2 id =
                none := by
            change grantDrainDummyEdgeNextHost
              ring fresh update z.1 z.2 e id = none
            exact grantDrainDummyEdgeRetiredAbsorbing
              ring fresh update z.1 z.2 e id hOld
          have hRetired := grantDrainDummyEdgeWordRetired
            ring fresh update rest
            (grantDrainDummyEdgeWordStep ring fresh update z e)
            id hGone
          rw [hRetired] at hFinal
          cases hFinal
      | some host =>
          have hTail := ih
            (grantDrainDummyEdgeWordStep ring fresh update z e)
            b hFinal
          have hHead :
              (if e = grantDrainDummyRetireChosen ring id z
               then 1 else 0) =
                (if z.2 id = some e then 1 else 0) := by
            by_cases he : e = host
            · simp [grantDrainDummyRetireChosen, hOld, he, eq_comm]
            · simp [grantDrainDummyRetireChosen, hOld, he, eq_comm]
          change
            (if e = grantDrainDummyRetireChosen ring id z
             then 1 else 0) +
              grantDrainDummyRetireChosenHits ring fresh update id
                (grantDrainDummyEdgeWordStep ring fresh update z e) rest =
            (if z.2 id = some e then 1 else 0) +
              grantDrainDummyOutgoingHits ring fresh update id
                (grantDrainDummyEdgeWordStep ring fresh update z e) rest
          rw [hHead, hTail]

/-- The actual n-hit quota, transferred to the total
predictable nomination only on still-living paths. -/
theorem grantDrainDummyRetireNotDoneShortHits
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (word : List (Fin n))
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hNotDone :
      ¬ GrantDrainDummyUncleanRetired
        (word.foldl (grantDrainDummyEdgeWordStep ring fresh update)
          (s, grantDrainDummyInitialUncleanHosts ring s))) :
    ∃ id : Fin n,
      grantDrainDummyRetireChosenHits ring fresh update id
        (s, grantDrainDummyInitialUncleanHosts ring s) word < n := by
  classical
  unfold GrantDrainDummyUncleanRetired at hNotDone
  obtain ⟨id, hNonempty⟩ := Classical.not_forall.mp hNotDone
  cases hFinal :
      (word.foldl (grantDrainDummyEdgeWordStep ring fresh update)
        (s, grantDrainDummyInitialUncleanHosts ring s)).2 id with
  | none =>
      exact False.elim (hNonempty hFinal)
  | some b =>
      cases hOld : grantDrainDummyInitialUncleanHosts ring s id with
      | none =>
          have hGone := grantDrainDummyEdgeWordRetired
            ring fresh update word
            (s, grantDrainDummyInitialUncleanHosts ring s)
            id hOld
          rw [hGone] at hFinal
          cases hFinal
      | some origin =>
          have hBad : GrantDrainEntranceUncleanDummyAt ring
              s.native origin :=
            (grantDrainDummyInitialFaithful ring s hPB hNoBad).1
              id origin hOld
          have hQuota := grantDrainDummyUncleanNominatedQuota
            ring hn fresh update
            (s, grantDrainDummyInitialUncleanHosts ring s)
            word id origin b hPB hNoBad hBad hOld hFinal
          have hEqual := grantDrainDummyRetireChosenHitsOfSurvivor
            ring fresh update id word
            (s, grantDrainDummyInitialUncleanHosts ring s) b hFinal
          exact ⟨id, by rw [hEqual]; exact hQuota⟩

/-- Surviving a first-hit word means the end is not done. -/
private theorem grantDrainDummyRetireSurvivalEndNot
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) :
    ∀ (x : S) (word : List (Fin n)),
      UniformFirstHit.survivalWord next P x word = 1 →
      ¬ P (word.foldl next x) := by
  classical
  intro x word
  induction word generalizing x with
  | nil =>
      intro hs hp
      simp [UniformFirstHit.survivalWord] at hs
      exact hs hp
  | cons e rest ih =>
      intro hs
      by_cases hp : P x
      · simp [UniformFirstHit.survivalWord, hp] at hs
      · have ht :
            UniformFirstHit.survivalWord next P (next x e) rest = 1 := by
          simpa only [UniformFirstHit.survivalWord, if_neg hp] using hs
        change ¬ P (rest.foldl next (next x e))
        exact ih (next x e) ht

private theorem grantDrainDummyRetireSurvivalBit
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) :
    ∀ (x : S) (w : List (Fin n)),
      UniformFirstHit.survivalWord next P x w ≤ 1 := by
  classical
  intro x w
  induction w generalizing x with
  | nil =>
      by_cases hp : P x
      · simp [UniformFirstHit.survivalWord, hp]
      · simp [UniformFirstHit.survivalWord, hp]
  | cons e es ih =>
      by_cases hp : P x
      · simp [UniformFirstHit.survivalWord, hp]
      · simpa only [UniformFirstHit.survivalWord, if_neg hp] using
          ih (next x e)

private theorem grantDrainDummyRetireOneLeSum
    (xs : List Nat) (h : (1 : Nat) ∈ xs) :
    1 ≤ xs.sum := by
  induction xs with
  | nil =>
      cases h
  | cons a rest ih =>
      simp only [List.mem_cons] at h
      rcases h with ha | hr
      · subst a
        simp only [List.sum_cons]
        omega
      · have ht := ih hr
        simp only [List.sum_cons]
        omega

private def grantDrainDummyRetireTailMissWeight {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n) :
    S → List (Fin n) → Nat
  | _, [] => 1
  | x, e :: es =>
      (if e = chosen x then 1 else 2) *
        grantDrainDummyRetireTailMissWeight next chosen (next x e) es

private theorem grantDrainDummyRetireTailEdgeWeight {n : Nat} (a : Fin n) :
    (List.ofFn (fun e : Fin n => if e = a then 1 else 2)).sum =
      2 * n - 1 := by
  induction n with
  | zero =>
      exact Fin.elim0 a
  | succ n ih =>
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then 1 else 2)).sum =
              n * 2 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then 1 else 2)
            (fun _ : Fin n => 2)
            (by
              intro i
              have hne : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hne])
          rw [hh, ofFn_sum_const]
        rw [if_pos rfl, ht]
        omega
      · intro b
        rw [List.ofFn_succ, List.sum_cons]
        have hne : (0 : Fin (n + 1)) ≠ b.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = b.val + 1 at hv
          omega
        rw [if_neg hne]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = b.succ then 1 else 2)
          (fun i : Fin n => if i = b then 1 else 2)
          (by
            intro i
            simp only [Fin.succ_inj])
        rw [hh, ih b]
        have hb := b.isLt
        omega

private theorem grantDrainDummyRetireTailScheduleMul {n : Nat} (T c : Nat)
    (f : List (Fin n) → Nat) :
    L3.Prob.scheduleSum n T (fun w => c * f w) =
      c * L3.Prob.scheduleSum n T f := by
  change FixedSpanRenewalPayload.wordSum n T (fun w => c * f w) =
    c * FixedSpanRenewalPayload.wordSum n T f
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun w => c * f w),
    ← FixedSpanRenewalPayload.rawWord_sum n T f,
    ofFn_sum_mul_left]

private theorem grantDrainDummyRetireTailMass {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n)
    (x : S) (T : Nat) (hn : 0 < n) :
    L3.Prob.scheduleSum n T
      (fun w => grantDrainDummyRetireTailMissWeight next chosen x w) =
        (2 * n - 1) ^ T := by
  induction T generalizing x with
  | zero =>
      simp [L3.Prob.scheduleSum, FixedSpanRenewalPayload.wordSum,
        allSchedules, grantDrainDummyRetireTailMissWeight]
  | succ T ih =>
      have hrow (e : Fin n) :
          L3.Prob.scheduleSum n T
            (fun w => grantDrainDummyRetireTailMissWeight next chosen x (e :: w)) =
          (if e = chosen x then 1 else 2) * (2 * n - 1) ^ T := by
        calc
          _ = L3.Prob.scheduleSum n T
                (fun w => (if e = chosen x then 1 else 2) *
                  grantDrainDummyRetireTailMissWeight next chosen (next x e) w) := rfl
          _ = (if e = chosen x then 1 else 2) *
                L3.Prob.scheduleSum n T
                  (fun w => grantDrainDummyRetireTailMissWeight next chosen (next x e) w) :=
                grantDrainDummyRetireTailScheduleMul T _ _
          _ = (if e = chosen x then 1 else 2) *
                (2 * n - 1) ^ T := by
                rw [ih (next x e)]
      calc
        L3.Prob.scheduleSum n (T + 1)
            (fun w => grantDrainDummyRetireTailMissWeight next chosen x w) =
          (List.ofFn (fun e : Fin n =>
            L3.Prob.scheduleSum n T
              (fun w => grantDrainDummyRetireTailMissWeight next chosen x (e :: w)))).sum :=
            FixedSpanRenewalPayload.wordSum_succ n T _
        _ = (List.ofFn (fun e : Fin n =>
              (if e = chosen x then 1 else 2) *
                (2 * n - 1) ^ T)).sum :=
            ofFn_sum_eq _ _ hrow
        _ = (List.ofFn (fun e : Fin n =>
              (2 * n - 1) ^ T *
                (if e = chosen x then 1 else 2))).sum :=
            ofFn_sum_eq _ _ (fun e => Nat.mul_comm _ _)
        _ = (2 * n - 1) ^ T *
              (List.ofFn (fun e : Fin n =>
                if e = chosen x then 1 else 2)).sum := by
            rw [ofFn_sum_mul_left]
        _ = (2 * n - 1) ^ T * (2 * n - 1) := by
            rw [grantDrainDummyRetireTailEdgeWeight]
        _ = (2 * n - 1) ^ (T + 1) := by
            rw [Nat.pow_succ]

private theorem grantDrainDummyRetireTailHitsProduct {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n)
    (hits : S → List (Fin n) → Nat)
    (hzero : ∀ y : S, hits y [] = 0)
    (hcons : ∀ (y : S) (e : Fin n) (es : List (Fin n)),
      hits y (e :: es) =
        (if e = chosen y then 1 else 0) + hits (next y e) es)
    (x : S) (w : List (Fin n)) :
    2 ^ (hits x w) * grantDrainDummyRetireTailMissWeight next chosen x w =
      2 ^ w.length := by
  induction w generalizing x with
  | nil =>
      simp [hzero, grantDrainDummyRetireTailMissWeight]
  | cons e es ih =>
      rw [hcons x e es]
      by_cases he : e = chosen x
      · simp only [if_pos he, grantDrainDummyRetireTailMissWeight,
          List.length_cons, Nat.one_mul]
        have hadd :
            1 + hits (next x e) es = hits (next x e) es + 1 := by
          omega
        rw [hadd, Nat.pow_succ, Nat.pow_succ]
        calc
          (2 ^ hits (next x e) es * 2) *
              grantDrainDummyRetireTailMissWeight next chosen (next x e) es =
            (2 ^ hits (next x e) es *
              grantDrainDummyRetireTailMissWeight next chosen (next x e) es) * 2 := by
                simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = 2 ^ es.length * 2 := by
                rw [ih (next x e)]
      · simp only [if_neg he, grantDrainDummyRetireTailMissWeight,
          List.length_cons, Nat.zero_add]
        rw [Nat.pow_succ]
        calc
          2 ^ hits (next x e) es *
              (2 * grantDrainDummyRetireTailMissWeight next chosen (next x e) es) =
            (2 ^ hits (next x e) es *
              grantDrainDummyRetireTailMissWeight next chosen (next x e) es) * 2 := by
                simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = 2 ^ es.length * 2 := by
                rw [ih (next x e)]

private theorem grantDrainDummyRetireTailScheduleLengthMul {n : Nat}
    (T c : Nat) (f : List (Fin n) → Nat) :
    L3.Prob.scheduleSum n T
      (fun w => c ^ (w.length + 1) * f w) =
    c ^ (T + 1) * L3.Prob.scheduleSum n T f := by
  change FixedSpanRenewalPayload.wordSum n T
      (fun w => c ^ (w.length + 1) * f w) =
    c ^ (T + 1) * FixedSpanRenewalPayload.wordSum n T f
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (fun w => c ^ (w.length + 1) * f w),
    ← FixedSpanRenewalPayload.rawWord_sum n T f]
  calc
    (List.ofFn (fun i : Fin (n ^ T) =>
        c ^ ((FixedSpanRenewalPayload.rawWord n T i).length + 1) *
          f (FixedSpanRenewalPayload.rawWord n T i))).sum =
      (List.ofFn (fun i : Fin (n ^ T) =>
        c ^ (T + 1) *
          f (FixedSpanRenewalPayload.rawWord n T i))).sum := by
        apply ofFn_sum_eq
        intro i
        rw [FixedSpanRenewalPayload.rawWord_length n T i]
    _ = c ^ (T + 1) *
          (List.ofFn (fun i : Fin (n ^ T) =>
            f (FixedSpanRenewalPayload.rawWord n T i))).sum := by
        rw [ofFn_sum_mul_left]

private theorem grantDrainDummyRetireTailWeighted {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n)
    (hits : S → List (Fin n) → Nat)
    (hzero : ∀ y : S, hits y [] = 0)
    (hcons : ∀ (y : S) (e : Fin n) (es : List (Fin n)),
      hits y (e :: es) =
        (if e = chosen y then 1 else 0) + hits (next y e) es)
    (x : S) (T Q : Nat) (hn : 0 < n) :
    2 ^ (T + 1) *
      L3.Prob.scheduleSum n T
        (fun w => if hits x w < Q then 1 else 0) ≤
      2 ^ Q * (2 * n - 1) ^ T := by
  have hpoint (w : List (Fin n)) :
      2 ^ (w.length + 1) *
        (if hits x w < Q then 1 else 0) ≤
      2 ^ Q * grantDrainDummyRetireTailMissWeight next chosen x w := by
    by_cases h : hits x w < Q
    · have hpow : 2 * 2 ^ (hits x w) ≤ 2 ^ Q := by
        have hmono : 2 ^ (hits x w + 1) ≤ 2 ^ Q :=
          Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)
        simpa only [Nat.pow_succ, Nat.mul_comm] using hmono
      simp only [if_pos h, Nat.mul_one]
      calc
        2 ^ (w.length + 1) =
          (2 * 2 ^ (hits x w)) *
            grantDrainDummyRetireTailMissWeight next chosen x w := by
              rw [Nat.pow_succ,
                ← grantDrainDummyRetireTailHitsProduct next chosen hits hzero hcons x w]
              simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ ≤ 2 ^ Q * grantDrainDummyRetireTailMissWeight next chosen x w :=
          Nat.mul_le_mul_right _ hpow
    · simp [h]
  calc
    2 ^ (T + 1) *
        L3.Prob.scheduleSum n T
          (fun w => if hits x w < Q then 1 else 0) =
      L3.Prob.scheduleSum n T
        (fun w => 2 ^ (w.length + 1) *
          (if hits x w < Q then 1 else 0)) :=
        (grantDrainDummyRetireTailScheduleLengthMul T 2 _).symm
    _ ≤ L3.Prob.scheduleSum n T
          (fun w => 2 ^ Q * grantDrainDummyRetireTailMissWeight next chosen x w) :=
        L3.Density.schedule_sum_mono T _ _ hpoint
    _ = 2 ^ Q * (2 * n - 1) ^ T := by
        rw [grantDrainDummyRetireTailScheduleMul, grantDrainDummyRetireTailMass next chosen x T hn]

theorem grantDrainDummyRetireWeightedFamilySurvival
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) (T : Nat) :
    2 ^ (T + 1) *
      UniformFirstHit.survivalNumerator
        (grantDrainDummyEdgeWordStep ring fresh update)
        GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s) T ≤
      n * (2 ^ n * (2 * n - 1) ^ T) := by
  classical
  have hpoint (w : List (Fin n)) :
      UniformFirstHit.survivalWord
        (grantDrainDummyEdgeWordStep ring fresh update)
        GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s) w ≤
      (List.ofFn (fun j : Fin n =>
        if grantDrainDummyRetireChosenHits ring fresh update j
          (s, grantDrainDummyInitialUncleanHosts ring s) w < n then 1 else 0)).sum := by
    by_cases hs : UniformFirstHit.survivalWord
        (grantDrainDummyEdgeWordStep ring fresh update)
        GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s) w = 1
    · have hNotDone := grantDrainDummyRetireSurvivalEndNot
        (grantDrainDummyEdgeWordStep ring fresh update)
        GrantDrainDummyUncleanRetired
        (s, grantDrainDummyInitialUncleanHosts ring s) w hs
      obtain ⟨j, hj⟩ := grantDrainDummyRetireNotDoneShortHits
        ring hn fresh update s w hPB hNoBad hNotDone
      have hMember : (1 : Nat) ∈
          List.ofFn (fun j : Fin n =>
            if grantDrainDummyRetireChosenHits ring fresh update j
              (s, grantDrainDummyInitialUncleanHosts ring s) w < n then 1 else 0) :=
        List.mem_ofFn.mpr ⟨j, by simp [hj]⟩
      rw [hs]
      exact grantDrainDummyRetireOneLeSum _ hMember
    · have hZero :
          UniformFirstHit.survivalWord
            (grantDrainDummyEdgeWordStep ring fresh update)
            GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s) w = 0 := by
        have hb := grantDrainDummyRetireSurvivalBit
          (grantDrainDummyEdgeWordStep ring fresh update)
          GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s) w
        omega
      rw [hZero]
      exact Nat.zero_le _
  have hmass :
      UniformFirstHit.survivalNumerator
        (grantDrainDummyEdgeWordStep ring fresh update)
        GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s) T ≤
      L3.Prob.scheduleSum n T
        (fun w => (List.ofFn (fun j : Fin n =>
          if grantDrainDummyRetireChosenHits ring fresh update j
            (s, grantDrainDummyInitialUncleanHosts ring s) w < n then 1 else 0)).sum) := by
    change L3.Prob.scheduleSum n T
      (UniformFirstHit.survivalWord
        (grantDrainDummyEdgeWordStep ring fresh update)
        GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)) ≤ _
    exact L3.Density.schedule_sum_mono T _ _ hpoint
  have hrow (j : Fin n) :
      2 ^ (T + 1) *
        L3.Prob.scheduleSum n T
          (fun w => if grantDrainDummyRetireChosenHits ring fresh update
            j (s, grantDrainDummyInitialUncleanHosts ring s) w < n then 1 else 0) ≤
      2 ^ n * (2 * n - 1) ^ T :=
    grantDrainDummyRetireTailWeighted
      (grantDrainDummyEdgeWordStep ring fresh update)
      (fun x => grantDrainDummyRetireChosen ring j x)
      (grantDrainDummyRetireChosenHits ring fresh update j)
      (by intro y; rfl)
      (by intro y e es; rfl)
      (s, grantDrainDummyInitialUncleanHosts ring s) T n (by omega : 0 < n)
  calc
    2 ^ (T + 1) *
        UniformFirstHit.survivalNumerator
          (grantDrainDummyEdgeWordStep ring fresh update)
          GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s) T ≤
      2 ^ (T + 1) *
        L3.Prob.scheduleSum n T
          (fun w => (List.ofFn (fun j : Fin n =>
            if grantDrainDummyRetireChosenHits ring fresh update j
              (s, grantDrainDummyInitialUncleanHosts ring s) w < n then 1 else 0)).sum) :=
        Nat.mul_le_mul_left _ hmass
    _ = (List.ofFn (fun j : Fin n =>
          2 ^ (T + 1) *
            L3.Prob.scheduleSum n T
              (fun w => if grantDrainDummyRetireChosenHits ring fresh update j
                (s, grantDrainDummyInitialUncleanHosts ring s) w < n then 1 else 0))).sum := by
        rw [L3.Density.schedule_sum_fin, ← ofFn_sum_mul_left]
    _ ≤ (List.ofFn (fun _ : Fin n =>
          2 ^ n * (2 * n - 1) ^ T)).sum :=
      ofFn_sum_le _ _ hrow
    _ = n * (2 ^ n * (2 * n - 1) ^ T) := by
      rw [ofFn_sum_const]

theorem grantDrainDummyRetireSurvivalAfterCutoff
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) (u : Nat) :
    4 * 2 ^ (3 * n ^ 2 + u) *
      UniformFirstHit.survivalNumerator
        (grantDrainDummyEdgeWordStep ring fresh update)
        GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
        (3 * n ^ 2 + u) ≤
      n * (2 * n) ^ (3 * n ^ 2) * (2 * n - 1) ^ u := by
  have hFamily := grantDrainDummyRetireWeightedFamilySurvival
    ring hn fresh update s hPB hNoBad (3 * n ^ 2 + u)
  have hCut := grantDrainEntranceThreeSquareCutoff n hn
  calc
    4 * 2 ^ (3 * n ^ 2 + u) *
        UniformFirstHit.survivalNumerator
          (grantDrainDummyEdgeWordStep ring fresh update)
          GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
          (3 * n ^ 2 + u) ≤
      2 * (n * (2 ^ n * (2 * n - 1) ^ (3 * n ^ 2 + u))) := by
        have hEq :
            4 * 2 ^ (3 * n ^ 2 + u) *
              UniformFirstHit.survivalNumerator
                (grantDrainDummyEdgeWordStep ring fresh update)
                GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
                (3 * n ^ 2 + u) =
            2 * (2 ^ ((3 * n ^ 2 + u) + 1) *
              UniformFirstHit.survivalNumerator
                (grantDrainDummyEdgeWordStep ring fresh update)
                GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
                (3 * n ^ 2 + u)) := by
          have hFour : (2 : Nat) * 2 = 4 := by decide
          have hPower :
              2 ^ ((3 * n ^ 2 + u) + 1) =
                2 ^ (3 * n ^ 2 + u) * 2 :=
            Nat.pow_succ 2 (3 * n ^ 2 + u)
          rw [hPower, ← hFour]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        rw [hEq]
        exact Nat.mul_le_mul_left 2 hFamily
    _ = n * (2 ^ (n + 1) * (2 * n - 1) ^ (3 * n ^ 2)) *
          (2 * n - 1) ^ u := by
        have hSplit :
            (2 * n - 1) ^ (3 * n ^ 2 + u) =
              (2 * n - 1) ^ (3 * n ^ 2) *
                (2 * n - 1) ^ u :=
          Nat.pow_add (2 * n - 1) (3 * n ^ 2) u
        have hPower : 2 ^ (n + 1) = 2 ^ n * 2 :=
          Nat.pow_succ 2 n
        rw [hSplit, hPower]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ ≤ n * (2 * n) ^ (3 * n ^ 2) * (2 * n - 1) ^ u :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left n hCut)

private theorem grantDrainDummyRetireSurvivalCountCap
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) (x : S) :
    ∀ t : Nat,
      UniformFirstHit.survivalNumerator next P x t ≤ n ^ t := by
  classical
  intro t
  induction t with
  | zero =>
      by_cases hx : P x
      · rw [UniformFirstHit.survivalNumerator_of_target next P x hx 0]
        exact Nat.zero_le _
      · rw [UniformFirstHit.survivalNumerator_zero_of_not next P x hx]
        exact Nat.le_refl _
  | succ t ih =>
      have hs := UniformFirstHit.survivalNumerator_succ_le next P x t
      calc
        UniformFirstHit.survivalNumerator next P x (t + 1) ≤
          n * UniformFirstHit.survivalNumerator next P x t := hs
        _ ≤ n * n ^ t := Nat.mul_le_mul_left n ih
        _ = n ^ (t + 1) := by
          rw [Nat.pow_succ]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The first T terms of the cost are at most T before scaling.
This pays for the entire first 3n² steps without a stochastic
estimate. -/
private theorem grantDrainDummyRetireCostTrivial
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) (x : S) :
    ∀ T : Nat,
      K2ArbitraryElimination.FiniteAccounting.costNumerator next P x T ≤ T * n ^ T := by
  intro T
  induction T with
  | zero =>
      rw [K2ArbitraryElimination.FiniteAccounting.costNumerator_zero]
      exact Nat.zero_le _
  | succ T ih =>
      have hs := grantDrainDummyRetireSurvivalCountCap next P x T
      calc
        K2ArbitraryElimination.FiniteAccounting.costNumerator next P x (T + 1) =
          n * (K2ArbitraryElimination.FiniteAccounting.costNumerator next P x T +
            UniformFirstHit.survivalNumerator next P x T) :=
            UniformFirstHit.costNumerator_succ_eq next P x T
        _ ≤ n * (T * n ^ T + n ^ T) :=
          Nat.mul_le_mul_left n (Nat.add_le_add ih hs)
        _ = (T + 1) * n ^ (T + 1) := by
          simp only [Nat.pow_succ, Nat.succ_mul, Nat.one_mul,
            Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem grantDrainDummyRetireCostAfterCutoff
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) :
    ∀ u : Nat,
      4 * 2 ^ (3 * n ^ 2 + u) *
        K2ArbitraryElimination.FiniteAccounting.costNumerator
          (grantDrainDummyEdgeWordStep ring fresh update)
          GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
          (3 * n ^ 2 + u) ≤
      4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2 + u) +
        n * (2 * n) ^ (3 * n ^ 2) *
          grantDrainEntranceGeometricTail (2 * n) u := by
  intro u
  induction u with
  | zero =>
      have ht := grantDrainDummyRetireCostTrivial
        (grantDrainDummyEdgeWordStep ring fresh update)
        GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
        (3 * n ^ 2)
      have hscaled :
          4 * 2 ^ (3 * n ^ 2) *
            K2ArbitraryElimination.FiniteAccounting.costNumerator
              (grantDrainDummyEdgeWordStep ring fresh update)
              GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
              (3 * n ^ 2) ≤
          4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2) := by
        calc
          _ ≤ 4 * 2 ^ (3 * n ^ 2) *
                ((3 * n ^ 2) * n ^ (3 * n ^ 2)) :=
            Nat.mul_le_mul_left _ ht
          _ = 4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2) := by
            rw [Nat.mul_pow]
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      simpa only [Nat.add_zero, grantDrainEntranceGeometricTail,
        Nat.mul_zero] using hscaled
  | succ u ih =>
      have hSurv := grantDrainDummyRetireSurvivalAfterCutoff
        ring hn fresh update s hPB hNoBad u
      have hstep : 3 * n ^ 2 + (u + 1) =
          (3 * n ^ 2 + u) + 1 := by omega
      calc
        4 * 2 ^ (3 * n ^ 2 + (u + 1)) *
            K2ArbitraryElimination.FiniteAccounting.costNumerator
              (grantDrainDummyEdgeWordStep ring fresh update)
              GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
              (3 * n ^ 2 + (u + 1)) =
          (2 * n) *
            (4 * 2 ^ (3 * n ^ 2 + u) *
              K2ArbitraryElimination.FiniteAccounting.costNumerator
                (grantDrainDummyEdgeWordStep ring fresh update)
                GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
                (3 * n ^ 2 + u) +
             4 * 2 ^ (3 * n ^ 2 + u) *
              UniformFirstHit.survivalNumerator
                (grantDrainDummyEdgeWordStep ring fresh update)
                GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
                (3 * n ^ 2 + u)) := by
          rw [hstep, UniformFirstHit.costNumerator_succ_eq,
            show 2 ^ (3 * n ^ 2 + u + 1) = 2 ^ (3 * n ^ 2 + u) * 2 from
              Nat.pow_succ 2 (3 * n ^ 2 + u)]
          generalize 2 ^ (3 * n ^ 2 + u) = P
          generalize K2ArbitraryElimination.FiniteAccounting.costNumerator
              (grantDrainDummyEdgeWordStep ring fresh update)
              GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
              (3 * n ^ 2 + u) = C
          generalize UniformFirstHit.survivalNumerator
              (grantDrainDummyEdgeWordStep ring fresh update)
              GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
              (3 * n ^ 2 + u) = V
          simp only [Nat.mul_add, Nat.add_mul,
            Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ (2 * n) *
          ((4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2 + u) +
            n * (2 * n) ^ (3 * n ^ 2) *
              grantDrainEntranceGeometricTail (2 * n) u) +
            n * (2 * n) ^ (3 * n ^ 2) *
              (2 * n - 1) ^ u) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add ih hSurv)
        _ = 4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2 + (u + 1)) +
            n * (2 * n) ^ (3 * n ^ 2) *
              grantDrainEntranceGeometricTail (2 * n) (u + 1) := by
          rw [hstep, Nat.pow_succ]
          change
            (2 * n) *
              ((4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2 + u) +
                n * (2 * n) ^ (3 * n ^ 2) *
                  grantDrainEntranceGeometricTail (2 * n) u) +
                n * (2 * n) ^ (3 * n ^ 2) * (2 * n - 1) ^ u) =
            4 * (3 * n ^ 2) *
              ((2 * n) ^ (3 * n ^ 2 + u) * (2 * n)) +
              n * (2 * n) ^ (3 * n ^ 2) *
                ((2 * n) * grantDrainEntranceGeometricTail (2 * n) u +
                  (2 * n) * (2 * n - 1) ^ u)
          simp only [Nat.mul_add]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- R8d first-stage clock. The pure integer proof pays 3n² for
the early phase and at most n²/2 for the later geometric tail.
The resulting 3.5n² envelope is below the accepted 4n² ceiling. -/
theorem grantDrainDummyUncleanRetirementCost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (T : Nat) :
    K2ArbitraryElimination.FiniteAccounting.costNumerator
      (grantDrainDummyEdgeWordStep ring fresh update)
      GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s) T ≤
        n ^ T * (4 * n ^ 2) := by
  by_cases hEarly : T ≤ 3 * n ^ 2
  · have hTriv := grantDrainDummyRetireCostTrivial
      (grantDrainDummyEdgeWordStep ring fresh update)
      GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s) T
    calc
      _ ≤ T * n ^ T := hTriv
      _ ≤ (4 * n ^ 2) * n ^ T :=
        Nat.mul_le_mul_right _ (by omega)
      _ = n ^ T * (4 * n ^ 2) := by simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · have hLong : 3 * n ^ 2 ≤ T := by omega
    obtain ⟨u, hu⟩ : ∃ u : Nat, T = 3 * n ^ 2 + u :=
      ⟨T - 3 * n ^ 2, by omega⟩
    subst T
    have hTail := grantDrainDummyRetireCostAfterCutoff
      ring hn fresh update s hPB hNoBad u
    have hGeomId := grantDrainEntranceGeometricTailIdentity
      (2 * n) (by omega : 1 ≤ 2 * n) u
    have hGeom :
        grantDrainEntranceGeometricTail (2 * n) u ≤
          (2 * n) ^ (u + 1) := by omega
    have hPart : n * (2 * n) = 2 * n ^ 2 := by
      rw [Nat.pow_two]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hCoeff :
        4 * (3 * n ^ 2) + n * (2 * n) ≤ 16 * n ^ 2 := by
      rw [hPart]
      omega
    have hScaled :
        4 * 2 ^ (3 * n ^ 2 + u) *
          K2ArbitraryElimination.FiniteAccounting.costNumerator
            (grantDrainDummyEdgeWordStep ring fresh update)
            GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
            (3 * n ^ 2 + u) ≤
          16 * n ^ 2 * (2 * n) ^ (3 * n ^ 2 + u) := by
      calc
        _ ≤ 4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2 + u) +
              n * (2 * n) ^ (3 * n ^ 2) *
                grantDrainEntranceGeometricTail (2 * n) u := hTail
        _ ≤ 4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2 + u) +
              n * (2 * n) ^ (3 * n ^ 2) *
                (2 * n) ^ (u + 1) :=
          Nat.add_le_add_left
            (Nat.mul_le_mul_left _ hGeom) _
        _ = (4 * (3 * n ^ 2) + n * (2 * n)) *
              (2 * n) ^ (3 * n ^ 2 + u) := by
          simp only [Nat.pow_add, Nat.pow_succ, Nat.add_mul,
            Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ ≤ 16 * n ^ 2 * (2 * n) ^ (3 * n ^ 2 + u) :=
          Nat.mul_le_mul_right _ hCoeff
    have hFour : (4 : Nat) * 4 = 16 := by decide
    have hPowerEq :
        16 * n ^ 2 * (2 * n) ^ (3 * n ^ 2 + u) =
        (4 * 2 ^ (3 * n ^ 2 + u)) *
          (4 * n ^ 2 * n ^ (3 * n ^ 2 + u)) := by
      rw [← hFour, Nat.mul_pow]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hPowerEq] at hScaled
    have hPositive : 0 < 4 * 2 ^ (3 * n ^ 2 + u) := by
      have hp : 0 < 2 ^ (3 * n ^ 2 + u) :=
        Nat.pow_pos (by decide : 0 < (2 : Nat))
      omega
    have hCancel := Nat.le_of_mul_le_mul_left hScaled hPositive
    calc
      K2ArbitraryElimination.FiniteAccounting.costNumerator
          (grantDrainDummyEdgeWordStep ring fresh update)
          GrantDrainDummyUncleanRetired (s, grantDrainDummyInitialUncleanHosts ring s)
          (3 * n ^ 2 + u) ≤
        4 * n ^ 2 * n ^ (3 * n ^ 2 + u) := hCancel
      _ = n ^ (3 * n ^ 2 + u) * (4 * n ^ 2) := by simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The genuinely unclean DUMMY cohort is fully represented by
initial labels throughout the word, because the literal E+FIRE
clean-geometry/origin theorem and NoBadLive preservation are proved. -/
theorem grantDrainDummyUncleanRetiredPhysicalClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (word : List (Fin n))
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hRetired : GrantDrainDummyUncleanRetired
      (word.foldl (grantDrainDummyEdgeWordStep ring fresh update)
        (s, grantDrainDummyInitialUncleanHosts ring s))) :
    ∀ b : Fin n, ¬ GrantDrainEntranceUncleanDummyAt ring
      (word.foldl (grantDrainDummyEdgeWordStep ring fresh update)
        (s, grantDrainDummyInitialUncleanHosts ring s)).1.native b := by
  have hInitial :
      GrantDrainDummyHostFaithful ring s.native
        (grantDrainDummyInitialUncleanHosts ring s) :=
    grantDrainDummyInitialFaithful ring s hPB hNoBad
  have hFaithful :=
    grantDrainDummyEdgeWordFaithfulOfOrigins
      ring hn fresh update
      (fun state edge hP hNoBadNow =>
        grantDrainDummyEdgeOriginHolds
          ring hn fresh update state edge hP hNoBadNow)
      word (s, grantDrainDummyInitialUncleanHosts ring s)
      hPB hNoBad hInitial
  intro b hBad
  have hBullet :
      HasBullet
        (word.foldl (grantDrainDummyEdgeWordStep ring fresh update)
          (s, grantDrainDummyInitialUncleanHosts ring s)).1.native b := by
    change
      ((word.foldl (grantDrainDummyEdgeWordStep ring fresh update)
          (s, grantDrainDummyInitialUncleanHosts ring s)).1.native b).b ≠
            (0 : Fin 3)
    rw [hBad.1]
    decide
  obtain ⟨id, hHosted⟩ := hFaithful.2 b hBullet hBad.2
  have hGone := hRetired id
  rw [hGone] at hHosted
  cases hHosted

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireChosenHitsOfSurvivor
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireNotDoneShortHits
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireSurvivalEndNot
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireSurvivalBit
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireOneLeSum
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireTailEdgeWeight
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireTailScheduleMul
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireTailMass
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireTailHitsProduct
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireTailScheduleLengthMul
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireTailWeighted
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireWeightedFamilySurvival
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireSurvivalAfterCutoff
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireSurvivalCountCap
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireCostTrivial
#print axioms L3.GrantDrainEntrance.grantDrainDummyRetireCostAfterCutoff
#print axioms L3.GrantDrainEntrance.grantDrainDummyUncleanRetirementCost
#print axioms L3.GrantDrainEntrance.grantDrainDummyUncleanRetiredPhysicalClean

namespace L3.GrantDrainEntrance
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Physical leader-death fields and two literal five-site
regressions for D.6. This is NOT an arbitrary-n proof of (M1).
The exceptional ghost flag requires a separate reachable-label
invariant; an arbitrary exhausted flag is not such a certificate.
-/

/-- The actual no-FIRE E+FIRE native step with a LIVE follower
source killing a quiet, unshielded leader responder. The killer
is consumed; a resident DUMMY at the victim remains. -/
theorem grantDrainD6DeathUnreadyPhysicalFields
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hXFollower : (s.native e).l = false)
    (hXLive : (s.native e).b = (2 : Fin 3))
    (hYLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hYUnshielded : (s.native (ring.rightNeighbor e)).sh = false)
    (hYQuiet : (s.native (ring.rightNeighbor e)).sg = false)
    (hNoFire : grantDrainSelect ring s e = .none) :
    ((grantDrainStep ring fresh update s e).native e).b =
        (0 : Fin 3) ∧
    ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = false ∧
    ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b =
        (s.native (ring.rightNeighbor e)).b ∧
    ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).sg = false ∧
    (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
      (grantDrainStep ring fresh update s e).native i =
        s.native i) := by
  have hNative := grantDrainWarmPhysicalNoBirthNative
    ring fresh update s e hNoFire
  have hPair := grantDrainWarmUnreadyFrontDeathPair
    (s.native e) (s.native (ring.rightNeighbor e))
    hXFollower hXLive hYLeader hYUnshielded hYQuiet
  have hDistinct := grantDrainWarmPhysicalPairDistinct ring hn e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hNative]
    simpa [nativeE] using hPair.1
  · rw [hNative]
    simpa [nativeE, hDistinct] using hPair.2.1
  · rw [hNative]
    simpa [nativeE, hDistinct] using hPair.2.2.1
  · rw [hNative]
    simpa [nativeE, hDistinct] using hPair.2.2.2
  · intro i hiX hiY
    change grantDrainNativeNext ring s e i = s.native i
    exact grantDrainMarksNativeOutsidePairFrame
      ring s e i hiX hiY

/-- A ready leader at the killing SOURCE can fire its LIVE
even if its OLD bullet field is zero. This row must be
included in a general front-death scan proof. -/
theorem grantDrainD6DeathReadySourcePair
    (x y : CertNative)
    (hXL : x.l = true) (hXS : x.sg = true)
    (hYL : y.l = true) (hYSh : y.sh = false) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, hXL, hXS, hYL, hYSh,
    certFinThree]

def grantDrainD6DeathWitnessRing : DirectedRing 5 :=
  ⟨by decide⟩

/-- In both cuts, 0 and 3 are the only leaders, site 2
holds the unique killer LIVE of sector [0,3), and 4
is the warm unheld grant. The optional site-3 DUMMY
is the survivor control for the merge. -/
def grantDrainD6DeathWitnessNative
    (frontBullet : Bool) (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (0 : Fin 3), sh := true, sg := false }
  else if i.val == 2 then
    { l := false, b := (2 : Fin 3), sh := false, sg := false }
  else if i.val == 3 then
    { l := true,
      b := if frontBullet then (1 : Fin 3) else (0 : Fin 3),
      sh := false, sg := false }
  else if i.val == 4 then
    { l := false, b := (0 : Fin 3), sh := false, sg := true }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

def grantDrainD6DeathWitnessState
    (frontBullet : Bool) : GrantDrainState 5 Unit :=
  { native := grantDrainD6DeathWitnessNative frontBullet
    request := fun _ => false
    grant := fun i => i.val == 4
    scratch := ()
    history := [] }

def grantDrainD6DeathWitnessAfter
    (frontBullet : Bool) : GrantDrainState 5 Unit :=
  grantDrainStep grantDrainD6DeathWitnessRing
    (fun _ _ => false) (fun _ _ => ())
    (grantDrainD6DeathWitnessState frontBullet) (2 : Fin 5)

/-- The TWO fully specified physical cuts satisfy PPlus,
C_native (settled SS), NoBadLive, warmAt and the actual
stored grant bit, and the selected edge has no FIRE. -/
theorem grantDrainD6DeathWitnessAdmissible
    (frontBullet : Bool) :
    PPlus grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState frontBullet).native ∧
    C_native grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState frontBullet).native ∧
    GrantDrainEntranceNoBadLive grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState frontBullet) ∧
    grantDrainWarmAt
      (grantDrainD6DeathWitnessState frontBullet)
      (4 : Fin 5) = true ∧
    (grantDrainD6DeathWitnessState frontBullet).grant
      (4 : Fin 5) = true ∧
    grantDrainSelect grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState frontBullet)
      (2 : Fin 5) = .none := by
  cases frontBullet
  · refine ⟨by decide, by decide, ?_, by decide, by decide, by decide⟩
    intro b
    unfold SharedPaperNonleftmostLiveExact
    revert b
    decide
  · refine ⟨by decide, by decide, ?_, by decide, by decide, by decide⟩
    intro b
    unfold SharedPaperNonleftmostLiveExact
    revert b
    decide

/-- The n=5 exceptional no-bullet merge saturates the
paper's 2(n-2) charge: W changes 3 -> 9 on e_2.
The old nearest leader at 3 dies and the next at 0 is
at backward distance 4. -/
theorem grantDrainD6DeathTightMergeWitness :
    ((grantDrainD6DeathWitnessState false).native
        (3 : Fin 5)).l = true ∧
    ((grantDrainD6DeathWitnessAfter false).native
        (3 : Fin 5)).l = false ∧
    grantDrainLeftLeaderDistance grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState false).native
        (4 : Fin 5) = 1 ∧
    grantDrainLeftLeaderDistance grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessAfter false).native
        (4 : Fin 5) = 4 ∧
    grantDrainLeftBulletDistance grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState false).native
        (4 : Fin 5) 1 = none ∧
    grantDrainLeftBulletDistance grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessAfter false).native
        (4 : Fin 5) 4 = none ∧
    grantDrainExceptionalDeath grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState false)
        (2 : Fin 5) (4 : Fin 5) = true ∧
    grantDrainWarmRank grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState false).native
        (4 : Fin 5) = 3 ∧
    grantDrainWarmRank grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessAfter false).native
        (4 : Fin 5) = 9 ∧
    grantDrainWarmRank grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessAfter false).native
        (4 : Fin 5) =
      grantDrainWarmRank grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState false).native
        (4 : Fin 5) + 2 * (5 - 2) := by
  unfold grantDrainD6DeathWitnessAfter
    grantDrainD6DeathWitnessState grantDrainD6DeathWitnessNative
    grantDrainD6DeathWitnessRing grantDrainExceptionalDeath
    grantDrainWarmRank grantDrainLeftLeaderDistance
    grantDrainLeftBulletDistance grantDrainTerminalRun
  decide

/-- If a DUMMY remains on the dying leader's site, it
survives as the new left bullet, and W is exactly
unchanged on the same n=5 physical death edge. -/
theorem grantDrainD6DeathSurvivingBulletWitness :
    ((grantDrainD6DeathWitnessState true).native
        (3 : Fin 5)).b = (1 : Fin 3) ∧
    ((grantDrainD6DeathWitnessAfter true).native
        (3 : Fin 5)).b = (1 : Fin 3) ∧
    ((grantDrainD6DeathWitnessAfter true).native
        (3 : Fin 5)).l = false ∧
    grantDrainLeftLeaderDistance grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState true).native
        (4 : Fin 5) = 1 ∧
    grantDrainLeftLeaderDistance grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessAfter true).native
        (4 : Fin 5) = 4 ∧
    grantDrainLeftBulletDistance grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState true).native
        (4 : Fin 5) 1 = some 1 ∧
    grantDrainLeftBulletDistance grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessAfter true).native
        (4 : Fin 5) 4 = some 1 ∧
    grantDrainExceptionalDeath grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState true)
        (2 : Fin 5) (4 : Fin 5) = false ∧
    grantDrainWarmRank grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState true).native
        (4 : Fin 5) = 1 ∧
    grantDrainWarmRank grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessAfter true).native
        (4 : Fin 5) = 1 := by
  unfold grantDrainD6DeathWitnessAfter
    grantDrainD6DeathWitnessState grantDrainD6DeathWitnessNative
    grantDrainD6DeathWitnessRing grantDrainExceptionalDeath
    grantDrainWarmRank grantDrainLeftLeaderDistance
    grantDrainLeftBulletDistance grantDrainTerminalRun
  decide

/-- An arbitrary ghost may have already spent its allowance
without the physical state being past the exceptional merge.
This label is not asserted to be reachable from a canonical
initial warm label. -/
private def grantDrainD6DeathExhaustedGhost : GrantDrainWarmLabel 5 :=
  { identity := (4 : Fin 5)
    host := some (4 : Fin 5)
    warm := true
    birthsLeft := 5
    exceptionalLeft := false }

/-- The unrestricted implication 'exceptionalLeft=false
implies W'≤W' is false with all native SS/PB premises true.
The missing condition is ghost reachability, not any of
SS, PB, uniqueness of the left bullet or B_g=0. -/
theorem grantDrainD6DeathGhostFlagRequiresReachability :
    grantDrainD6DeathExhaustedGhost.exceptionalLeft = false ∧
    grantDrainExceptionalDeath grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false)
      (2 : Fin 5) (4 : Fin 5) = true ∧
    ¬ grantDrainWarmRank grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessAfter false).native
        (4 : Fin 5) ≤
      grantDrainWarmRank grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState false).native
        (4 : Fin 5) := by
  unfold grantDrainD6DeathExhaustedGhost
    grantDrainD6DeathWitnessAfter
    grantDrainD6DeathWitnessState grantDrainD6DeathWitnessNative
    grantDrainD6DeathWitnessRing grantDrainExceptionalDeath
    grantDrainWarmRank grantDrainLeftLeaderDistance
    grantDrainLeftBulletDistance grantDrainTerminalRun
  decide

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6DeathUnreadyPhysicalFields
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathReadySourcePair
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathWitnessAdmissible
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathTightMergeWitness
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathSurvivingBulletWitness
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathGhostFlagRequiresReachability

namespace L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-!
Birth-split foundation.
The following interval facts are independent of any hypothetical
native-step closure leaf.
-/

/-- Restrict an arbitrary zero-star/one-star signal suffix to an
inner half-open interval, allowing its switching point to fall
outside the smaller interval. -/
theorem grantDrainSettledSignalRestrict
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n)
    (lo hi a b : Nat)
    (hhi : hi ≤ n)
    (hBounds : lo ≤ a ∧ a ≤ b ∧ b ≤ hi)
    (hOld : signalZeroStarOneStar ring N p lo hi) :
    signalZeroStarOneStar ring N p a b := by
  unfold signalZeroStarOneStar at hOld ⊢
  obtain ⟨c, hclo, hchi, hzero, hone⟩ := hOld
  by_cases hLow : c.val ≤ a
  · refine ⟨⟨a, show a < n + 1 by omega⟩,
        Nat.le_refl _, hBounds.2.1, ?_, ?_⟩
    · intro j hjlo hjcut
      (try dsimp only at *)
      omega
    · intro j hjcut hjhi
      exact hone j (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
  · by_cases hHigh : b ≤ c.val
    · refine ⟨⟨b, show b < n + 1 by omega⟩,
          hBounds.2.1, Nat.le_refl _, ?_, ?_⟩
      · intro j hjlo hjcut
        exact hzero j (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
      · intro j hjcut hjhi
        (try dsimp only at *)
        omega
    · refine ⟨c, (by (try dsimp only at *); omega), (by (try dsimp only at *); omega), ?_, ?_⟩
      · intro j hjlo hjcut
        exact hzero j (by (try dsimp only at *); omega) hjcut
      · intro j hjcut hjhi
        exact hone j hjcut (by (try dsimp only at *); omega)

/-- Affine clockwise rebase of a signal suffix. It only requires
equality of the physical signals on the new half-open arc. -/
theorem grantDrainSettledSignalRebase
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (p : Fin n)
    (base lo hi oldLo oldHi : Nat)
    (hLimit : oldHi ≤ n)
    (hBounds : lo ≤ hi ∧ oldLo ≤ base + lo ∧
      base + hi ≤ oldHi)
    (hOld : signalZeroStarOneStar ring N p oldLo oldHi)
    (hSignals : ∀ j : Fin n, lo ≤ j.val → j.val < hi →
      (M (PPL.shiftRight ring
        (PPL.shiftRight ring p base) j.val)).sg =
      (N (PPL.shiftRight ring p (base + j.val))).sg) :
    signalZeroStarOneStar ring M
      (PPL.shiftRight ring p base) lo hi := by
  unfold signalZeroStarOneStar at hOld ⊢
  obtain ⟨c, hclo, hchi, hzero, hone⟩ := hOld
  by_cases hLow : c.val ≤ base + lo
  · refine ⟨⟨lo, show lo < n + 1 by omega⟩,
        Nat.le_refl _, hBounds.1, ?_, ?_⟩
    · intro j hjlo hjcut
      (try dsimp only at *)
      omega
    · intro j hjcut hjhi
      rw [hSignals j hjcut hjhi]
      exact hone
        (⟨base + j.val, show base + j.val < n by omega⟩ : Fin n)
        (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
  · by_cases hHigh : base + hi ≤ c.val
    · refine ⟨⟨hi, show hi < n + 1 by omega⟩,
          hBounds.1, Nat.le_refl _, ?_, ?_⟩
      · intro j hjlo hjcut
        change j.val < hi at hjcut
        rw [hSignals j hjlo hjcut]
        exact hzero
          (⟨base + j.val, show base + j.val < n by omega⟩ : Fin n)
          (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
      · intro j hjcut hjhi
        (try dsimp only at *)
        omega
    · refine ⟨⟨c.val - base, show c.val - base < n + 1 by omega⟩,
          (by (try dsimp only at *); omega), (by (try dsimp only at *); omega), ?_, ?_⟩
      · intro j hjlo hjcut
        change j.val < c.val - base at hjcut
        rw [hSignals j hjlo (by (try dsimp only at *); omega)]
        exact hzero
          (⟨base + j.val, show base + j.val < n by omega⟩ : Fin n)
          (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
      · intro j hjcut hjhi
        rw [hSignals j (by (try dsimp only at *); omega) hjhi]
        exact hone
          (⟨base + j.val, show base + j.val < n by omega⟩ : Fin n)
          (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)

/-- A canonical birth frames every old offset distinct from its
new source offset, including the old sector root. -/
theorem grantDrainSettledBirthOldArcFrame
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p z : Fin n)
    (k j : Nat)
    (hz : z = PPL.shiftRight ring p k)
    (hk : k < n) (hj : j < n) (hne : j ≠ k) :
    canonicalBirth N z (PPL.shiftRight ring p j) =
      N (PPL.shiftRight ring p j) := by
  have hSite : PPL.shiftRight ring p j ≠ z := by
    rw [hz]
    exact grantDrainWeakDeathShiftRightNe
      ring p j k hj hk hne
  simp [canonicalBirth, hSite]

/-- At positive offsets of the new sector body, the native fields
are unchanged and coincide with the old sector at offset k+j. -/
theorem grantDrainSettledBirthRebasedFollower
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p z : Fin n)
    (k j : Nat)
    (hz : z = PPL.shiftRight ring p k)
    (hjPos : 0 < j) (hjLt : j < n) :
    canonicalBirth N z (PPL.shiftRight ring z j) =
      N (PPL.shiftRight ring p (k + j)) := by
  have hSite : PPL.shiftRight ring z j ≠ z := by
    have hne := grantDrainWeakDeathShiftRightNe
      ring z j 0 hjLt (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
    simpa only [grantDrainWeakDeathShiftRightZero] using hne
  calc
    canonicalBirth N z (PPL.shiftRight ring z j) =
        N (PPL.shiftRight ring z j) := by
          simp [canonicalBirth, hSite]
    _ = N (PPL.shiftRight ring p (k + j)) := by
          rw [hz, grantDrainWeakDeathShiftRightAdd]

/-- The two sectorLength witnesses after an interior canonical birth,
including d=n when the original sector wraps at its sole leader. -/
theorem grantDrainSettledCanonicalBirthSectorLengths
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p z : Fin n)
    (d : Fin (n + 1)) (k : Nat)
    (hz : z = PPL.shiftRight ring p k)
    (hk : 0 < k) (hkd : k < d.val)
    (hOld : sectorLength ring N p d) :
    sectorLength ring (canonicalBirth N z) p
        (⟨k, show k < n + 1 by omega⟩ : Fin (n + 1)) ∧
      sectorLength ring (canonicalBirth N z) z
        (⟨d.val - k, show d.val - k < n + 1 by omega⟩ :
          Fin (n + 1)) := by
  have hmax : d.val ≤ n := Nat.le_of_lt_succ d.isLt
  have hkLt : k < n := by omega
  have hRoot :
      canonicalBirth N z p = N p := by
    have hframe :=
      grantDrainSettledBirthOldArcFrame
        ring N p z k 0 hz hkLt (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
    simpa only [grantDrainWeakDeathShiftRightZero] using hframe
  have hEndShift :
      PPL.shiftRight ring z (d.val - k) =
        PPL.shiftRight ring p d.val := by
    rw [hz, grantDrainWeakDeathShiftRightAdd]
    have hsum : k + (d.val - k) = d.val := by omega
    rw [hsum]
  have hEndAway :
      PPL.shiftRight ring z (d.val - k) ≠ z := by
    have hne := grantDrainWeakDeathShiftRightNe
      ring z (d.val - k) 0 (by (try dsimp only at *); omega) (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
    simpa only [grantDrainWeakDeathShiftRightZero] using hne
  constructor
  · unfold sectorLength
    refine ⟨hk, ?_, ?_, ?_⟩
    · rw [hRoot]
      exact hOld.2.1
    · rw [← hz]
      simp [canonicalBirth, firedNative]
    · intro i hpos hshort
      have hframe :=
        grantDrainSettledBirthOldArcFrame ring N p z k i.val
          hz hkLt (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
      rw [hframe]
      exact hOld.2.2.2 i hpos (by (try dsimp only at *); omega)
  · unfold sectorLength
    refine ⟨(by (try dsimp only at *); omega), ?_, ?_, ?_⟩
    · simp [canonicalBirth, firedNative]
    · rw [hEndShift]
      have hEq :
          canonicalBirth N z
            (PPL.shiftRight ring p d.val) =
            N (PPL.shiftRight ring p d.val) := by
        rw [← hEndShift]
        simp [canonicalBirth, hEndAway]
      rw [hEq]
      exact hOld.2.2.1
    · intro i hpos hshort
      change i.val < d.val - k at hshort
      have hrebased :=
        grantDrainSettledBirthRebasedFollower
          ring N p z k i.val hz hpos (by (try dsimp only at *); omega)
      rw [hrebased]
      exact hOld.2.2.2
        (⟨k + i.val, show k + i.val < n by omega⟩ : Fin n)
        (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)

/-- The full READY/RETURN branch of case (b): a canonical birth
strictly inside a BULLET-FREE settled sector produces two
settled sectors. The old signal front is arbitrary and d=n
(the singleton-root wrap) is included. NoBadLive is unused. -/
theorem grantDrainSettledCanonicalBirthBulletFreeSplit
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p z : Fin n)
    (d : Fin (n + 1)) (k : Nat)
    (hz : z = PPL.shiftRight ring p k)
    (hk : 0 < k) (hkd : k < d.val)
    (hOldSector : sectorLength ring N p d)
    (hOldSettled : GrantDrainSettledSector ring N p d)
    (hNo : ∀ i : Fin n, i.val < d.val →
      ¬ HasBullet N (PPL.shiftRight ring p i.val)) :
    (sectorLength ring (canonicalBirth N z) p
        (⟨k, show k < n + 1 by omega⟩ : Fin (n + 1)) ∧
      GrantDrainSettledSector ring (canonicalBirth N z) p
        (⟨k, show k < n + 1 by omega⟩ : Fin (n + 1))) ∧
    (sectorLength ring (canonicalBirth N z) z
        (⟨d.val - k, show d.val - k < n + 1 by omega⟩ :
          Fin (n + 1)) ∧
      GrantDrainSettledSector ring (canonicalBirth N z) z
        (⟨d.val - k, show d.val - k < n + 1 by omega⟩ :
          Fin (n + 1))) := by
  have hmax : d.val ≤ n := Nat.le_of_lt_succ d.isLt
  have hkLt : k < n := by omega
  have hlengths := grantDrainSettledCanonicalBirthSectorLengths
    ring N p z d k hz hk hkd hOldSector
  have hphase :
      signalZeroStarOneStar ring N p 1 d.val ∧
      ((N p).sg = true →
        ∀ i : Fin n, 1 ≤ i.val → i.val < d.val →
          (N (PPL.shiftRight ring p i.val)).sg = true) := by
    rcases hOldSettled.2.2 with hbullet | hnone
    · obtain ⟨i, hi, hbi, _, _⟩ := hbullet
      exact False.elim (hNo i hi hbi)
    · exact ⟨hnone.2.1, hnone.2.2⟩
  have hRoot :
      canonicalBirth N z p = N p := by
    have hframe :=
      grantDrainSettledBirthOldArcFrame
        ring N p z k 0 hz hkLt (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
    simpa only [grantDrainWeakDeathShiftRightZero] using hframe
  have hLeftNo : ∀ i : Fin n, i.val < k →
      ¬ HasBullet (canonicalBirth N z)
        (PPL.shiftRight ring p i.val) := by
    intro i hi hb
    have hframe := grantDrainSettledBirthOldArcFrame
      ring N p z k i.val hz hkLt (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
    unfold HasBullet at hb
    rw [hframe] at hb
    exact hNo i (by (try dsimp only at *); omega) hb
  have hRightNo : ∀ i : Fin n, i.val < d.val - k →
      ¬ HasBullet (canonicalBirth N z)
        (PPL.shiftRight ring z i.val) := by
    intro i hi hb
    by_cases hzIndex : i.val = 0
    · have hsource : PPL.shiftRight ring z i.val = z := by
        rw [hzIndex, grantDrainWeakDeathShiftRightZero]
      rw [hsource] at hb
      have hclear :
          ¬ HasBullet (canonicalBirth N z) z := by
        simp [HasBullet, canonicalBirth, firedNative]
      exact hclear hb
    · have hpos : 0 < i.val := by omega
      have hframe := grantDrainSettledBirthRebasedFollower
        ring N p z k i.val hz hpos (by (try dsimp only at *); omega)
      unfold HasBullet at hb
      rw [hframe] at hb
      exact hNo
        (⟨k + i.val, show k + i.val < n by omega⟩ : Fin n)
        (by (try dsimp only at *); omega) hb
  have hLeftSuffix :
      signalZeroStarOneStar ring (canonicalBirth N z) p 1 k := by
    have hrebased := grantDrainSettledSignalRebase
      ring N (canonicalBirth N z) p 0 1 k 1 d.val
      hmax
      (show 1 ≤ k ∧ 1 ≤ 0 + 1 ∧ 0 + k ≤ d.val by omega)
      hphase.1
      (by
        intro i hi hlo
        have hframe := grantDrainSettledBirthOldArcFrame
          ring N p z k i.val hz hkLt (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
        simpa only [grantDrainWeakDeathShiftRightZero, Nat.zero_add]
          using congrArg (fun c : CertNative => c.sg) hframe)
    simpa only [grantDrainWeakDeathShiftRightZero] using hrebased
  have hRightSuffix :
      signalZeroStarOneStar ring (canonicalBirth N z) z
        1 (d.val - k) := by
    have hrebased := grantDrainSettledSignalRebase
      ring N (canonicalBirth N z) p k 1 (d.val - k) 1 d.val
      hmax
      (show 1 ≤ d.val - k ∧ 1 ≤ k + 1 ∧
        k + (d.val - k) ≤ d.val by omega)
      hphase.1
      (by
        intro i hpos hi
        simpa only [hz] using congrArg (fun c : CertNative => c.sg)
          (grantDrainSettledBirthRebasedFollower
            ring N p z k i.val hz hpos (by (try dsimp only at *); omega)))
    simpa only [hz] using hrebased
  have hLeftSettled :
      GrantDrainSettledSector ring (canonicalBirth N z) p
        (⟨k, show k < n + 1 by omega⟩ : Fin (n + 1)) := by
    refine ⟨?_, ?_, Or.inr ?_⟩
    · intro a b ha hb hba
      exact False.elim (hLeftNo a ha hba)
    · intro a ha hba
      exact False.elim (hLeftNo a ha hba)
    · refine ⟨hLeftNo, hLeftSuffix, ?_⟩
      intro hready i hpos hi
      have hOldReady : (N p).sg = true := by
        rw [← hRoot]
        exact hready
      have hOldSignal := hphase.2 hOldReady i hpos (by (try dsimp only at *); omega)
      have hframe := grantDrainSettledBirthOldArcFrame
        ring N p z k i.val hz hkLt (by (try dsimp only at *); omega) (by (try dsimp only at *); omega)
      rw [hframe]
      exact hOldSignal
  have hRightSettled :
      GrantDrainSettledSector ring (canonicalBirth N z) z
        (⟨d.val - k, show d.val - k < n + 1 by omega⟩ :
          Fin (n + 1)) := by
    refine ⟨?_, ?_, Or.inr ?_⟩
    · intro a b ha hb hba
      exact False.elim (hRightNo a ha hba)
    · intro a ha hba
      exact False.elim (hRightNo a ha hba)
    · refine ⟨hRightNo, hRightSuffix, ?_⟩
      intro hready
      have hfalse :
          (canonicalBirth N z z).sg = false := by
        simp [canonicalBirth, firedNative]
      rw [hfalse] at hready
      cases hready
  exact ⟨⟨hlengths.1, hLeftSettled⟩,
    ⟨hlengths.2, hRightSettled⟩⟩

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainSettledSignalRestrict
#print axioms L3.GrantDrainEntrance.grantDrainSettledSignalRebase
#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthOldArcFrame
#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthRebasedFollower
#print axioms L3.GrantDrainEntrance.grantDrainSettledCanonicalBirthSectorLengths
#print axioms L3.GrantDrainEntrance.grantDrainSettledCanonicalBirthBulletFreeSplit

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
D6-PAIR-SCAN. Physical audit.

The literal R1 target places the OLD first bullet at the
RESPONDER of e, but native E moves a bullet in the opposite
direction of that description: FROM the OLD initiator TO
its follower responder. Servicing an edge INTO the old
first bullet may leave its position untouched, so the
requested strict decrease is false exactly as stated.

Even on the corrected OUTGOING bullet service the
grantDrainD6PairFirstBulletMoveRank cannot be applied
directly: its global hSignal demands all signal flags
unchanged, while native E clears the responder signal.
The five-site trace below has this genuine change and still
satisfies the desired numerical strict drop.

The ready-front SOURCE and simultaneous ready-responder
death cases are checked separately on complete native
five-site configurations. These closed examples are not
a claimed all-n ready-front scan theorem.
-/

/-- The genuine clean-sector class gives a zero signal at
every occupied bullet site, including DUMMY bullets. -/
theorem grantDrainD6CleanBulletOwnSignalZero
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hC : C_native ring N)
    (b : Fin n) (hBullet : HasBullet N b) :
    (N b).sg = false := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hC.1
  exact grantDrainEntranceILocalBulletSignalZero
    ring N hLocal b hBullet

/-!
R1's exact responder-oriented wording, on the
production source grantDrainWarmPairCaseLeader:

    n=5, g=3, first OLD bullet=1 at left-distance 2.
    Edge e=0 has RESPONDER 1, but source 0 is the
    quiet bullet-free leader. No bullet moves on e=0.
    Native fields and the warm rank are unchanged.

The moving-bullet edge is e=1, not e=0.
-/

private def grantDrainD6IncomingBulletFiveAfter :
    GrantDrainState 5 Unit :=
  grantDrainStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWarmPairCaseLeader (0 : Fin 5)

/-- All three required production assumptions hold at this
fully specified n=5 cut; the third component is the actual
NoBadLive predicate, not a surrogate. -/
theorem grantDrainD6IncomingBulletFiveProtected :
    PPlus grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native ∧
    C_native grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native ∧
    GrantDrainEntranceNoBadLive grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader := by
  exact grantDrainWarmLeftBulletFiveProduction

/-- The counterexample meets the requested responder condition,
warm grant, first bullet scan and no-FIRE condition literally. -/
theorem grantDrainD6IncomingBulletFiveGuards :
    grantDrainWarmAt grantDrainWarmPairCaseLeader
      (3 : Fin 5) = true ∧
    grantDrainWarmPairCaseLeader.grant (3 : Fin 5) = true ∧
    PPL.shiftLeft grantDrainWarmPairCaseRing
      (3 : Fin 5) 2 =
      grantDrainWarmPairCaseRing.rightNeighbor (0 : Fin 5) ∧
    grantDrainLeftLeaderDistance grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) = 3 ∧
    grantDrainLeftBulletDistance grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) 3 =
        some 2 ∧
    grantDrainSelect grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader (0 : Fin 5) = .none := by
  decide

/-- Literal n=5 negative answer to R1 AS WORDED:
no FIRE or birth, old first bullet is at the responder
at distance k+1=2, but its bullet does not move and
the rank stays 2 rather than dropping by one. -/
theorem grantDrainD6IncomingBulletFiveNoStrictDrop :
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) = 2 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainD6IncomingBulletFiveAfter.native (3 : Fin 5) = 2 ∧
    ¬ (grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainD6IncomingBulletFiveAfter.native (3 : Fin 5) + 1 ≤
      grantDrainWarmRank grantDrainWarmPairCaseRing
        grantDrainWarmPairCaseLeader.native (3 : Fin 5)) := by
  decide

/-- On the CORRECT physical outgoing edge e=1 the bullet
moves from distance 2 to 1, and the terminal signal-one run
loses a site: site 2 changes from signal-one to signal-zero.
Thus global hSignal in D6PairFirstBulletMoveRank is false,
although the actual D.6 rank drops from 2 to 1. -/
theorem grantDrainD6OutgoingBulletFiveSignalChanges :
    PPL.shiftLeft grantDrainWarmPairCaseRing
      (3 : Fin 5) 2 = (1 : Fin 5) ∧
    grantDrainWarmPairCaseRing.rightNeighbor (1 : Fin 5) =
      PPL.shiftLeft grantDrainWarmPairCaseRing (3 : Fin 5) 1 ∧
    (grantDrainWarmPairCaseLeader.native (2 : Fin 5)).sg =
      true ∧
    (grantDrainWarmLeftBulletFiveAfter.native (2 : Fin 5)).sg =
      false ∧
    ¬ (∀ i : Fin 5,
       (grantDrainWarmLeftBulletFiveAfter.native i).sg =
         (grantDrainWarmPairCaseLeader.native i).sg) ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmLeftBulletFiveAfter.native (3 : Fin 5) + 1 ≤
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) := by
  decide

/-! R2(a): genuine ready leader as INITIATOR.
This is the production source at e=0:
source's ready LIVE fires into site 1, without remaining
as a bullet at the leader; warm rank at site 3 is 4 -> 2. -/

/-- The exact ready-SOURCE row has the physical bullet
at the responder and a strict warm-rank decrease. -/
theorem grantDrainD6ReadySourceFiveStrict :
    C_native grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native ∧
    PPlus grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native ∧
    GrantDrainEntranceNoBadLive grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial ∧
    grantDrainWarmAt grantDrainWarmPairCaseInitial
      (3 : Fin 5) = true ∧
    grantDrainWarmPairCaseInitial.grant (3 : Fin 5) = true ∧
    grantDrainSelect grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial (0 : Fin 5) = .none ∧
    (grantDrainWarmPairCaseInitial.native (0 : Fin 5)).l = true ∧
    (grantDrainWarmPairCaseInitial.native (0 : Fin 5)).sg = true ∧
    (grantDrainWarmPairCaseLeader.native (0 : Fin 5)).b =
      (0 : Fin 3) ∧
    (grantDrainWarmPairCaseLeader.native (1 : Fin 5)).b =
      (2 : Fin 3) ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native (3 : Fin 5) = 4 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) = 2 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseLeader.native (3 : Fin 5) + 1 ≤
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmPairCaseInitial.native (3 : Fin 5) := by
  have hC := grantDrainWarmPairCaseClean
  have hNoBad := grantDrainWarmPairCaseNoBad
  refine ⟨hC.2, hC.1, hNoBad, ?_⟩
  decide

/-! R2(b): complete n=5 ready-RESPONDER deletion.
Old protected leader 0 with quiet zero trail through its
unique LIVE at 2; ready leader 3; warm grant g=4.

Edge e=2 sends the LIVE into ready leader 3.
Native E first makes leader 3 unshielded, dummy-fires it,
then consumes the strong killer and deletes the leader.
The DUMMY remains at 3; the nearest OLD leader 3 is now
deleted, and the NEW left leader of g=4 is leader 0.
The new first bullet is the DUMMY at distance 1.
No FIRE overlay is selected.
-/

private def grantDrainD6ReadyResponderFiveNative
    (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (0 : Fin 3), sh := true, sg := false }
  else if i.val == 2 then
    { l := false, b := (2 : Fin 3), sh := false, sg := false }
  else if i.val == 3 then
    { l := true, b := (0 : Fin 3), sh := true, sg := true }
  else if i.val == 4 then
    { l := false, b := (0 : Fin 3), sh := false, sg := true }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

private def grantDrainD6ReadyResponderFiveBefore :
    GrantDrainState 5 Unit :=
  { native := grantDrainD6ReadyResponderFiveNative
    request := fun _ => false
    grant := fun i => i.val == 4
    scratch := ()
    history := [] }

private def grantDrainD6ReadyResponderFiveAfter :
    GrantDrainState 5 Unit :=
  grantDrainStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainD6ReadyResponderFiveBefore (2 : Fin 5)

/-- The simultaneous-ready-death test is within the literal
clean-sector and NoBadLive production class, not a forged
non-SS precondition. -/
theorem grantDrainD6ReadyResponderFiveProtected :
    C_native grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveBefore.native ∧
    PPlus grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveBefore.native ∧
    GrantDrainEntranceNoBadLive grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveBefore := by
  refine ⟨by decide, by decide, ?_⟩
  intro b
  unfold L3.GrantDrainShared.SharedPaperNonleftmostLiveExact
  revert b
  decide

/-- Exact old guards and new E+FIRE physical fields for the
ready-responder kill: OLD LIVE(2) at e=2, OLD ready leader(3),
post-step consumed source bullet, dead leader, surviving
dummy and signal zero at site 3. -/
theorem grantDrainD6ReadyResponderFiveFields :
    grantDrainWarmAt grantDrainD6ReadyResponderFiveBefore
      (4 : Fin 5) = true ∧
    grantDrainD6ReadyResponderFiveBefore.grant
      (4 : Fin 5) = true ∧
    (grantDrainD6ReadyResponderFiveBefore.native
      (2 : Fin 5)).b = (2 : Fin 3) ∧
    (grantDrainD6ReadyResponderFiveBefore.native
      (3 : Fin 5)).l = true ∧
    (grantDrainD6ReadyResponderFiveBefore.native
      (3 : Fin 5)).sg = true ∧
    grantDrainSelect grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveBefore (2 : Fin 5) = .none ∧
    (grantDrainD6ReadyResponderFiveAfter.native
      (2 : Fin 5)).b = (0 : Fin 3) ∧
    (grantDrainD6ReadyResponderFiveAfter.native
      (3 : Fin 5)).l = false ∧
    (grantDrainD6ReadyResponderFiveAfter.native
      (3 : Fin 5)).b = (1 : Fin 3) ∧
    (grantDrainD6ReadyResponderFiveAfter.native
      (3 : Fin 5)).sg = false := by
  decide

/-- Ready-responder simultaneous deletion has OLD leader
distance 1, no left bullet and rank 2. The new left leader
has distance 4, the retained dummy is scanned at distance
1, and the rank is 1. The nontrivial leader-change branch
cannot use a global hLeader frame. -/
theorem grantDrainD6ReadyResponderFiveRank :
    grantDrainLeftLeaderDistance grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveBefore.native (4 : Fin 5) = 1 ∧
    grantDrainLeftBulletDistance grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveBefore.native
      (4 : Fin 5) 1 = none ∧
    grantDrainLeftLeaderDistance grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveAfter.native (4 : Fin 5) = 4 ∧
    grantDrainLeftBulletDistance grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveAfter.native
      (4 : Fin 5) 4 = some 1 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveBefore.native (4 : Fin 5) = 2 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveAfter.native (4 : Fin 5) = 1 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveAfter.native (4 : Fin 5) + 1 ≤
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveBefore.native (4 : Fin 5) := by
  decide

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6CleanBulletOwnSignalZero
#print axioms L3.GrantDrainEntrance.grantDrainD6IncomingBulletFiveProtected
#print axioms L3.GrantDrainEntrance.grantDrainD6IncomingBulletFiveGuards
#print axioms L3.GrantDrainEntrance.grantDrainD6IncomingBulletFiveNoStrictDrop
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletFiveSignalChanges
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadySourceFiveStrict
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderFiveProtected
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderFiveFields
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderFiveRank

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Initial reserve and all of X2, plus the two immediate
one-step X1 cases: unused reserve and a physically framed
backward scan. The general interacting-pair X1 preservation
claim is NOT established by these declarations.
-/

/-- The actual nearest counterclockwise leader of the current
warm pointer; this is recomputed after every physical step. -/
def grantDrainD6MergeFront
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) : Fin n :=
  PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring N g)

/-- D.6 exceptional reserve has been spent only when the current
warm host is no longer at an unshielded, signal-zero, bullet-free
front. No initial-site or frozen-leader approximation is used. -/
def GrantDrainWarmMergeSpent
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n) : Prop :=
  ∀ g : Fin n,
    label.warm = true →
    label.host = some g →
    label.exceptionalLeft = false →
      (s.native (grantDrainD6MergeFront ring s.native g)).sh =
          true ∨
      (s.native (grantDrainD6MergeFront ring s.native g)).sg =
          true ∨
      grantDrainLeftBulletDistance ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) ≠ none

/-- The natural entrance ghost has an unspent reserve. -/
def grantDrainD6MergeInitialLabel
    {n : Nat} (id : Fin n)
    (warm : Bool) (birthBudget : Nat) : GrantDrainWarmLabel n :=
  { identity := id
    host := some id
    warm := warm
    birthsLeft := birthBudget
    exceptionalLeft := true }

/-- X1 base case is unconditional, with the actual supplied
configuration and no hypothesis about its sector geometry. -/
theorem grantDrainD6MergeInitially
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (id : Fin n) (warm : Bool) (birthBudget : Nat) :
    GrantDrainWarmMergeSpent ring s
      (grantDrainD6MergeInitialLabel id warm birthBudget) := by
  intro g _ _ hSpent
  change true = false at hSpent
  cases hSpent

/-- A small Boolean arithmetic fact isolating every field of
the exceptional-death guard. No native-row assumption is added. -/
private theorem grantDrainD6MergeBooleanFields
    (leader shield signal dead : Bool)
    (bullet : Option Nat)
    (h : (leader && !shield && !signal &&
      bullet.isNone && !dead) = true) :
    leader = true ∧ shield = false ∧ signal = false ∧
      bullet = none ∧ dead = false := by
  cases leader <;> cases shield <;> cases signal <;>
    cases bullet <;> cases dead <;> simp at *

/-- X2 field extraction from the EXACT OLD physical guard.
The last conjunct is death during nativeE, BEFORE any FIRE. -/
theorem grantDrainD6MergeExceptionalFields
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hExceptional : grantDrainExceptionalDeath ring s e g = true) :
    (s.native (grantDrainD6MergeFront ring s.native g)).l =
        true ∧
    (s.native (grantDrainD6MergeFront ring s.native g)).sh =
        false ∧
    (s.native (grantDrainD6MergeFront ring s.native g)).sg =
        false ∧
    grantDrainLeftBulletDistance ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) = none ∧
    (nativeE ring s.native e
        (grantDrainD6MergeFront ring s.native g)).l = false := by
  have hCore :
      ((s.native (grantDrainD6MergeFront ring s.native g)).l &&
        !(s.native (grantDrainD6MergeFront ring s.native g)).sh &&
        !(s.native (grantDrainD6MergeFront ring s.native g)).sg &&
        (grantDrainLeftBulletDistance ring s.native g
          (grantDrainLeftLeaderDistance ring s.native g)).isNone &&
        !(nativeE ring s.native e
          (grantDrainD6MergeFront ring s.native g)).l) = true := by
    change
      ((s.native (grantDrainD6MergeFront ring s.native g)).l &&
        !(s.native (grantDrainD6MergeFront ring s.native g)).sh &&
        !(s.native (grantDrainD6MergeFront ring s.native g)).sg &&
        (grantDrainLeftBulletDistance ring s.native g
          (grantDrainLeftLeaderDistance ring s.native g)).isNone &&
        !(nativeE ring s.native e
          (grantDrainD6MergeFront ring s.native g)).l) = true at hExceptional
    exact hExceptional
  exact grantDrainD6MergeBooleanFields
    (s.native (grantDrainD6MergeFront ring s.native g)).l
    (s.native (grantDrainD6MergeFront ring s.native g)).sh
    (s.native (grantDrainD6MergeFront ring s.native g)).sg
    (nativeE ring s.native e
      (grantDrainD6MergeFront ring s.native g)).l
    (grantDrainLeftBulletDistance ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g))
    hCore

/-- X2: no exceptional front death while an invariant-respecting
warm label already has exceptionalLeft=false. -/
theorem grantDrainD6MergeSpentExcludesExceptional
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n) (e g : Fin n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false) :
    grantDrainExceptionalDeath ring s e g = false := by
  cases hExceptional : grantDrainExceptionalDeath ring s e g with
  | false =>
      rfl
  | true =>
      obtain ⟨_, hShield, hSignal, hBullet, _⟩ :=
        grantDrainD6MergeExceptionalFields ring s e g hExceptional
      rcases hInv g hWarm hHost hSpent with hSh | hSg | hB
      · rw [hShield] at hSh
        cases hSh
      · rw [hSignal] at hSg
        cases hSg
      · exact False.elim (hB hBullet)

/-- The remaining exceptional reserve is necessary on any
step that actually satisfies the exceptional-death test. -/
theorem grantDrainD6MergeExceptionalRequiresReserve
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n) (e g : Fin n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    label.exceptionalLeft = true := by
  cases hFlag : label.exceptionalLeft with
  | true =>
      rfl
  | false =>
      have hNo := grantDrainD6MergeSpentExcludesExceptional
        ring s label e g hInv hWarm hHost hFlag
      rw [hNo] at hExceptional
      cases hExceptional

/-- A spent reserve never regenerates under any actual
physical/ghost service, regardless of births or requests. -/
theorem grantDrainD6MergeReserveNeverRefills
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hSpent : label.exceptionalLeft = false) :
    (grantDrainWarmLabelStep ring fresh update s e
      label).exceptionalLeft = false := by
  simp [grantDrainWarmLabelStep, hSpent]

/-- X1 nonexceptional unspent step: when the actual OLD
exceptional test is false at the old ghost host, the reserve
stays true and the invariant holds trivially in the NEW state.
No physical state transition is replaced by an abstract leaf. -/
theorem grantDrainD6MergeUnspentWithoutExceptional
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hAvailable : label.exceptionalLeft = true)
    (hNoExceptional : ∀ g : Fin n, label.host = some g →
      grantDrainExceptionalDeath ring s e g = false) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hNext :
      (grantDrainWarmLabelStep ring fresh update s e
        label).exceptionalLeft = true := by
    cases hHost : label.host with
    | none =>
        simp [grantDrainWarmLabelStep, hAvailable, hHost]
    | some g =>
        have hNo := hNoExceptional g hHost
        simp [grantDrainWarmLabelStep, hAvailable, hHost, hNo]
  intro g _ _ hSpent
  rw [hNext] at hSpent
  cases hSpent

/-- X1 genuinely physical off-pair step for a SPENT warm
identity. The geometric guard is only that the actual OLD
scan, including its terminal leader, misses the selected pair.
The native frame follows from the literal E+FIRE transition. -/
theorem grantDrainD6MergeSpentOutsidePair
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n)
    (e g : Fin n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (hOutside :
      ∀ k : Nat,
        k ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g k ≠ e ∧
        PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hAwayZero := hOutside 0 (Nat.zero_le _)
  have hX : g ≠ e := by
    simpa only [grantDrainWarmShiftLeftZero] using hAwayZero.1
  have hY : g ≠ ring.rightNeighbor e := by
    simpa only [grantDrainWarmShiftLeftZero] using hAwayZero.2
  have hFrame :
      ∀ k : Nat,
        k ≤ grantDrainLeftLeaderDistance ring s.native g →
        (grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring g k) =
        s.native (PPL.shiftLeft ring g k) := by
    intro k hk
    exact grantDrainSettledNativeStepOutsidePair
      ring fresh update s e (PPL.shiftLeft ring g k)
      (hOutside k hk).1 (hOutside k hk).2
  have hScan :=
    grantDrainWarmFullScanFrame ring s.native
      (grantDrainStep ring fresh update s e).native g hFrame
  have hOld := hInv g hWarm hHost hSpent
  have hPost :
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native g)).sh =
        true ∨
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native g)).sg =
        true ∨
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g) ≠
        none := by
    rcases hOld with hSh | hSg | hB
    · left
      unfold grantDrainD6MergeFront
      rw [hScan.1, hFrame _ (Nat.le_refl _)]
      exact hSh
    · right
      left
      unfold grantDrainD6MergeFront
      rw [hScan.1, hFrame _ (Nat.le_refl _)]
      exact hSg
    · right
      right
      rw [hScan.1, hScan.2.2.1]
      exact hB
  have hNextHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost, hX, hY]
  intro q _ hQ _
  have hSame : q = g :=
    Option.some.inj (hQ.symm.trans hNextHost)
  subst q
  exact hPost

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6MergeInitially
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeExceptionalFields
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeSpentExcludesExceptional
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeExceptionalRequiresReserve
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeReserveNeverRefills
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeUnspentWithoutExceptional
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeSpentOutsidePair

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! D6-PAIR-SCAN.
The terminal scan can lose one position at the nearer serviced site.
The outgoing physical rank row is for an interior bullet whose
responder is still strictly to the left of the tracked warm host.
The distance-one contact case is recorded separately below. -/

/-- Two signal arrays agreeing strictly before offset k cannot
lose more than one terminal-run position if the old run ends
at or before k. No agreement at k or k+1 is required. -/
private theorem grantDrainD6MoveTerminalAtMostOneLost
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (d k : Nat) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hWarm : (N g).sg = true)
    (hPrefix : ∀ j : Nat, j < k →
      (M (PPL.shiftLeft ring g j)).sg =
        (N (PPL.shiftLeft ring g j)).sg)
    (hOldBound : grantDrainTerminalRun ring N g d ≤ k) :
    grantDrainTerminalRun ring N g d ≤
      grantDrainTerminalRun ring M g d + 1 := by
  have hNewWarm : (M g).sg = true := by
    have hHead := hPrefix 0 (by omega)
    rw [grantDrainWarmShiftLeftZero] at hHead
    rw [hHead]
    exact hWarm
  have hOld :=
    (grantDrainWarmTerminalCharacterization ring N g d
      (grantDrainTerminalRun ring N g d) hd hWarm).mp rfl
  have hNew :=
    (grantDrainWarmTerminalCharacterization ring M g d
      (grantDrainTerminalRun ring M g d) hd hNewWarm).mp rfl
  by_cases hBound :
      grantDrainTerminalRun ring N g d ≤
        grantDrainTerminalRun ring M g d + 1
  · exact hBound
  · have hIndex :
        grantDrainTerminalRun ring M g d + 1 < k := by
      omega
    have hOldTrue :=
      hOld.2.1 (grantDrainTerminalRun ring M g d + 1)
        (by omega)
    have hNewTrue :
        (M (PPL.shiftLeft ring g
          (grantDrainTerminalRun ring M g d + 1))).sg =
          true := by
      rw [hPrefix _ hIndex]
      exact hOldTrue
    rcases hNew.2.2 with hFull | hStop
    · omega
    · rw [hStop] at hNewTrue
      cases hNewTrue

/-- Under genuine native settlement the first left bullet's
own signal is zero. Consequently the warm terminal scan cannot
extend beyond the immediately nearer offset k. This also covers
the inclusive endpoint case k+1=d. -/
private theorem grantDrainD6MoveOldRunBeforeBullet
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n)
    (d k : Nat)
    (hC : C_native ring N)
    (hd : 1 ≤ d) (hWarm : (N g).sg = true)
    (hFirst :
      grantDrainLeftBulletDistance ring N g d = some (k + 1)) :
    grantDrainTerminalRun ring N g d ≤ k := by
  have hHit :
      (N (PPL.shiftLeft ring g (k + 1))).b.val ≠ 0 :=
    ((grantDrainWarmBulletSomeCharacterization
      ring N g d (k + 1)).mp hFirst).2.2.1
  have hBullet :
      HasBullet N (PPL.shiftLeft ring g (k + 1)) := by
    intro hEmpty
    apply hHit
    rw [hEmpty]
    rfl
  have hZero := grantDrainD6CleanBulletOwnSignalZero
    ring N hC (PPL.shiftLeft ring g (k + 1)) hBullet
  have hTerminal :=
    (grantDrainWarmTerminalCharacterization ring N g d
      (grantDrainTerminalRun ring N g d) hd hWarm).mp rfl
  by_cases hBound : grantDrainTerminalRun ring N g d ≤ k
  · exact hBound
  · have hAt := hTerminal.2.1 (k + 1) (by omega)
    rw [hZero] at hAt
    cases hAt

/-- S1. The old first bullet moves from offset k+1 to k.
Signals may change at both serviced sites, and the only
signal frame needed is the strict prefix j<k. Settlement
supplies the stopping signal at the old bullet. The exact
terminal-run replacement is a one-position loss bound, not
equality; this is sharp on the five-site trace. -/
theorem grantDrainD6PairFirstBulletMoveRankSignal
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (d k : Nat)
    (hk : 1 ≤ k) (hInside : k + 1 ≤ d)
    (hC : C_native ring N)
    (hWarm : (N g).sg = true)
    (hLeader : ∀ i : Fin n, (M i).l = (N i).l)
    (hSignalPrefix : ∀ j : Nat, j < k →
      (M (PPL.shiftLeft ring g j)).sg =
        (N (PPL.shiftLeft ring g j)).sg)
    (hBulletPrefix : ∀ j : Nat, 1 ≤ j → j < k →
      (M (PPL.shiftLeft ring g j)).b.val =
        (N (PPL.shiftLeft ring g j)).b.val)
    (hDistance : grantDrainLeftLeaderDistance ring N g = d)
    (hOldFirst :
      grantDrainLeftBulletDistance ring N g d = some (k + 1))
    (hNewNear :
      (M (PPL.shiftLeft ring g k)).b.val ≠ 0)
    (hNewFarEmpty :
      (M (PPL.shiftLeft ring g (k + 1))).b.val = 0) :
    grantDrainLeftLeaderDistance ring M g = d ∧
    grantDrainLeftBulletDistance ring M g d = some k ∧
    grantDrainTerminalRun ring N g d ≤
      grantDrainTerminalRun ring M g d + 1 ∧
    grantDrainWarmRank ring M g + 1 ≤
      grantDrainWarmRank ring N g := by
  have hDistanceNew :
      grantDrainLeftLeaderDistance ring M g = d := by
    have hEqual :
        grantDrainLeftLeaderDistance ring M g =
          grantDrainLeftLeaderDistance ring N g := by
      simp [grantDrainLeftLeaderDistance, hLeader]
    exact hEqual.trans hDistance
  obtain ⟨_, _, _, hNoEarlier⟩ :=
    (grantDrainWarmBulletSomeCharacterization
      ring N g d (k + 1)).mp hOldFirst
  have hBulletNew :
      grantDrainLeftBulletDistance ring M g d = some k := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring M g d k).mpr
    refine ⟨hk, by omega, hNewNear, ?_⟩
    intro j hj hjk
    rw [hBulletPrefix j hj hjk]
    exact hNoEarlier j hj (by omega)
  have hOldBound :=
    grantDrainD6MoveOldRunBeforeBullet ring N g d k
      hC (by omega) hWarm hOldFirst
  have hTerminalBound :=
    grantDrainD6MoveTerminalAtMostOneLost ring N M g d k
      hk (by omega) hWarm hSignalPrefix hOldBound
  have hArithmetic :=
    grantDrainWarmLeftBulletMoveRankArithmetic
      (k + 1)
      (grantDrainTerminalRun ring N g d)
      (grantDrainTerminalRun ring M g d)
      (by omega) hTerminalBound
  have hSubtract : k + 1 - 1 = k := by omega
  rw [hSubtract] at hArithmetic
  refine ⟨hDistanceNew, hBulletNew, hTerminalBound, ?_⟩
  calc
    grantDrainWarmRank ring M g + 1 =
        k + 2 * (k -
          (grantDrainTerminalRun ring M g d + 1)) + 1 := by
      simp [grantDrainWarmRank, hDistanceNew, hBulletNew]
    _ ≤ (k + 1) + 2 * ((k + 1) -
          (grantDrainTerminalRun ring N g d + 1)) := hArithmetic
    _ = grantDrainWarmRank ring N g := by
      simp [grantDrainWarmRank, hDistance, hOldFirst]

/-- Two counterclockwise shifts with different offsets below n
cannot designate the same ring site. -/
private theorem grantDrainD6MoveShiftInjective
    {n : Nat} (ring : DirectedRing n) (g : Fin n)
    (a b : Nat) (ha : a < n) (hb : b < n)
    (hEq : PPL.shiftLeft ring g a =
      PPL.shiftLeft ring g b) : a = b := by
  have hv := congrArg Fin.val hEq
  change (g.val + n - a % n) % n =
    (g.val + n - b % n) % n at hv
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
  by_cases hA : a ≤ g.val
  · have hLeft : g.val + n - a = n + (g.val - a) := by
      omega
    rw [hLeft, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : g.val - a < n)] at hv
    by_cases hB : b ≤ g.val
    · have hRight : g.val + n - b = n + (g.val - b) := by
        omega
      rw [hRight, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega : g.val - b < n)] at hv
      omega
    · have hRight : g.val + n - b < n := by omega
      rw [Nat.mod_eq_of_lt hRight] at hv
      omega
  · have hLeft : g.val + n - a < n := by omega
    rw [Nat.mod_eq_of_lt hLeft] at hv
    by_cases hB : b ≤ g.val
    · have hRight : g.val + n - b = n + (g.val - b) := by
        omega
      rw [hRight, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega : g.val - b < n)] at hv
      omega
    · have hRight : g.val + n - b < n := by omega
      rw [Nat.mod_eq_of_lt hRight] at hv
      omega

/-- The first positive leader scan always returns a distance at
most n, including its no-hit getD fallback. -/
private theorem grantDrainD6MoveLeaderDistanceLe
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) :
    grantDrainLeftLeaderDistance ring N g ≤ n := by
  have hScan :
      grantDrainLeftLeaderDistance ring N g =
        ((List.range' 1 n).find?
          (fun j => (N (PPL.shiftLeft ring g j)).l)).getD n := by
    unfold grantDrainLeftLeaderDistance
    rw [grantDrainWarmPositiveRange]
  rw [hScan]
  cases hf : (List.range' 1 n).find?
      (fun j => (N (PPL.shiftLeft ring g j)).l) with
  | none =>
      simp [hf]
  | some p =>
      obtain ⟨_, hpBound, _, _⟩ :=
        grantDrainWarmRangeFindConverse
          (fun j => (N (PPL.shiftLeft ring g j)).l)
          n 1 p hf
      simpa [hf] using (show p ≤ n by omega)

/-- Every strictly interior position in the positive first-leader
scan is a follower, in both the d<n and d=n branches. -/
private theorem grantDrainD6MoveBeforeLeader
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n)
    (d j : Nat)
    (hDistance : grantDrainLeftLeaderDistance ring N g = d)
    (hj : 1 ≤ j) (hBefore : j < d) :
    (N (PPL.shiftLeft ring g j)).l = false := by
  have hLe := grantDrainD6MoveLeaderDistanceLe ring N g
  rw [hDistance] at hLe
  by_cases hFull : d = n
  · rw [hFull] at hDistance hBefore
    exact ((grantDrainWarmLeaderFullCharacterization
      ring N g).mp hDistance) j hj hBefore
  · have hd : d < n := by omega
    exact ((grantDrainWarmLeaderFirstCharacterization
      ring N g d (by omega) hd).mp hDistance).2 j hj hBefore

/-- The literal E row cannot change either leader flag when
both serviced sites are followers. -/
private theorem grantDrainD6MoveFollowerPairLeaders
    (x y : CertNative)
    (hXL : x.l = false) (hYL : y.l = false) :
    (certLiteralEPair x y).1.l = x.l ∧
    (certLiteralEPair x y).2.l = y.l := by
  simp [certLiteralEPair, hXL, hYL]

/-- S2 (interior, continuing warm-pointer row). This is an
actual grantDrainStep with no FIRE or birth. PPlus, NoBadLive,
C_native, the warm grant, the old first-bullet scan and the
two endpoints of the selected outgoing edge are all OLD
physical-state conditions. No post-state scan is assumed. -/
theorem grantDrainD6MovePhysicalFirstBulletRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (d k : Nat)
    (hC : C_native ring s.native)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = d)
    (hFirst :
      grantDrainLeftBulletDistance ring s.native g d =
        some (k + 1))
    (hk : 1 ≤ k) (hInterior : k + 1 < d)
    (hSource : e = PPL.shiftLeft ring g (k + 1))
    (hTo : ring.rightNeighbor e = PPL.shiftLeft ring g k)
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainWarmRank ring
      (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have hFirstFacts :=
    (grantDrainWarmBulletSomeCharacterization
      ring s.native g d (k + 1)).mp hFirst
  have hXval : (s.native e).b.val ≠ 0 := by
    rw [hSource]
    exact hFirstFacts.2.2.1
  have hXB : (s.native e).b ≠ (0 : Fin 3) := by
    intro hZero
    apply hXval
    rw [hZero]
    rfl
  have hXL : (s.native e).l = false := by
    rw [hSource]
    exact grantDrainD6MoveBeforeLeader ring s.native g
      d (k + 1) hDistance (by omega) hInterior
  have hYL : (s.native (ring.rightNeighbor e)).l =
      false := by
    rw [hTo]
    exact grantDrainD6MoveBeforeLeader ring s.native g
      d k hDistance hk (by omega)
  have hYB : (s.native (ring.rightNeighbor e)).b =
      (0 : Fin 3) := by
    apply Fin.ext
    rw [hTo]
    exact hFirstFacts.2.2.2 k hk (by omega)
  have hFields :=
    grantDrainWarmLeftBulletMovePhysicalFields
      ring hn fresh update s e hXL hXB hYL hYB hNone
  have hNative := grantDrainWarmPhysicalNoBirthNative
    ring fresh update s e hNone
  have hPairLeaders :=
    grantDrainD6MoveFollowerPairLeaders
      (s.native e) (s.native (ring.rightNeighbor e)) hXL hYL
  have hLeader : ∀ i : Fin n,
      ((grantDrainStep ring fresh update s e).native i).l =
        (s.native i).l := by
    intro i
    rw [hNative]
    by_cases hi : i = e
    · subst i
      simpa [nativeE] using hPairLeaders.1
    · by_cases hy : i = ring.rightNeighbor e
      · subst i
        have hNe := grantDrainWarmPhysicalPairDistinct ring hn e
        simpa [nativeE, hNe] using hPairLeaders.2
      · simp [nativeE, hi, hy]
  have hLe := grantDrainD6MoveLeaderDistanceLe ring s.native g
  rw [hDistance] at hLe
  have hkN : k + 1 < n := by omega
  have hPrefix :
      ∀ j : Nat, j < k →
        (grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring g j) =
        s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    have hjN : j < n := by omega
    have hNE : PPL.shiftLeft ring g j ≠ e := by
      rw [hSource]
      intro heq
      have hEqual := grantDrainD6MoveShiftInjective
        ring g j (k + 1) hjN hkN heq
      omega
    have hNY :
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
      rw [hTo]
      intro heq
      have hEqual := grantDrainD6MoveShiftInjective
        ring g j k hjN (by omega) heq
      omega
    exact hFields.2.2.2 _ hNE hNY
  have hSignalPrefix : ∀ j : Nat, j < k →
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g j)).sg =
        (s.native (PPL.shiftLeft ring g j)).sg := by
    intro j hj
    exact congrArg CertNative.sg (hPrefix j hj)
  have hBulletPrefix : ∀ j : Nat, 1 ≤ j → j < k →
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g j)).b.val =
        (s.native (PPL.shiftLeft ring g j)).b.val := by
    intro j _ hj
    exact congrArg (fun x : CertNative => x.b.val)
      (hPrefix j hj)
  have hNearEq :
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g k)).b = (s.native e).b := by
    rw [← hTo]
    exact hFields.2.1
  have hNewNear :
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g k)).b.val ≠ 0 := by
    rw [hNearEq]
    exact hXval
  have hNewFarEmpty :
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g (k + 1))).b.val = 0 := by
    rw [← hSource]
    rw [hFields.1]
    rfl
  have hWarmSignal : (s.native g).sg = true := by
    cases hs : (s.native g).sg with
    | true =>
        rfl
    | false =>
        simp [grantDrainWarmAt, hs] at hWarm
  exact (grantDrainD6PairFirstBulletMoveRankSignal
    ring s.native (grantDrainStep ring fresh update s e).native
    g d k hk (by omega) hC hWarmSignal hLeader
    hSignalPrefix hBulletPrefix hDistance hFirst
    hNewNear hNewFarEmpty).2.2.2

/-! The unqualified k=0 version of S2 is false. At the
contact service e=2 the old first bullet moves from distance
one into the warm grant's own site g=3. The grant ceases to
be warm and the rank is not a continuing-label potential. -/

private def grantDrainD6MoveContactFiveAfter : GrantDrainState 5 Unit :=
  grantDrainStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWarmLeftBulletFiveAfter (2 : Fin 5)

/-- Closed n=5 OLD state and selected edge. The first bullet
is at distance k+1=1, all required protective premises hold,
and the raw fixed-g numerical strict decrease fails. -/
theorem grantDrainD6MoveContactFiveCounter :
    C_native grantDrainWarmPairCaseRing
      grantDrainWarmLeftBulletFiveAfter.native ∧
    PPlus grantDrainWarmPairCaseRing
      grantDrainWarmLeftBulletFiveAfter.native ∧
    GrantDrainEntranceNoBadLive grantDrainWarmPairCaseRing
      grantDrainWarmLeftBulletFiveAfter ∧
    grantDrainWarmAt grantDrainWarmLeftBulletFiveAfter
      (3 : Fin 5) = true ∧
    grantDrainWarmLeftBulletFiveAfter.grant (3 : Fin 5) = true ∧
    PPL.shiftLeft grantDrainWarmPairCaseRing
      (3 : Fin 5) 1 = (2 : Fin 5) ∧
    grantDrainWarmPairCaseRing.rightNeighbor (2 : Fin 5) =
      (3 : Fin 5) ∧
    grantDrainLeftLeaderDistance grantDrainWarmPairCaseRing
      grantDrainWarmLeftBulletFiveAfter.native (3 : Fin 5) = 3 ∧
    grantDrainLeftBulletDistance grantDrainWarmPairCaseRing
      grantDrainWarmLeftBulletFiveAfter.native (3 : Fin 5) 3 =
        some 1 ∧
    grantDrainSelect grantDrainWarmPairCaseRing
      grantDrainWarmLeftBulletFiveAfter (2 : Fin 5) = .none ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainWarmLeftBulletFiveAfter.native (3 : Fin 5) = 1 ∧
    grantDrainWarmRank grantDrainWarmPairCaseRing
      grantDrainD6MoveContactFiveAfter.native (3 : Fin 5) = 7 ∧
    ¬ (grantDrainWarmRank grantDrainWarmPairCaseRing
        grantDrainD6MoveContactFiveAfter.native (3 : Fin 5) + 1 ≤
      grantDrainWarmRank grantDrainWarmPairCaseRing
        grantDrainWarmLeftBulletFiveAfter.native (3 : Fin 5)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | decide
    | (intro b
       unfold L3.GrantDrainShared.SharedPaperNonleftmostLiveExact
       revert b
       decide)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6PairFirstBulletMoveRankSignal
#print axioms L3.GrantDrainEntrance.grantDrainD6MovePhysicalFirstBulletRank
#print axioms L3.GrantDrainEntrance.grantDrainD6MoveContactFiveCounter

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Literal Y1/Y2/Y3 components for D.6.
There is NO claim of the unrestricted
grantDrainD6MergeSpentStep: its interacting-pair closure remains
open. The three five-site regressions below are actual E+FIRE
and actual grantDrainWarmLabelStep, not imaginary native steps.
-/

/-- A READY responder emits a DUMMY, even when a source LIVE
simultaneously deletes that responder's leader flag. This is
the Y2 shield-loss mechanism in the literal E pair. -/
theorem grantDrainD6MergeReadyResponderDummyPair
    (x y : CertNative)
    (hyLeader : y.l = true)
    (hyReady : y.sg = true) :
    (certLiteralEPair x y).2.sh = false ∧
    (certLiteralEPair x y).2.b = (1 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, hyLeader, hyReady, certFinThree]

/-- The only way to turn an OLD shielded leader into an
unshielded RESPONDER is a ready DUMMY fire. The latter
simultaneously leaves a bullet on the responder. -/
theorem grantDrainD6MergeResponderShieldLossHasDummy
    (x y : CertNative)
    (hyLeader : y.l = true)
    (hyShield : y.sh = true)
    (hNewShield : (certLiteralEPair x y).2.sh = false) :
    y.sg = true ∧
    (certLiteralEPair x y).2.b = (1 : Fin 3) := by
  cases hyReady : y.sg with
  | true =>
      exact ⟨rfl,
        (grantDrainD6MergeReadyResponderDummyPair
          x y hyLeader hyReady).2.1⟩
  | false =>
      have hRetained :
          (certLiteralEPair x y).2.sh = true := by
        simp [certLiteralEPair, hyLeader, hyShield,
          hyReady, certFinThree]
      rw [hRetained] at hNewShield
      cases hNewShield

/-- A shielded SOURCE remains shielded across literal E,
including when it fires a fresh LIVE. -/
theorem grantDrainD6MergeSourceShieldMonotone
    (x y : CertNative)
    (hxShield : x.sh = true) :
    (certLiteralEPair x y).1.sh = true := by
  cases hxLeader : x.l <;>
    cases hxSignal : x.sg <;>
    simp [certLiteralEPair, hxLeader, hxSignal,
      hxShield, certFinThree]

/-- A canonical birth always installs a shielded leader,
also when the birth splits the old backward scan. -/
theorem grantDrainD6MergeCanonicalBirthProtected
    {n : Nat} (N : Fin n → CertNative) (z : Fin n) :
    (canonicalBirth N z z).l = true ∧
    (canonicalBirth N z z).sh = true ∧
    (canonicalBirth N z z).sg = false ∧
    (canonicalBirth N z z).b = (0 : Fin 3) := by
  simp [canonicalBirth, firedNative]

/-- An outgoing bullet from a quiet follower into a follower
forces the source's POST-E signal to zero. It is important
that we do not treat the ordinary signal-copy row here. -/
theorem grantDrainD6MergeOutgoingBulletSourceSignalZeroPair
    (x y : CertNative)
    (hxFollower : x.l = false)
    (hxBullet : x.b ≠ (0 : Fin 3))
    (hxQuiet : x.sg = false)
    (hyFollower : y.l = false) :
    (certLiteralEPair x y).1.sg = false := by
  have hPositive : 0 < x.b.val := by
    have hNonzero : x.b.val ≠ 0 := by
      intro h
      apply hxBullet
      apply Fin.ext
      exact h
    omega
  simp [certLiteralEPair, hxFollower, hxQuiet,
    hyFollower, hPositive, certFinThree]

/-- A real no-FIRE outgoing bullet into an empty follower
makes BOTH selected endpoints non-warm: the source signal
is zero; the responder carries the nonzero bullet.
This is the physical heart of Y3's crossing exit. -/
theorem grantDrainD6MergeOutgoingBulletNoFireColdEndpoints
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hxQuiet : (s.native e).sg = false)
    (hyFollower : (s.native (ring.rightNeighbor e)).l = false)
    (hyEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hNoFire : grantDrainSelect ring s e = .none) :
    grantDrainWarmAt (grantDrainStep ring fresh update s e) e =
        false ∧
    grantDrainWarmAt (grantDrainStep ring fresh update s e)
        (ring.rightNeighbor e) = false := by
  have hNative := grantDrainWarmPhysicalNoBirthNative
    ring fresh update s e hNoFire
  have hSignalPair :=
    grantDrainD6MergeOutgoingBulletSourceSignalZeroPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hxFollower hxBullet hxQuiet hyFollower
  have hSignal :
      ((grantDrainStep ring fresh update s e).native e).sg =
        false := by
    rw [hNative]
    simpa [nativeE] using hSignalPair
  have hFields := grantDrainWarmLeftBulletMovePhysicalFields
    ring hn fresh update s e hxFollower hxBullet
    hyFollower hyEmpty hNoFire
  have hResponderBullet :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b ≠ (0 : Fin 3) := by
    rw [hFields.2.1]
    exact hxBullet
  constructor
  · simp [grantDrainWarmAt, hSignal]
  · exact grantDrainWarmPhysicalBulletEndsWarm
      (grantDrainStep ring fresh update s e)
      (ring.rightNeighbor e) hResponderBullet

/-- An already cold ghost remains outside the warm phase on
every literal step, regardless of native changes or FIRE. -/
theorem grantDrainD6MergeColdLabelRemainsCold
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hCold : label.warm = false) :
    (grantDrainWarmLabelStep ring fresh update s e
      label).warm = false := by
  unfold grantDrainWarmLabelStep
  dsimp only
  split
  · rfl
  · simp [hCold]

/-- Y1: genuine n=5 spent reserve on the SHARP exceptional
leader death. All the fields refer to the physical step and
the actual ghost step with the initially available reserve. -/
private def grantDrainD6MergeTightLabel : GrantDrainWarmLabel 5 :=
  grantDrainD6MergeInitialLabel (4 : Fin 5) true 5

private def grantDrainD6MergeTightLabelAfter : GrantDrainWarmLabel 5 :=
  grantDrainWarmLabelStep grantDrainD6DeathWitnessRing
    (fun _ _ => false) (fun _ _ => ())
    (grantDrainD6DeathWitnessState false) (2 : Fin 5)
    grantDrainD6MergeTightLabel

theorem grantDrainD6MergeTightExceptionalSpentFields :
    grantDrainExceptionalDeath grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false)
      (2 : Fin 5) (4 : Fin 5) = true ∧
    grantDrainD6MergeTightLabelAfter.exceptionalLeft = false ∧
    grantDrainD6MergeTightLabelAfter.host = some (4 : Fin 5) ∧
    grantDrainD6MergeTightLabelAfter.warm = true ∧
    grantDrainD6MergeFront grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessAfter false).native
      (4 : Fin 5) = (0 : Fin 5) ∧
    ((grantDrainD6DeathWitnessAfter false).native
      (grantDrainD6MergeFront grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessAfter false).native
        (4 : Fin 5))).sh = true := by
  unfold grantDrainD6MergeTightLabelAfter
    grantDrainD6MergeTightLabel grantDrainD6MergeInitialLabel
    grantDrainD6DeathWitnessAfter
    grantDrainD6DeathWitnessState
    grantDrainD6DeathWitnessNative
    grantDrainD6DeathWitnessRing
    grantDrainD6MergeFront
  decide

/-- Y1, concrete complete preservation: the true reserve is
consumed; the warm label remains alive; the new front is
shielded; the whole spent invariant holds. -/
theorem grantDrainD6MergeTightExceptionalSpentInvariant :
    GrantDrainWarmMergeSpent grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessAfter false)
      grantDrainD6MergeTightLabelAfter := by
  have hFields := grantDrainD6MergeTightExceptionalSpentFields
  intro q _ hHost _
  have hSame : q = (4 : Fin 5) :=
    Option.some.inj (hHost.symm.trans hFields.2.2.1)
  subst q
  exact Or.inl hFields.2.2.2.2.2

/-- Y2: a shielded, ready old front can disappear on a
LIVE collision; the outgoing killer is consumed, the ready
DUMMY survives, and the new nearest leader is shielded.
We start with a spent reserve (not a fresh exception). -/
private def grantDrainD6MergeReadySpentLabel : GrantDrainWarmLabel 5 :=
  { identity := (4 : Fin 5)
    host := some (4 : Fin 5)
    warm := true
    birthsLeft := 5
    exceptionalLeft := false }

private def grantDrainD6MergeReadySpentLabelAfter :
    GrantDrainWarmLabel 5 :=
  grantDrainWarmLabelStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainD6ReadyResponderFiveBefore (2 : Fin 5)
    grantDrainD6MergeReadySpentLabel

theorem grantDrainD6MergeReadySpentFieldTrace :
    grantDrainD6MergeReadySpentLabelAfter.warm = true ∧
    grantDrainD6MergeReadySpentLabelAfter.host =
      some (4 : Fin 5) ∧
    grantDrainD6MergeReadySpentLabelAfter.exceptionalLeft = false ∧
    ((grantDrainD6ReadyResponderFiveAfter.native
      (3 : Fin 5)).b = (1 : Fin 3)) ∧
    grantDrainD6MergeFront grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveAfter.native
      (4 : Fin 5) = (0 : Fin 5) ∧
    ((grantDrainD6ReadyResponderFiveAfter.native
      (grantDrainD6MergeFront grantDrainWarmPairCaseRing
        grantDrainD6ReadyResponderFiveAfter.native
        (4 : Fin 5))).sh = true) := by
  unfold grantDrainD6MergeReadySpentLabelAfter
    grantDrainD6MergeReadySpentLabel
    grantDrainD6ReadyResponderFiveAfter
    grantDrainD6ReadyResponderFiveBefore
    grantDrainD6ReadyResponderFiveNative
    grantDrainWarmPairCaseRing
    grantDrainD6MergeFront
  decide

/-- Y2 old and new spent invariants, with an ACTUAL physical
leader deletion. These are not fictional successor sectors. -/
theorem grantDrainD6MergeReadySpentStep :
    GrantDrainWarmMergeSpent grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveBefore
      grantDrainD6MergeReadySpentLabel ∧
    GrantDrainWarmMergeSpent grantDrainWarmPairCaseRing
      grantDrainD6ReadyResponderFiveAfter
      grantDrainD6MergeReadySpentLabelAfter := by
  have hBefore :
      ((grantDrainD6ReadyResponderFiveBefore.native
        (grantDrainD6MergeFront grantDrainWarmPairCaseRing
          grantDrainD6ReadyResponderFiveBefore.native
          (4 : Fin 5))).sh = true) := by
    unfold grantDrainD6ReadyResponderFiveBefore
      grantDrainD6ReadyResponderFiveNative
      grantDrainWarmPairCaseRing
      grantDrainD6MergeFront
    decide
  have hAfter := (grantDrainD6MergeReadySpentFieldTrace).2.2.2.2.2
  constructor
  · intro q _ hHost _
    have hSame : q = (4 : Fin 5) := by
      change some (4 : Fin 5) = some q at hHost
      exact (Option.some.inj hHost).symm
    subst q
    exact Or.inl hBefore
  · intro q _ hHost _
    have hSame : q = (4 : Fin 5) :=
      Option.some.inj (hHost.symm.trans
        (grantDrainD6MergeReadySpentFieldTrace).2.1)
    subst q
    exact Or.inl hAfter

/-- Y3 finite bullet motion and subsequent crossing of the
warm label. Once the bullet enters the old grant site,
the physical token moves counterclockwise but its warm
phase terminates rather than restarting with an unprotected
front. -/
private def grantDrainD6MergeMovingSpentLabel : GrantDrainWarmLabel 5 :=
  { identity := (3 : Fin 5)
    host := some (3 : Fin 5)
    warm := true
    birthsLeft := 5
    exceptionalLeft := false }

private def grantDrainD6MergeMovingSpentLabelAfter :
    GrantDrainWarmLabel 5 :=
  grantDrainWarmLabelStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWarmPairCaseLeader (1 : Fin 5)
    grantDrainD6MergeMovingSpentLabel

private def grantDrainD6MergeCrossingSpentLabelAfter :
    GrantDrainWarmLabel 5 :=
  grantDrainWarmLabelStep grantDrainWarmPairCaseRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWarmLeftBulletFiveAfter (2 : Fin 5)
    grantDrainD6MergeMovingSpentLabelAfter

theorem grantDrainD6MergeBulletMoveAndCrossTrace :
    grantDrainD6MergeMovingSpentLabelAfter.host =
      some (3 : Fin 5) ∧
    grantDrainD6MergeMovingSpentLabelAfter.warm = true ∧
    grantDrainD6MergeMovingSpentLabelAfter.exceptionalLeft = false ∧
    (grantDrainWarmLeftBulletFiveAfter.native
      (2 : Fin 5)).b = (2 : Fin 3) ∧
    grantDrainD6MergeCrossingSpentLabelAfter.warm = false := by
  unfold grantDrainD6MergeMovingSpentLabelAfter
    grantDrainD6MergeCrossingSpentLabelAfter
    grantDrainD6MergeMovingSpentLabel
    grantDrainWarmLeftBulletFiveAfter
    grantDrainWarmPairCaseLeader
    grantDrainWarmPairCaseInitial
    grantDrainWarmPairCaseNative
    grantDrainWarmPairCaseRing
  decide

/-- Y3: after crossing the unique left bullet, the actual
spent-label successor satisfies the invariant by leaving
the warm phase, not by an unjustified scan equality. -/
theorem grantDrainD6MergeBulletCrossingSpentInvariant :
    GrantDrainWarmMergeSpent grantDrainWarmPairCaseRing
      (grantDrainStep grantDrainWarmPairCaseRing
        (fun _ _ => false) (fun _ _ => ())
        grantDrainWarmLeftBulletFiveAfter (2 : Fin 5))
      grantDrainD6MergeCrossingSpentLabelAfter := by
  intro g hWarm _ _
  have hCold := (grantDrainD6MergeBulletMoveAndCrossTrace).2.2.2.2
  rw [hCold] at hWarm
  cases hWarm

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6MergeReadyResponderDummyPair
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeResponderShieldLossHasDummy
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeSourceShieldMonotone
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeCanonicalBirthProtected
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeOutgoingBulletSourceSignalZeroPair
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeOutgoingBulletNoFireColdEndpoints
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeColdLabelRemainsCold
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeTightExceptionalSpentFields
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeTightExceptionalSpentInvariant
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeReadySpentFieldTrace
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeReadySpentStep
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeBulletMoveAndCrossTrace
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeBulletCrossingSpentInvariant

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Canonical-birth split in the two occupied-bullet phases.
These are purely local lemmas.  No multi-leader E-closure is assumed.
-/

/-- A canonical newborn has no bullet. -/
theorem grantDrainSettledBirthRootNoBullet
    {n : Nat} (N : Fin n → CertNative) (z : Fin n) :
    ¬ HasBullet (canonicalBirth N z) z := by
  simp [HasBullet, canonicalBirth, firedNative]

/-- A canonical newborn starts with a zero signal. -/
theorem grantDrainSettledBirthRootSignalZero
    {n : Nat} (N : Fin n → CertNative) (z : Fin n) :
    (canonicalBirth N z z).sg = false := by
  simp [canonicalBirth, firedNative]

/-- Bullets on the original left arc, away from the birth site,
are unchanged. -/
theorem grantDrainSettledBirthLeftBulletTransport
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p z : Fin n)
    (k j : Nat)
    (hz : z = PPL.shiftRight ring p k)
    (hk : k < n) (hj : j < n) (hne : j ≠ k) :
    HasBullet (canonicalBirth N z)
        (PPL.shiftRight ring p j) ↔
      HasBullet N (PPL.shiftRight ring p j) := by
  unfold HasBullet
  rw [grantDrainSettledBirthOldArcFrame
    ring N p z k j hz hk hj hne]

/-- Bullets at strictly positive new right offsets coincide with
the old bullets at the corresponding offset k+j. -/
theorem grantDrainSettledBirthRightBulletTransport
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p z : Fin n)
    (k j : Nat)
    (hz : z = PPL.shiftRight ring p k)
    (hjPos : 0 < j) (hjLt : j < n) :
    HasBullet (canonicalBirth N z)
        (PPL.shiftRight ring z j) ↔
      HasBullet N (PPL.shiftRight ring p (k + j)) := by
  unfold HasBullet
  rw [grantDrainSettledBirthRebasedFollower
    ring N p z k j hz hjPos hjLt]

/-- Extract the unique old bullet phase with the specified bullet
position from a settled sector. No phase premise is assumed. -/
theorem grantDrainSettledBirthBulletPhase
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n)
    (d : Fin (n + 1)) (h : Fin n)
    (hh : h.val < d.val)
    (hb : HasBullet N (PPL.shiftRight ring p h.val))
    (hOld : GrantDrainSettledSector ring N p d) :
    (∀ i : Fin n, i.val ≤ h.val →
      (N (PPL.shiftRight ring p i.val)).sg = false) ∧
      signalZeroStarOneStar ring N p (h.val + 1) d.val := by
  rcases hOld.2.2 with hSome | hNone
  · obtain ⟨a, ha, haBullet, haZero, haSuffix⟩ := hSome
    have heq : h = a := hOld.1 h a hh ha hb haBullet
    subst a
    exact ⟨haZero, haSuffix⟩
  · exact False.elim (hNone.1 h hh hb)

/-- B1. An interior birth strictly AFTER the old unique bullet
retains that bullet in the left sector; its zero trail and suffix
are inherited. The new right sector has no bullets and retains
the rebased terminal suffix, including the d=n wrap case. -/
theorem grantDrainSettledBirthBeforeBulletSplit
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p z : Fin n)
    (d : Fin (n + 1)) (k : Nat) (h : Fin n)
    (hz : z = PPL.shiftRight ring p k)
    (hk : 0 < k) (hkd : k < d.val)
    (hh : h.val < k)
    (hb : HasBullet N (PPL.shiftRight ring p h.val))
    (hOldSector : sectorLength ring N p d)
    (hOldSettled : GrantDrainSettledSector ring N p d) :
    (sectorLength ring (canonicalBirth N z) p
        (⟨k, show k < n + 1 by omega⟩ : Fin (n + 1)) ∧
      GrantDrainSettledSector ring (canonicalBirth N z) p
        (⟨k, show k < n + 1 by omega⟩ : Fin (n + 1))) ∧
    (sectorLength ring (canonicalBirth N z) z
        (⟨d.val - k, show d.val - k < n + 1 by omega⟩ :
          Fin (n + 1)) ∧
      GrantDrainSettledSector ring (canonicalBirth N z) z
        (⟨d.val - k, show d.val - k < n + 1 by omega⟩ :
          Fin (n + 1))) := by
  have hmax : d.val ≤ n := Nat.le_of_lt_succ d.isLt
  have hkLt : k < n := by omega
  have hhd : h.val < d.val := by omega
  have hLengths := grantDrainSettledCanonicalBirthSectorLengths
    ring N p z d k hz hk hkd hOldSector
  have hPhase := grantDrainSettledBirthBulletPhase
    ring N p d h hhd hb hOldSettled
  have hLeftBullet :
      HasBullet (canonicalBirth N z)
        (PPL.shiftRight ring p h.val) :=
    (grantDrainSettledBirthLeftBulletTransport
      ring N p z k h.val hz hkLt h.isLt (by omega)).2 hb
  have hLeftUnique :
      ∀ a b : Fin n, a.val < k → b.val < k →
        HasBullet (canonicalBirth N z)
          (PPL.shiftRight ring p a.val) →
        HasBullet (canonicalBirth N z)
          (PPL.shiftRight ring p b.val) → a = b := by
    intro a b ha hbnd haBullet hbBullet
    have haOld :=
      (grantDrainSettledBirthLeftBulletTransport
        ring N p z k a.val hz hkLt a.isLt (by omega)).1 haBullet
    have hbOld :=
      (grantDrainSettledBirthLeftBulletTransport
        ring N p z k b.val hz hkLt b.isLt (by omega)).1 hbBullet
    exact hOldSettled.1 a b (by omega) (by omega) haOld hbOld
  have hLeftZero :
      ∀ a : Fin n, a.val < k →
        HasBullet (canonicalBirth N z)
          (PPL.shiftRight ring p a.val) →
        ∀ i : Fin n, i.val ≤ a.val →
          ((canonicalBirth N z)
            (PPL.shiftRight ring p i.val)).sg = false := by
    intro a ha haBullet i hi
    have haOld :=
      (grantDrainSettledBirthLeftBulletTransport
        ring N p z k a.val hz hkLt a.isLt (by omega)).1 haBullet
    have hOldZero := hOldSettled.2.1
      a (by omega) haOld i hi
    have hFrame := grantDrainSettledBirthOldArcFrame
      ring N p z k i.val hz hkLt i.isLt (by omega)
    rw [hFrame]
    exact hOldZero
  have hLeftTrail :
      ∀ i : Fin n, i.val ≤ h.val →
        ((canonicalBirth N z)
          (PPL.shiftRight ring p i.val)).sg = false := by
    intro i hi
    have hFrame := grantDrainSettledBirthOldArcFrame
      ring N p z k i.val hz hkLt i.isLt (by omega)
    rw [hFrame]
    exact hPhase.1 i hi
  have hLeftSuffix :
      signalZeroStarOneStar ring (canonicalBirth N z)
        p (h.val + 1) k := by
    have hRebased := grantDrainSettledSignalRebase
      ring N (canonicalBirth N z) p 0
      (h.val + 1) k (h.val + 1) d.val
      hmax
      (show h.val + 1 ≤ k ∧
        h.val + 1 ≤ 0 + (h.val + 1) ∧
        0 + k ≤ d.val by omega)
      hPhase.2
      (by
        intro i hi hlo
        have hFrame := grantDrainSettledBirthOldArcFrame
          ring N p z k i.val hz hkLt i.isLt (by omega)
        simpa only [grantDrainWeakDeathShiftRightZero, Nat.zero_add]
          using congrArg (fun c : CertNative => c.sg) hFrame)
    simpa only [grantDrainWeakDeathShiftRightZero] using hRebased
  have hRightNo :
      ∀ i : Fin n, i.val < d.val - k →
        ¬ HasBullet (canonicalBirth N z)
          (PPL.shiftRight ring z i.val) := by
    intro i hi hiBullet
    by_cases hiZero : i.val = 0
    · have hSite : PPL.shiftRight ring z i.val = z := by
        rw [hiZero, grantDrainWeakDeathShiftRightZero]
      rw [hSite] at hiBullet
      exact (grantDrainSettledBirthRootNoBullet N z) hiBullet
    · have hiPos : 0 < i.val := by omega
      have hiOld :=
        (grantDrainSettledBirthRightBulletTransport
          ring N p z k i.val hz hiPos i.isLt).1 hiBullet
      have hiIndex : k + i.val < n := by omega
      have heq : h = (⟨k + i.val, hiIndex⟩ : Fin n) :=
        hOldSettled.1 h
          (⟨k + i.val, hiIndex⟩ : Fin n)
          hhd (show k + i.val < d.val by omega) hb hiOld
      have hval : h.val = k + i.val := congrArg Fin.val heq
      omega
  have hRightSuffix :
      signalZeroStarOneStar ring (canonicalBirth N z)
        z 1 (d.val - k) := by
    have hRebased := grantDrainSettledSignalRebase
      ring N (canonicalBirth N z) p k
      1 (d.val - k) (h.val + 1) d.val
      hmax
      (show 1 ≤ d.val - k ∧
        h.val + 1 ≤ k + 1 ∧
        k + (d.val - k) ≤ d.val by omega)
      hPhase.2
      (by
        intro i hi hlo
        simpa only [hz] using
          congrArg (fun c : CertNative => c.sg)
            (grantDrainSettledBirthRebasedFollower
              ring N p z k i.val hz hi i.isLt))
    simpa only [hz] using hRebased
  have hLeftSettled :
      GrantDrainSettledSector ring (canonicalBirth N z) p
        (⟨k, show k < n + 1 by omega⟩ : Fin (n + 1)) := by
    refine ⟨hLeftUnique, hLeftZero, Or.inl ?_⟩
    exact ⟨h, hh, hLeftBullet, hLeftTrail, hLeftSuffix⟩
  have hRightSettled :
      GrantDrainSettledSector ring (canonicalBirth N z) z
        (⟨d.val - k, show d.val - k < n + 1 by omega⟩ :
          Fin (n + 1)) := by
    refine ⟨?_, ?_, Or.inr ?_⟩
    · intro a b ha hbnd haBullet
      exact False.elim (hRightNo a ha haBullet)
    · intro a ha haBullet
      exact False.elim (hRightNo a ha haBullet)
    · refine ⟨hRightNo, hRightSuffix, ?_⟩
      intro hReady
      have hZero := grantDrainSettledBirthRootSignalZero N z
      rw [hZero] at hReady
      cases hReady
  exact ⟨⟨hLengths.1, hLeftSettled⟩,
    ⟨hLengths.2, hRightSettled⟩⟩




/-- The position of an actual in-sector bullet is bounded by
the sector length, and it is unique. The explicit witness
identification is necessary; an arbitrary bullet on the ring
may be outside this sector. -/
theorem grantDrainSettledBirthBulletIndexBound
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n)
    (d : Fin (n + 1))
    (hOldSettled : GrantDrainSettledSector ring N p d)
    (h : Fin n)
    (hSectorWitness :
      ∃ a : Fin n,
        a.val < d.val ∧
        HasBullet N (PPL.shiftRight ring p a.val) ∧
        a = h) :
    h.val < d.val ∧
      (∀ j : Fin n, j.val < d.val →
        HasBullet N (PPL.shiftRight ring p j.val) → j = h) := by
  obtain ⟨a, ha, hb, heq⟩ := hSectorWitness
  subst h
  refine ⟨ha, ?_⟩
  intro j hj jBullet
  exact hOldSettled.1 j a hj ha jBullet hb

/-- B2. An interior birth strictly BEFORE the old unique bullet
leaves a bullet-free, entirely zero-signal left sector. The old
bullet moves into the right sector with its zero trail measured
from the newborn leader, and its old terminal suffix is rebased.
In particular the new leader's zero signal repairs, rather than
violates, the required zero-trail predicate. -/
theorem grantDrainSettledBirthAfterBulletSplit
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p z : Fin n)
    (d : Fin (n + 1)) (k : Nat) (h : Fin n)
    (hz : z = PPL.shiftRight ring p k)
    (hk : 0 < k) (hkd : k < d.val)
    (hh : k < h.val) (hSectorIndex : h.val < d.val)
    (hb : HasBullet N (PPL.shiftRight ring p h.val))
    (hOldSector : sectorLength ring N p d)
    (hOldSettled : GrantDrainSettledSector ring N p d) :
    (sectorLength ring (canonicalBirth N z) p
        (⟨k, show k < n + 1 by omega⟩ : Fin (n + 1)) ∧
      GrantDrainSettledSector ring (canonicalBirth N z) p
        (⟨k, show k < n + 1 by omega⟩ : Fin (n + 1))) ∧
    (sectorLength ring (canonicalBirth N z) z
        (⟨d.val - k, show d.val - k < n + 1 by omega⟩ :
          Fin (n + 1)) ∧
      GrantDrainSettledSector ring (canonicalBirth N z) z
        (⟨d.val - k, show d.val - k < n + 1 by omega⟩ :
          Fin (n + 1))) := by
  have hmax : d.val ≤ n := Nat.le_of_lt_succ d.isLt
  have hkLt : k < n := by omega
  have hIndexBound := grantDrainSettledBirthBulletIndexBound
    ring N p d hOldSettled h
    ⟨h, hSectorIndex, hb, rfl⟩
  have hhd : h.val < d.val := hIndexBound.1
  have hLengths := grantDrainSettledCanonicalBirthSectorLengths
    ring N p z d k hz hk hkd hOldSector
  have hPhase := grantDrainSettledBirthBulletPhase
    ring N p d h hhd hb hOldSettled
  have hLeftNo :
      ∀ i : Fin n, i.val < k →
        ¬ HasBullet (canonicalBirth N z)
          (PPL.shiftRight ring p i.val) := by
    intro i hi hiBullet
    have hiOld :=
      (grantDrainSettledBirthLeftBulletTransport
        ring N p z k i.val hz hkLt i.isLt (by omega)).1 hiBullet
    have heq : h = i :=
      hOldSettled.1 h i hhd (by omega) hb hiOld
    have hval : h.val = i.val := congrArg Fin.val heq
    omega
  have hLeftZero :
      ∀ i : Fin n, i.val < k →
        ((canonicalBirth N z)
          (PPL.shiftRight ring p i.val)).sg = false := by
    intro i hi
    have hFrame := grantDrainSettledBirthOldArcFrame
      ring N p z k i.val hz hkLt i.isLt (by omega)
    rw [hFrame]
    exact hPhase.1 i (by omega)
  have hCutBounds : 1 ≤ k ∧ k < n + 1 := by
    omega
  have hLeftSuffix :
      signalZeroStarOneStar ring (canonicalBirth N z) p 1 k := by
    unfold signalZeroStarOneStar
    refine ⟨⟨k, hCutBounds.2⟩,
      hCutBounds.1, Nat.le_refl _, ?_, ?_⟩
    · intro i hiOne hiCut
      exact hLeftZero i (by (try dsimp only at *); omega)
    · intro i hiCut hiHi
      (try dsimp only at *)
      omega
  have hLeftRootZero :
      ((canonicalBirth N z) p).sg = false := by
    have hAtZero := hLeftZero
      (⟨0, show 0 < n by omega⟩ : Fin n)
      (show 0 < k by omega)
    simpa only [grantDrainWeakDeathShiftRightZero] using hAtZero
  have hRightRootNo := grantDrainSettledBirthRootNoBullet N z
  have hRightPositive :
      ∀ i : Fin n,
        HasBullet (canonicalBirth N z)
          (PPL.shiftRight ring z i.val) →
        0 < i.val := by
    intro i hiBullet
    by_cases hiZero : i.val = 0
    · have hSite : PPL.shiftRight ring z i.val = z := by
        rw [hiZero, grantDrainWeakDeathShiftRightZero]
      rw [hSite] at hiBullet
      exact False.elim (hRightRootNo hiBullet)
    · omega
  have hRightUnique :
      ∀ a b : Fin n, a.val < d.val - k →
        b.val < d.val - k →
        HasBullet (canonicalBirth N z)
          (PPL.shiftRight ring z a.val) →
        HasBullet (canonicalBirth N z)
          (PPL.shiftRight ring z b.val) → a = b := by
    intro a b ha hbnd haBullet hbBullet
    have haPos := hRightPositive a haBullet
    have hbPos := hRightPositive b hbBullet
    have haOld :=
      (grantDrainSettledBirthRightBulletTransport
        ring N p z k a.val hz haPos a.isLt).1 haBullet
    have hbOld :=
      (grantDrainSettledBirthRightBulletTransport
        ring N p z k b.val hz hbPos b.isLt).1 hbBullet
    have haIndex : k + a.val < n := by omega
    have hbIndex : k + b.val < n := by omega
    have heq :
        (⟨k + a.val, haIndex⟩ : Fin n) =
          (⟨k + b.val, hbIndex⟩ : Fin n) :=
      hOldSettled.1
        (⟨k + a.val, haIndex⟩ : Fin n)
        (⟨k + b.val, hbIndex⟩ : Fin n)
        (show k + a.val < d.val by omega)
        (show k + b.val < d.val by omega)
        haOld hbOld
    have hval : k + a.val = k + b.val := congrArg Fin.val heq
    apply Fin.ext
    omega
  have hRightZero :
      ∀ a : Fin n, a.val < d.val - k →
        HasBullet (canonicalBirth N z)
          (PPL.shiftRight ring z a.val) →
        ∀ i : Fin n, i.val ≤ a.val →
          ((canonicalBirth N z)
            (PPL.shiftRight ring z i.val)).sg = false := by
    intro a ha haBullet i hi
    have haPos := hRightPositive a haBullet
    have haOld :=
      (grantDrainSettledBirthRightBulletTransport
        ring N p z k a.val hz haPos a.isLt).1 haBullet
    have haIndex : k + a.val < n := by omega
    have hOldZero := hOldSettled.2.1
      (⟨k + a.val, haIndex⟩ : Fin n)
      (show k + a.val < d.val by omega) haOld
    by_cases hiZero : i.val = 0
    · have hSite : PPL.shiftRight ring z i.val = z := by
        rw [hiZero, grantDrainWeakDeathShiftRightZero]
      rw [hSite]
      exact grantDrainSettledBirthRootSignalZero N z
    · have hiPos : 0 < i.val := by omega
      have hiIndex : k + i.val < n := by omega
      have hOldSignal :
          (N (PPL.shiftRight ring p (k + i.val))).sg = false :=
        hOldZero
          (⟨k + i.val, hiIndex⟩ : Fin n)
          (show k + i.val ≤ k + a.val by omega)
      rw [grantDrainSettledBirthRebasedFollower
        ring N p z k i.val hz hiPos i.isLt]
      exact hOldSignal
  have hRightIndex : h.val - k < n := by omega
  have hRightIndexPos : 0 < h.val - k := by omega
  have hRightBullet :
      HasBullet (canonicalBirth N z)
        (PPL.shiftRight ring z (h.val - k)) := by
    have hAddition : k + (h.val - k) = h.val := by omega
    have hOldShifted :
        HasBullet N
          (PPL.shiftRight ring p (k + (h.val - k))) := by
      rw [hAddition]
      exact hb
    exact (grantDrainSettledBirthRightBulletTransport
      ring N p z k (h.val - k)
      hz hRightIndexPos hRightIndex).2 hOldShifted
  have hRightTrail :
      ∀ i : Fin n, i.val ≤ h.val - k →
        ((canonicalBirth N z)
          (PPL.shiftRight ring z i.val)).sg = false := by
    intro i hi
    by_cases hiZero : i.val = 0
    · have hSite : PPL.shiftRight ring z i.val = z := by
        rw [hiZero, grantDrainWeakDeathShiftRightZero]
      rw [hSite]
      exact grantDrainSettledBirthRootSignalZero N z
    · have hiPos : 0 < i.val := by omega
      have hiIndex : k + i.val < n := by omega
      have hOldSignal :
          (N (PPL.shiftRight ring p (k + i.val))).sg = false :=
        hPhase.1
          (⟨k + i.val, hiIndex⟩ : Fin n)
          (show k + i.val ≤ h.val by omega)
      rw [grantDrainSettledBirthRebasedFollower
        ring N p z k i.val hz hiPos i.isLt]
      exact hOldSignal
  have hRightSuffix :
      signalZeroStarOneStar ring (canonicalBirth N z)
        z (h.val - k + 1) (d.val - k) := by
    have hRebased := grantDrainSettledSignalRebase
      ring N (canonicalBirth N z) p k
      (h.val - k + 1) (d.val - k) (h.val + 1) d.val
      hmax
      (show h.val - k + 1 ≤ d.val - k ∧
        h.val + 1 ≤ k + (h.val - k + 1) ∧
        k + (d.val - k) ≤ d.val by omega)
      hPhase.2
      (by
        intro i hi hlo
        have hiPos : 0 < i.val := by omega
        simpa only [hz] using
          congrArg (fun c : CertNative => c.sg)
            (grantDrainSettledBirthRebasedFollower
              ring N p z k i.val hz hiPos i.isLt))
    simpa only [hz] using hRebased
  have hLeftSettled :
      GrantDrainSettledSector ring (canonicalBirth N z) p
        (⟨k, show k < n + 1 by omega⟩ : Fin (n + 1)) := by
    refine ⟨?_, ?_, Or.inr ?_⟩
    · intro a b ha hbnd haBullet
      exact False.elim (hLeftNo a ha haBullet)
    · intro a ha haBullet
      exact False.elim (hLeftNo a ha haBullet)
    · refine ⟨hLeftNo, hLeftSuffix, ?_⟩
      intro hReady
      rw [hLeftRootZero] at hReady
      cases hReady
  have hRightSettled :
      GrantDrainSettledSector ring (canonicalBirth N z) z
        (⟨d.val - k, show d.val - k < n + 1 by omega⟩ :
          Fin (n + 1)) := by
    refine ⟨hRightUnique, hRightZero, Or.inl ?_⟩
    refine ⟨(⟨h.val - k, hRightIndex⟩ : Fin n),
      (show h.val - k < d.val - k by omega),
      hRightBullet, ?_, ?_⟩
    · exact hRightTrail
    · exact hRightSuffix
  exact ⟨⟨hLengths.1, hLeftSettled⟩,
    ⟨hLengths.2, hRightSettled⟩⟩

/-- The unconditional index bound is false, even at n=5 and
under C_native. The sector from p=3 to 0 has length d=2,
but the same settled configuration has a bullet at offset
h=4 (physical site 2) in a different sector. -/
theorem grantDrainSettledBirthGlobalBulletOutsideSector :
    C_native grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native ∧
    sectorLength grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native
      (3 : Fin 5) (2 : Fin 6) ∧
    GrantDrainSettledSector grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native
      (3 : Fin 5) (2 : Fin 6) ∧
    HasBullet (grantDrainD6DeathWitnessState false).native
      (PPL.shiftRight grantDrainD6DeathWitnessRing
        (3 : Fin 5) 4) ∧
    (2 : Fin 6).val ≤ (4 : Fin 5).val := by
  have hC : C_native grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native :=
    (grantDrainD6DeathWitnessAdmissible false).2.1
  have hSector : sectorLength grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native
      (3 : Fin 5) (2 : Fin 6) := by
    unfold sectorLength
    decide
  have hLocal : GrantDrainSettledSector
      grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native
      (3 : Fin 5) (2 : Fin 6) :=
    ((grantDrainC_native_iff_sectors
      grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native).mp hC).2
        (3 : Fin 5) (2 : Fin 6) hSector
  refine ⟨hC, hSector, hLocal, ?_, ?_⟩
  · unfold HasBullet grantDrainD6DeathWitnessState
      grantDrainD6DeathWitnessNative grantDrainD6DeathWitnessRing
    decide
  · decide


end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthAfterBulletSplit
#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthBeforeBulletSplit
#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthBulletIndexBound
#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthBulletPhase
#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthGlobalBulletOutsideSector
#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthLeftBulletTransport
#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthRightBulletTransport
#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthRootNoBullet
#print axioms L3.GrantDrainEntrance.grantDrainSettledBirthRootSignalZero

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
D6-PAIR-SCAN.

"Fire" below is the native E emission at a ready leader.
The actual canonical FIRE/birth overlay is absent, as required
by the existing physical-field lemmas (hNone).
For F1, a >= 2 means the emitted bullet remains strictly
behind g. The a = 1 contact is already covered by
grantDrainWarmReadyFrontSourceContactPhysical: warm ends there.
-/

/-- The counterclockwise coordinate of an interior sector point. -/
private theorem grantDrainD6FireFrontCoordinate
    {n : Nat} (ring : DirectedRing n)
    (p g : Fin n) (a : Nat)
    (ha : a < n)
    (hAt : g = PPL.shiftRight ring p a) :
    PPL.shiftLeft ring g a = p := by
  rw [hAt]
  rw [grantDrainMarksArcShiftLeftRight
    ring p a a (Nat.le_refl _) ha]
  rw [Nat.sub_self]
  exact grantDrainWeakDeathShiftRightZero ring p

/-- A ready settled sector is bullet-free all the way from its
front to g and carries signal one at every site strictly between
that front and g, including g itself. This is obtained from the
actual C_native disjunction rather than assumed as a scan leaf. -/
private theorem grantDrainD6FireReadyPrefix
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring N)
    (hSector : sectorLength ring N p D)
    (ha : 1 ≤ a) (haInside : a < D.val)
    (hAt : g = PPL.shiftRight ring p a)
    (hReady : (N p).sg = true) :
    (∀ j : Nat, j < a →
      (N (PPL.shiftLeft ring g j)).sg = true) ∧
    (∀ j : Nat, j ≤ a →
      (N (PPL.shiftLeft ring g j)).b = (0 : Fin 3)) := by
  have haN : a < n := by
    have hD := D.isLt
    omega
  rcases hC.2 p D hSector with hOccupied | hEmpty
  · obtain ⟨q, _, _, hTrail, _⟩ := hOccupied
    have hZeroAt :
        (N (PPL.shiftRight ring p 0)).sg = false :=
      hTrail (⟨0, ring.hn⟩ : Fin n) (Nat.zero_le _)
    rw [grantDrainWeakDeathShiftRightZero ring p, hReady] at hZeroAt
    cases hZeroAt
  · obtain ⟨hNoBullet, _, hReadyBody⟩ := hEmpty
    constructor
    · intro j hj
      have hArc :
          PPL.shiftLeft ring g j =
            PPL.shiftRight ring p (a - j) := by
        rw [hAt]
        exact grantDrainMarksArcShiftLeftRight
          ring p a j (by omega) haN
      rw [hArc]
      exact hReadyBody hReady
        (⟨a - j, show a - j < n by omega⟩ : Fin n)
        (show 1 ≤ a - j by omega)
        (show a - j < D.val by omega)
    · intro j hj
      have hArc :
          PPL.shiftLeft ring g j =
            PPL.shiftRight ring p (a - j) := by
        rw [hAt]
        exact grantDrainMarksArcShiftLeftRight
          ring p a j hj haN
      rw [hArc]
      by_cases hb :
          (N (PPL.shiftRight ring p (a - j))).b =
            (0 : Fin 3)
      · exact hb
      · have hImpossible :=
          hNoBullet
            (⟨a - j, show a - j < n by omega⟩ : Fin n)
            (show a - j < D.val by omega) hb
        exact False.elim hImpossible

/-- Lower bound for the actual first-leader scan, including its
getD n fallback. No hypothesis about the terminal leader is made. -/
private theorem grantDrainD6FireLeaderPrefixLowerBound
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) (a : Nat)
    (ha : a ≤ n)
    (hNoLeader : ∀ j : Nat, 1 ≤ j → j < a →
      (N (PPL.shiftLeft ring g j)).l = false) :
    a ≤ grantDrainLeftLeaderDistance ring N g := by
  have hScan :
      grantDrainLeftLeaderDistance ring N g =
        ((List.range' 1 n).find?
          (fun j => (N (PPL.shiftLeft ring g j)).l)).getD n := by
    unfold grantDrainLeftLeaderDistance
    rw [grantDrainWarmPositiveRange]
  rw [hScan]
  cases hf : (List.range' 1 n).find?
      (fun j => (N (PPL.shiftLeft ring g j)).l) with
  | none =>
      simpa [hf] using ha
  | some q =>
      obtain ⟨hqPos, _, hHit, _⟩ :=
        grantDrainWarmRangeFindConverse
          (fun j => (N (PPL.shiftLeft ring g j)).l)
          n 1 q hf
      have hLower : a ≤ q := by
        by_cases hEarlier : q < a
        · have hFalse := hNoLeader q hqPos hEarlier
          rw [hFalse] at hHit
          cases hHit
        · omega
      simpa [hf] using hLower

/-- A ready source and its empty follower keep their leader flags
and clear the new LIVE responder's signal. -/
private theorem grantDrainD6FireReadySourcePair
    (x y : CertNative)
    (hXL : x.l = true) (hXS : x.sg = true)
    (hYL : y.l = false) (hYB : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.l = x.l ∧
    (certLiteralEPair x y).2.l = y.l ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, hXL, hXS, hYL, hYB, certFinThree]

/-- F1, all n >= 5, strictly interior ready-front source.
The ready leader sends its new LIVE to offset a-1. The entire
old inclusive bullet scan is empty; the new first bullet is
at a-1, and the physical warm rank drops by at least one.
The actual step is E-only (native firing but no canonical birth). -/
theorem grantDrainD6FireReadySourceRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hSector : sectorLength ring s.native e D)
    (hAt : g = PPL.shiftRight ring e a)
    (ha : 2 ≤ a) (haInside : a < D.val)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = a)
    (hReady : (s.native e).sg = true)
    (hTo : ring.rightNeighbor e =
      PPL.shiftLeft ring g (a - 1))
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainLeftBulletDistance ring s.native g a = none ∧
    grantDrainLeftBulletDistance ring
      (grantDrainStep ring fresh update s e).native g a =
        some (a - 1) ∧
    grantDrainWarmRank ring
      (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have haN : a < n := by
    have hD := D.isLt
    omega
  have hFront :
      PPL.shiftLeft ring g a = e :=
    grantDrainD6FireFrontCoordinate ring e g a haN hAt
  have hReadyArc :=
    grantDrainD6FireReadyPrefix ring s.native e g D a
      hC hSector (by omega) haInside hAt hReady
  have hOldNone :
      grantDrainLeftBulletDistance ring s.native g a = none := by
    apply (grantDrainWarmBulletNoneCharacterization
      ring s.native g a).mpr
    intro j _ hj
    exact congrArg Fin.val (hReadyArc.2 j hj)
  have hXL : (s.native e).l = true := hSector.2.1
  have hYL :
      (s.native (ring.rightNeighbor e)).l = false := by
    rw [hTo]
    exact grantDrainD6MoveBeforeLeader ring s.native g
      a (a - 1) hDistance (by omega) (by omega)
  have hYB :
      (s.native (ring.rightNeighbor e)).b =
        (0 : Fin 3) := by
    rw [hTo]
    exact hReadyArc.2 (a - 1) (by omega)
  have hFields :=
    grantDrainWarmReadyFrontSourcePhysicalFields
      ring hn fresh update s e hXL hReady hYL hYB hNone
  have hNative :=
    grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone
  have hPair :=
    grantDrainD6FireReadySourcePair
      (s.native e) (s.native (ring.rightNeighbor e))
      hXL hReady hYL hYB
  have hLeaders : ∀ i : Fin n,
      ((grantDrainStep ring fresh update s e).native i).l =
        (s.native i).l := by
    intro i
    rw [hNative]
    by_cases hi : i = e
    · subst i
      simpa [nativeE] using hPair.1
    · by_cases hy : i = ring.rightNeighbor e
      · subst i
        have hNe := grantDrainWarmPhysicalPairDistinct ring hn e
        simpa [nativeE, hNe] using hPair.2.1
      · simp [nativeE, hi, hy]
  have hNewDistance :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g = a := by
    have hEq :
        grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g =
        grantDrainLeftLeaderDistance ring s.native g := by
      simp [grantDrainLeftLeaderDistance, hLeaders]
    exact hEq.trans hDistance
  have hPrefix : ∀ j : Nat, j < a - 1 →
      (grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g j) =
      s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    have hjN : j < n := by omega
    have hNE : PPL.shiftLeft ring g j ≠ e := by
      rw [← hFront]
      intro heq
      have hSame := grantDrainD6MoveShiftInjective
        ring g j a hjN haN heq
      omega
    have hNY :
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
      rw [hTo]
      intro heq
      have hSame := grantDrainD6MoveShiftInjective
        ring g j (a - 1) hjN (by omega) heq
      omega
    exact hFields.2.2 _ hNE hNY
  have hNewHit :
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g (a - 1))).b.val ≠ 0 := by
    rw [← hTo, hFields.2.1]
    decide
  have hNewBullet :
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native g a =
          some (a - 1) := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring (grantDrainStep ring fresh update s e).native
      g a (a - 1)).mpr
    refine ⟨by omega, by omega, hNewHit, ?_⟩
    intro j hj hjk
    rw [hPrefix j hjk, hReadyArc.2 j (by omega)]
    rfl
  have hNewStop :
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g (a - 1))).sg = false := by
    rw [← hTo, hNative]
    have hNe := grantDrainWarmPhysicalPairDistinct ring hn e
    simpa [nativeE, hNe] using hPair.2.2
  have hNewSignal :
      ∀ j : Nat, j < a - 1 →
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring g j)).sg = true := by
    intro j hj
    rw [hPrefix j hj]
    exact hReadyArc.1 j (by omega)
  have hNewWarmSignal :
      ((grantDrainStep ring fresh update s e).native g).sg =
        true := by
    have hHead := hNewSignal 0 (by omega)
    rw [grantDrainWarmShiftLeftZero] at hHead
    exact hHead
  have hNewTerminal :
      grantDrainTerminalRun ring
        (grantDrainStep ring fresh update s e).native g a =
          a - 2 := by
    apply (grantDrainWarmTerminalCharacterization
      ring (grantDrainStep ring fresh update s e).native
      g a (a - 2) (by omega) hNewWarmSignal).mpr
    refine ⟨by omega, ?_, Or.inr ?_⟩
    · intro j hj
      exact hNewSignal j (by omega)
    · have hIndex : a - 2 + 1 = a - 1 := by omega
      rw [hIndex]
      exact hNewStop
  have hOldRank :
      grantDrainWarmRank ring s.native g = 1 + a := by
    simp [grantDrainWarmRank, hDistance, hOldNone,
      hFront, hReady]
  have hNewRank :
      grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g =
          a - 1 := by
    simp [grantDrainWarmRank, hNewDistance,
      hNewBullet, hNewTerminal] <;> omega
  refine ⟨hOldNone, hNewBullet, ?_⟩
  rw [hNewRank, hOldRank]
  omega

/-- F2, all n >= 5, including simultaneous READY responder
DUMMY emission and deletion of that leader by an OLD incoming
LIVE. The killed leader remains as the FIRST new bullet at its
old distance a, even though the first-leader distance increases.
No post-step leader scan or bullet scan is assumed. -/
theorem grantDrainD6FireReadyResponderKilledRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hSector : sectorLength ring s.native p D)
    (hAt : g = PPL.shiftRight ring p a)
    (ha : 1 ≤ a) (haInside : a < D.val)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = a)
    (hReady : (s.native p).sg = true)
    (hTo : ring.rightNeighbor e = p)
    (hXL : (s.native e).l = false)
    (hXB : (s.native e).b = (2 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainLeftBulletDistance ring s.native g a = none ∧
    ((grantDrainStep ring fresh update s e).native p).l = false ∧
    ((grantDrainStep ring fresh update s e).native p).b =
      (1 : Fin 3) ∧
    grantDrainLeftBulletDistance ring
      (grantDrainStep ring fresh update s e).native g
      (grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g) =
        some a ∧
    grantDrainWarmRank ring
      (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have haN : a < n := by
    have hD := D.isLt
    omega
  have hFront :
      PPL.shiftLeft ring g a = p :=
    grantDrainD6FireFrontCoordinate ring p g a haN hAt
  have hReadyArc :=
    grantDrainD6FireReadyPrefix ring s.native p g D a
      hC hSector ha haInside hAt hReady
  have hOldNone :
      grantDrainLeftBulletDistance ring s.native g a = none := by
    apply (grantDrainWarmBulletNoneCharacterization
      ring s.native g a).mpr
    intro j _ hj
    exact congrArg Fin.val (hReadyArc.2 j hj)
  have hFields :=
    grantDrainWarmReadyFrontResponderPhysicalFields
      ring hn fresh update s e hXL hXB
      (by rw [hTo]; exact hSector.2.1)
      (by rw [hTo]; exact hReady) hNone
  have hNewPLeader :
      ((grantDrainStep ring fresh update s e).native p).l =
        false := by
    rw [← hTo]
    exact hFields.2.1
  have hNewPBullet :
      ((grantDrainStep ring fresh update s e).native p).b =
        (1 : Fin 3) := by
    rw [← hTo]
    exact hFields.2.2.1
  have hNewPSignal :
      ((grantDrainStep ring fresh update s e).native p).sg =
        false := by
    rw [← hTo]
    exact hFields.2.2.2.1
  have hPrefix : ∀ j : Nat, j < a →
      (grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g j) =
      s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    have hNE : PPL.shiftLeft ring g j ≠ e := by
      intro hEq
      have hZero : (s.native e).b = (0 : Fin 3) := by
        rw [← hEq]
        exact hReadyArc.2 j (by omega)
      rw [hXB] at hZero
      cases hZero
    have hNP : PPL.shiftLeft ring g j ≠ p := by
      rw [← hFront]
      intro hEq
      have hSame := grantDrainD6MoveShiftInjective
        ring g j a (by omega) haN hEq
      omega
    exact hFields.2.2.2.2 _ hNE (by rw [hTo]; exact hNP)
  have hOldLeaderPrefix :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g a (by omega) haN).mp hDistance
  have hLeaderLower :
      a ≤ grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g := by
    apply grantDrainD6FireLeaderPrefixLowerBound
      ring (grantDrainStep ring fresh update s e).native
      g a (by omega)
    intro j hj hja
    rw [hPrefix j hja]
    exact hOldLeaderPrefix.2 j hj hja
  have hNewHit :
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g a)).b.val ≠ 0 := by
    rw [hFront, hNewPBullet]
    decide
  have hNewBullet :
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g) =
          some a := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring (grantDrainStep ring fresh update s e).native
      g (grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g) a).mpr
    refine ⟨ha, hLeaderLower, hNewHit, ?_⟩
    intro j hj hja
    rw [hPrefix j hja, hReadyArc.2 j (by omega)]
    rfl
  have hNewSignal :
      ∀ j : Nat, j < a →
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring g j)).sg = true := by
    intro j hj
    rw [hPrefix j hj]
    exact hReadyArc.1 j hj
  have hNewWarmSignal :
      ((grantDrainStep ring fresh update s e).native g).sg =
        true := by
    have hHead := hNewSignal 0 (by omega)
    rw [grantDrainWarmShiftLeftZero] at hHead
    exact hHead
  have hNewTerminal :
      grantDrainTerminalRun ring
        (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g) =
          a - 1 := by
    apply (grantDrainWarmTerminalCharacterization
      ring (grantDrainStep ring fresh update s e).native
      g (grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g)
      (a - 1) (by omega) hNewWarmSignal).mpr
    refine ⟨by omega, ?_, ?_⟩
    · intro j hj
      exact hNewSignal j (by omega)
    · by_cases hEq :
          grantDrainLeftLeaderDistance ring
            (grantDrainStep ring fresh update s e).native g =
            a
      · exact Or.inl (by omega)
      · right
        have hIndex : a - 1 + 1 = a := by omega
        rw [hIndex, hFront]
        exact hNewPSignal
  have hOldRank :
      grantDrainWarmRank ring s.native g = 1 + a := by
    simp [grantDrainWarmRank, hDistance, hOldNone,
      hFront, hReady]
  have hNewRank :
      grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g = a := by
    simp [grantDrainWarmRank, hNewBullet,
      hNewTerminal] <;> omega
  refine ⟨hOldNone, hNewPLeader, hNewPBullet,
    hNewBullet, ?_⟩
  rw [hNewRank, hOldRank]
  omega

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6FireReadySourceRank
#print axioms L3.GrantDrainEntrance.grantDrainD6FireReadyResponderKilledRank

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
E1/E2 physical kernels and closed five-site controls.
The full arbitrary-n C_native preservation is NOT claimed.
-/

/-- E1: if the OLD responder is a follower, the literal native E
cannot delete any leader. No singleton or unproved sector closure
assumption is needed. -/
theorem grantDrainSettledEdgeFollowerNativeLeadersFixed
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hyFollower : (N (ring.rightNeighbor e)).l = false) :
    ∀ i : Fin n, (nativeE ring N e i).l = (N i).l := by
  have hDistinct := grantDrainEntranceRightNeighborDistinct
    ring (by omega : 2 ≤ n) e
  have hTarget :
      (nativeE ring N e (ring.rightNeighbor e)).l = false := by
    simpa [nativeE, hDistinct] using
      grantDrainEntranceLiteralEFollowerResponderRemains
        (N e) (N (ring.rightNeighbor e)) hyFollower
  have hKeep :
      (nativeE ring N e (ring.rightNeighbor e)).l =
        (N (ring.rightNeighbor e)).l :=
    hTarget.trans hyFollower.symm
  exact grantDrainEntranceNativeELeadersFixed
    ring (by omega : 2 ≤ n) N e hKeep

/-- E1 with or without FIRE: on a follower-responder edge,
every OLD leader survives the complete physical step.
Any newly appearing leader is due to a canonical birth.
This does not yet assert the signal suffix is settled. -/
theorem grantDrainSettledEdgeFollowerPhysicalKeepsOldLeaders
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false) :
    ∀ i : Fin n, (s.native i).l = true →
      ((grantDrainStep ring fresh update s e).native i).l =
        true := by
  have hFixed := grantDrainSettledEdgeFollowerNativeLeadersFixed
    ring hn s.native e hyFollower
  have hBirthKeeps :
      ∀ (N : Fin n → CertNative) (z i : Fin n),
        (N i).l = true → (canonicalBirth N z i).l = true := by
    intro N z i hi
    by_cases hiz : i = z
    · subst i
      simp [canonicalBirth, firedNative]
    · simpa [canonicalBirth, hiz] using hi
  intro i hi
  have hAtE : (nativeE ring s.native e i).l = true :=
    (hFixed i).trans hi
  rcases grantDrainEntranceNativeOwnerCases
    ring fresh update s e with hNone | hLeft | hRight
  · rw [hNone]
    exact hAtE
  · rw [hLeft]
    exact hBirthKeeps (nativeE ring s.native e) e i hAtE
  · rw [hRight]
    exact hBirthKeeps (nativeE ring s.native e)
      (ring.rightNeighbor e) i hAtE

/-- The global I factor survives every literal E plus any FIRE
branch, for any number of old leaders. Unlike C_native, this
requires no unproved 0*1* signal suffix preservation. -/
theorem grantDrainSettledEdgePhysicalPreservesI
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native) :
    I ring (grantDrainStep ring fresh update s e).native := by
  have hOld : GrantDrainEntranceILocal ring s.native :=
    (grantDrainEntranceIffILocal ring s.native).mp hC.1
  have hE : GrantDrainEntranceILocal ring
      (nativeE ring s.native e) :=
    grantDrainEntranceILocalNativeEAll
      ring (by omega : 3 ≤ n) s.native e hOld
  have hNext := grantDrainEntranceILocalPhysicalNextFromE
    ring fresh update s e hE
  exact (grantDrainEntranceIffILocal ring
    (grantDrainStep ring fresh update s e).native).mpr hNext

/-- E2: an actual no-FIRE responder-leader death has the exact
consumed-killer, zero-signal and retained/dummy-bullet fields.
The complete I factor follows from C_native, but the extra
SS suffix on the merged sector is NOT asserted. -/
theorem grantDrainSettledMergeDeathPhysicalKernel
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false)
    (hNoFire : grantDrainSelect ring s e = .none) :
    I ring (grantDrainStep ring fresh update s e).native ∧
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).l = false ∧
    ((grantDrainStep ring fresh update s e).native e).b =
      (0 : Fin 3) ∧
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).sg = false ∧
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).b =
      (if (s.native (ring.rightNeighbor e)).sg then
        (1 : Fin 3)
      else (s.native (ring.rightNeighbor e)).b) := by
  have hPhysical :
      (grantDrainStep ring fresh update s e).native =
        nativeE ring s.native e := by
    change grantDrainNativeNext ring s e =
      nativeE ring s.native e
    simp [grantDrainNativeNext, hNoFire]
  have hDestination := grantDrainEntranceNativeELeaderBulletAfter
    ring (by omega : 2 ≤ n) s.native e hyLeader
  refine ⟨grantDrainSettledEdgePhysicalPreservesI
      ring hn fresh update s e hC, ?_, ?_, ?_, ?_⟩
  · rw [hPhysical]
    exact hDeath
  · rw [hPhysical]
    exact grantDrainEntranceNativeESourceBulletZero
      ring s.native e
  · rw [hPhysical]
    exact hDestination.2
  · rw [hPhysical]
    exact hDestination.1

/-- E3's unconditional, physically assembled portion:
both I and NoBadLive persist, including leader death and FIRE.
This leaves the SS suffix part of C_native unproved. -/
theorem grantDrainSettledEdgePhysicalPreservesINoBad
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) :
    I ring (grantDrainStep ring fresh update s e).native ∧
    GrantDrainEntranceNoBadLive ring
      (grantDrainStep ring fresh update s e) := by
  refine ⟨grantDrainSettledEdgePhysicalPreservesI
    ring hn fresh update s e hC, ?_⟩
  exact grantDrainEntrancePhysicalNoBadNext
    ring hn fresh update s e hC.1.1 hNoBad

/-- Two-leader n=5 control. Enable FIRE at site 4 on e3
while retaining the D6 death-witness native word:
leaders 0,3 and one protected LIVE at site 2. -/
private def grantDrainSettledEdgeFiveFireChoice
    (enableFire : Bool) : GrantDrainState 5 Unit :=
  { native := grantDrainD6DeathWitnessNative false
    request := fun i => enableFire && (i.val == 4)
    grant := fun i => i.val == 4
    scratch := ()
    history := [] }

/-- E1 control with and without FIRE. The e3 service updates
the signal at leader 3 from follower 4, and optional post-E
FIRE births at 4. Both complete native outputs satisfy C_native.
This is a CLOSED n=5 example, not the general theorem. -/
theorem grantDrainSettledEdgeFiveFireControl
    (enableFire : Bool) :
    C_native grantDrainD6DeathWitnessRing
      (grantDrainSettledEdgeFiveFireChoice enableFire).native ∧
    PPlus grantDrainD6DeathWitnessRing
      (grantDrainSettledEdgeFiveFireChoice enableFire).native ∧
    GrantDrainEntranceNoBadLive grantDrainD6DeathWitnessRing
      (grantDrainSettledEdgeFiveFireChoice enableFire) ∧
    (if enableFire then
      grantDrainSelect grantDrainD6DeathWitnessRing
        (grantDrainSettledEdgeFiveFireChoice enableFire)
        (3 : Fin 5) = .rightLocal
     else
      grantDrainSelect grantDrainD6DeathWitnessRing
        (grantDrainSettledEdgeFiveFireChoice enableFire)
        (3 : Fin 5) = .none) ∧
    C_native grantDrainD6DeathWitnessRing
      (grantDrainStep grantDrainD6DeathWitnessRing
        (fun _ _ => false) (fun _ _ => ())
        (grantDrainSettledEdgeFiveFireChoice enableFire)
        (3 : Fin 5)).native := by
  have hPre := grantDrainD6DeathWitnessAdmissible false
  refine ⟨hPre.2.1, hPre.1, hPre.2.2.1, ?_, ?_⟩
  · cases enableFire
    · unfold grantDrainSelect grantDrainEligible
      decide
    · unfold grantDrainSelect grantDrainEligible
      decide
  · cases enableFire
    · unfold C_native
      decide
    · unfold C_native
      decide

/-- E2 control: the LIVE at site 2 kills the old leader
at 3 on e2; the resulting singleton is settled.
The pre-state passes C_native, PPlus, and NoBadLive. -/
theorem grantDrainSettledMergeFiveDeathControl :
    C_native grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native ∧
    PPlus grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native ∧
    GrantDrainEntranceNoBadLive grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false) ∧
    grantDrainSelect grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false)
      (2 : Fin 5) = .none ∧
    ((grantDrainD6DeathWitnessAfter false).native
      (3 : Fin 5)).l = false ∧
    C_native grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessAfter false).native := by
  have hPre := grantDrainD6DeathWitnessAdmissible false
  refine ⟨hPre.2.1, hPre.1, hPre.2.2.1,
    hPre.2.2.2.2.2,
    (grantDrainD6DeathTightMergeWitness).2.1, ?_⟩
  unfold C_native
  decide

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainSettledEdgeFollowerNativeLeadersFixed
#print axioms L3.GrantDrainEntrance.grantDrainSettledEdgeFollowerPhysicalKeepsOldLeaders
#print axioms L3.GrantDrainEntrance.grantDrainSettledEdgePhysicalPreservesI
#print axioms L3.GrantDrainEntrance.grantDrainSettledMergeDeathPhysicalKernel
#print axioms L3.GrantDrainEntrance.grantDrainSettledEdgePhysicalPreservesINoBad
#print axioms L3.GrantDrainEntrance.grantDrainSettledEdgeFiveFireControl
#print axioms L3.GrantDrainEntrance.grantDrainSettledMergeFiveDeathControl

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
D6-PAIR-SCAN.
F3 is the OLD-pair guard for a ready responder which survives its
DUMMY emission. The no-kill test is exact: a ready responder has
already unshielded itself, so an emitted or resident source LIVE
kills it even when the OLD responder had shield=true.

The all-edge D6 table is not asserted here. In particular the
merged five-site leader-death/surviving-DUMMY witness is not a
uniform all-n leader-death scan lemma. See the final concrete
table row below.
-/

/-- All three possible values of a native bullet register.
This is an elementary finite elimination, not a large decide. -/
private theorem grantDrainD6FireBulletCases (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨
      b = (2 : Fin 3) := by
  have hlt := b.isLt
  have hv : b.val = 0 ∨ b.val = 1 ∨ b.val = 2 := by omega
  rcases hv with hz | ho | ht
  · exact Or.inl (Fin.ext hz)
  · exact Or.inr (Or.inl (Fin.ext ho))
  · exact Or.inr (Or.inr (Fin.ext ht))

/-- Exact *OLD-pair* characterization of the surviving ready
responder. It is not an assumed post-step leaf. The ready
responder first emits a DUMMY and loses its shield, so any
effective source LIVE kills it. -/
private theorem grantDrainD6FireReadyResponderNoKillIff
    (x y : CertNative)
    (hYL : y.l = true) (hReady : y.sg = true) :
    (certLiteralEPair x y).2.l = true ↔
      (x.l && x.sg) = false ∧ x.b ≠ (2 : Fin 3) := by
  cases hEmit : (x.l && x.sg) with
  | true =>
      simp [certLiteralEPair, hEmit, hYL, hReady,
        certFinThree]
  | false =>
      rcases grantDrainD6FireBulletCases x.b with hz | ho | ht
      · simp [certLiteralEPair, hEmit, hYL, hReady,
          hz, certFinThree]
      · simp [certLiteralEPair, hEmit, hYL, hReady,
          ho, certFinThree]
      · simp [certLiteralEPair, hEmit, hYL, hReady,
          ht, certFinThree]

/-- A follower's existing signal survives a literal E source
service; in particular this handles g=e when a=n-1. -/
private theorem grantDrainD6FireFollowerSourceKeepsSignal
    (x y : CertNative)
    (hXL : x.l = false) (hXS : x.sg = true) :
    (certLiteralEPair x y).1.sg = true := by
  simp [certLiteralEPair, hXL, hXS]

/-- Left by one and right by n-1 designate the same site. -/
private theorem grantDrainD6FireLeftOneRightLast
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (p : Fin n) :
    PPL.shiftLeft ring p 1 =
      PPL.shiftRight ring p (n - 1) := by
  apply Fin.ext
  change (p.val + n - 1 % n) % n =
    (p.val + (n - 1)) % n
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hSub : p.val + n - 1 = p.val + (n - 1) := by omega
  rw [hSub]

/-- The source of the incoming edge into p cannot be any
strictly positive scanned position between p and its warm
follower g. It *can* be g itself in the single-root case
a=n-1, which is why F3 handles the signal at g separately. -/
private theorem grantDrainD6FireResponderSourceOutsidePositive
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (e p g : Fin n) (a : Nat)
    (ha : a < n)
    (hAt : g = PPL.shiftRight ring p a)
    (hTo : ring.rightNeighbor e = p) :
    ∀ j : Nat, 1 ≤ j → j < a →
      PPL.shiftLeft ring g j ≠ e := by
  have hPre : PPL.shiftLeft ring p 1 = e := by
    rw [← hTo]
    exact grantDrainWarmRightNeighborLeftOne ring hn e
  have hE : e = PPL.shiftRight ring p (n - 1) :=
    hPre.symm.trans
      (grantDrainD6FireLeftOneRightLast ring hn p)
  intro j hj hja hEq
  have hArc :
      PPL.shiftLeft ring g j =
        PPL.shiftRight ring p (a - j) := by
    rw [hAt]
    exact grantDrainMarksArcShiftLeftRight
      ring p a j (by omega) ha
  rw [hArc, hE] at hEq
  exact (grantDrainWeakDeathShiftRightNe ring p
    (a - j) (n - 1)
    (by omega : a - j < n)
    (by omega : n - 1 < n)
    (by omega : a - j ≠ n - 1)) hEq

/-- F3. A ready preceding leader is the actual responder of
the selected physical service, emits a DUMMY, and survives.
The no-kill assumptions read OLD fields only; the preceding
iff theorem shows they describe *all* surviving ready-responder
E rows. The new first bullet is at the unchanged nearest
leader, its distance is a, and W drops from a+1 to a.

The genuine outgoing scan may wrap when a=n-1; the source
is then g, but the follower source signal remains one.
No post-state scan equality is hypothesized. -/
theorem grantDrainD6FireReadyResponderSurvivingRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hSector : sectorLength ring s.native p D)
    (hAt : g = PPL.shiftRight ring p a)
    (ha : 1 ≤ a) (haInside : a < D.val)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = a)
    (hReady : (s.native p).sg = true)
    (hTo : ring.rightNeighbor e = p)
    (hSourceNotEmitting :
      ((s.native e).l && (s.native e).sg) = false)
    (hSourceNotLive : (s.native e).b ≠ (2 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainLeftBulletDistance ring s.native g a = none ∧
    ((grantDrainStep ring fresh update s e).native p).l = true ∧
    ((grantDrainStep ring fresh update s e).native p).b =
      (1 : Fin 3) ∧
    grantDrainLeftBulletDistance ring
      (grantDrainStep ring fresh update s e).native g a =
        some a ∧
    grantDrainWarmRank ring
      (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have haN : a < n := by
    have hBound := D.isLt
    omega
  have hFront :
      PPL.shiftLeft ring g a = p :=
    grantDrainD6FireFrontCoordinate ring p g a haN hAt
  have hOldReady :=
    grantDrainD6FireReadyPrefix ring s.native p g D a
      hC hSector ha haInside hAt hReady
  have hOldNoBullet :
      grantDrainLeftBulletDistance ring s.native g a = none := by
    apply (grantDrainWarmBulletNoneCharacterization
      ring s.native g a).mpr
    intro j _ hj
    exact congrArg Fin.val (hOldReady.2 j hj)
  have hNative := grantDrainWarmPhysicalNoBirthNative
    ring fresh update s e hNone
  have hNoKill :
      (certLiteralEPair (s.native e) (s.native p)).2.l =
        true :=
    (grantDrainD6FireReadyResponderNoKillIff
      (s.native e) (s.native p)
      hSector.2.1 hReady).mpr
        ⟨hSourceNotEmitting, hSourceNotLive⟩
  have hNoKillEdge :
      (certLiteralEPair
        (s.native e) (s.native (ring.rightNeighbor e))).2.l =
          true := by
    rw [hTo]
    exact hNoKill
  have hDummy :=
    grantDrainD6MergeReadyResponderDummyPair
      (s.native e) (s.native p)
      hSector.2.1 hReady
  have hDummyEdge :
      (certLiteralEPair
        (s.native e) (s.native (ring.rightNeighbor e))).2.b =
          (1 : Fin 3) := by
    rw [hTo]
    exact hDummy.2.1
  have hNe := grantDrainWarmPhysicalPairDistinct ring hn e
  have hNewPLeader :
      ((grantDrainStep ring fresh update s e).native p).l =
        true := by
    rw [← hTo, hNative]
    simpa [nativeE, hNe] using hNoKillEdge
  have hNewPBullet :
      ((grantDrainStep ring fresh update s e).native p).b =
        (1 : Fin 3) := by
    rw [← hTo, hNative]
    simpa [nativeE, hNe] using hDummyEdge
  have hOutside :=
    grantDrainD6FireResponderSourceOutsidePositive
      ring hn e p g a haN hAt hTo
  have hPositiveFrame : ∀ j : Nat, 1 ≤ j → j < a →
      (grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g j) =
      s.native (PPL.shiftLeft ring g j) := by
    intro j hj hja
    have hNotP : PPL.shiftLeft ring g j ≠ p := by
      rw [← hFront]
      intro hEq
      have hIndex := grantDrainD6MoveShiftInjective
        ring g j a (by omega) haN hEq
      omega
    exact grantDrainSettledNativeStepOutsidePair
      ring fresh update s e (PPL.shiftLeft ring g j)
      (hOutside j hj hja)
      (by rw [hTo]; exact hNotP)
  have hOldFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g a (by omega) haN).mp hDistance
  have hNewDistance :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g = a := by
    apply (grantDrainWarmLeaderFirstCharacterization
      ring (grantDrainStep ring fresh update s e).native
      g a (by omega) haN).mpr
    constructor
    · rw [hFront]
      exact hNewPLeader
    · intro j hj hja
      rw [hPositiveFrame j hj hja]
      exact hOldFirst.2 j hj hja
  have hNewBullet :
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native g a =
          some a := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring (grantDrainStep ring fresh update s e).native
      g a a).mpr
    refine ⟨ha, Nat.le_refl _, ?_, ?_⟩
    · rw [hFront, hNewPBullet]
      decide
    · intro j hj hja
      rw [hPositiveFrame j hj hja, hOldReady.2 j (by omega)]
      rfl
  have hOldGNotLeader : (s.native g).l = false := by
    cases hl : (s.native g).l with
    | false =>
        rfl
    | true =>
        simp [grantDrainWarmAt, hl] at hWarm
  have hOldGSignal : (s.native g).sg = true := by
    cases hs : (s.native g).sg with
    | true =>
        rfl
    | false =>
        simp [grantDrainWarmAt, hs] at hWarm
  have hNotFront : g ≠ p := by
    intro hEq
    have hRoot := hSector.2.1
    rw [← hEq, hOldGNotLeader] at hRoot
    cases hRoot
  have hNewGSignal :
      ((grantDrainStep ring fresh update s e).native g).sg =
        true := by
    by_cases hg : g = e
    · have hOldSourceFollower : (s.native e).l = false := by
        rw [← hg]
        exact hOldGNotLeader
      have hOldSourceSignal : (s.native e).sg = true := by
        rw [← hg]
        exact hOldGSignal
      have hSourceSignal :=
        grantDrainD6FireFollowerSourceKeepsSignal
          (s.native e) (s.native (ring.rightNeighbor e))
          hOldSourceFollower hOldSourceSignal
      rw [hg, hNative]
      simpa [nativeE] using hSourceSignal
    · have hFrame :=
        grantDrainSettledNativeStepOutsidePair
          ring fresh update s e g hg
          (by rw [hTo]; exact hNotFront)
      rw [hFrame]
      exact hOldGSignal
  have hNewSignalPrefix :
      ∀ j : Nat, j < a →
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring g j)).sg = true := by
    intro j hja
    by_cases hj : j = 0
    · subst j
      simpa only [grantDrainWarmShiftLeftZero] using hNewGSignal
    · have hjPos : 1 ≤ j := by omega
      rw [hPositiveFrame j hjPos hja]
      exact hOldReady.1 j hja
  have hNewTerminal :
      grantDrainTerminalRun ring
        (grantDrainStep ring fresh update s e).native g a =
          a - 1 := by
    apply (grantDrainWarmTerminalCharacterization
      ring (grantDrainStep ring fresh update s e).native
      g a (a - 1) (by omega) hNewGSignal).mpr
    refine ⟨by omega, ?_, Or.inl (by omega)⟩
    intro j hj
    exact hNewSignalPrefix j (by omega)
  have hOldRank :
      grantDrainWarmRank ring s.native g = 1 + a := by
    simp [grantDrainWarmRank, hDistance, hOldNoBullet,
      hFront, hReady]
  have hNewRank :
      grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g = a := by
    simp [grantDrainWarmRank, hNewDistance,
      hNewBullet, hNewTerminal] <;> omega
  refine ⟨hOldNoBullet, hNewPLeader, hNewPBullet,
    hNewBullet, ?_⟩
  rw [hNewRank, hOldRank]
  omega

/-! T is not yet a theorem of the merged interfaces.
The missing arbitrary-n row is the deletion of an unready
front while a pre-existing DUMMY survives at that front.
The source already gives its true n=5 occurrence
(grantDrainD6DeathSurvivingBulletWitness); this regression
records the rank-neutral and nonexceptional branch without
pretending that its all-n scan transport has been proved. -/

/-- Concrete T-table row: a shieldless quiet old front dies,
its DUMMY remains, the nearest leader jumps from distance 1 to
4, yet the continuing warm rank stays 1 and the exceptional
guard is false. This is a true physical step, not an assumed
abstract before/after map. -/
theorem grantDrainD6TableLeaderDeathSurvivingBulletFive :
    C_native grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState true).native ∧
    grantDrainWarmAt
      (grantDrainD6DeathWitnessState true)
      (4 : Fin 5) = true ∧
    grantDrainSelect grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState true)
      (2 : Fin 5) = .none ∧
    grantDrainExceptionalDeath grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState true)
      (2 : Fin 5) (4 : Fin 5) = false ∧
    grantDrainWarmRank grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessAfter true).native
      (4 : Fin 5) =
    grantDrainWarmRank grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState true).native
      (4 : Fin 5) := by
  have hAdmissible := grantDrainD6DeathWitnessAdmissible true
  refine ⟨hAdmissible.2.1, hAdmissible.2.2.2.1,
    hAdmissible.2.2.2.2.2, ?_, ?_⟩
  · unfold grantDrainExceptionalDeath
      grantDrainD6DeathWitnessState
      grantDrainD6DeathWitnessNative
      grantDrainD6DeathWitnessRing
    decide
  · unfold grantDrainD6DeathWitnessAfter
      grantDrainD6DeathWitnessState
      grantDrainD6DeathWitnessNative
      grantDrainD6DeathWitnessRing
      grantDrainWarmRank grantDrainLeftLeaderDistance
      grantDrainLeftBulletDistance grantDrainTerminalRun
    decide

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6FireReadyResponderSurvivingRank
#print axioms L3.GrantDrainEntrance.grantDrainD6TableLeaderDeathSurvivingBulletFive
