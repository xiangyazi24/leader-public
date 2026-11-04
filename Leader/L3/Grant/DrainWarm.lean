import Leader.L3.Grant.DrainDummy

/-!
# Grant drain: D.6 warm-rank case table, the single merge jump, and C_native closure

Downstream of `Leader.L3.Grant.DrainDummy`, opened on 2026-10-31 when that file reached
983 KB, close to the 1 MB limit of the GitHub contents API. Declarations stay in the
namespace `L3.GrantDrainEntrance`. Private declarations of `GrantDrainDummy` are not
visible here.
-/

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
D6-PAIR-SCAN: unconditional physical endpoint and exceptional-source lemmas.

The full general theorem grantDrainD6MergeSpentStep is NOT
established by this block. The outstanding all-n obligations
are (1) mapping a killed old front to the actual NEW nearest
leader after E and optional canonical birth, and (2) transporting
a left-bullet/front witness across every interacting-pair
case, including a grant-host move. No unproved leaf is assumed.
-/

/-- Protected old source leaders keep a shield in the literal E pair. -/
theorem grantDrainD6MergeLeaderSourceProtection
    (x y : CertNative)
    (hLeader : x.l = true)
    (hOld : x.sh = true ∨ x.sg = true) :
    (certLiteralEPair x y).1.sh = true := by
  rcases hOld with hShield | hSignal
  · exact grantDrainD6MergeSourceShieldMonotone x y hShield
  · simp [certLiteralEPair, hLeader, hSignal, certFinThree]

/-- A protected old responder leader retains a shield or
leaves the ready-responder DUMMY at its physical site. -/
theorem grantDrainD6MergeLeaderResponderProtection
    (x y : CertNative)
    (hLeader : y.l = true)
    (hOld : y.sh = true ∨ y.sg = true) :
    (certLiteralEPair x y).2.sh = true ∨
      (certLiteralEPair x y).2.b ≠ (0 : Fin 3) := by
  rcases hOld with hShield | hSignal
  · cases hReady : y.sg with
    | false =>
        left
        simp [certLiteralEPair, hLeader, hShield,
          hReady, certFinThree]
    | true =>
        right
        have hDummy :=
          (grantDrainD6MergeReadyResponderDummyPair
            x y hLeader hReady).2.1
        rw [hDummy]
        decide
  · right
    have hDummy :=
      (grantDrainD6MergeReadyResponderDummyPair
        x y hLeader hSignal).2.1
    rw [hDummy]
    decide

/-- An absent OLD ghost host never becomes a warm next ghost. -/
theorem grantDrainD6MergeAbsentHostCold
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hNone : label.host = none) :
    (grantDrainWarmLabelStep ring fresh update s e
      label).warm = false := by
  simp [grantDrainWarmLabelStep, hNone]

/-- A failed step with an available reserve
must satisfy the actual old exceptional-death guard. -/
theorem grantDrainD6MergeUnspentFailureExceptional
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hAvailable : label.exceptionalLeft = true)
    (hFailure :
      ¬ GrantDrainWarmMergeSpent ring
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)) :
    ∃ g : Fin n,
      label.host = some g ∧
      grantDrainExceptionalDeath ring s e g = true := by
  cases hHost : label.host with
  | none =>
      have hNoExceptional :
          ∀ g : Fin n, label.host = some g →
            grantDrainExceptionalDeath ring s e g = false := by
        intro g hEq
        rw [hHost] at hEq
        cases hEq
      have hGood :=
        grantDrainD6MergeUnspentWithoutExceptional
          ring fresh update s e label hAvailable hNoExceptional
      exact False.elim (hFailure hGood)
  | some p =>
      cases hExceptional :
          grantDrainExceptionalDeath ring s e p with
      | true =>
          exact ⟨p, rfl, hExceptional⟩
      | false =>
          have hNoExceptional :
              ∀ g : Fin n, label.host = some g →
                grantDrainExceptionalDeath ring s e g = false := by
            intro g hEq
            have hSame : g = p :=
              Option.some.inj (hEq.symm.trans hHost)
            subst g
            exact hExceptional
          have hGood :=
            grantDrainD6MergeUnspentWithoutExceptional
              ring fresh update s e label hAvailable hNoExceptional
          exact False.elim (hFailure hGood)

/-- A spent-reserve failure must meet
the OLD backward leader/bullet scan in the physical pair. -/
theorem grantDrainD6MergeSpentFailureMeetsScan
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (g : Fin n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (hFailure :
      ¬ GrantDrainWarmMergeSpent ring
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)) :
    ∃ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g ∧
        (PPL.shiftLeft ring g k = e ∨
          PPL.shiftLeft ring g k = ring.rightNeighbor e) := by
  classical
  by_cases hMeets :
      ∃ k : Nat,
        k ≤ grantDrainLeftLeaderDistance ring s.native g ∧
          (PPL.shiftLeft ring g k = e ∨
            PPL.shiftLeft ring g k = ring.rightNeighbor e)
  · exact hMeets
  · have hOutside :
        ∀ k : Nat,
          k ≤ grantDrainLeftLeaderDistance ring s.native g →
            PPL.shiftLeft ring g k ≠ e ∧
            PPL.shiftLeft ring g k ≠ ring.rightNeighbor e := by
      intro k hk
      constructor
      · intro he
        apply hMeets
        exact ⟨k, hk, Or.inl he⟩
      · intro hy
        apply hMeets
        exact ⟨k, hk, Or.inr hy⟩
    have hGood :=
      grantDrainD6MergeSpentOutsidePair
        ring fresh update s label e g hInv
        hWarm hHost hSpent hOutside
    exact False.elim (hFailure hGood)

/-- Dichotomy; dependent cases rewrite the goal. -/
theorem grantDrainD6MergeFailureDichotomy
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hFailure :
      ¬ GrantDrainWarmMergeSpent ring
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)) :
    (∃ g : Fin n,
      label.host = some g ∧
      label.exceptionalLeft = true ∧
      grantDrainExceptionalDeath ring s e g = true) ∨
    (∃ g : Fin n,
      label.host = some g ∧
      label.exceptionalLeft = false ∧
      ∃ k : Nat,
        k ≤ grantDrainLeftLeaderDistance ring s.native g ∧
          (PPL.shiftLeft ring g k = e ∨
            PPL.shiftLeft ring g k = ring.rightNeighbor e)) := by
  cases hReserve : label.exceptionalLeft with
  | true =>
      obtain ⟨g, hHost, hExceptional⟩ :=
        grantDrainD6MergeUnspentFailureExceptional
          ring fresh update s e label hReserve hFailure
      exact Or.inl ⟨g, hHost, rfl, hExceptional⟩
  | false =>
      have hOldWarm : label.warm = true := by
        cases hWarm : label.warm with
        | true =>
            rfl
        | false =>
            have hNextCold :=
              grantDrainD6MergeColdLabelRemainsCold
                ring fresh update s e label hWarm
            have hGood :
                GrantDrainWarmMergeSpent ring
                  (grantDrainStep ring fresh update s e)
                  (grantDrainWarmLabelStep ring fresh update s e
                    label) := by
              intro g hg _ _
              rw [hNextCold] at hg
              cases hg
            exact False.elim (hFailure hGood)
      cases hHost : label.host with
      | none =>
          have hNextCold :=
            grantDrainD6MergeAbsentHostCold
              ring fresh update s e label hHost
          have hGood :
              GrantDrainWarmMergeSpent ring
                (grantDrainStep ring fresh update s e)
                (grantDrainWarmLabelStep ring fresh update s e
                  label) := by
            intro g hg _ _
            rw [hNextCold] at hg
            cases hg
          exact False.elim (hFailure hGood)
      | some g =>
          have hMeets :=
            grantDrainD6MergeSpentFailureMeetsScan
              ring fresh update s e label g
              hInv hOldWarm hHost hReserve hFailure
          exact Or.inr ⟨g, rfl, rfl, hMeets⟩

/-- An exceptional OLD front death can only occur at the responder. -/
theorem grantDrainD6MergeExceptionalAtResponder
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e g : Fin n)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    grantDrainD6MergeFront ring s.native g =
      ring.rightNeighbor e := by
  obtain ⟨hLeader, _, _, _, hDeath⟩ :=
    grantDrainD6MergeExceptionalFields
      ring s e g hExceptional
  by_cases hAt :
      grantDrainD6MergeFront ring s.native g =
        ring.rightNeighbor e
  · exact hAt
  · have hUnchanged :=
      grantDrainDummyNativeELeaderAwayResponder
        ring s.native e
        (grantDrainD6MergeFront ring s.native g) hAt
    rw [hUnchanged, hLeader] at hDeath
    cases hDeath

/-- An OLD warm exceptional hit consumes the actual ghost reserve. -/
theorem grantDrainD6MergeExceptionalConsumesReserve
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainWarmLabel n)
    (hHost : label.host = some g)
    (hWarm : label.warm = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    (grantDrainWarmLabelStep ring fresh update s e
      label).exceptionalLeft = false := by
  simp [grantDrainWarmLabelStep, hHost, hWarm, hExceptional]

/-- A protected OLD source leader stays protected after E + FIRE. -/
theorem grantDrainD6MergeProtectedSourcePhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader : (s.native e).l = true)
    (hProtected :
      (s.native e).sh = true ∨ (s.native e).sg = true) :
    ((grantDrainStep ring fresh update s e).native e).l = true ∧
    ((grantDrainStep ring fresh update s e).native e).sh = true := by
  have hPairShield :=
    grantDrainD6MergeLeaderSourceProtection
      (s.native e) (s.native (ring.rightNeighbor e))
      hLeader hProtected
  have hELeader :
      (nativeE ring s.native e e).l = true := by
    have hSource :=
      grantDrainEntranceLiteralESourceLeaderFixed
        (s.native e) (s.native (ring.rightNeighbor e))
    simpa [nativeE, hLeader] using hSource
  have hEShield :
      (nativeE ring s.native e e).sh = true := by
    simpa [nativeE] using hPairShield
  have hDistinct : e ≠ ring.rightNeighbor e :=
    Ne.symm (grantDrainMarksNeighborDistinct
      (by omega : 3 ≤ n) ring e)
  change
    (grantDrainNativeNext ring s e e).l = true ∧
    (grantDrainNativeNext ring s e e).sh = true
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using
        (And.intro hELeader hEShield)
  | leftLocal =>
      simp [grantDrainNativeNext, hf,
        canonicalBirth, firedNative]
  | rightLocal =>
      simpa [grantDrainNativeNext, hf, canonicalBirth,
        hDistinct] using (And.intro hELeader hEShield)
  | cross =>
      simp [grantDrainNativeNext, hf,
        canonicalBirth, firedNative]

/-- A protected OLD responder remains shielded or bullet-hosting
after E + FIRE, even if a ready-responder death occurs. -/
theorem grantDrainD6MergeProtectedResponderPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hProtected :
      (s.native (ring.rightNeighbor e)).sh = true ∨
      (s.native (ring.rightNeighbor e)).sg = true) :
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).sh = true ∨
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).b ≠ (0 : Fin 3) := by
  have hPair :=
    grantDrainD6MergeLeaderResponderProtection
      (s.native e) (s.native (ring.rightNeighbor e))
      hLeader hProtected
  have hDistinct : e ≠ ring.rightNeighbor e :=
    Ne.symm (grantDrainMarksNeighborDistinct
      (by omega : 3 ≤ n) ring e)
  have hDistinctRev : ring.rightNeighbor e ≠ e :=
    Ne.symm hDistinct
  have hE :
      (nativeE ring s.native e (ring.rightNeighbor e)).sh =
          true ∨
      (nativeE ring s.native e (ring.rightNeighbor e)).b ≠
          (0 : Fin 3) := by
    simpa [nativeE, hDistinctRev] using hPair
  change
    (grantDrainNativeNext ring s e (ring.rightNeighbor e)).sh =
        true ∨
    (grantDrainNativeNext ring s e (ring.rightNeighbor e)).b ≠
        (0 : Fin 3)
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hE
  | leftLocal =>
      simpa [grantDrainNativeNext, hf, canonicalBirth,
        hDistinctRev] using hE
  | rightLocal =>
      left
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]
  | cross =>
      simpa [grantDrainNativeNext, hf, canonicalBirth,
        hDistinctRev] using hE

/-- Exceptional-front death: protected killer or peaceful OLD LIVE.
This does NOT identify the new nearest leader after a full step. -/
theorem grantDrainD6MergeExceptionalSourceAlternative
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n)
    (hPB : PPlus ring s.native)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    (((grantDrainStep ring fresh update s e).native e).l =
        true ∧
      ((grantDrainStep ring fresh update s e).native e).sh =
        true ∧
      ((grantDrainStep ring fresh update s e).native e).sg =
        false) ∨
    PPL.PeacefulCore ring
      (fun i : Fin n => (s.native i).l)
      (fun i : Fin n => (s.native i).sh)
      (fun i : Fin n => (s.native i).sg) e := by
  obtain ⟨hLeader, hUnshielded, hQuiet, _, hDeath⟩ :=
    grantDrainD6MergeExceptionalFields
      ring s e g hExceptional
  have hAt :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  rw [hAt] at hLeader hUnshielded hQuiet hDeath
  rcases grantDrainWeakDeathEffectiveSourceProtectionOrLive
      ring hn fresh update s e hLeader hUnshielded
      hQuiet hDeath with hReady | hLive
  · exact Or.inl hReady
  · exact Or.inr (hPB.2 e hLive)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6MergeLeaderSourceProtection
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeLeaderResponderProtection
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeAbsentHostCold
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeUnspentFailureExceptional
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeSpentFailureMeetsScan
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeFailureDichotomy
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeExceptionalAtResponder
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeExceptionalConsumesReserve
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeProtectedSourcePhysical
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeProtectedResponderPhysical
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeExceptionalSourceAlternative

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- The positive consecutive scan range.  The corresponding
lemma in GrantDrainDummy is private, so this copy is public. -/
theorem grantDrainD6DeathPositiveRange (length : Nat) :
    (List.range length).map (fun k : Nat => k + 1) =
      List.range' 1 length := by
  have hFun : (fun k : Nat => k + 1) =
      (fun k : Nat => 1 + k) := by
    funext k
    omega
  rw [hFun]
  exact (List.range'_eq_map_range
    (s := 1) (n := length)).symm

/-- The first-hit inverse, restated here because the corresponding
GrantDrainDummy declaration is private. -/
theorem grantDrainD6DeathFindConverse
    (f : Nat → Bool) :
    ∀ length start d,
      (List.range' start length).find? f = some d →
      start ≤ d ∧ d < start + length ∧ f d = true ∧
        (∀ k : Nat, start ≤ k → k < d → f k = false) := by
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

/-- A leader-free prefix gives a lower bound on the literal nearest
leader scan, including its getD n fallback. -/
theorem grantDrainD6DeathLeaderPrefixLowerBound
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
    rw [grantDrainD6DeathPositiveRange]
  rw [hScan]
  cases hf : (List.range' 1 n).find?
      (fun j => (N (PPL.shiftLeft ring g j)).l) with
  | none =>
      simpa [hf] using ha
  | some q =>
      obtain ⟨hqPos, _, hHit, _⟩ :=
        grantDrainD6DeathFindConverse
          (fun j => (N (PPL.shiftLeft ring g j)).l)
          n 1 q hf
      have hLower : a ≤ q := by
        by_cases hEarlier : q < a
        · have hFalse := hNoLeader q hqPos hEarlier
          rw [hFalse] at hHit
          cases hHit
        · omega
      simpa [hf] using hLower

/-- The forward right offset n-1 is the left predecessor.
The corresponding GrantDrainDummy declaration is private. -/
theorem grantDrainD6DeathLeftOneRightLast
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (p : Fin n) :
    PPL.shiftLeft ring p 1 =
      PPL.shiftRight ring p (n - 1) := by
  apply Fin.ext
  change (p.val + n - 1 % n) % n =
    (p.val + (n - 1)) % n
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hSub : p.val + n - 1 = p.val + (n - 1) := by
    omega
  rw [hSub]

/-- The source of a service into the old front is outside the
positive part of the old follower-to-front scan, endpoint included.
This statement does not assert that the source differs from g. -/
theorem grantDrainD6DeathSourceOutsidePositive
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (e p g : Fin n) (a : Nat)
    (ha : a < n)
    (hAt : g = PPL.shiftRight ring p a)
    (hTo : ring.rightNeighbor e = p) :
    ∀ j : Nat, 1 ≤ j → j ≤ a →
      PPL.shiftLeft ring g j ≠ e := by
  have hPre : PPL.shiftLeft ring p 1 = e := by
    rw [← hTo]
    exact grantDrainWarmRightNeighborLeftOne ring hn e
  have hE : e = PPL.shiftRight ring p (n - 1) :=
    hPre.symm.trans (grantDrainD6DeathLeftOneRightLast ring hn p)
  intro j hj hja hEq
  have hArc :
      PPL.shiftLeft ring g j =
        PPL.shiftRight ring p (a - j) := by
    rw [hAt]
    exact grantDrainMarksArcShiftLeftRight
      ring p a j hja ha
  rw [hArc, hE] at hEq
  exact (grantDrainWeakDeathShiftRightNe ring p
    (a - j) (n - 1)
    (by omega : a - j < n)
    (by omega : n - 1 < n)
    (by omega : a - j ≠ n - 1)) hEq

/-- A bullet-free follower cannot kill a quiet leader by native E.
This also excludes the wraparound case in which the death source
would otherwise coincide with the warm grant. -/
theorem grantDrainD6DeathEmptyFollowerCannotKill
    (x y : CertNative)
    (hXL : x.l = false)
    (hXB : x.b = (0 : Fin 3))
    (hYL : y.l = true)
    (hYSh : y.sh = false)
    (hYS : y.sg = false) :
    (certLiteralEPair x y).2.l = true := by
  simp [certLiteralEPair, hXL, hXB, hYL, hYSh, hYS,
    certFinThree]

/-- Scan transport across a deleted front when the first bullet
survives.  The new first-leader distance may be larger or equal to n;
neither the first bullet nor the terminal signal run changes.
These are field hypotheses, not a claimed physical-step theorem. -/
theorem grantDrainD6DeathBulletRankPrefix
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (d k : Nat)
    (hd : 1 ≤ d)
    (hOldDistance : grantDrainLeftLeaderDistance ring N g = d)
    (hNewDistance :
      d ≤ grantDrainLeftLeaderDistance ring M g)
    (hOldBullet :
      grantDrainLeftBulletDistance ring N g d = some k)
    (hOldWarm : (N g).sg = true)
    (hSignalPrefix : ∀ j : Nat, j < d →
      (M (PPL.shiftLeft ring g j)).sg =
        (N (PPL.shiftLeft ring g j)).sg)
    (hBulletPrefix : ∀ j : Nat, 1 ≤ j → j ≤ d →
      (M (PPL.shiftLeft ring g j)).b.val =
        (N (PPL.shiftLeft ring g j)).b.val)
    (hNewFrontQuiet :
      (M (PPL.shiftLeft ring g d)).sg = false) :
    grantDrainLeftBulletDistance ring M g
      (grantDrainLeftLeaderDistance ring M g) = some k ∧
    grantDrainTerminalRun ring M g
      (grantDrainLeftLeaderDistance ring M g) =
        grantDrainTerminalRun ring N g d ∧
    grantDrainWarmRank ring M g = grantDrainWarmRank ring N g := by
  obtain ⟨hkPos, hkBound, hkHit, hkBefore⟩ :=
    (grantDrainWarmBulletSomeCharacterization
      ring N g d k).mp hOldBullet
  have hNewBullet :
      grantDrainLeftBulletDistance ring M g
        (grantDrainLeftLeaderDistance ring M g) = some k := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring M g (grantDrainLeftLeaderDistance ring M g) k).mpr
    refine ⟨hkPos, by omega, ?_, ?_⟩
    · rw [hBulletPrefix k hkPos hkBound]
      exact hkHit
    · intro j hj hjk
      rw [hBulletPrefix j hj (by omega)]
      exact hkBefore j hj hjk
  have hOldTerminal :=
    (grantDrainWarmTerminalCharacterization
      ring N g d (grantDrainTerminalRun ring N g d)
      hd hOldWarm).mp rfl
  have hNewWarm : (M g).sg = true := by
    have hHead := hSignalPrefix 0 (by omega)
    rw [grantDrainWarmShiftLeftZero ring g] at hHead
    exact hHead.trans hOldWarm
  have hNewTerminal :
      grantDrainTerminalRun ring M g
        (grantDrainLeftLeaderDistance ring M g) =
          grantDrainTerminalRun ring N g d := by
    apply (grantDrainWarmTerminalCharacterization
      ring M g
      (grantDrainLeftLeaderDistance ring M g)
      (grantDrainTerminalRun ring N g d)
      (by omega) hNewWarm).mpr
    refine ⟨by omega, ?_, Or.inr ?_⟩
    · intro j hj
      rw [hSignalPrefix j (by omega)]
      exact hOldTerminal.2.1 j hj
    · by_cases hEnd :
          grantDrainTerminalRun ring N g d + 1 = d
      · rw [hEnd]
        exact hNewFrontQuiet
      · have hBefore : grantDrainTerminalRun ring N g d + 1 < d :=
          by omega
        rw [hSignalPrefix _ hBefore]
        rcases hOldTerminal.2.2 with hFull | hStop
        · exact False.elim (hEnd hFull)
        · exact hStop
  refine ⟨hNewBullet, hNewTerminal, ?_⟩
  calc
    grantDrainWarmRank ring M g =
        k + 2 * (k -
          (grantDrainTerminalRun ring M g
            (grantDrainLeftLeaderDistance ring M g) + 1)) := by
      simp [grantDrainWarmRank, hNewBullet]
    _ = k + 2 * (k - (grantDrainTerminalRun ring N g d + 1)) := by
      rw [hNewTerminal]
    _ = grantDrainWarmRank ring N g := by
      simp [grantDrainWarmRank, hOldDistance, hOldBullet]

/-- D1: the complete no-FIRE native deletion of a quiet unshielded
front, retaining an old first left bullet, is rank-neutral.
The native death premise covers both a resident LIVE source and a
ready emitting source; no precomputed post-step scan is assumed.
The retained bullet can be strictly left of p or p's own DUMMY. -/
theorem grantDrainD6DeathSurvivingBulletRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (D : Fin (n + 1)) (a k : Nat)
    (hC : C_native ring s.native)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hSector : sectorLength ring s.native p D)
    (hAt : g = PPL.shiftRight ring p a)
    (ha : 1 ≤ a) (haInside : a < D.val)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = a)
    (hUnshield : (s.native p).sh = false)
    (hUnready : (s.native p).sg = false)
    (hTo : ring.rightNeighbor e = p)
    (hDeath : (nativeE ring s.native e p).l = false)
    (hOldBullet :
      grantDrainLeftBulletDistance ring s.native g a = some k)
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainWarmRank ring
      (grantDrainStep ring fresh update s e).native g =
        grantDrainWarmRank ring s.native g := by
  have haN : a < n := by
    have hD := D.isLt
    omega
  have hFront : PPL.shiftLeft ring g a = p := by
    rw [hAt]
    rw [grantDrainMarksArcShiftLeftRight
      ring p a a (Nat.le_refl _) haN]
    rw [Nat.sub_self]
    exact grantDrainWeakDeathShiftRightZero ring p
  have hGNotLeader : (s.native g).l = false := by
    cases hl : (s.native g).l with
    | false => rfl
    | true => simp [grantDrainWarmAt, hl] at hWarm
  have hGEmpty : (s.native g).b = (0 : Fin 3) := by
    by_cases hb : (s.native g).b = (0 : Fin 3)
    · exact hb
    · have hCold :=
        grantDrainWarmPhysicalBulletEndsWarm s g hb
      rw [hWarm] at hCold
      cases hCold
  have hGSignal : (s.native g).sg = true := by
    cases hs : (s.native g).sg with
    | true => rfl
    | false => simp [grantDrainWarmAt, hs] at hWarm
  have hNotGE : g ≠ e := by
    intro hGE
    have hXLeader : (s.native e).l = false := by
      rw [← hGE]
      exact hGNotLeader
    have hXEmpty : (s.native e).b = (0 : Fin 3) := by
      rw [← hGE]
      exact hGEmpty
    have hXTarget : (s.native (ring.rightNeighbor e)).l = true := by
      rw [hTo]
      exact hSector.2.1
    have hXTargetSh :
        (s.native (ring.rightNeighbor e)).sh = false := by
      rw [hTo]
      exact hUnshield
    have hXTargetSg :
        (s.native (ring.rightNeighbor e)).sg = false := by
      rw [hTo]
      exact hUnready
    have hPair := grantDrainD6DeathEmptyFollowerCannotKill
      (s.native e) (s.native (ring.rightNeighbor e))
      hXLeader hXEmpty hXTarget hXTargetSh hXTargetSg
    have hDistinct := grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
    have hAlive :
        (nativeE ring s.native e
          (ring.rightNeighbor e)).l = true := by
      simpa [nativeE, hDistinct] using hPair
    have hDead :
        (nativeE ring s.native e
          (ring.rightNeighbor e)).l = false := by
      rw [hTo]
      exact hDeath
    rw [hDead] at hAlive
    cases hAlive
  have hOldLeader :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g a ha haN).mp hDistance
  have hFrame : ∀ j : Nat, j < a →
      (grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g j) =
      s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    have hNotP : PPL.shiftLeft ring g j ≠ p := by
      intro hEq
      have hArc :
          PPL.shiftLeft ring g j =
            PPL.shiftRight ring p (a - j) := by
        rw [hAt]
        exact grantDrainMarksArcShiftLeftRight
          ring p a j (by omega) haN
      have hEqR :
          PPL.shiftRight ring p (a - j) =
            PPL.shiftRight ring p 0 := by
        calc
          PPL.shiftRight ring p (a - j) =
              PPL.shiftLeft ring g j := hArc.symm
          _ = p := hEq
          _ = PPL.shiftRight ring p 0 :=
            (grantDrainWeakDeathShiftRightZero ring p).symm
      exact (grantDrainWeakDeathShiftRightNe ring p
        (a - j) 0 (by omega) (by omega) (by omega)) hEqR
    have hNotE : PPL.shiftLeft ring g j ≠ e := by
      by_cases hz : j = 0
      · subst j
        rw [grantDrainWarmShiftLeftZero ring g]
        exact hNotGE
      · exact grantDrainD6DeathSourceOutsidePositive
          ring hn e p g a haN hAt hTo j (by omega) (by omega)
    exact grantDrainSettledNativeStepOutsidePair
      ring fresh update s e (PPL.shiftLeft ring g j)
      hNotE (by rw [hTo]; exact hNotP)
  have hNewNoLeader :
      ∀ j : Nat, 1 ≤ j → j < a →
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring g j)).l = false := by
    intro j hj hja
    rw [hFrame j hja]
    exact hOldLeader.2 j hj hja
  have hNewDistance :
      a ≤ grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g :=
    grantDrainD6DeathLeaderPrefixLowerBound ring
      (grantDrainStep ring fresh update s e).native g a
      (by omega) hNewNoLeader
  have hPhysical := grantDrainSettledMergeDeathPhysicalKernel
    ring hn fresh update s e hC
    (by rw [hTo]; exact hSector.2.1)
    (by rw [hTo]; exact hDeath)
    hNone
  have hNewPQuiet :
      ((grantDrainStep ring fresh update s e).native p).sg =
        false := by
    rw [← hTo]
    exact hPhysical.2.2.2.1
  have hNewPBullet :
      ((grantDrainStep ring fresh update s e).native p).b =
        (s.native p).b := by
    have hBullet := hPhysical.2.2.2.2
    rw [hTo, hUnready] at hBullet
    exact hBullet
  have hSignalPrefix : ∀ j : Nat, j < a →
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g j)).sg =
      (s.native (PPL.shiftLeft ring g j)).sg := by
    intro j hj
    rw [hFrame j hj]
  have hBulletPrefix : ∀ j : Nat, 1 ≤ j → j ≤ a →
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g j)).b.val =
      (s.native (PPL.shiftLeft ring g j)).b.val := by
    intro j hj hja
    by_cases hEq : j = a
    · subst j
      rw [hFront, hNewPBullet]
    · rw [hFrame j (by omega)]
  have hNewFrontQuiet :
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g a)).sg = false := by
    rw [hFront]
    exact hNewPQuiet
  exact (grantDrainD6DeathBulletRankPrefix
    ring s.native (grantDrainStep ring fresh update s e).native
    g a k ha hDistance hNewDistance hOldBullet hGSignal
    hSignalPrefix hBulletPrefix hNewFrontQuiet).2.2

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6DeathPositiveRange
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathFindConverse
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathLeaderPrefixLowerBound
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathLeftOneRightLast
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathSourceOutsidePositive
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathEmptyFollowerCannotKill
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathBulletRankPrefix
#print axioms L3.GrantDrainEntrance.grantDrainD6DeathSurvivingBulletRank

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Q2. The 0*1* suffix is treated as one monotone word on the
whole half-open sector, including its old leader. These lemmas
do not assume an unproved native-E or death-merge closure leaf.
-/

/-- Append a genuine zero prefix to an existing zero-star/one-star
suffix. The cut of the suffix is also the cut of the concatenation. -/
theorem grantDrainSettledSuffixZeroPrefixGlue
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n)
    (lo mid hi : Nat)
    (hBounds : lo ≤ mid ∧ mid ≤ hi)
    (hSuffix : signalZeroStarOneStar ring N p mid hi)
    (hZero : ∀ i : Fin n, lo ≤ i.val → i.val < mid →
      (N (PPL.shiftRight ring p i.val)).sg = false) :
    signalZeroStarOneStar ring N p lo hi := by
  unfold signalZeroStarOneStar at hSuffix ⊢
  obtain ⟨cut, hMid, hHi, hBefore, hAfter⟩ := hSuffix
  refine ⟨cut, (by (try dsimp only at *); omega), hHi, ?_, ?_⟩
  · intro i hLo hCut
    by_cases hEarly : i.val < mid
    · exact hZero i hLo hEarly
    · exact hBefore i (by (try dsimp only at *); omega) hCut
  · intro i hCut hHiNow
    exact hAfter i hCut hHiNow

/-- If the source at offset j is zero, resetting exactly offset j+1
to zero preserves an old zero-star/one-star word. An old cut j+1
moves to j+2; otherwise the cut stays fixed. -/
theorem grantDrainSettledSuffixResetNext
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (p : Fin n)
    (lo hi j : Nat)
    (hHi : hi ≤ n) (hLo : lo ≤ j) (hNext : j + 1 < hi)
    (hSourceZero :
      (N (PPL.shiftRight ring p j)).sg = false)
    (hOld : signalZeroStarOneStar ring N p lo hi)
    (hReset :
      ∀ i : Fin n, lo ≤ i.val → i.val < hi →
        (M (PPL.shiftRight ring p i.val)).sg =
          if i.val = j + 1 then false
          else (N (PPL.shiftRight ring p i.val)).sg) :
    signalZeroStarOneStar ring M p lo hi := by
  unfold signalZeroStarOneStar at hOld ⊢
  obtain ⟨cut, hcLo, hcHi, hZero, hOne⟩ := hOld
  have hCutPastSource : j < cut.val := by
    by_cases hPast : j < cut.val
    · exact hPast
    · have hAtSource :
          (N (PPL.shiftRight ring p j)).sg = true :=
        hOne (⟨j, show j < n by omega⟩ : Fin n)
          (by (try dsimp only at *); omega)
          (by (try dsimp only at *); omega)
      rw [hSourceZero] at hAtSource
      cases hAtSource
  by_cases hBoundary : cut.val = j + 1
  · refine ⟨⟨j + 2, show j + 2 < n + 1 by omega⟩,
      (by (try dsimp only at *); omega),
      (by (try dsimp only at *); omega), ?_, ?_⟩
    · intro i hiLo hiCut
      change i.val < j + 2 at hiCut
      have hiHi : i.val < hi := by omega
      rw [hReset i hiLo hiHi]
      by_cases hiEq : i.val = j + 1
      · rw [if_pos hiEq]
      · rw [if_neg hiEq]
        exact hZero i hiLo (by (try dsimp only at *); omega)
    · intro i hiCut hiHi
      change j + 2 ≤ i.val at hiCut
      have hiLo : lo ≤ i.val := by omega
      have hiNe : i.val ≠ j + 1 := by omega
      rw [hReset i hiLo hiHi, if_neg hiNe]
      exact hOne i (by (try dsimp only at *); omega) hiHi
  · have hLater : j + 1 < cut.val := by omega
    refine ⟨cut, hcLo, hcHi, ?_, ?_⟩
    · intro i hiLo hiCut
      have hiHi : i.val < hi := by omega
      rw [hReset i hiLo hiHi]
      by_cases hiEq : i.val = j + 1
      · rw [if_pos hiEq]
      · rw [if_neg hiEq]
        exact hZero i hiLo hiCut
    · intro i hiCut hiHi
      have hiLo : lo ≤ i.val := by omega
      have hiNe : i.val ≠ j + 1 := by omega
      rw [hReset i hiLo hiHi, if_neg hiNe]
      exact hOne i hiCut hiHi


/-- G3, literal native E on two followers, moving the nonempty source
bullet into the responder. No conditional preservation leaf.
The exact new signal word has a cut at most one place later. -/
theorem grantDrainSettledSuffixFollowerBulletNativeE
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (p e : Fin n)
    (lo hi j : Nat)
    (hHi : hi ≤ n) (hLo : lo ≤ j) (hNext : j + 1 < hi)
    (he : e = PPL.shiftRight ring p j)
    (hI : I ring N)
    (hxFollower : (N e).l = false)
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hxBullet : HasBullet N e)
    (hOld : signalZeroStarOneStar ring N p lo hi) :
    signalZeroStarOneStar ring (nativeE ring N e) p lo hi := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hI
  have hxZero :
      (N e).sg = false :=
    grantDrainEntranceILocalBulletSignalZero
      ring N hLocal e hxBullet
  have hRow := grantDrainEntranceILocalFollowerBulletNativeE
    ring (by omega : 2 ≤ n) N e hLocal
    hxFollower hyFollower hxBullet
  have hSourceZero :
      (N (PPL.shiftRight ring p j)).sg = false := by
    rw [← he]
    exact hxZero
  have hTarget :
      ring.rightNeighbor e =
        PPL.shiftRight ring p (j + 1) := by
    rw [he]
    exact grantDrainEntranceAheadShiftSucc ring p j
  have hj : j < n := by omega
  have hNextLt : j + 1 < n := by omega
  have hReset :
      ∀ i : Fin n, lo ≤ i.val → i.val < hi →
        (nativeE ring N e
          (PPL.shiftRight ring p i.val)).sg =
          if i.val = j + 1 then false
          else (N (PPL.shiftRight ring p i.val)).sg := by
    intro i hiLo hiHi
    by_cases hiSource : i.val = j
    · have hSite : PPL.shiftRight ring p i.val = e := by
        rw [hiSource]
        exact he.symm
      rw [hSite, if_neg (show i.val ≠ j + 1 by omega)]
      rw [hRow.2.1]
      exact hxZero.symm
    · by_cases hiDest : i.val = j + 1
      · have hSite :
            PPL.shiftRight ring p i.val =
              ring.rightNeighbor e := by
          rw [hiDest]
          exact hTarget.symm
        rw [hSite, if_pos hiDest]
        exact hRow.2.2.2
      · have hAwayX :
            PPL.shiftRight ring p i.val ≠ e := by
          rw [he]
          exact grantDrainWeakDeathShiftRightNe
            ring p i.val j i.isLt hj
            (by (try dsimp only at *); omega)
        have hAwayY :
            PPL.shiftRight ring p i.val ≠
              ring.rightNeighbor e := by
          rw [hTarget]
          exact grantDrainWeakDeathShiftRightNe
            ring p i.val (j + 1) i.isLt hNextLt
            (by (try dsimp only at *); omega)
        rw [grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring p i.val)
          hAwayX hAwayY]
        rw [if_neg hiDest]
  exact grantDrainSettledSuffixResetNext
    ring N (nativeE ring N e) p lo hi j
    hHi hLo hNext hSourceZero hOld hReset


theorem grantDrainSettledSuffixWholeOfSettled
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n)
    (d : Fin (n + 1))
    (hSector : sectorLength ring N p d)
    (hSettled : GrantDrainSettledSector ring N p d) :
    signalZeroStarOneStar ring N p 0 d.val := by
  have hPos : 0 < d.val := hSector.1
  rcases hSettled.2.2 with hSome | hNone
  · obtain ⟨h, hh, hBullet, hZero, hSuffix⟩ := hSome
    exact grantDrainSettledSuffixZeroPrefixGlue
      ring N p 0 (h.val + 1) d.val
      (show 0 ≤ h.val + 1 ∧ h.val + 1 ≤ d.val by omega)
      hSuffix (by
        intro i hLower hUpper
        exact hZero i (by (try dsimp only at *); omega))
  · obtain ⟨hNoBullet, hSuffix, hReady⟩ := hNone
    cases hRoot : (N p).sg with
    | false =>
      exact grantDrainSettledSuffixZeroPrefixGlue
        ring N p 0 1 d.val
        (show 0 ≤ 1 ∧ 1 ≤ d.val by omega)
        hSuffix (by
          intro i hLower hUpper
          have hiZero : i.val = 0 := by omega
          have hSite : PPL.shiftRight ring p i.val = p := by
            rw [hiZero, grantDrainWeakDeathShiftRightZero]
          rw [hSite]
          exact hRoot)
    | true =>
      unfold signalZeroStarOneStar
      refine ⟨⟨0, show 0 < n + 1 by omega⟩,
        Nat.le_refl _, (by (try dsimp only at *); omega), ?_, ?_⟩
      · intro i hZero hShort
        change i.val < 0 at hShort
        (try dsimp only at *)
        omega
      · intro i hLower hUpper
        by_cases hiZero : i.val = 0
        · have hSite : PPL.shiftRight ring p i.val = p := by
            rw [hiZero, grantDrainWeakDeathShiftRightZero]
          rw [hSite]
          exact hRoot
        · exact hReady hRoot i (by (try dsimp only at *); omega) hUpper


theorem grantDrainSettledSuffixSettledOfWhole
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n)
    (d : Fin (n + 1))
    (hI : I ring N)
    (hSector : sectorLength ring N p d)
    (hWhole : signalZeroStarOneStar ring N p 0 d.val) :
    GrantDrainSettledSector ring N p d := by
  have hIndex : d.val ≤ n := Nat.le_of_lt_succ d.isLt
  have hPos : 0 < d.val := hSector.1
  have hLocal := hI.2 p d hSector
  refine ⟨hLocal.1, hLocal.2, ?_⟩
  by_cases hSome :
      ∃ a : Fin n, a.val < d.val ∧
        HasBullet N (PPL.shiftRight ring p a.val)
  · obtain ⟨h, hh, hb⟩ := hSome
    left
    refine ⟨h, hh, hb, hLocal.2 h hh hb, ?_⟩
    exact grantDrainSettledSignalRestrict
      ring N p 0 d.val (h.val + 1) d.val
      hIndex
      (show 0 ≤ h.val + 1 ∧
        h.val + 1 ≤ d.val ∧ d.val ≤ d.val by omega)
      hWhole
  · right
    have hNo :
        ∀ h : Fin n, h.val < d.val →
          ¬ HasBullet N (PPL.shiftRight ring p h.val) := by
      intro h hh hb
      exact hSome ⟨h, hh, hb⟩
    have hSuffix := grantDrainSettledSignalRestrict
      ring N p 0 d.val 1 d.val hIndex
      (show 0 ≤ 1 ∧ 1 ≤ d.val ∧ d.val ≤ d.val by omega)
      hWhole
    refine ⟨hNo, hSuffix, ?_⟩
    intro hReady k hkPos hkShort
    unfold signalZeroStarOneStar at hWhole
    obtain ⟨cut, hZeroLo, hCutHi, hZero, hOne⟩ := hWhole
    have hCutZero : cut.val = 0 := by
      by_cases hc : cut.val = 0
      · exact hc
      · have hcPos : 0 < cut.val := by omega
        have hAtZero :
            (N (PPL.shiftRight ring p 0)).sg = false :=
          hZero (⟨0, show 0 < n by omega⟩ : Fin n)
            (Nat.zero_le _) (by (try dsimp only at *); omega)
        have hRoot : (N p).sg = false := by
          simpa only [grantDrainWeakDeathShiftRightZero] using hAtZero
        rw [hReady] at hRoot
        cases hRoot
    exact hOne k (by (try dsimp only at *); omega) hkShort


/-- A characterization that removes the four separate bullet,
ready, and signal-phase subcases from the remaining C_native
closure proof. It is an equivalence, not an E-preservation leaf. -/
theorem grantDrainSettledSuffixC_nativeIffWhole
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) :
    C_native ring N ↔
      I ring N ∧
      ∀ (p : Fin n) (d : Fin (n + 1)),
        sectorLength ring N p d →
          signalZeroStarOneStar ring N p 0 d.val := by
  constructor
  · intro hC
    refine ⟨hC.1, ?_⟩
    intro p d hSector
    have hSettled :=
      ((grantDrainC_native_iff_sectors ring N).mp hC).2
        p d hSector
    exact grantDrainSettledSuffixWholeOfSettled
      ring N p d hSector hSettled
  · rintro ⟨hI, hAll⟩
    apply (grantDrainC_native_iff_sectors ring N).mpr
    refine ⟨hI.1, ?_⟩
    intro p d hSector
    exact grantDrainSettledSuffixSettledOfWhole
      ring N p d hI hSector (hAll p d hSector)

theorem grantDrainSettledSuffixCopyLeft
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (p : Fin n)
    (lo hi j : Nat)
    (hHi : hi ≤ n) (hLo : lo ≤ j) (hNext : j + 1 < hi)
    (hOld : signalZeroStarOneStar ring N p lo hi)
    (hCopy :
      ∀ i : Fin n, lo ≤ i.val → i.val < hi →
        (M (PPL.shiftRight ring p i.val)).sg =
          if i.val = j then
            ((N (PPL.shiftRight ring p j)).sg ||
              (N (PPL.shiftRight ring p (j + 1))).sg)
          else (N (PPL.shiftRight ring p i.val)).sg) :
    signalZeroStarOneStar ring M p lo hi := by
  unfold signalZeroStarOneStar at hOld ⊢
  obtain ⟨cut, hcLo, hcHi, hZero, hOne⟩ := hOld
  by_cases hBoundary : cut.val = j + 1
  · refine ⟨⟨j, show j < n + 1 by omega⟩,
      hLo, (by (try dsimp only at *); omega), ?_, ?_⟩
    · intro i hiLo hiCut
      change i.val < j at hiCut
      have hiHi : i.val < hi := by omega
      rw [hCopy i hiLo hiHi]
      have hNe : i.val ≠ j := by omega
      rw [if_neg hNe]
      exact hZero i hiLo (by (try dsimp only at *); omega)
    · intro i hiCut hiHi
      by_cases hiEq : i.val = j
      · rw [hCopy i (by (try dsimp only at *); omega) hiHi, if_pos hiEq]
        have hNextOne :
            (N (PPL.shiftRight ring p (j + 1))).sg = true :=
          hOne (⟨j + 1, show j + 1 < n by omega⟩ : Fin n)
            (by (try dsimp only at *); omega)
            (by (try dsimp only at *); omega)
        simp [hNextOne]
      · rw [hCopy i (by (try dsimp only at *); omega) hiHi, if_neg hiEq]
        exact hOne i (by (try dsimp only at *); omega) hiHi
  · have hSame :
        ((N (PPL.shiftRight ring p j)).sg ||
          (N (PPL.shiftRight ring p (j + 1))).sg) =
            (N (PPL.shiftRight ring p j)).sg := by
      by_cases hEarly : cut.val ≤ j
      · have hj :
            (N (PPL.shiftRight ring p j)).sg = true :=
          hOne (⟨j, show j < n by omega⟩ : Fin n)
            (by (try dsimp only at *); omega)
            (by (try dsimp only at *); omega)
        simp [hj]
      · have hLate : j + 1 < cut.val := by omega
        have hj :
            (N (PPL.shiftRight ring p j)).sg = false :=
          hZero (⟨j, show j < n by omega⟩ : Fin n)
            (by (try dsimp only at *); omega)
            (by (try dsimp only at *); omega)
        have hy :
            (N (PPL.shiftRight ring p (j + 1))).sg = false :=
          hZero (⟨j + 1, show j + 1 < n by omega⟩ : Fin n)
            (by (try dsimp only at *); omega)
            (by (try dsimp only at *); omega)
        simp [hj, hy]
    have hSignals :
        ∀ i : Fin n, lo ≤ i.val → i.val < hi →
          (M (PPL.shiftRight ring p i.val)).sg =
            (N (PPL.shiftRight ring p i.val)).sg := by
      intro i hiLo hiHi
      rw [hCopy i hiLo hiHi]
      by_cases hiEq : i.val = j
      · rw [if_pos hiEq, hSame, hiEq]
      · rw [if_neg hiEq]
    refine ⟨cut, hcLo, hcHi, ?_, ?_⟩
    · intro i hiLo hiCut
      rw [hSignals i hiLo (by (try dsimp only at *); omega)]
      exact hZero i hiLo hiCut
    · intro i hiCut hiHi
      rw [hSignals i (by (try dsimp only at *); omega) hiHi]
      exact hOne i hiCut hiHi


/-- G1: the ACTUAL native E on two bullet-free followers copies the
responder's signal leftward, i.e. source := source OR responder.
The responder does NOT copy the source. The affected interior
signal word remains 0*1* for arbitrary old cut and ring wrap. -/
theorem grantDrainSettledSuffixFollowerEmptyNativeE
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (p e : Fin n)
    (lo hi j : Nat)
    (hHi : hi ≤ n) (hLo : lo ≤ j) (hNext : j + 1 < hi)
    (he : e = PPL.shiftRight ring p j)
    (hxFollower : (N e).l = false)
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyEmpty : (N (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hOld : signalZeroStarOneStar ring N p lo hi) :
    signalZeroStarOneStar ring (nativeE ring N e) p lo hi := by
  have hRows := grantDrainEntranceFollowerEmptyNativeRows
    ring (by omega : 2 ≤ n) N e
      hxFollower hyFollower hxEmpty hyEmpty
  have hTarget :
      ring.rightNeighbor e =
        PPL.shiftRight ring p (j + 1) := by
    rw [he]
    exact grantDrainEntranceAheadShiftSucc ring p j
  have hj : j < n := by omega
  have hNextLt : j + 1 < n := by omega
  have hCopy :
      ∀ i : Fin n, lo ≤ i.val → i.val < hi →
        (nativeE ring N e
          (PPL.shiftRight ring p i.val)).sg =
          if i.val = j then
            ((N (PPL.shiftRight ring p j)).sg ||
              (N (PPL.shiftRight ring p (j + 1))).sg)
          else (N (PPL.shiftRight ring p i.val)).sg := by
    intro i hiLo hiHi
    by_cases hiSource : i.val = j
    · have hSite : PPL.shiftRight ring p i.val = e := by
        rw [hiSource]
        exact he.symm
      rw [hSite, if_pos hiSource]
      rw [← he, ← hTarget]
      exact hRows.2.1
    · by_cases hiDest : i.val = j + 1
      · rw [hiDest, if_neg (show j + 1 ≠ j by omega)]
        rw [← hTarget]
        exact hRows.2.2
      · have hAwayX :
            PPL.shiftRight ring p i.val ≠ e := by
          rw [he]
          exact grantDrainWeakDeathShiftRightNe
            ring p i.val j i.isLt hj (by (try dsimp only at *); omega)
        have hAwayY :
            PPL.shiftRight ring p i.val ≠
              ring.rightNeighbor e := by
          rw [hTarget]
          exact grantDrainWeakDeathShiftRightNe
            ring p i.val (j + 1) i.isLt hNextLt
              (by (try dsimp only at *); omega)
        rw [grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring p i.val)
          hAwayX hAwayY]
        rw [if_neg hiSource]
  exact grantDrainSettledSuffixCopyLeft
    ring N (nativeE ring N e) p lo hi j
      hHi hLo hNext hOld hCopy

/-- G1, leader-source subcase. If the old settled leader is
ready, its old follower signals are all one. After the literal E
on its first edge the tail from offset two remains entirely one,
even if the responder acquired a new LIVE bullet. -/
theorem grantDrainSettledSuffixReadyLeaderTailNativeE
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (p : Fin n)
    (d : Fin (n + 1))
    (hSector : sectorLength ring N p d)
    (hSettled : GrantDrainSettledSector ring N p d)
    (hTwo : 2 ≤ d.val)
    (hReady : (N p).sg = true) :
    signalZeroStarOneStar ring (nativeE ring N p)
      p 2 d.val := by
  have hMax : d.val ≤ n := Nat.le_of_lt_succ d.isLt
  have hBody :
      ∀ i : Fin n, 1 ≤ i.val → i.val < d.val →
        (N (PPL.shiftRight ring p i.val)).sg = true := by
    rcases hSettled.2.2 with hSome | hNone
    · obtain ⟨b, hb, hBullet, hZero, hSuffix⟩ := hSome
      have hAtZero :
          (N (PPL.shiftRight ring p 0)).sg = false :=
        hZero (⟨0, show 0 < n by omega⟩ : Fin n)
          (by (try dsimp only at *); omega)
      have hRootZero : (N p).sg = false := by
        simpa only [grantDrainWeakDeathShiftRightZero] using hAtZero
      rw [hReady] at hRootZero
      cases hRootZero
    · exact hNone.2.2 hReady
  unfold signalZeroStarOneStar
  refine ⟨⟨2, show 2 < n + 1 by omega⟩,
    Nat.le_refl _, (by (try dsimp only at *); omega), ?_, ?_⟩
  · intro i hLo hCut
    change i.val < 2 at hCut
    (try dsimp only at *)
    omega
  · intro i hiCut hiShort
    have hAwayX :
        PPL.shiftRight ring p i.val ≠ p := by
      have hNe := grantDrainWeakDeathShiftRightNe
        ring p i.val 0 i.isLt
        (show 0 < n by omega) (by (try dsimp only at *); omega)
      simpa only [grantDrainWeakDeathShiftRightZero] using hNe
    have hAwayY :
        PPL.shiftRight ring p i.val ≠ ring.rightNeighbor p := by
      have hNe := grantDrainWeakDeathShiftRightNe
        ring p i.val 1 i.isLt
        (show 1 < n by omega) (by (try dsimp only at *); omega)
      have hNeighbor :
          ring.rightNeighbor p = PPL.shiftRight ring p 1 := rfl
      rw [hNeighbor]
      exact hNe
    rw [grantDrainEntranceNativeEFrame
      ring N p (PPL.shiftRight ring p i.val)
      hAwayX hAwayY]
    exact hBody i (by (try dsimp only at *); omega) hiShort

theorem grantDrainSettledSuffixTranslate
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n)
    (base lo hi : Nat)
    (hLimit : base + hi ≤ n)
    (hOld :
      signalZeroStarOneStar ring N
        (PPL.shiftRight ring p base) lo hi) :
    signalZeroStarOneStar ring N p
      (base + lo) (base + hi) := by
  unfold signalZeroStarOneStar at hOld ⊢
  obtain ⟨cut, hcLo, hcHi, hZero, hOne⟩ := hOld
  refine ⟨⟨base + cut.val,
      show base + cut.val < n + 1 by omega⟩,
    (by (try dsimp only at *); omega), (by (try dsimp only at *); omega), ?_, ?_⟩
  · intro i hiLo hiCut
    have hPos : base ≤ i.val := by omega
    have hIndex : i.val - base < n := by omega
    have hAt :
        (N (PPL.shiftRight ring
            (PPL.shiftRight ring p base)
            (i.val - base))).sg = false :=
      hZero (⟨i.val - base, hIndex⟩ : Fin n)
        (by (try dsimp only at *); omega)
        (by (try dsimp only at *); omega)
    rw [grantDrainWeakDeathShiftRightAdd] at hAt
    have hSum : base + (i.val - base) = i.val := by omega
    rw [hSum] at hAt
    exact hAt
  · intro i hiCut hiHi
    change base + cut.val ≤ i.val at hiCut
    have hPos : base ≤ i.val := by omega
    have hIndex : i.val - base < n := by omega
    have hAt :
        (N (PPL.shiftRight ring
            (PPL.shiftRight ring p base)
            (i.val - base))).sg = true :=
      hOne (⟨i.val - base, hIndex⟩ : Fin n)
        (by (try dsimp only at *); omega)
        (by (try dsimp only at *); omega)
    rw [grantDrainWeakDeathShiftRightAdd] at hAt
    have hSum : base + (i.val - base) = i.val := by omega
    rw [hSum] at hAt
    exact hAt


/-- Physical off-pair signal equality on the body of the old
victim sector after the fatal incoming edge. The front site
at offset zero is deliberately excluded: its signal was reset. -/
theorem grantDrainSettledSuffixDeathTailSignalsFrame
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (p e : Fin n)
    (d : Fin (n + 1)) (j lo hi : Nat)
    (he : e = PPL.shiftRight ring p j)
    (hEnd : j + 1 = d.val)
    (hLo : 1 ≤ lo)
    (hLimit : d.val + hi ≤ n) :
    ∀ i : Fin n, lo ≤ i.val → i.val < hi →
      (nativeE ring N e
        (PPL.shiftRight ring (ring.rightNeighbor e) i.val)).sg =
      (N (PPL.shiftRight ring (ring.rightNeighbor e) i.val)).sg := by
  have hTarget :
      ring.rightNeighbor e =
        PPL.shiftRight ring p d.val := by
    calc
      ring.rightNeighbor e =
          ring.rightNeighbor (PPL.shiftRight ring p j) := by
            rw [he]
      _ = PPL.shiftRight ring p (j + 1) :=
        grantDrainEntranceAheadShiftSucc ring p j
      _ = PPL.shiftRight ring p d.val := by rw [hEnd]
  intro i hiLo hiHi
  have hLift :
      PPL.shiftRight ring (ring.rightNeighbor e) i.val =
        PPL.shiftRight ring p (d.val + i.val) := by
    rw [hTarget, grantDrainWeakDeathShiftRightAdd]
  have hAwayX :
      PPL.shiftRight ring (ring.rightNeighbor e) i.val ≠ e := by
    rw [hLift, he]
    exact grantDrainWeakDeathShiftRightNe
      ring p (d.val + i.val) j
        (by omega : d.val + i.val < n)
        (by omega : j < n)
        (by omega : d.val + i.val ≠ j)
  have hAwayY :
      PPL.shiftRight ring (ring.rightNeighbor e) i.val ≠
        ring.rightNeighbor e := by
    rw [hLift, hTarget]
    exact grantDrainWeakDeathShiftRightNe
      ring p (d.val + i.val) d.val
        (by omega : d.val + i.val < n)
        (by omega : d.val < n)
        (by omega : d.val + i.val ≠ d.val)
  rw [grantDrainEntranceNativeEFrame
    ring N e (PPL.shiftRight ring (ring.rightNeighbor e) i.val)
    hAwayX hAwayY]

/-- Transport any OLD victim-body suffix past the incoming fatal
E edge. The old and new signals are equal at every used offset,
so its cut is unchanged. -/
theorem grantDrainSettledSuffixDeathTail
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (p e : Fin n)
    (d : Fin (n + 1)) (j lo hi : Nat)
    (he : e = PPL.shiftRight ring p j)
    (hEnd : j + 1 = d.val)
    (hLo : 1 ≤ lo)
    (hLimit : d.val + hi ≤ n)
    (hOld :
      signalZeroStarOneStar ring N
        (ring.rightNeighbor e) lo hi) :
    signalZeroStarOneStar ring (nativeE ring N e)
      (ring.rightNeighbor e) lo hi := by
  unfold signalZeroStarOneStar at hOld ⊢
  obtain ⟨cut, hcLo, hcHi, hZero, hOne⟩ := hOld
  refine ⟨cut, hcLo, hcHi, ?_, ?_⟩
  · intro i hiLo hiCut
    have hiHi : i.val < hi := by omega
    rw [grantDrainSettledSuffixDeathTailSignalsFrame
      ring hn N p e d j lo hi
      he hEnd hLo hLimit i hiLo hiHi]
    exact hZero i hiLo hiCut
  · intro i hiCut hiHi
    rw [grantDrainSettledSuffixDeathTailSignalsFrame
      ring hn N p e d j lo hi
      he hEnd hLo hLimit i (by (try dsimp only at *); omega) hiHi]
    exact hOne i hiCut hiHi

theorem grantDrainSettledSuffixQuietSourceNativeE
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (p e : Fin n)
    (lo hi j : Nat)
    (hHi : hi ≤ n) (hLo : lo ≤ j) (hNext : j + 1 < hi)
    (he : e = PPL.shiftRight ring p j)
    (hxNotReady : (N e).l = false ∨ (N e).sg = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hOld : signalZeroStarOneStar ring N p lo hi) :
    signalZeroStarOneStar ring (nativeE ring N e) p lo hi := by
  have hRows := grantDrainEntranceQuietEmptySourceNativeERows
    ring (by omega : 2 ≤ n) N e
      hxNotReady hxEmpty hyFollower
  have hTarget :
      ring.rightNeighbor e =
        PPL.shiftRight ring p (j + 1) := by
    rw [he]
    exact grantDrainEntranceAheadShiftSucc ring p j
  have hj : j < n := by omega
  have hNextLt : j + 1 < n := by omega
  have hCopy :
      ∀ i : Fin n, lo ≤ i.val → i.val < hi →
        (nativeE ring N e
          (PPL.shiftRight ring p i.val)).sg =
          if i.val = j then
            ((N (PPL.shiftRight ring p j)).sg ||
              (N (PPL.shiftRight ring p (j + 1))).sg)
          else (N (PPL.shiftRight ring p i.val)).sg := by
    intro i hiLo hiHi
    by_cases hiSource : i.val = j
    · have hSite : PPL.shiftRight ring p i.val = e := by
        rw [hiSource]
        exact he.symm
      rw [hSite, if_pos hiSource]
      rw [← he, ← hTarget]
      exact hRows.2.1
    · by_cases hiDest : i.val = j + 1
      · rw [hiDest, if_neg (show j + 1 ≠ j by omega)]
        rw [← hTarget]
        exact hRows.2.2
      · have hAwayX :
            PPL.shiftRight ring p i.val ≠ e := by
          rw [he]
          exact grantDrainWeakDeathShiftRightNe
            ring p i.val j i.isLt hj (by (try dsimp only at *); omega)
        have hAwayY :
            PPL.shiftRight ring p i.val ≠
              ring.rightNeighbor e := by
          rw [hTarget]
          exact grantDrainWeakDeathShiftRightNe
            ring p i.val (j + 1) i.isLt hNextLt
              (by (try dsimp only at *); omega)
        rw [grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring p i.val)
          hAwayX hAwayY]
        rw [if_neg hiSource]
  exact grantDrainSettledSuffixCopyLeft
    ring N (nativeE ring N e) p lo hi j
      hHi hLo hNext hOld hCopy


/-- One-site signal formula for E on an empty, non-ready source
and follower responder; the responder itself is unchanged. -/
theorem grantDrainSettledSuffixQuietSourceSignalAt
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e i : Fin n)
    (hxNotReady : (N e).l = false ∨ (N e).sg = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyFollower : (N (ring.rightNeighbor e)).l = false) :
    (nativeE ring N e i).sg =
      if i = e then
        ((N e).sg || (N (ring.rightNeighbor e)).sg)
      else (N i).sg := by
  have hRows := grantDrainEntranceQuietEmptySourceNativeERows
    ring (by omega : 2 ≤ n) N e
      hxNotReady hxEmpty hyFollower
  by_cases hiE : i = e
  · subst i
    rw [if_pos rfl]
    exact hRows.2.1
  · by_cases hiY : i = ring.rightNeighbor e
    · subst i
      rw [if_neg (grantDrainEntranceRightNeighborDistinct
        ring (by omega : 2 ≤ n) e)]
      exact hRows.2.2
    · rw [if_neg hiE]
      exact congrArg (fun c : CertNative => c.sg)
        (grantDrainEntranceNativeEFrame ring N e i hiE hiY)

/-- Whole signal-word transport requires equality only on the
half-open old sector, never at its terminal next leader. -/
theorem grantDrainSettledSuffixHalfOpenFrame
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (p : Fin n)
    (lo hi : Nat)
    (hOld : signalZeroStarOneStar ring N p lo hi)
    (hSignals : ∀ i : Fin n, lo ≤ i.val → i.val < hi →
      (M (PPL.shiftRight ring p i.val)).sg =
        (N (PPL.shiftRight ring p i.val)).sg) :
    signalZeroStarOneStar ring M p lo hi := by
  unfold signalZeroStarOneStar at hOld ⊢
  obtain ⟨cut, hLo, hHi, hZero, hOne⟩ := hOld
  refine ⟨cut, hLo, hHi, ?_, ?_⟩
  · intro i hiLo hiCut
    rw [hSignals i hiLo (by (try dsimp only at *); omega)]
    exact hZero i hiLo hiCut
  · intro i hiCut hiHi
    rw [hSignals i (by (try dsimp only at *); omega) hiHi]
    exact hOne i hiCut hiHi

/-- G1: every old sector retains a 0*1* signal word under the
literal quiet-empty-source E row, even if other sectors exist. -/
theorem grantDrainSettledSuffixQuietSourceAllSectors
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hC : C_native ring N)
    (hxNotReady : (N e).l = false ∨ (N e).sg = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring N p d) :
    signalZeroStarOneStar ring (nativeE ring N e)
      p 0 d.val := by
  have hOld : signalZeroStarOneStar ring N p 0 d.val :=
    ((grantDrainSettledSuffixC_nativeIffWhole ring N).mp hC).2
      p d hSector
  have hOff : PPL.shiftRight ring p
      (PPL.cyclicOffset ring p e) = e :=
    grantDrainMarksArcShiftRightOffset ring p e
  have hOffLt : PPL.cyclicOffset ring p e < n :=
    grantDrainEntranceArcOffsetLt ring p e
  have hMax : d.val ≤ n := Nat.le_of_lt_succ d.isLt
  by_cases hInside : PPL.cyclicOffset ring p e < d.val
  · have hNext :
        ring.rightNeighbor e =
          PPL.shiftRight ring p
            (PPL.cyclicOffset ring p e + 1) := by
      calc
        ring.rightNeighbor e =
            ring.rightNeighbor (PPL.shiftRight ring p
              (PPL.cyclicOffset ring p e)) := by rw [hOff]
        _ = PPL.shiftRight ring p
            (PPL.cyclicOffset ring p e + 1) :=
          grantDrainEntranceAheadShiftSucc ring p
            (PPL.cyclicOffset ring p e)
    have hInsideNext :
        PPL.cyclicOffset ring p e + 1 < d.val := by
      by_cases hTerminal :
          PPL.cyclicOffset ring p e + 1 = d.val
      · have hyLeader : (N (ring.rightNeighbor e)).l =
            true := by
          rw [hNext, hTerminal]
          exact hSector.2.2.1
        rw [hyLeader] at hyFollower
        cases hyFollower
      · omega
    exact grantDrainSettledSuffixQuietSourceNativeE
      ring hn N p e 0 d.val (PPL.cyclicOffset ring p e)
      hMax (Nat.zero_le _) hInsideNext hOff.symm
      hxNotReady hxEmpty hyFollower hOld
  · have hSignal :
        ∀ i : Fin n, 0 ≤ i.val → i.val < d.val →
          (nativeE ring N e (PPL.shiftRight ring p i.val)).sg =
            (N (PPL.shiftRight ring p i.val)).sg := by
      intro i hiZero hiD
      have hiAway : PPL.shiftRight ring p i.val ≠ e := by
        rw [← hOff]
        exact grantDrainWeakDeathShiftRightNe
          ring p i.val (PPL.cyclicOffset ring p e)
          i.isLt hOffLt (by (try dsimp only at *); omega)
      have hSource := grantDrainSettledSuffixQuietSourceSignalAt
        ring hn N e (PPL.shiftRight ring p i.val)
        hxNotReady hxEmpty hyFollower
      rw [if_neg hiAway] at hSource
      exact hSource
    exact grantDrainSettledSuffixHalfOpenFrame
      ring N (nativeE ring N e) p 0 d.val hOld hSignal

/-- A full arbitrary-n G1 E-row theorem, not an assumed leaf:
quiet/empty source, follower responder, any number of leaders. -/
theorem grantDrainSettledSuffixQuietSourceNativeEPreservesC
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hC : C_native ring N)
    (hxNotReady : (N e).l = false ∨ (N e).sg = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyFollower : (N (ring.rightNeighbor e)).l = false) :
    C_native ring (nativeE ring N e) := by
  have hOldLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hC.1
  have hNewLocal : GrantDrainEntranceILocal ring
      (nativeE ring N e) :=
    grantDrainEntranceILocalNativeEAll
      ring (by omega : 3 ≤ n) N e hOldLocal
  have hNewI : I ring (nativeE ring N e) :=
    (grantDrainEntranceIffILocal ring (nativeE ring N e)).mpr
      hNewLocal
  apply (grantDrainSettledSuffixC_nativeIffWhole
    ring (nativeE ring N e)).mpr
  refine ⟨hNewI, ?_⟩
  intro p d hNewSector
  have hOldSector : sectorLength ring N p d :=
    (grantDrainEntranceR8eSectorRowFollowerResponder
      ring (by omega : 2 ≤ n) N e hyFollower p d).mp
        hNewSector
  exact grantDrainSettledSuffixQuietSourceAllSectors
    ring hn N e hC hxNotReady hxEmpty hyFollower
    p d hOldSector


/-- G2. Genuine zero-signal prefix after a death, including a
READY source leader that emitted LIVE during the selected edge.
The source-prefix theorem covers both effective killers. -/
theorem grantDrainSettledSuffixDeathPrefixGeneral
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (p e : Fin n)
    (d : Fin (n + 1)) (j : Nat)
    (hC : C_native ring N)
    (hSector : sectorLength ring N p d)
    (hShort : d.val < n)
    (hEnd : j + 1 = d.val)
    (he : e = PPL.shiftRight ring p j)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    ∀ i : Fin n, i.val ≤ d.val →
      (nativeE ring N e
        (PPL.shiftRight ring p i.val)).sg = false := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hC.1
  have hRight :
      PPL.shiftRight ring p d.val = ring.rightNeighbor e := by
    calc
      PPL.shiftRight ring p d.val =
          PPL.shiftRight ring p (j + 1) := by rw [hEnd]
      _ = ring.rightNeighbor (PPL.shiftRight ring p j) := by
        exact (grantDrainEntranceAheadShiftSucc ring p j).symm
      _ = ring.rightNeighbor e := by rw [← he]
  have hSource :
      PPL.shiftRight ring p (d.val - 1) = e := by
    have hJ : j = d.val - 1 := by omega
    rw [← hJ]
    exact he.symm
  have hOldPrefix := grantDrainEntranceDeathSourcePrefixClean
    ring (by omega : 2 ≤ n) N e hLocal hyLeader hDeath
      p d hSector.1 hShort hRight hSource hSector
  have hFields := grantDrainEntranceNativeEDeathFields
    ring (by omega : 2 ≤ n) N e hLocal hyLeader hDeath
  have hEnds := grantDrainEntranceILocalNativeEDeathEndpointZeros
    ring (by omega : 2 ≤ n) N e hLocal hyLeader hDeath
  intro i hi
  by_cases hiLt : i.val < d.val
  · have hOldZero := (hOldPrefix i.val hiLt).2
    exact ((hFields (PPL.shiftRight ring p i.val)).2.2).trans
      hOldZero
  · have hiEq : i.val = d.val := by omega
    rw [hiEq, hRight]
    exact hEnds.2.2.2


theorem grantDrainSettledSuffixDeathGlueGeneral
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (p e : Fin n)
    (dLeft dRight : Fin (n + 1))
    (j lo : Nat)
    (hC : C_native ring N)
    (hSector : sectorLength ring N p dLeft)
    (hEnd : j + 1 = dLeft.val)
    (he : e = PPL.shiftRight ring p j)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hRightPos : 0 < dRight.val)
    (hGap : dLeft.val + dRight.val ≤ n)
    (hLo : 1 ≤ lo)
    (hLoHi : lo ≤ dRight.val)
    (hOldSuffix :
      signalZeroStarOneStar ring N
        (ring.rightNeighbor e) lo dRight.val)
    (hVictimZero :
      ∀ i : Fin n, 1 ≤ i.val → i.val < lo →
        (N (PPL.shiftRight ring
          (ring.rightNeighbor e) i.val)).sg = false) :
    signalZeroStarOneStar ring (nativeE ring N e)
      p 0 (dLeft.val + dRight.val) := by
  have hLeftShort : dLeft.val < n := by omega
  have hPrefix := grantDrainSettledSuffixDeathPrefixGeneral
    ring hn N p e dLeft j hC hSector hLeftShort
      hEnd he hyLeader hDeath
  have hTarget :
      ring.rightNeighbor e =
        PPL.shiftRight ring p dLeft.val := by
    calc
      ring.rightNeighbor e =
          ring.rightNeighbor (PPL.shiftRight ring p j) := by
            rw [he]
      _ = PPL.shiftRight ring p (j + 1) :=
        grantDrainEntranceAheadShiftSucc ring p j
      _ = PPL.shiftRight ring p dLeft.val := by rw [hEnd]
  have hTail := grantDrainSettledSuffixDeathTail
    ring hn N p e dLeft j lo dRight.val
      he hEnd hLo hGap hOldSuffix
  have hRebased :
      signalZeroStarOneStar ring (nativeE ring N e)
        p (dLeft.val + lo) (dLeft.val + dRight.val) := by
    have hTranslated := grantDrainSettledSuffixTranslate
      ring (nativeE ring N e) p
      dLeft.val lo dRight.val hGap
      (by simpa only [← hTarget] using hTail)
    exact hTranslated
  apply grantDrainSettledSuffixZeroPrefixGlue
    ring (nativeE ring N e) p
      0 (dLeft.val + lo) (dLeft.val + dRight.val)
      (show 0 ≤ dLeft.val + lo ∧
        dLeft.val + lo ≤ dLeft.val + dRight.val by omega)
      hRebased
  intro i hiZero hiShort
  by_cases hLeft : i.val ≤ dLeft.val
  · exact hPrefix i hLeft
  · have hOffsetPos : 1 ≤ i.val - dLeft.val := by omega
    have hOffsetLt : i.val - dLeft.val < lo := by omega
    have hOffsetN : i.val - dLeft.val < n := by omega
    have hOldSignal :
        (N (PPL.shiftRight ring
          (ring.rightNeighbor e) (i.val - dLeft.val))).sg = false :=
      hVictimZero
        (⟨i.val - dLeft.val, hOffsetN⟩ : Fin n)
        (by (try dsimp only at *); omega)
        (by (try dsimp only at *); omega)
    have hFrame := grantDrainSettledSuffixDeathTailSignalsFrame
      ring hn N p e dLeft j 1 lo
        he hEnd (by decide : 1 ≤ (1 : Nat))
        (by omega : dLeft.val + lo ≤ n)
        (⟨i.val - dLeft.val, hOffsetN⟩ : Fin n)
        (by (try dsimp only at *); omega)
        (by (try dsimp only at *); omega)
    have hShift :
        PPL.shiftRight ring (ring.rightNeighbor e)
            (i.val - dLeft.val) =
          PPL.shiftRight ring p i.val := by
      calc
        PPL.shiftRight ring (ring.rightNeighbor e)
            (i.val - dLeft.val) =
          PPL.shiftRight ring
            (PPL.shiftRight ring p dLeft.val)
            (i.val - dLeft.val) := by rw [hTarget]
        _ = PPL.shiftRight ring p
            (dLeft.val + (i.val - dLeft.val)) :=
          grantDrainWeakDeathShiftRightAdd
            ring p dLeft.val (i.val - dLeft.val)
        _ = PPL.shiftRight ring p i.val := by
          rw [show dLeft.val + (i.val - dLeft.val) =
            i.val by omega]
    rw [← hShift]
    rw [hFrame]
    exact hOldSignal


theorem grantDrainSettledSuffixDeathWholeMergedGeneral
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (p e : Fin n)
    (dLeft dRight : Fin (n + 1))
    (j : Nat)
    (hC : C_native ring N)
    (hLeftSector : sectorLength ring N p dLeft)
    (hRightSector :
      sectorLength ring N (ring.rightNeighbor e) dRight)
    (hEnd : j + 1 = dLeft.val)
    (he : e = PPL.shiftRight ring p j)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hGap : dLeft.val + dRight.val ≤ n) :
    signalZeroStarOneStar ring (nativeE ring N e)
      p 0 (dLeft.val + dRight.val) := by
  have hRightSettled : GrantDrainSettledSector ring N
      (ring.rightNeighbor e) dRight :=
    ((grantDrainC_native_iff_sectors ring N).mp hC).2
      (ring.rightNeighbor e) dRight hRightSector
  rcases hRightSettled.2.2 with hSome | hNone
  · obtain ⟨b, hb, hBulletRight, hTrail, hSuffix⟩ := hSome
    exact grantDrainSettledSuffixDeathGlueGeneral
      ring hn N p e dLeft dRight j (b.val + 1)
      hC hLeftSector hEnd he hRightSector.2.1 hDeath
      hRightSector.1 hGap
      (by omega : 1 ≤ b.val + 1)
      (by omega : b.val + 1 ≤ dRight.val)
      hSuffix
      (by
        intro i hiPos hiShort
        exact hTrail i (by (try dsimp only at *); omega))
  · obtain ⟨hNoRight, hSuffix, hReady⟩ := hNone
    exact grantDrainSettledSuffixDeathGlueGeneral
      ring hn N p e dLeft dRight j 1
      hC hLeftSector hEnd he hRightSector.2.1 hDeath
      hRightSector.1 hGap
      (by decide : 1 ≤ (1 : Nat))
      (hRightSector.1 : 1 ≤ dRight.val)
      hSuffix
      (by
        intro i hiPos hiShort
        omega)


/-- G2, arbitrary n: every POST-DEATH sector is either an old
sector untouched on its half-open signal body, or the merge of
two consecutive old sectors. Both have a whole 0*1* suffix. -/
theorem grantDrainSettledSuffixDeathAllSectors
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hC : C_native ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (p : Fin n) (d : Fin (n + 1))
    (hNewSector : sectorLength ring (nativeE ring N e) p d) :
    signalZeroStarOneStar ring (nativeE ring N e)
      p 0 d.val := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hC.1
  have hCases := grantDrainEntranceDeathSectorPartition
    ring (by omega : 2 ≤ n) N e hLocal
      hyLeader hDeath p d hNewSector
  rcases hCases with hFrame | hMerge
  · obtain ⟨hOldSector, hAway⟩ := hFrame
    have hOldWhole : signalZeroStarOneStar ring N p 0 d.val :=
      ((grantDrainSettledSuffixC_nativeIffWhole ring N).mp
        hC).2 p d hOldSector
    have hSignals :
        ∀ i : Fin n, 0 ≤ i.val → i.val < d.val →
          (nativeE ring N e
            (PPL.shiftRight ring p i.val)).sg =
            (N (PPL.shiftRight ring p i.val)).sg := by
      intro i hiZero hiLt
      exact congrArg (fun c : CertNative => c.sg)
        (grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring p i.val)
          (hAway i.val hiLt).1 (hAway i.val hiLt).2)
    exact grantDrainSettledSuffixHalfOpenFrame
      ring N (nativeE ring N e) p 0 d.val
      hOldWhole hSignals
  · obtain ⟨t, htPos, htLt, hRight, hSource,
      hLeftSector, hRightSector⟩ := hMerge
    have hRightIndex : d.val - t.val < n + 1 := by omega
    have hEnd : t.val - 1 + 1 = t.val := by omega
    have hSourceEq : e =
        PPL.shiftRight ring p (t.val - 1) := hSource.symm
    have hGap : t.val + (d.val - t.val) ≤ n := by
      have hDMax : d.val ≤ n := Nat.le_of_lt_succ d.isLt
      (try dsimp only at *)
      omega
    have hWhole := grantDrainSettledSuffixDeathWholeMergedGeneral
      ring hn N p e t
      (⟨d.val - t.val, hRightIndex⟩ : Fin (n + 1))
      (t.val - 1) hC hLeftSector hRightSector
      hEnd hSourceEq hDeath hGap
    have hSum : t.val + (d.val - t.val) = d.val := by omega
    simpa only [hSum] using hWhole

/-- G2, full native-E death case: the I factor and the global
0*1* sector-suffix factor are both preserved. An effective
killer may be a ready source leader or an old LIVE bullet. -/
theorem grantDrainSettledSuffixDeathNativeEPreservesC
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hC : C_native ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    C_native ring (nativeE ring N e) := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hC.1
  have hNewLocal : GrantDrainEntranceILocal ring
      (nativeE ring N e) :=
    grantDrainEntranceILocalNativeEAll
      ring (by omega : 3 ≤ n) N e hLocal
  have hNewI : I ring (nativeE ring N e) :=
    (grantDrainEntranceIffILocal ring (nativeE ring N e)).mpr
      hNewLocal
  apply (grantDrainSettledSuffixC_nativeIffWhole
    ring (nativeE ring N e)).mpr
  refine ⟨hNewI, ?_⟩
  intro p d hNewSector
  exact grantDrainSettledSuffixDeathAllSectors
    ring hn N e hC hyLeader hDeath p d hNewSector

/-- G3 physical death branch, provided no FIRE is selected.
No separate merged-sector preservation leaf is assumed. -/
theorem grantDrainSettledSuffixDeathPhysicalNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = false)
    (hNoFire : grantDrainSelect ring s e = .none) :
    C_native ring (grantDrainStep ring fresh update s e).native := by
  have hNative : C_native ring (nativeE ring s.native e) :=
    grantDrainSettledSuffixDeathNativeEPreservesC
      ring hn s.native e hC hyLeader hDeath
  change C_native ring (grantDrainNativeNext ring s e)
  simpa [grantDrainNativeNext, hNoFire] using hNative


/-- Physical G1 branch: when the old source is an empty, non-ready
site and the responder is a follower, an E-only selected edge
preserves full C_native with any number of old leaders. -/
theorem grantDrainSettledSuffixQuietSourcePhysicalNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hxNotReady :
      (s.native e).l = false ∨ (s.native e).sg = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hNoFire : grantDrainSelect ring s e = .none) :
    C_native ring (grantDrainStep ring fresh update s e).native := by
  have hNative : C_native ring (nativeE ring s.native e) :=
    grantDrainSettledSuffixQuietSourceNativeEPreservesC
      ring hn s.native e hC hxNotReady hxEmpty hyFollower
  change C_native ring (grantDrainNativeNext ring s e)
  simpa [grantDrainNativeNext, hNoFire] using hNative

/-- G3's physically selected E-only subtable. These are two
fully discharged native-row cases, not an assumed closure leaf:
quiet-empty source -> follower, or actual responder-leader death.
The NoBadLive factor is preserved by the physical theorem. -/
theorem grantDrainSettledSuffixSelectedNoFireRows
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hNoFire : grantDrainSelect ring s e = .none)
    (hRow :
      ((s.native (ring.rightNeighbor e)).l = false ∧
        (s.native e).b = (0 : Fin 3) ∧
        ((s.native e).l = false ∨ (s.native e).sg = false))
      ∨
      ((s.native (ring.rightNeighbor e)).l = true ∧
        (nativeE ring s.native e
          (ring.rightNeighbor e)).l = false)) :
    C_native ring (grantDrainStep ring fresh update s e).native ∧
    GrantDrainEntranceNoBadLive ring
      (grantDrainStep ring fresh update s e) := by
  have hNewC :
      C_native ring (grantDrainStep ring fresh update s e).native := by
    rcases hRow with hQuiet | hDeath
    · exact grantDrainSettledSuffixQuietSourcePhysicalNoFire
        ring hn fresh update s e hC
        hQuiet.2.2 hQuiet.2.1 hQuiet.1 hNoFire
    · exact grantDrainSettledSuffixDeathPhysicalNoFire
        ring hn fresh update s e hC hDeath.1 hDeath.2
        hNoFire
  exact ⟨hNewC,
    grantDrainEntrancePhysicalNoBadNext
      ring hn fresh update s e hC.1.1 hNoBad⟩

/-- A non-vacuous fatal-E n=5 control. The PRE native state has
C_native, PPlus, and NoBadLive. The all-n death theorem is then
instantiated on the known physical e2 kill. -/
theorem grantDrainSettledSuffixDeathFiveControl :
    C_native grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native ∧
    PPlus grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native ∧
    GrantDrainEntranceNoBadLive grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false) ∧
    C_native grantDrainD6DeathWitnessRing
      (nativeE grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState false).native
        (2 : Fin 5)) := by
  have hPreC : C_native grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native := by decide
  have hPrePB : PPlus grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false).native := by decide
  have hNoBad : GrantDrainEntranceNoBadLive
      grantDrainD6DeathWitnessRing
      (grantDrainD6DeathWitnessState false) := by
    intro b
    unfold SharedPaperNonleftmostLiveExact
    revert b
    decide
  have hLeader :
      ((grantDrainD6DeathWitnessState false).native
        (grantDrainD6DeathWitnessRing.rightNeighbor
          (2 : Fin 5))).l = true := by decide
  have hDeath :
      (nativeE grantDrainD6DeathWitnessRing
        (grantDrainD6DeathWitnessState false).native
        (2 : Fin 5)
        (grantDrainD6DeathWitnessRing.rightNeighbor
          (2 : Fin 5))).l = false := by decide
  refine ⟨hPreC, hPrePB, hNoBad, ?_⟩
  exact grantDrainSettledSuffixDeathNativeEPreservesC
    grantDrainD6DeathWitnessRing
    (by decide : 5 ≤ 5)
    (grantDrainD6DeathWitnessState false).native
    (2 : Fin 5) hPreC hLeader hDeath

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixZeroPrefixGlue
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixWholeOfSettled
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixSettledOfWhole
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixC_nativeIffWhole
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixCopyLeft
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixFollowerEmptyNativeE
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixReadyLeaderTailNativeE
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixTranslate
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixDeathTailSignalsFrame
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixDeathTail
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixQuietSourceNativeE
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixQuietSourceSignalAt
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixHalfOpenFrame
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixQuietSourceAllSectors
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixQuietSourceNativeEPreservesC
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixDeathPrefixGeneral
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixDeathGlueGeneral
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixDeathWholeMergedGeneral
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixDeathAllSectors
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixDeathNativeEPreservesC
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixDeathPhysicalNoFire
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixQuietSourcePhysicalNoFire
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixSelectedNoFireRows
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixDeathFiveControl
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixResetNext
#print axioms L3.GrantDrainEntrance.grantDrainSettledSuffixFollowerBulletNativeE

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
An unconditional all-edge *reduction*, not D2:
if neither endpoint touches the inclusive OLD nearest-left scan,
the literal step preserves the actual warm rank, the continuing
host, the one-time reserve, and GrantDrainWarmMergeSpent; its
charged rank cannot rise.  This holds with arbitrary FIRE and
arbitrary freshRequest / updateScratch functions.  Otherwise
the serviced pair meets that OLD scan.

The arc-contact branch still needs physical birth and moving-host
scan transport.  No assumed leaf, sorry, axiom, or fake D2.
-/

/-- Any old exceptional death necessarily touches the endpoint
of the inclusive old warm scan.  This is the local form of the
already merged exceptional-at-responder lemma. -/
theorem grantDrainD6WarmExceptionalScanContact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e g : Fin n)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    ∃ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g ∧
      PPL.shiftLeft ring g k = ring.rightNeighbor e := by
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  exact ⟨grantDrainLeftLeaderDistance ring s.native g,
    Nat.le_refl _, hResponder⟩

/-- If both selected endpoints are outside the inclusive old
left scan, the true OLD exceptional-death guard is false.
There is no no-FIRE hypothesis here. -/
theorem grantDrainD6WarmOutsidePairNoExceptional
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e g : Fin n)
    (hOutside : ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g k ≠ e ∧
      PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) :
    grantDrainExceptionalDeath ring s e g = false := by
  cases he : grantDrainExceptionalDeath ring s e g with
  | false =>
      rfl
  | true =>
      obtain ⟨k, hk, hAt⟩ :=
        grantDrainD6WarmExceptionalScanContact ring s e g he
      exact False.elim ((hOutside k hk).2 hAt)

/-- All-fire/no-fire outside-pair closure of the actual spent
reserve invariant, for the continuing old warm host.
The available-reserve branch cannot consume its exceptional
credit; the spent branch is the merged outside-pair lemma. -/
theorem grantDrainD6WarmOutsidePairInvariant
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainWarmLabel n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hOutside : ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g k ≠ e ∧
      PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hNoExceptional :=
    grantDrainD6WarmOutsidePairNoExceptional
      ring s e g hOutside
  cases hr : label.exceptionalLeft with
  | false =>
      exact grantDrainD6MergeSpentOutsidePair
        ring fresh update s label e g
        hInv hWarm hHost hr hOutside
  | true =>
      have hNoExceptionalAll :
          ∀ z : Fin n, label.host = some z →
            grantDrainExceptionalDeath ring s e z = false := by
        intro z hz
        have hEq : z = g :=
          Option.some.inj (hz.symm.trans hHost)
        subst z
        exact hNoExceptional
      exact grantDrainD6MergeUnspentWithoutExceptional
        ring fresh update s e label hr hNoExceptionalAll

/-- The actual physical and ghost host fields are unchanged
when the selected service is outside the inclusive warm scan.
No token-row assumption is introduced: both sites are outside g,
so the literal token row cannot write its stored grant/request. -/
theorem grantDrainD6WarmOutsidePairFields
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainWarmLabel n)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hWarmAt : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hOutside : ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g k ≠ e ∧
      PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) :
    (grantDrainWarmLabelStep ring fresh update s e label).host =
        some g ∧
    (grantDrainWarmLabelStep ring fresh update s e label).warm =
        true ∧
    (grantDrainWarmLabelStep ring fresh update s e
      label).exceptionalLeft = label.exceptionalLeft ∧
    (grantDrainStep ring fresh update s e).grant g = true := by
  have hX : g ≠ e := by
    simpa only [grantDrainWarmShiftLeftZero] using
      (hOutside 0 (Nat.zero_le _)).1
  have hY : g ≠ ring.rightNeighbor e := by
    simpa only [grantDrainWarmShiftLeftZero] using
      (hOutside 0 (Nat.zero_le _)).2
  have hNative :
      (grantDrainStep ring fresh update s e).native g =
        s.native g :=
    grantDrainSettledNativeStepOutsidePair
      ring fresh update s e g hX hY
  have hRequest :
      (grantDrainStep ring fresh update s e).request g =
        s.request g := by
    simp [grantDrainStep, hX, hY]
  have hGrantNext :
      (grantDrainStep ring fresh update s e).grant g =
        true := by
    have hFrame :
        (grantDrainStep ring fresh update s e).grant g =
          s.grant g := by
      simp [grantDrainStep, hX, hY]
    rw [hFrame]
    exact hGrant
  have hWarmNext :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true := by
    simpa [grantDrainWarmAt, hNative, hRequest] using hWarmAt
  have hHostNext :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost, hX, hY]
  have hWarmLabelNext :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true := by
    simp [grantDrainWarmLabelStep, hHost, hX, hY,
      hWarm, hWarmNext]
  have hNoExceptional :=
    grantDrainD6WarmOutsidePairNoExceptional
      ring s e g hOutside
  have hReserveNext :
      (grantDrainWarmLabelStep ring fresh update s e
        label).exceptionalLeft = label.exceptionalLeft := by
    simp [grantDrainWarmLabelStep, hHost, hNoExceptional]
  exact ⟨hHostNext, hWarmLabelNext, hReserveNext,
    hGrantNext⟩

/-- The complete outside-pair entry of D2: actual source step,
both FIRE and no-FIRE, unchanged native W, no growth of the
charged W, and preservation of the one-time ghost invariant. -/
theorem grantDrainD6WarmOutsidePairCase
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainWarmLabel n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hWarmAt : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hOutside : ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g k ≠ e ∧
      PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g =
      grantDrainWarmRank ring s.native g ∧
    grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label) ≤
      grantDrainChargedWarmRank ring s label ∧
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hRank : grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g =
      grantDrainWarmRank ring s.native g :=
    grantDrainWarmOutsidePairScanFrame
      ring fresh update s e g hOutside
  obtain ⟨hHostNext, hWarmNext, hReserveNext, hGrantNext⟩ :=
    grantDrainD6WarmOutsidePairFields
      ring fresh update s e g label
      hWarm hHost hWarmAt hGrant hOutside
  have hBudget :
      (grantDrainWarmLabelStep ring fresh update s e
        label).birthsLeft ≤ label.birthsLeft :=
    grantDrainWarmLabel_birthsLeft_le
      ring fresh update s e label
  have hOldCharged :
      grantDrainChargedWarmRank ring s label =
        grantDrainWarmRank ring s.native g +
          label.birthsLeft +
          (if label.exceptionalLeft then
            2 * (n - 2) else 0) := by
    simp [grantDrainChargedWarmRank,
      hWarm, hHost, hGrant]
  have hNewCharged :
      grantDrainChargedWarmRank ring
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label) =
        grantDrainWarmRank ring s.native g +
          (grantDrainWarmLabelStep ring fresh update s e
            label).birthsLeft +
          (if label.exceptionalLeft then
            2 * (n - 2) else 0) := by
    simp [grantDrainChargedWarmRank,
      hWarmNext, hHostNext, hGrantNext,
      hReserveNext, hRank]
  refine ⟨hRank, ?_, grantDrainD6WarmOutsidePairInvariant
    ring fresh update s e g label hInv
    hWarm hHost hOutside⟩
  rw [hOldCharged, hNewCharged]
  omega

/-- Every selected edge satisfies this genuine old-state
first-match reduction: either it misses the entire old scan
and ALL unchanged/charged/invariant conclusions are established,
or one of its two endpoints belongs to that scan.
The second branch is deliberately only a localization guard,
NOT a substitute for D2's missing in-scan rank cases. -/
theorem grantDrainD6WarmStepScanDichotomy
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainWarmLabel n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hWarmAt : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true) :
    ((∀ k : Nat,
        k ≤ grantDrainLeftLeaderDistance ring s.native g →
          PPL.shiftLeft ring g k ≠ e ∧
          PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) ∧
      grantDrainWarmRank ring
          (grantDrainStep ring fresh update s e).native g =
        grantDrainWarmRank ring s.native g ∧
      grantDrainChargedWarmRank ring
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label) ≤
        grantDrainChargedWarmRank ring s label ∧
      GrantDrainWarmMergeSpent ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label)) ∨
    (∃ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g ∧
        (PPL.shiftLeft ring g k = e ∨
          PPL.shiftLeft ring g k = ring.rightNeighbor e)) := by
  classical
  by_cases hMeets :
      ∃ k : Nat,
        k ≤ grantDrainLeftLeaderDistance ring s.native g ∧
          (PPL.shiftLeft ring g k = e ∨
            PPL.shiftLeft ring g k = ring.rightNeighbor e)
  · exact Or.inr hMeets
  · have hOutside : ∀ k : Nat,
        k ≤ grantDrainLeftLeaderDistance ring s.native g →
          PPL.shiftLeft ring g k ≠ e ∧
          PPL.shiftLeft ring g k ≠ ring.rightNeighbor e := by
      intro k hk
      constructor
      · intro he
        exact hMeets ⟨k, hk, Or.inl he⟩
      · intro hy
        exact hMeets ⟨k, hk, Or.inr hy⟩
    obtain ⟨hRank, hCharged, hNextInv⟩ :=
      grantDrainD6WarmOutsidePairCase
        ring fresh update s e g label
        hInv hWarm hHost hWarmAt hGrant hOutside
    exact Or.inl ⟨hOutside, hRank, hCharged, hNextInv⟩

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6WarmExceptionalScanContact
#print axioms L3.GrantDrainEntrance.grantDrainD6WarmOutsidePairNoExceptional
#print axioms L3.GrantDrainEntrance.grantDrainD6WarmOutsidePairInvariant
#print axioms L3.GrantDrainEntrance.grantDrainD6WarmOutsidePairFields
#print axioms L3.GrantDrainEntrance.grantDrainD6WarmOutsidePairCase
#print axioms L3.GrantDrainEntrance.grantDrainD6WarmStepScanDichotomy

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Physical contact subrows.

C1: a literal E pair whose two complete native records are unchanged,
    with no FIRE, leaves EVERY native site unchanged, hence the scan.
C2: the inherited first-bullet move gives strict rank drop at k>=1;
    k=0 enters the responder and ends warm.
C3 boundary: the ready-source / responder-at-g LIVE injection ends warm.
C5: the exceptional OLD death spends the unique reserve, and its
    responder belongs to the inclusive OLD scan.
C6: any selected canonical FIRE spends precisely one unit of
    the birth budget. This is NOT a proof of the +1 native-rank bound.
C7: exact source-host and responder-host transition readouts from
    the literal token row, plus the charged-rank expression at a
    continuing host. The missing comparison of rebased W is not assumed.
-/

/-- C1. A pair-local OLD guard on the complete literal native E
output, not an assumed equality of an arbitrary POST scan.
No FIRE is selected, so equality on the two native endpoints
implies full-array equality even if the OLD scan meets this pair. -/
theorem grantDrainD6ContactNoBirthPairFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hNone : grantDrainSelect ring s e = .none)
    (hPair :
      certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e)) =
      (s.native e, s.native (ring.rightNeighbor e))) :
    (grantDrainStep ring fresh update s e).native = s.native ∧
      grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g =
      grantDrainWarmRank ring s.native g := by
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hSource :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).1 = s.native e :=
    congrArg (fun q : CertNative × CertNative => q.1) hPair
  have hTarget :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2 =
          s.native (ring.rightNeighbor e) :=
    congrArg (fun q : CertNative × CertNative => q.2) hPair
  have hNative :
      (grantDrainStep ring fresh update s e).native =
        s.native := by
    rw [grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone]
    funext i
    by_cases hiX : i = e
    · subst i
      simpa [nativeE] using hSource
    · by_cases hiY : i = ring.rightNeighbor e
      · subst i
        simpa [nativeE, hDistinct] using hTarget
      · simp [nativeE, hiX, hiY]
  exact ⟨hNative, by rw [hNative]⟩

/-- C2, positive interior distance: the already-proved genuine
physical first-bullet move is in the OLD contact branch, and
decreases the fixed warm-host W by at least one. -/
theorem grantDrainD6ContactFirstBulletInterior
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
    (∃ j : Nat,
        j ≤ grantDrainLeftLeaderDistance ring s.native g ∧
        (PPL.shiftLeft ring g j = e ∨
          PPL.shiftLeft ring g j = ring.rightNeighbor e)) ∧
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have hRank :=
    grantDrainD6MovePhysicalFirstBulletRank
      ring hn fresh update s e g d k hC hPB hNoBad
      hWarm hGrant hDistance hFirst hk hInterior
      hSource hTo hNone
  refine ⟨?_, hRank⟩
  exact ⟨k + 1, (by rw [hDistance]; omega),
    Or.inl hSource.symm⟩

/-- C2, k=0 boundary: the moved first bullet enters the OLD
warm host g itself. A continuing fixed-g W inequality is
NOT asserted; the actual host is now physically cold. -/
theorem grantDrainD6ContactFirstBulletBoundary
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hEdge : ring.rightNeighbor e = g)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyFollower : (s.native g).l = false)
    (hyEmpty : (s.native g).b = (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    (∃ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native g ∧
      (PPL.shiftLeft ring g j = e ∨
        PPL.shiftLeft ring g j = ring.rightNeighbor e)) ∧
    grantDrainWarmAt (grantDrainStep ring fresh update s e) g =
      false := by
  refine ⟨?_, grantDrainWarmLeftBulletContactPhysical
    ring hn fresh update s e g hEdge hxFollower
    hxBullet hyFollower hyEmpty hNone⟩
  refine ⟨0, Nat.zero_le _, Or.inr ?_⟩
  rw [grantDrainWarmShiftLeftZero]
  exact hEdge.symm

/-- C3, boundary of ready-source F1: native LIVE issuance at
the selected responder (which is g) makes the physical
tracked site cold. The interior F1/F2/F3 cases are already
available as grantDrainD6FireReadySourceRank,
grantDrainD6FireReadyResponderKilledRank, and
grantDrainD6FireReadyResponderSurvivingRank. -/
theorem grantDrainD6ContactReadySourceBoundary
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hEdge : ring.rightNeighbor e = g)
    (hxLeader : (s.native e).l = true)
    (hxReady : (s.native e).sg = true)
    (hyFollower : (s.native g).l = false)
    (hyEmpty : (s.native g).b = (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainWarmAt (grantDrainStep ring fresh update s e) g =
      false := by
  exact grantDrainWarmReadyFrontSourceContactPhysical
    ring hn fresh update s e g hEdge hxLeader hxReady
    hyFollower hyEmpty hNone

/-- C5: a truly exceptional OLD-front death spends the
already-available one-time ghost reserve, and the actual
responder site lies in the inclusive OLD scan.
This is independent of FIRE, fresh REQs and scratch. -/
theorem grantDrainD6ContactExceptionalSpendsReserve
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainWarmLabel n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    label.exceptionalLeft = true ∧
    (grantDrainWarmLabelStep ring fresh update s e
      label).exceptionalLeft = false ∧
    (∃ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g ∧
      PPL.shiftLeft ring g k = ring.rightNeighbor e) := by
  have hReserved :
      label.exceptionalLeft = true :=
    grantDrainD6MergeExceptionalRequiresReserve
      ring s label e g hInv hWarm hHost hExceptional
  have hSpent :
      (grantDrainWarmLabelStep ring fresh update s e
        label).exceptionalLeft = false :=
    grantDrainD6MergeExceptionalConsumesReserve
      ring fresh update s e g label hHost hWarm hExceptional
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  exact ⟨hReserved, hSpent,
    ⟨grantDrainLeftLeaderDistance ring s.native g,
      Nat.le_refl _, hResponder⟩⟩

/-- C6: each physically selected canonical birth consumes one
unit of the remaining prepaid birth allowance. This is
ONLY the ghost half of the +1 rank charge, not the missing
physical birth-in-scan scan comparison. -/
theorem grantDrainD6ContactPhysicalBirthBudget
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    (grantDrainWarmLabelStep ring fresh update s e
        label).birthsLeft = label.birthsLeft - 1 := by
  simp [grantDrainWarmLabelStep, hFire]

/-- The actual source-site token-row grant, read using the real
OLD requests/grants, actual post-E/FIRE native leader flags,
and the actual first-match FIRE choice.  A definition, not
a guessed transport leaf. -/
def grantDrainD6ContactRowSourceGrant
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (s : GrantDrainState n Scratch) (e : Fin n) : Bool :=
  (grantDrainTokenRow
      (s.request e) (s.grant e)
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l
      (fresh s e)
      (grantDrainSelect ring s e)).1.grant

/-- C7 exact charged-rank expression after a continuing host
has been identified by the literal token row. This is a
definitional rank readout, not a statement that rebasing
decreases rank. -/
theorem grantDrainD6ContactContinuingHostRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n) (label : GrantDrainWarmLabel n)
    (hHostNext :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g)
    (hWarmNext :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true)
    (hGrantNext :
      (grantDrainStep ring fresh update s e).grant g = true) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) =
    grantDrainWarmRank ring
      (grantDrainStep ring fresh update s e).native g +
      (grantDrainWarmLabelStep ring fresh update s e
        label).birthsLeft +
      (if (grantDrainWarmLabelStep ring fresh update s e
          label).exceptionalLeft then
        2 * (n - 2) else 0) := by
  simp [grantDrainChargedWarmRank,
    hHostNext, hWarmNext, hGrantNext]

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6ContactNoBirthPairFrame
#print axioms L3.GrantDrainEntrance.grantDrainD6ContactFirstBulletInterior
#print axioms L3.GrantDrainEntrance.grantDrainD6ContactFirstBulletBoundary
#print axioms L3.GrantDrainEntrance.grantDrainD6ContactReadySourceBoundary
#print axioms L3.GrantDrainEntrance.grantDrainD6ContactExceptionalSpendsReserve
#print axioms L3.GrantDrainEntrance.grantDrainD6ContactPhysicalBirthBudget
#print axioms L3.GrantDrainEntrance.grantDrainD6ContactContinuingHostRank

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

theorem grantDrainD6ContactEmptyFollowersNoChange
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hxFollower : (s.native e).l = false)
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hyZero :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g =
      grantDrainWarmRank ring s.native g := by
  have hXEta :
      ({ l := (s.native e).l, b := (s.native e).b,
         sh := (s.native e).sh, sg := (s.native e).sg } :
          CertNative) = s.native e := by
    cases s.native e
    rfl
  have hYEta :
      ({ l := (s.native (ring.rightNeighbor e)).l,
         b := (s.native (ring.rightNeighbor e)).b,
         sh := (s.native (ring.rightNeighbor e)).sh,
         sg := (s.native (ring.rightNeighbor e)).sg } :
          CertNative) = s.native (ring.rightNeighbor e) := by
    cases s.native (ring.rightNeighbor e)
    rfl
  have hX :
      ({ l := false, b := (0 : Fin 3),
         sh := (s.native e).sh, sg := (s.native e).sg } :
          CertNative) = s.native e := by
    cases hc : s.native e with
    | mk l b sh sg =>
        rw [hc] at hxFollower hxEmpty
        change l = false at hxFollower
        change b = 0 at hxEmpty
        subst hxFollower
        subst hxEmpty
        rfl
  have hY :
      ({ l := false, b := (0 : Fin 3),
         sh := (s.native (ring.rightNeighbor e)).sh,
         sg := false } : CertNative) =
          s.native (ring.rightNeighbor e) := by
    cases hc : s.native (ring.rightNeighbor e) with
    | mk l b sh sg =>
        rw [hc] at hyFollower hyEmpty hyZero
        change l = false at hyFollower
        change b = 0 at hyEmpty
        change sg = false at hyZero
        subst hyFollower
        subst hyEmpty
        subst hyZero
        rfl
  have hPair :
      certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e)) =
        (s.native e, s.native (ring.rightNeighbor e)) := by
    simpa [certLiteralEPair, hxFollower, hyFollower,
      hxEmpty, hyEmpty, hyZero, certFinThree] using
        (And.intro hX hY)
  exact (grantDrainD6ContactNoBirthPairFrame
    ring hn fresh update s e g hNone hPair).2

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

theorem grantDrainD6ContactHostAtSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hHost : label.host = some e) :
    (grantDrainWarmLabelStep ring fresh update s e
       label).host =
      if grantDrainD6ContactRowSourceGrant ring fresh s e
        then some e else none := by
  simp [grantDrainWarmLabelStep,
    grantDrainD6ContactRowSourceGrant, hHost] <;>
    (split <;> rename_i h <;> simp [h])

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

theorem grantDrainD6ContactHostAtResponder
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hHost : label.host = some (ring.rightNeighbor e)) :
    (grantDrainWarmLabelStep ring fresh update s e
        label).host =
      if grantDrainSelect ring s e = .rightLocal ∨
          grantDrainSelect ring s e = .cross ∨
          (grantDrainNativeNext ring s e e).l = true ∨
          (grantDrainNativeNext ring s e
            (ring.rightNeighbor e)).l = true
        then none
      else if s.request (ring.rightNeighbor e) &&
          s.grant (ring.rightNeighbor e)
        then some (ring.rightNeighbor e)
      else if grantDrainD6ContactRowSourceGrant ring fresh s e
        then some e else none := by
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  simp [grantDrainWarmLabelStep,
    grantDrainD6ContactRowSourceGrant, hHost, hDistinct] <;>
    (repeat (split <;> try rfl)) <;> rfl

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

theorem grantDrainD6ContactIncomingGrantMovesHost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hUnheld : s.request (ring.rightNeighbor e) = false)
    (hGrant : s.grant (ring.rightNeighbor e) = true)
    (hNone : grantDrainSelect ring s e = .none)
    (hxFollower : (grantDrainNativeNext ring s e e).l = false)
    (hyFollower :
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l = false) :
    (grantDrainWarmLabelStep ring fresh update s e
       label).host = some e ∧
    (grantDrainStep ring fresh update s e).grant e = true := by
  have hRow :
      grantDrainD6ContactRowSourceGrant ring fresh s e =
        true := by
    unfold grantDrainD6ContactRowSourceGrant
    rw [hUnheld, hGrant, hxFollower, hyFollower, hNone]
    cases hRx : s.request e <;>
      cases hGx : s.grant e <;>
      cases hFresh : fresh s e <;>
      (unfold grantDrainTokenRow; decide)
  have hHostNext :=
    grantDrainD6ContactHostAtResponder ring hn
      fresh update s e label hHost
  have hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some e := by
    rw [hHostNext]
    simp [hNone, hxFollower, hyFollower, hUnheld, hRow]
  have hNewGrant :
      (grantDrainStep ring fresh update s e).grant e = true := by
    simpa [grantDrainStep, grantDrainD6ContactRowSourceGrant]
      using hRow
  exact ⟨hNewHost, hNewGrant⟩

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- S1/S2 physical primitive: the native step really is E
followed by zero or one canonicalBirth at one selected endpoint. -/
theorem grantDrainD6CompositeNativeCases
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    (grantDrainStep ring fresh update s e).native =
        nativeE ring s.native e ∨
    (grantDrainStep ring fresh update s e).native =
        canonicalBirth (nativeE ring s.native e) e ∨
    (grantDrainStep ring fresh update s e).native =
        canonicalBirth (nativeE ring s.native e)
          (ring.rightNeighbor e) := by
  change
    grantDrainNativeNext ring s e = nativeE ring s.native e ∨
    grantDrainNativeNext ring s e =
        canonicalBirth (nativeE ring s.native e) e ∨
    grantDrainNativeNext ring s e =
        canonicalBirth (nativeE ring s.native e)
          (ring.rightNeighbor e)
  cases hf : grantDrainSelect ring s e with
  | none =>
      exact Or.inl (by simp [grantDrainNativeNext, hf])
  | leftLocal =>
      exact Or.inr (Or.inl
        (by simp [grantDrainNativeNext, hf]))
  | rightLocal =>
      exact Or.inr (Or.inr
        (by simp [grantDrainNativeNext, hf]))
  | cross =>
      exact Or.inr (Or.inl
        (by simp [grantDrainNativeNext, hf]))

/-- A canonical left/cross birth really overwrites the source
with a leader, hence that *physical site* is no longer warm. -/
theorem grantDrainD6CompositeSourceBirthEndsWarm
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFire :
      grantDrainSelect ring s e = .leftLocal ∨
        grantDrainSelect ring s e = .cross) :
    grantDrainWarmAt
      (grantDrainStep ring fresh update s e) e = false := by
  have hLeader :
      ((grantDrainStep ring fresh update s e).native e).l =
        true := by
    change (grantDrainNativeNext ring s e e).l = true
    rcases hFire with hLeft | hCross
    · simp [grantDrainNativeNext, hLeft,
        canonicalBirth, firedNative]
    · simp [grantDrainNativeNext, hCross,
        canonicalBirth, firedNative]
  simp [grantDrainWarmAt, hLeader]

/-- A canonical right-local birth makes the responder the new
leader, so a surviving label cannot be warm *at that site*. -/
theorem grantDrainD6CompositeResponderBirthEndsWarm
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFire : grantDrainSelect ring s e = .rightLocal) :
    grantDrainWarmAt
      (grantDrainStep ring fresh update s e)
        (ring.rightNeighbor e) = false := by
  have hLeader :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = true := by
    change (grantDrainNativeNext ring s e
      (ring.rightNeighbor e)).l = true
    simp [grantDrainNativeNext, hFire,
      canonicalBirth, firedNative]
  simp [grantDrainWarmAt, hLeader]

/-- S2: a ready leader serving an empty follower cannot execute
any canonical FIRE on that edge, regardless of old requests/grants.
E leaves the source a leader and creates a LIVE at the follower;
both post-E eligibility tests are false. -/
theorem grantDrainD6CompositeReadySourceNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hxLeader : (s.native e).l = true)
    (hxReady : (s.native e).sg = true)
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hyEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3)) :
    grantDrainSelect ring s e = .none := by
  have hDifferent : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hSourceLeader :
      (nativeE ring s.native e e).l = true := by
    have hPair :=
      grantDrainEntranceLiteralESourceLeaderFixed
        (s.native e) (s.native (ring.rightNeighbor e))
    simpa [nativeE, hxLeader] using hPair
  have hTargetBullet :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).b = (2 : Fin 3) := by
    have hPair :=
      grantDrainEntranceReadySourceGeneralPairERow
        (s.native e) (s.native (ring.rightNeighbor e))
        hxLeader hxReady hyFollower hyEmpty
    simpa [nativeE, hDifferent] using hPair.2.1
  have hSourceIneligible :
      grantDrainEligible (nativeE ring s.native e) e =
        false := by
    simp [grantDrainEligible, hSourceLeader]
  have hTargetIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hTargetBullet]
  simp [grantDrainSelect, hSourceIneligible,
    hTargetIneligible]

/-- S2/F1 with no no-FIRE hypothesis: C_native and the old
ready-source sector imply the empty follower pair. In particular
a canonical FIRE is impossible, so the merged F1 physical rank
drop is available with no post-E sector premise. -/
theorem grantDrainD6CompositeReadySourceRank
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
      PPL.shiftLeft ring g (a - 1)) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have hOne : ring.rightNeighbor e =
      PPL.shiftRight ring e 1 := rfl
  have hFollower :
      (s.native (ring.rightNeighbor e)).l = false := by
    rw [hOne]
    exact hSector.2.2.2
      (⟨1, show 1 < n by omega⟩ : Fin n)
      (show 0 < 1 by decide) (by (try dsimp only at *); omega)
  have hLocal : GrantDrainEntranceILocal ring s.native :=
    (grantDrainEntranceIffILocal ring s.native).mp hC.1
  have hNoBullet :
      ¬ HasBullet s.native (ring.rightNeighbor e) := by
    rw [hOne]
    exact grantDrainEntranceReadyLeaderSectorBulletFree
      ring s.native e D hLocal hSector hReady
      (⟨1, show 1 < n by omega⟩ : Fin n)
      (by (try dsimp only at *); omega)
  have hEmpty :
      (s.native (ring.rightNeighbor e)).b =
        (0 : Fin 3) := by
    by_cases hb :
        (s.native (ring.rightNeighbor e)).b = (0 : Fin 3)
    · exact hb
    · exact False.elim (hNoBullet hb)
  have hNoFire :=
    grantDrainD6CompositeReadySourceNoFire
      ring hn s e hSector.2.1 hReady hFollower hEmpty
  exact (grantDrainD6FireReadySourceRank
    ring hn fresh update s e g D a hC hPB hNoBad
    hWarm hGrant hSector hAt ha haInside hDistance
    hReady hTo hNoFire).2.2

/-- S2: a ready responder always emits a DUMMY on native E.
The responder cannot be a canonical birth site on that service,
whether the old leader survives or is killed. -/
theorem grantDrainD6CompositeReadyResponderNotRightFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true) :
    grantDrainSelect ring s e ≠ .rightLocal := by
  have hDummy :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).b = (1 : Fin 3) :=
    grantDrainEntranceNativeEReadyVictimBulletDummy
      ring (by omega : 2 ≤ n) s.native e hyLeader hyReady
  have hIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hDummy]
  exact grantDrainEntranceResponderIneligibleNoRightFire
    ring s e hIneligible

/-- In the ready-responder row, zero OLD source request also
disables leftLocal/cross, while the emitted DUMMY disables
rightLocal. Thus this OLD guard gives a truly E-only physical step. -/
theorem grantDrainD6CompositeReadyResponderNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hxNoRequest : s.request e = false) :
    grantDrainSelect ring s e = .none := by
  have hDummy :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).b = (1 : Fin 3) :=
    grantDrainEntranceNativeEReadyVictimBulletDummy
      ring (by omega : 2 ≤ n) s.native e hyLeader hyReady
  have hIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hDummy]
  simp [grantDrainSelect, hxNoRequest, hIneligible]

/-- S2/F2. On an incoming LIVE-killer ready-responder contact,
if the source has no OLD request, FIRE is absent automatically.
The existing merged physical F2 rank-drop theorem then applies. -/
theorem grantDrainD6CompositeReadyResponderKilledRank
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
    (hxNoRequest : s.request e = false) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have hNoFire :=
    grantDrainD6CompositeReadyResponderNoFire
      ring hn s e (by rw [hTo]; exact hSector.2.1)
      (by rw [hTo]; exact hReady) hxNoRequest
  exact (grantDrainD6FireReadyResponderKilledRank
    ring hn fresh update s e p g D a hC hPB hNoBad
    hWarm hGrant hSector hAt ha haInside hDistance
    hReady hTo hXL hXB hNoFire).2.2.2.2

/-- S2/F3. A surviving ready responder with no OLD source
request also has no canonical FIRE; its emitted DUMMY is the
first left bullet and the merged physical F3 rank drops. -/
theorem grantDrainD6CompositeReadyResponderSurvivingRank
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
    (hxNoRequest : s.request e = false) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have hNoFire :=
    grantDrainD6CompositeReadyResponderNoFire
      ring hn s e (by rw [hTo]; exact hSector.2.1)
      (by rw [hTo]; exact hReady) hxNoRequest
  exact (grantDrainD6FireReadyResponderSurvivingRank
    ring hn fresh update s e p g D a hC hPB hNoBad
    hWarm hGrant hSector hAt ha haInside hDistance
    hReady hTo hSourceNotEmitting hSourceNotLive hNoFire).2.2.2.2

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6ContactEmptyFollowersNoChange
#print axioms L3.GrantDrainEntrance.grantDrainD6ContactHostAtSource
#print axioms L3.GrantDrainEntrance.grantDrainD6ContactHostAtResponder
#print axioms L3.GrantDrainEntrance.grantDrainD6ContactIncomingGrantMovesHost
#print axioms L3.GrantDrainEntrance.grantDrainD6CompositeNativeCases
#print axioms L3.GrantDrainEntrance.grantDrainD6CompositeSourceBirthEndsWarm
#print axioms L3.GrantDrainEntrance.grantDrainD6CompositeResponderBirthEndsWarm
#print axioms L3.GrantDrainEntrance.grantDrainD6CompositeReadySourceNoFire
#print axioms L3.GrantDrainEntrance.grantDrainD6CompositeReadySourceRank
#print axioms L3.GrantDrainEntrance.grantDrainD6CompositeReadyResponderNotRightFire
#print axioms L3.GrantDrainEntrance.grantDrainD6CompositeReadyResponderNoFire
#print axioms L3.GrantDrainEntrance.grantDrainD6CompositeReadyResponderKilledRank
#print axioms L3.GrantDrainEntrance.grantDrainD6CompositeReadyResponderSurvivingRank

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
The requested unconditional s1 numerical claim is FALSE even
with C_native, PPlus, NoBadLive, a surviving, continuing warm
grant, an actual selected source FIRE, and a positive prepaid
birth budget.

In the exact n=5 witness below, E first kills a quiet,
unshielded old front. The full rank goes 3 -> 9.
On the SAME service an eligible .leftLocal FIRE creates a
canonical leader immediately behind the dead front. The
composite rank is 5. Thus 5 > 3+1. The one-time exceptional
reserve pays for this additional change. Consequently an
s1 theorem with only a +1 birth charge cannot be used in the
exceptional-death subcase. The numerical bound must include
the exceptional term, or s1 must exclude the exceptional guard.

A concrete two-leader SS/PB cut is proved here. No scheduler
word from a one-leader predecessor is asserted.
-/

/-- Reuse the exact five-site native death configuration.
Only the OLD request/grant owner differs from the no-FIRE
witness: at site 2 a request and a grant authorize source FIRE,
while the old warm tracked grant at site 4 is retained. -/
def grantDrainD6ExceptionalBirthState :
    GrantDrainState 5 Unit :=
  { native := grantDrainD6DeathWitnessNative false
    request := fun i => i.val == 2
    grant := fun i => i.val == 2 || i.val == 4
    scratch := ()
    history := [] }

def grantDrainD6ExceptionalBirthAfter :
    GrantDrainState 5 Unit :=
  grantDrainStep grantDrainD6DeathWitnessRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainD6ExceptionalBirthState (2 : Fin 5)

def grantDrainD6ExceptionalBirthLabel :
    GrantDrainWarmLabel 5 :=
  grantDrainD6MergeInitialLabel (4 : Fin 5) true 5

def grantDrainD6ExceptionalBirthLabelAfter :
    GrantDrainWarmLabel 5 :=
  grantDrainWarmLabelStep grantDrainD6DeathWitnessRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainD6ExceptionalBirthState (2 : Fin 5)
    grantDrainD6ExceptionalBirthLabel

/-- The same OLD native tuple as the already-merged
grantDrainD6DeathWitnessAdmissible false. In particular its
two-leader cut is genuinely peaceful, settled and contains
no nonleftmost bad LIVE. The new token owner has no bearing
on these three native predicates. -/
theorem grantDrainD6ExceptionalBirthAdmissible :
    PPlus grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthState.native ∧
    C_native grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthState.native ∧
    GrantDrainEntranceNoBadLive grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthState := by
  have hOld := grantDrainD6DeathWitnessAdmissible false
  exact ⟨hOld.1, hOld.2.1, hOld.2.2.1⟩

/-- A true physical E-then-FIRE service, not an invented
native pair. At e=2, the source LIVE is consumed killing
the old unshielded leader at 3; source now has empty bullet
and is eligible for leftLocal FIRE. The new leader at 2
leaves the tracked grant at 4 warm. The strict s1
inequality W_new <= W_old+1 fails: 5 > 3+1.

The displayed 3 -> 9 -> 5 gives separately the native-E
exceptional jump and the subsequent canonical birth effect.
The ghost spends its birth allowance and exceptional reserve.
All propositions below are closed five-site calculations. -/
theorem grantDrainD6ExceptionalBirthCounter :
    grantDrainSelect grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthState
      (2 : Fin 5) = .leftLocal ∧
    grantDrainExceptionalDeath grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthState
      (2 : Fin 5) (4 : Fin 5) = true ∧
    grantDrainWarmAt grantDrainD6ExceptionalBirthState
      (4 : Fin 5) = true ∧
    grantDrainD6ExceptionalBirthState.grant (4 : Fin 5) =
      true ∧
    grantDrainWarmAt grantDrainD6ExceptionalBirthAfter
      (4 : Fin 5) = true ∧
    grantDrainD6ExceptionalBirthLabelAfter.host =
      some (4 : Fin 5) ∧
    grantDrainD6ExceptionalBirthLabelAfter.warm = true ∧
    grantDrainD6ExceptionalBirthLabelAfter.exceptionalLeft =
      false ∧
    grantDrainD6ExceptionalBirthLabelAfter.birthsLeft = 4 ∧
    grantDrainWarmRank grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthState.native
      (4 : Fin 5) = 3 ∧
    grantDrainWarmRank grantDrainD6DeathWitnessRing
      (nativeE grantDrainD6DeathWitnessRing
        grantDrainD6ExceptionalBirthState.native (2 : Fin 5))
      (4 : Fin 5) = 9 ∧
    grantDrainWarmRank grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthAfter.native
      (4 : Fin 5) = 5 ∧
    ¬ (grantDrainWarmRank grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthAfter.native (4 : Fin 5) ≤
      grantDrainWarmRank grantDrainD6DeathWitnessRing
        grantDrainD6ExceptionalBirthState.native
        (4 : Fin 5) + 1) ∧
    grantDrainWarmRank grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthAfter.native (4 : Fin 5) ≤
      grantDrainWarmRank grantDrainD6DeathWitnessRing
        grantDrainD6ExceptionalBirthState.native
        (4 : Fin 5) + 1 + 2 * (5 - 2) := by
  unfold grantDrainD6ExceptionalBirthAfter
    grantDrainD6ExceptionalBirthLabelAfter
    grantDrainD6ExceptionalBirthLabel
    grantDrainD6ExceptionalBirthState
    grantDrainD6DeathWitnessNative
    grantDrainD6DeathWitnessRing
    grantDrainD6MergeInitialLabel
    grantDrainExceptionalDeath
    grantDrainWarmRank
    grantDrainLeftLeaderDistance
    grantDrainLeftBulletDistance
    grantDrainTerminalRun
  decide

/-- The corresponding corrected *numerical* five-site
control. Both independently consumed credits must be counted;
the full charged ghost does not rise on this false-to-s1
counterexample. -/
theorem grantDrainD6ExceptionalBirthChargedControl :
    grantDrainChargedWarmRank grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthAfter
      grantDrainD6ExceptionalBirthLabelAfter ≤
    grantDrainChargedWarmRank grantDrainD6DeathWitnessRing
      grantDrainD6ExceptionalBirthState
      grantDrainD6ExceptionalBirthLabel := by
  unfold grantDrainD6ExceptionalBirthAfter
    grantDrainD6ExceptionalBirthLabelAfter
    grantDrainD6ExceptionalBirthLabel
    grantDrainD6ExceptionalBirthState
    grantDrainD6DeathWitnessNative
    grantDrainD6DeathWitnessRing
    grantDrainD6MergeInitialLabel
    grantDrainChargedWarmRank
    grantDrainWarmRank
    grantDrainLeftLeaderDistance
    grantDrainLeftBulletDistance
    grantDrainTerminalRun
  decide

/-!
s2: ready-responder FIRE with an eligible source.  This
does not depend on the (false) unconditional s1 theorem.
The first-match selector cannot choose rightLocal because
native E necessarily puts DUMMY at the old ready responder.
Any selected FIRE therefore births at the source e.
-/

/-- All old ready-responder FIRE choices are precisely
leftLocal or cross: rightLocal is forbidden by the actual
post-E DUMMY, and none is excluded by the OLD selector guard. -/
theorem grantDrainD6ReadyResponderFireAtSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    grantDrainSelect ring s e = .leftLocal ∨
      grantDrainSelect ring s e = .cross := by
  have hNoRight :=
    grantDrainD6CompositeReadyResponderNotRightFire
      ring hn s e hyLeader hyReady
  cases hf : grantDrainSelect ring s e with
  | none =>
      exact False.elim (hFire hf)
  | leftLocal =>
      exact Or.inl rfl
  | rightLocal =>
      exact False.elim (hNoRight hf)
  | cross =>
      exact Or.inr rfl

/-- Exact physical native projection in the simultaneous
ready-responder/fire branch. Every such FIRE overwrites the
source and only the source with the canonical born tuple. -/
theorem grantDrainD6ReadyResponderSourceFireNative
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    (grantDrainStep ring fresh update s e).native =
      canonicalBirth (nativeE ring s.native e) e := by
  have hChoice :=
    grantDrainD6ReadyResponderFireAtSource
      ring hn s e hyLeader hyReady hFire
  change grantDrainNativeNext ring s e =
    canonicalBirth (nativeE ring s.native e) e
  rcases hChoice with hLeft | hCross
  · simp [grantDrainNativeNext, hLeft]
  · simp [grantDrainNativeNext, hCross]

/-- Even when the ready responder dies under an incoming LIVE
and the source is immediately reborn, the DUMMY placed by E
at the responder is not overwritten by the source FIRE.
This is the actual physical retained-bullet fact needed by
the surviving/dead F3/F2 scan geometry. -/
theorem grantDrainD6ReadyResponderSourceFireRetainsDummy
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).b = (1 : Fin 3) := by
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPair :=
    grantDrainD6MergeReadyResponderDummyPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hyLeader hyReady
  have hE :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).b = (1 : Fin 3) := by
    simpa [nativeE, hDistinct] using hPair.2.1
  have hBorn :=
    grantDrainD6ReadyResponderSourceFireNative
      ring hn fresh update s e hyLeader hyReady hFire
  rw [hBorn]
  simpa [canonicalBirth, hDistinct] using hE

/-!
s4: a restricted but genuinely physical moving-host scan
transfer, for the empty-follower E row with no canonical FIRE.
The OLD first leader distance 2 <= d < n is a checkable OLD
warm-scan guard, not a post-state scan hypothesis.

This proves the missing composition:
W(nativeE, e)+1 <= W(nativeE, y) <= W(old, y),
where y = rightNeighbor e is the OLD tracked grant host.
The real token owner then moves the warm grant from y to e.
-/

/-- A real no-FIRE incoming Y-to-X grant movement with two
empty old follower endpoints has strict warm-rank progress
at the NEW physical host. Nothing about the E-state scan,
its terminal run, or its first bullet is assumed; all are
derived from OLD pair fields and the OLD first-leader scan. -/
theorem grantDrainD6MovingHostEmptyFollowerRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (d : Nat)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hUnheld : s.request (ring.rightNeighbor e) = false)
    (hGrant : s.grant (ring.rightNeighbor e) = true)
    (hWarm :
      grantDrainWarmAt s (ring.rightNeighbor e) = true)
    (hOldDistance :
      grantDrainLeftLeaderDistance ring s.native
        (ring.rightNeighbor e) = d)
    (hd : 2 ≤ d) (hdShort : d < n)
    (hxFollower : (s.native e).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hyEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    (grantDrainWarmLabelStep ring fresh update s e
      label).host = some e ∧
    grantDrainWarmRank ring
      (grantDrainStep ring fresh update s e).native e + 1 ≤
    grantDrainWarmRank ring s.native
      (ring.rightNeighbor e) := by
  have hE :=
    grantDrainWarmEmptyFollowerSignalCopyNativeE
      ring s.native e hxFollower hxEmpty hyFollower hyEmpty
  have hOldFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native (ring.rightNeighbor e) d
      (by omega) hdShort).mp hOldDistance
  have hLeader : ∀ i : Fin n,
      (nativeE ring s.native e i).l = (s.native i).l := by
    intro i
    exact (hE i).1
  have hBullet : ∀ i : Fin n,
      (nativeE ring s.native e i).b = (s.native i).b := by
    intro i
    exact (hE i).2.1
  have hSignal : ∀ i : Fin n,
      (s.native i).sg = true →
      (nativeE ring s.native e i).sg = true := by
    intro i
    exact (hE i).2.2.1
  have hFrontSignal :
      (nativeE ring s.native e
        (PPL.shiftLeft ring (ring.rightNeighbor e) d)).sg =
      (s.native
        (PPL.shiftLeft ring (ring.rightNeighbor e) d)).sg :=
    (hE (PPL.shiftLeft ring (ring.rightNeighbor e) d)).2.2.2
      hOldFirst.1
  have hOldToE :
      grantDrainWarmRank ring (nativeE ring s.native e)
          (ring.rightNeighbor e) ≤
        grantDrainWarmRank ring s.native
          (ring.rightNeighbor e) :=
    grantDrainWarmSignalExpansionRank
      ring s.native (nativeE ring s.native e)
      (ring.rightNeighbor e)
      hLeader hBullet (by rw [hOldDistance]; exact hFrontSignal) hSignal
  have hNewDistance :
      grantDrainLeftLeaderDistance ring
        (nativeE ring s.native e) (ring.rightNeighbor e) =
          d := by
    apply (grantDrainWarmLeaderFirstCharacterization
      ring (nativeE ring s.native e)
      (ring.rightNeighbor e) d (by omega) hdShort).mpr
    constructor
    · rw [hLeader]
      exact hOldFirst.1
    · intro k hk hkd
      rw [hLeader]
      exact hOldFirst.2 k hk hkd
  have hOldSignal :
      (s.native (ring.rightNeighbor e)).sg = true := by
    cases hs : (s.native (ring.rightNeighbor e)).sg with
    | true =>
        rfl
    | false =>
        simp [grantDrainWarmAt, hs] at hWarm
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPair :=
    grantDrainWarmEmptyFollowerSignalCopyPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hxFollower hxEmpty hyFollower hyEmpty
  have hResponderE :
      nativeE ring s.native e (ring.rightNeighbor e) =
        s.native (ring.rightNeighbor e) := by
    simpa [nativeE, hDistinct] using hPair.2.2.2
  have hNewSignal :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).sg = true := by
    rw [hResponderE]
    exact hOldSignal
  have hNewSourceBullet :
      (nativeE ring s.native e e).b = (0 : Fin 3) := by
    rw [hBullet]
    exact hxEmpty
  have hFirstBulletNotAdjacent :
      ∀ p : Nat,
        grantDrainLeftBulletDistance ring
          (nativeE ring s.native e)
          (ring.rightNeighbor e) d = some p →
          2 ≤ p := by
    intro p hp
    have hFacts :=
      (grantDrainWarmBulletSomeCharacterization
        ring (nativeE ring s.native e)
        (ring.rightNeighbor e) d p).mp hp
    by_cases hpOne : p = 1
    · have hIndex :
          PPL.shiftLeft ring (ring.rightNeighbor e) p = e := by
        rw [hpOne]
        exact grantDrainWarmRightNeighborLeftOne ring hn e
      have hZero :
          (nativeE ring s.native e
            (PPL.shiftLeft ring
              (ring.rightNeighbor e) p)).b.val = 0 := by
        rw [hIndex, hNewSourceBullet]
        rfl
      exact False.elim (hFacts.2.2.1 hZero)
    · omega
  have hRebase :
      grantDrainWarmRank ring (nativeE ring s.native e) e +
          1 ≤
        grantDrainWarmRank ring (nativeE ring s.native e)
          (ring.rightNeighbor e) := by
    have h :=
      grantDrainWarmIncomingRebaseRank
        ring hn (nativeE ring s.native e)
        (ring.rightNeighbor e) d
        (grantDrainTerminalRun ring (nativeE ring s.native e)
          (ring.rightNeighbor e) d)
        hd hdShort hNewDistance hNewSignal rfl
        hFirstBulletNotAdjacent
    rw [grantDrainWarmRightNeighborLeftOne ring hn e] at h
    exact h
  have hN :
      grantDrainNativeNext ring s e = nativeE ring s.native e := by
    simp [grantDrainNativeNext, hNone]
  have hxNext :
      (grantDrainNativeNext ring s e e).l = false := by
    rw [hN, hLeader]
    exact hxFollower
  have hyNext :
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l = false := by
    rw [hN, hLeader]
    exact hyFollower
  obtain ⟨hHostNext, _⟩ :=
    grantDrainD6ContactIncomingGrantMovesHost
      ring hn fresh update s e label hHost hUnheld hGrant
      hNone hxNext hyNext
  refine ⟨hHostNext, ?_⟩
  calc
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native e + 1 =
        grantDrainWarmRank ring (nativeE ring s.native e) e + 1 := by
          rw [grantDrainWarmPhysicalNoBirthNative
            ring fresh update s e hNone]
    _ ≤ grantDrainWarmRank ring (nativeE ring s.native e)
          (ring.rightNeighbor e) := hRebase
    _ ≤ grantDrainWarmRank ring s.native
          (ring.rightNeighbor e) := hOldToE

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalBirthAdmissible
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalBirthCounter
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalBirthChargedControl
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderFireAtSource
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderSourceFireNative
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderSourceFireRetainsDummy
#print axioms L3.GrantDrainEntrance.grantDrainD6MovingHostEmptyFollowerRank

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- D6-PAIR-SCAN, nonexceptional branch: the literal selected FIRE
creates exactly one canonical leader at one of the physical pair
endpoints. The E result is evaluated before the birth. -/
theorem grantDrainD6SelectedBirthAtPair
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    ∃ z : Fin n,
      (z = e ∨ z = ring.rightNeighbor e) ∧
      grantDrainNativeNext ring s e =
        canonicalBirth (nativeE ring s.native e) z := by
  cases hsel : grantDrainSelect ring s e with
  | none =>
      simp [hsel] at hFire
  | leftLocal =>
      refine ⟨e, Or.inl rfl, ?_⟩
      simp only [grantDrainNativeNext, hsel]
  | rightLocal =>
      refine ⟨ring.rightNeighbor e, Or.inr rfl, ?_⟩
      simp only [grantDrainNativeNext, hsel]
  | cross =>
      refine ⟨e, Or.inl rfl, ?_⟩
      simp only [grantDrainNativeNext, hsel]

/-- No exceptional death: in the only dangerous old front
configuration (unshielded, quiet, no old left bullet), the
literal native E step cannot delete that front leader.
This is a direct consequence of the OLD guard, not a
hypothesis about a post-step scan. -/
theorem grantDrainD6NonExceptionalQuietFrontSurvivesE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hNoExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hOldLeader :
      (s.native (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))).l =
          true)
    (hUnshielded :
      (s.native (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))).sh =
          false)
    (hQuiet :
      (s.native (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))).sg =
          false)
    (hNoBullet :
      grantDrainLeftBulletDistance ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) = none) :
    (nativeE ring s.native e
      (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))).l =
        true := by
  cases hnew :
      (nativeE ring s.native e
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))).l with
  | true =>
      rfl
  | false =>
      have hExceptional :
          grantDrainExceptionalDeath ring s e g = true := by
        simp [grantDrainExceptionalDeath, hOldLeader,
          hUnshielded, hQuiet, hNoBullet, hnew]
      have hcontradiction : false = true :=
        hNoExceptional.symm.trans hExceptional
      cases hcontradiction

/-- The complete physical selected-FIRE subcase whose two
endpoints miss the inclusive OLD warm scan. This is stronger
than the required +1 lift: the rank is EXACTLY unchanged.
No post-E equality or rank comparison is assumed. -/
theorem grantDrainD6NonExceptionalSelectedOutsideScan
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n)
    (_hFire : grantDrainSelect ring s e ≠ .none)
    (hOutside : ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g k ≠ e ∧
        PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) :
    grantDrainExceptionalDeath ring s e g = false ∧
    grantDrainWarmRank ring
      (grantDrainNativeNext ring s e) g =
        grantDrainWarmRank ring s.native g ∧
    grantDrainWarmRank ring
      (grantDrainNativeNext ring s e) g ≤
        grantDrainWarmRank ring s.native g + 1 := by
  have hNoException :=
    grantDrainD6WarmOutsidePairNoExceptional
      ring s e g hOutside
  have hRank :=
    grantDrainWarmOutsidePairScanFrame
      ring fresh update s e g hOutside
  change grantDrainWarmRank ring
    (grantDrainNativeNext ring s e) g =
      grantDrainWarmRank ring s.native g at hRank
  refine ⟨hNoException, hRank, ?_⟩
  rw [hRank]
  exact Nat.le_succ _

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6SelectedBirthAtPair
#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalQuietFrontSurvivesE
#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalSelectedOutsideScan

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
s1x: the five-site exceptional E+source-FIRE counterexample obeys
the paper's *charged* bound, and all-n exceptional events with
a selected FIRE spend both prescribed ghost credits. The all-n
exceptional *numeric* bound is not proved here.

s2: a same-service source FIRE at a ready responder is handled
directly from OLD C_native/sector/request guards. No post-step
rank/scan assumption and no impossible no-FIRE assumption are used.
The proof treats killed and surviving responders uniformly.
-/

/-- The corrected exceptional bound on the exact physical
counterexample: 3 -> 9 -> 5. Its ghost spends the reserve. -/
theorem grantDrainD6ExceptionalBirthChargedBoundAndSpend :
    grantDrainWarmRank grantDrainD6DeathWitnessRing
        grantDrainD6ExceptionalBirthAfter.native (4 : Fin 5) ≤
      grantDrainWarmRank grantDrainD6DeathWitnessRing
        grantDrainD6ExceptionalBirthState.native (4 : Fin 5) +
        2 * (5 - 2) + 1 ∧
    grantDrainD6ExceptionalBirthLabelAfter.exceptionalLeft =
      false := by
  unfold grantDrainD6ExceptionalBirthAfter
    grantDrainD6ExceptionalBirthLabelAfter
    grantDrainD6ExceptionalBirthLabel
    grantDrainD6ExceptionalBirthState
    grantDrainD6DeathWitnessNative
    grantDrainD6DeathWitnessRing
    grantDrainD6MergeInitialLabel
    grantDrainWarmRank
    grantDrainLeftLeaderDistance
    grantDrainLeftBulletDistance
    grantDrainTerminalRun
  decide

/-- Regardless of which FIRE port was selected, a true OLD
exceptional-death test with a legitimate warm ghost expends
the unique reserve. A simultaneous FIRE expends one birth credit.
This is a physical-step theorem, not an assumed numerical leaf. -/
theorem grantDrainD6ExceptionalBirthCredits
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    label.exceptionalLeft = true ∧
    (grantDrainWarmLabelStep ring fresh update s e
      label).exceptionalLeft = false ∧
    (grantDrainWarmLabelStep ring fresh update s e
      label).birthsLeft = label.birthsLeft - 1 := by
  obtain ⟨hAvailable, hSpent, _⟩ :=
    grantDrainD6ContactExceptionalSpendsReserve
      ring fresh update s e g label
      hInv hWarm hHost hExceptional
  exact ⟨hAvailable, hSpent,
    grantDrainD6ContactPhysicalBirthBudget
      ring fresh update s e label hFire⟩

/-- Public version of the ready-sector prefix calculation.
The similarly named helper is private in GrantDrainDummy
and cannot be referenced from this downstream file. -/
theorem grantDrainD6ReadyResponderWarmPrefix
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
    have hBound := D.isLt
    omega
  rcases hC.2 p D hSector with hOccupied | hEmpty
  · obtain ⟨q, _, _, hTrail, _⟩ := hOccupied
    have hZero :
        (N (PPL.shiftRight ring p 0)).sg = false :=
      hTrail (⟨0, ring.hn⟩ : Fin n) (Nat.zero_le _)
    rw [grantDrainWeakDeathShiftRightZero ring p,
      hReady] at hZero
    cases hZero
  · obtain ⟨hNoBullet, _, hBody⟩ := hEmpty
    constructor
    · intro j hj
      have hArc :
          PPL.shiftLeft ring g j =
            PPL.shiftRight ring p (a - j) := by
        rw [hAt]
        exact grantDrainMarksArcShiftLeftRight
          ring p a j (by omega) haN
      rw [hArc]
      exact hBody hReady
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
      · exact False.elim
          (hNoBullet
            (⟨a - j, show a - j < n by omega⟩ : Fin n)
            (show a - j < D.val by omega) hb)

/-- F2/F3 with simultaneous source FIRE:
the responder's literal E DUMMY is still the first left bullet
after the canonical birth at e. The old ready sector has no
earlier bullet and has signal one on the full g-to-p interior.
Even if p is killed, the first-bullet branch yields W'=a,
whereas OLD W=1+a. Thus the source FIRE does not erase the
strict progress; no post-state scan is hypothesized. -/
theorem grantDrainD6ReadyResponderSourceFireRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hSector : sectorLength ring s.native p D)
    (hAt : g = PPL.shiftRight ring p a)
    (ha : 1 ≤ a) (haInside : a < D.val)
    (hDistance :
      grantDrainLeftLeaderDistance ring s.native g = a)
    (hReady : (s.native p).sg = true)
    (hTo : ring.rightNeighbor e = p)
    (hSourceRequest : s.request e = true)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have haN : a < n := by
    have hBound := D.isLt
    omega
  have hFront :
      PPL.shiftLeft ring g a = p := by
    rw [hAt]
    rw [grantDrainMarksArcShiftLeftRight
      ring p a a (Nat.le_refl _) haN]
    rw [Nat.sub_self]
    exact grantDrainWeakDeathShiftRightZero ring p
  have hReadyArc :=
    grantDrainD6ReadyResponderWarmPrefix
      ring s.native p g D a hC hSector
      ha haInside hAt hReady
  have hOldFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g a ha haN).mp hDistance
  have hOldNone :
      grantDrainLeftBulletDistance ring s.native g a =
        none := by
    apply (grantDrainWarmBulletNoneCharacterization
      ring s.native g a).mpr
    intro j _ hj
    exact congrArg Fin.val (hReadyArc.2 j hj)
  have hOldRank :
      grantDrainWarmRank ring s.native g = 1 + a := by
    simp [grantDrainWarmRank, hDistance, hOldNone,
      hFront, hReady]
  have hNoReqG : s.request g = false := by
    cases hr : s.request g with
    | false => rfl
    | true =>
        simp [grantDrainWarmAt, hr] at hWarm
  have hNotSourceHost : g ≠ e := by
    intro he
    rw [he, hSourceRequest] at hNoReqG
    cases hNoReqG
  have hOldGNotLeader : (s.native g).l = false := by
    cases hl : (s.native g).l with
    | false => rfl
    | true =>
        simp [grantDrainWarmAt, hl] at hWarm
  have hAwaySource : ∀ j : Nat, j < a →
      PPL.shiftLeft ring g j ≠ e := by
    intro j hj
    by_cases hz : j = 0
    · subst j
      simpa only [grantDrainWarmShiftLeftZero] using
        hNotSourceHost
    · exact grantDrainD6DeathSourceOutsidePositive
        ring hn e p g a haN hAt hTo j
        (by omega) (by omega)
  have hAwayResponder : ∀ j : Nat, j < a →
      PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
    intro j hj
    rw [hTo]
    intro heq
    by_cases hz : j = 0
    · subst j
      rw [grantDrainWarmShiftLeftZero] at heq
      rw [heq, hSector.2.1] at hOldGNotLeader
      cases hOldGNotLeader
    · have hFollower := hOldFirst.2 j (by omega) hj
      rw [heq, hSector.2.1] at hFollower
      cases hFollower
  have hFrame : ∀ j : Nat, j < a →
      (grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g j) =
      s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    exact grantDrainSettledNativeStepOutsidePair
      ring fresh update s e (PPL.shiftLeft ring g j)
      (hAwaySource j hj) (hAwayResponder j hj)
  have hNewLeaderLower :
      a ≤ grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g := by
    apply grantDrainD6DeathLeaderPrefixLowerBound
      ring (grantDrainStep ring fresh update s e).native
      g a (by omega)
    intro j hj hja
    rw [hFrame j hja]
    exact hOldFirst.2 j hj hja
  have hNewPBullet :
      ((grantDrainStep ring fresh update s e).native p).b =
        (1 : Fin 3) := by
    rw [← hTo]
    exact grantDrainD6ReadyResponderSourceFireRetainsDummy
      ring hn fresh update s e
      (by rw [hTo]; exact hSector.2.1)
      (by rw [hTo]; exact hReady) hFire
  have hDistinct : ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hEDummy :=
    grantDrainD6MergeReadyResponderDummyPair
      (s.native e) (s.native (ring.rightNeighbor e))
      (by rw [hTo]; exact hSector.2.1)
      (by rw [hTo]; exact hReady)
  have hESignal :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).sg = false := by
    simpa [nativeE, hDistinct] using hEDummy.2.2
  have hNative :=
    grantDrainD6ReadyResponderSourceFireNative
      ring hn fresh update s e
      (by rw [hTo]; exact hSector.2.1)
      (by rw [hTo]; exact hReady) hFire
  have hNewPSignal :
      ((grantDrainStep ring fresh update s e).native p).sg =
        false := by
    rw [hNative, ← hTo]
    simpa [canonicalBirth, hDistinct] using hESignal
  have hNewBullet :
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g) =
          some a := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring (grantDrainStep ring fresh update s e).native
      g (grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g)
      a).mpr
    refine ⟨ha, hNewLeaderLower, ?_, ?_⟩
    · rw [hFront, hNewPBullet]
      decide
    · intro j hj hja
      rw [hFrame j hja, hReadyArc.2 j (by omega)]
      rfl
  have hNewSignals : ∀ j : Nat, j < a →
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring g j)).sg = true := by
    intro j hj
    rw [hFrame j hj]
    exact hReadyArc.1 j hj
  have hNewGSignal :
      ((grantDrainStep ring fresh update s e).native g).sg =
        true := by
    have hHead := hNewSignals 0 (by omega)
    simpa only [grantDrainWarmShiftLeftZero] using hHead
  have hNewTerminal :
      grantDrainTerminalRun ring
        (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g) =
          a - 1 := by
    apply (grantDrainWarmTerminalCharacterization
      ring (grantDrainStep ring fresh update s e).native g
      (grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g)
      (a - 1) (by omega) hNewGSignal).mpr
    refine ⟨by omega, ?_, ?_⟩
    · intro j hj
      exact hNewSignals j (by omega)
    · by_cases hEq :
          grantDrainLeftLeaderDistance ring
            (grantDrainStep ring fresh update s e).native g =
              a
      · exact Or.inl (by omega)
      · right
        have hIndex : a - 1 + 1 = a := by omega
        rw [hIndex, hFront]
        exact hNewPSignal
  have hNewRank :
      grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g =
          a := by
    simp [grantDrainWarmRank, hNewBullet,
      hNewTerminal] <;> omega
  rw [hNewRank, hOldRank]
  omega

/-- F2: OLD incoming LIVE kills the ready responder; source
FIRE is allowed on the same service and W still drops. -/
theorem grantDrainD6ReadyResponderKilledSourceFireRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hSector : sectorLength ring s.native p D)
    (hAt : g = PPL.shiftRight ring p a)
    (ha : 1 ≤ a) (haInside : a < D.val)
    (hDistance :
      grantDrainLeftLeaderDistance ring s.native g = a)
    (hReady : (s.native p).sg = true)
    (hTo : ring.rightNeighbor e = p)
    (hSourceFollower : (s.native e).l = false)
    (hSourceLive : (s.native e).b = (2 : Fin 3))
    (hSourceRequest : s.request e = true)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  exact grantDrainD6ReadyResponderSourceFireRank
    ring hn fresh update s e p g D a
    hC hWarm hGrant hSector hAt ha haInside hDistance
    hReady hTo hSourceRequest hFire

/-- F3: the OLD source does not kill the ready responder;
source FIRE is still permitted and W still drops. -/
theorem grantDrainD6ReadyResponderSurvivingSourceFireRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hSector : sectorLength ring s.native p D)
    (hAt : g = PPL.shiftRight ring p a)
    (ha : 1 ≤ a) (haInside : a < D.val)
    (hDistance :
      grantDrainLeftLeaderDistance ring s.native g = a)
    (hReady : (s.native p).sg = true)
    (hTo : ring.rightNeighbor e = p)
    (hSourceNotEmitting :
      ((s.native e).l && (s.native e).sg) = false)
    (hSourceNotLive : (s.native e).b ≠ (2 : Fin 3))
    (hSourceRequest : s.request e = true)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  exact grantDrainD6ReadyResponderSourceFireRank
    ring hn fresh update s e p g D a
    hC hWarm hGrant hSector hAt ha haInside hDistance
    hReady hTo hSourceRequest hFire

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalBirthChargedBoundAndSpend
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalBirthCredits
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderWarmPrefix
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderSourceFireRank
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderKilledSourceFireRank
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderSurvivingSourceFireRank

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- f1: no change to the actual inclusive old scan on an E-step
whose two physical endpoints are outside that scan. -/
theorem grantDrainD6EScanOutsidePair
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e g : Fin n)
    (hOutside : ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring N g →
        PPL.shiftLeft ring g k ≠ e ∧
        PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) :
    grantDrainWarmRank ring (nativeE ring N e) g =
      grantDrainWarmRank ring N g := by
  exact (grantDrainWarmFullScanFrame
    ring N (nativeE ring N e) g
    (by
      intro k hk
      have hx := (hOutside k hk).1
      have hy := (hOutside k hk).2
      simp [nativeE, hx, hy])).2.2.2

/-- f1: the empty-follower/empty-follower literal E row only
enlarges signals. At a genuine old preceding leader its signal
is framed, so the fixed-host native W cannot increase. -/
theorem grantDrainD6EScanEmptyFollowerPair
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e g : Fin n)
    (hxl : (N e).l = false)
    (hxb : (N e).b = (0 : Fin 3))
    (hyl : (N (ring.rightNeighbor e)).l = false)
    (hyb : (N (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hFront :
      (N (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring N g))).l = true) :
    grantDrainWarmRank ring (nativeE ring N e) g ≤
      grantDrainWarmRank ring N g := by
  have hE := grantDrainWarmEmptyFollowerSignalCopyNativeE
    ring N e hxl hxb hyl hyb
  exact grantDrainWarmSignalExpansionRank
    ring N (nativeE ring N e) g
    (fun i => (hE i).1)
    (fun i => (hE i).2.1)
    ((hE (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring N g))).2.2.2 hFront)
    (fun i => (hE i).2.2.1)

/-- f2: the clockwise inverse of a bounded left shift. -/
private theorem grantDrainD6BirthShiftCancel
    {n : Nat} (ring : DirectedRing n)
    (g : Fin n) (w : Nat) (hw : w < n) :
    PPL.shiftRight ring (PPL.shiftLeft ring g w) w = g := by
  apply Fin.ext
  change (((g.val + n - w % n) % n + w) % n) = g.val
  rw [Nat.mod_eq_of_lt hw]
  by_cases hge : w ≤ g.val
  · have he : g.val + n - w = n + (g.val - w) := by omega
    rw [he, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : g.val - w < n)]
    have hs : g.val - w + w = g.val := by omega
    rw [hs, Nat.mod_eq_of_lt g.isLt]
  · have hlt : g.val + n - w < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hs : g.val + n - w + w = g.val + n := by omega
    rw [hs, Nat.add_mod_right, Nat.mod_eq_of_lt g.isLt]

theorem grantDrainD6BirthLeftOffset
    {n : Nat} (ring : DirectedRing n)
    (g : Fin n) (w : Nat) (hw : w < n) :
    PPL.cyclicOffset ring (PPL.shiftLeft ring g w) g = w := by
  have h := grantDrainWeakDeathOffsetShiftRight
    ring (PPL.shiftLeft ring g w) w hw
  rw [grantDrainD6BirthShiftCancel ring g w hw] at h
  exact h

theorem grantDrainD6BirthLeftOffsetsDistinct
    {n : Nat} (ring : DirectedRing n)
    (g : Fin n) (j w : Nat)
    (hj : j < n) (hw : w < n) (hne : j ≠ w) :
    PPL.shiftLeft ring g j ≠ PPL.shiftLeft ring g w := by
  intro heq
  have h := congrArg (fun x : Fin n =>
    PPL.cyclicOffset ring x g) heq
  rw [grantDrainD6BirthLeftOffset ring g j hj,
    grantDrainD6BirthLeftOffset ring g w hw] at h
  exact hne h

/-- Every index strictly before the new leader is unchanged
by the genuine canonicalBirth function. -/
theorem grantDrainD6BirthLeftPrefixFrame
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (w j : Nat)
    (hw : w < n) (hj : j < w)
    (hz : z = PPL.shiftLeft ring g w) :
    canonicalBirth N z (PPL.shiftLeft ring g j) =
      N (PPL.shiftLeft ring g j) := by
  have hne : PPL.shiftLeft ring g j ≠ z := by
    rw [hz]
    exact grantDrainD6BirthLeftOffsetsDistinct
      ring g j w (by omega) hw (by omega)
  simp [canonicalBirth, hne]

theorem grantDrainD6BirthNewFrontFields
    {n : Nat} (N : Fin n → CertNative) (z : Fin n) :
    (canonicalBirth N z z).l = true ∧
    (canonicalBirth N z z).b.val = 0 ∧
    (canonicalBirth N z z).sg = false := by
  simp [canonicalBirth, firedNative]

/-- Exact first-leader scan result under its real old prefix
of followers, including a birth across the cyclic wrap. -/
theorem grantDrainD6BirthFirstLeaderOfPrefix
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (w : Nat) (hw : 1 ≤ w) (hshort : w < n)
    (hz : z = PPL.shiftLeft ring g w)
    (hOldNo : ∀ j : Nat, 1 ≤ j → j < w →
      (N (PPL.shiftLeft ring g j)).l = false) :
    grantDrainLeftLeaderDistance ring (canonicalBirth N z) g =
      w := by
  apply (grantDrainWarmLeaderFirstCharacterization
    ring (canonicalBirth N z) g w hw hshort).mpr
  constructor
  · rw [← hz]
    exact (grantDrainD6BirthNewFrontFields N z).1
  · intro j hj hjw
    rw [grantDrainD6BirthLeftPrefixFrame
      ring N g z w j hshort hjw hz]
    exact hOldNo j hj hjw

/-- No nearest bullet moves if its index is strictly closer
than the newborn leader's index. -/
theorem grantDrainD6BirthBulletBeforeRetained
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (d p w : Nat) (hw : 1 ≤ w) (hshort : w < n)
    (hz : z = PPL.shiftLeft ring g w)
    (hOld : grantDrainLeftBulletDistance ring N g d = some p)
    (hp : p < w) :
    grantDrainLeftBulletDistance ring (canonicalBirth N z) g w =
      some p := by
  obtain ⟨hpos, _, hhit, hbefore⟩ :=
    (grantDrainWarmBulletSomeCharacterization
      ring N g d p).mp hOld
  apply (grantDrainWarmBulletSomeCharacterization
    ring (canonicalBirth N z) g w p).mpr
  refine ⟨hpos, by omega, ?_, ?_⟩
  · rw [grantDrainD6BirthLeftPrefixFrame
      ring N g z w p hshort hp hz]
    exact hhit
  · intro j hj hjp
    rw [grantDrainD6BirthLeftPrefixFrame
      ring N g z w j hshort (by omega) hz]
    exact hbefore j hj hjp

/-- A first bullet at or behind the birth point is no longer
in the new inclusive bullet scan. The new root is bullet-free. -/
theorem grantDrainD6BirthBulletAtOrBeyondRemoved
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (d p w : Nat) (hw : 1 ≤ w) (hshort : w < n)
    (hz : z = PPL.shiftLeft ring g w)
    (hOld : grantDrainLeftBulletDistance ring N g d = some p)
    (hwp : w ≤ p) :
    grantDrainLeftBulletDistance ring (canonicalBirth N z) g w =
      none := by
  obtain ⟨_, _, _, hbefore⟩ :=
    (grantDrainWarmBulletSomeCharacterization
      ring N g d p).mp hOld
  apply (grantDrainWarmBulletNoneCharacterization
    ring (canonicalBirth N z) g w).mpr
  intro j hj hjw
  by_cases he : j = w
  · rw [he, ← hz]
    exact (grantDrainD6BirthNewFrontFields N z).2.1
  · rw [grantDrainD6BirthLeftPrefixFrame
      ring N g z w j hshort (by omega) hz]
    exact hbefore j hj (by omega)

/-- The old no-bullet result also holds on the truncated
post-birth scan, with the new leader endpoint included. -/
theorem grantDrainD6BirthBulletNoneRemainsNone
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (d w : Nat) (hw : 1 ≤ w) (hwd : w < d)
    (hshort : w < n)
    (hz : z = PPL.shiftLeft ring g w)
    (hOld : grantDrainLeftBulletDistance ring N g d = none) :
    grantDrainLeftBulletDistance ring (canonicalBirth N z) g w =
      none := by
  have hNo := (grantDrainWarmBulletNoneCharacterization
    ring N g d).mp hOld
  apply (grantDrainWarmBulletNoneCharacterization
    ring (canonicalBirth N z) g w).mpr
  intro j hj hjw
  by_cases he : j = w
  · rw [he, ← hz]
    exact (grantDrainD6BirthNewFrontFields N z).2.1
  · rw [grantDrainD6BirthLeftPrefixFrame
      ring N g z w j hshort (by omega) hz]
    exact hNo j hj (by omega)

/-- The exact truncated 0..w-1 signal scan, expressed as
min of the old signal-run value and the new limit w-1. -/
theorem grantDrainD6BirthTerminalMin
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (d f w : Nat)
    (hw : 1 ≤ w) (hwd : w < d) (hshort : w < n)
    (hz : z = PPL.shiftLeft ring g w)
    (hSignal : (N g).sg = true)
    (hOldRun : grantDrainTerminalRun ring N g d = f) :
    grantDrainTerminalRun ring (canonicalBirth N z) g w =
      Nat.min f (w - 1) := by
  have hNewSignal : ((canonicalBirth N z) g).sg = true := by
    have hframe := grantDrainD6BirthLeftPrefixFrame
      ring N g z w 0 hshort (by omega) hz
    rw [grantDrainWarmShiftLeftZero] at hframe
    rw [hframe]
    exact hSignal
  obtain ⟨hfBound, hfPrefix, hfStop⟩ :=
    (grantDrainWarmTerminalCharacterization
      ring N g d f (by omega) hSignal).mp hOldRun
  by_cases hshortRun : f + 1 < w
  · have hmin : Nat.min f (w - 1) = f := by show min f (w - 1) = _; omega
    rw [hmin]
    apply (grantDrainWarmTerminalCharacterization
      ring (canonicalBirth N z) g w f hw hNewSignal).mpr
    refine ⟨by omega, ?_, Or.inr ?_⟩
    · intro j hj
      rw [grantDrainD6BirthLeftPrefixFrame
        ring N g z w j hshort (by omega) hz]
      exact hfPrefix j hj
    · rw [grantDrainD6BirthLeftPrefixFrame
        ring N g z w (f + 1) hshort hshortRun hz]
      rcases hfStop with hFull | hFalse
      · omega
      · exact hFalse
  · have hmin : Nat.min f (w - 1) = w - 1 := by show min f (w - 1) = _; omega
    rw [hmin]
    apply (grantDrainWarmTerminalCharacterization
      ring (canonicalBirth N z) g w (w - 1)
      hw hNewSignal).mpr
    refine ⟨by omega, ?_, Or.inl (by omega)⟩
    intro j hj
    rw [grantDrainD6BirthLeftPrefixFrame
      ring N g z w j hshort (by omega) hz]
    exact hfPrefix j (by omega)

/-- Scalar rank transfer in the retained-bullet case.
Truncating the signal scan cannot increase the amount
p-(f+1) when p<w. -/
theorem grantDrainD6BirthRetainedBulletArithmetic
    (p f w : Nat) (hp : p < w) :
    p + 2 * (p - (Nat.min f (w - 1) + 1)) ≤
      p + 2 * (p - (f + 1)) := by
  by_cases hs : f + 1 < w
  · have hm : Nat.min f (w - 1) = f := by show min f (w - 1) = _; omega
    rw [hm]
    exact Nat.le_refl _
  · have hm : Nat.min f (w - 1) = w - 1 := by show min f (w - 1) = _; omega
    rw [hm]
    have hzero : p - ((w - 1) + 1) = 0 := by omega
    rw [hzero]
    exact Nat.le_add_right _ _

/-- f2 numerical birth lift when the first old bullet is
strictly nearer than the new leader. All scan equalities
are proved above from the literal canonicalBirth state. -/
theorem grantDrainD6BirthRetainedBulletRankLe
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (d p f w : Nat)
    (hw : 1 ≤ w) (hwd : w < d) (hshort : w < n)
    (hz : z = PPL.shiftLeft ring g w)
    (hOldNo : ∀ j : Nat, 1 ≤ j → j < w →
      (N (PPL.shiftLeft ring g j)).l = false)
    (hOldD : grantDrainLeftLeaderDistance ring N g = d)
    (hOldP : grantDrainLeftBulletDistance ring N g d = some p)
    (hp : p < w)
    (hSignal : (N g).sg = true)
    (hOldRun : grantDrainTerminalRun ring N g d = f) :
    grantDrainWarmRank ring (canonicalBirth N z) g ≤
      grantDrainWarmRank ring N g := by
  have hNewD := grantDrainD6BirthFirstLeaderOfPrefix
    ring N g z w hw hshort hz hOldNo
  have hNewP := grantDrainD6BirthBulletBeforeRetained
    ring N g z d p w hw hshort hz hOldP hp
  have hNewRun := grantDrainD6BirthTerminalMin
    ring N g z d f w hw hwd hshort hz hSignal hOldRun
  have hOldRank :
      grantDrainWarmRank ring N g =
        p + 2 * (p - (f + 1)) := by
    simp [grantDrainWarmRank, hOldD, hOldP, hOldRun]
  have hNewRank :
      grantDrainWarmRank ring (canonicalBirth N z) g =
        p + 2 * (p - (Nat.min f (w - 1) + 1)) := by
    simp [grantDrainWarmRank, hNewD, hNewP, hNewRun]
  rw [hOldRank, hNewRank]
  exact grantDrainD6BirthRetainedBulletArithmetic p f w hp

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6EScanOutsidePair
#print axioms L3.GrantDrainEntrance.grantDrainD6EScanEmptyFollowerPair
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthLeftOffset
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthLeftOffsetsDistinct
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthLeftPrefixFrame
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthNewFrontFields
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthFirstLeaderOfPrefix
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthBulletBeforeRetained
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthBulletAtOrBeyondRemoved
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthBulletNoneRemainsNone
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthTerminalMin
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthRetainedBulletArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthRetainedBulletRankLe

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- The genuine old first-leader scan contains only followers
at every strictly smaller positive distance. -/
theorem grantDrainD6BirthOldLeaderPrefix
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n)
    (d : Nat) (hd : 1 ≤ d) (hshort : d < n)
    (hDistance : grantDrainLeftLeaderDistance ring N g = d) :
    ∀ j : Nat, 1 ≤ j → j < d →
      (N (PPL.shiftLeft ring g j)).l = false := by
  exact ((grantDrainWarmLeaderFirstCharacterization
    ring N g d hd hshort).mp hDistance).2

/-- A ready front in a settled OLD sector has a signal-one
trail from that front through every interior follower.
This publicly restates the needed part of the private
ready-sector argument in GrantDrainDummy.lean. -/
theorem grantDrainD6BirthReadySectorPrefix
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g : Fin n)
    (D : Fin (n + 1)) (d : Nat)
    (hC : C_native ring N)
    (hSector : sectorLength ring N p D)
    (hd : 1 ≤ d) (hInside : d < D.val)
    (hAt : g = PPL.shiftRight ring p d)
    (hReady : (N p).sg = true) :
    ∀ j : Nat, j < d →
      (N (PPL.shiftLeft ring g j)).sg = true := by
  have hdshort : d < n := by
    have hD := D.isLt
    omega
  rcases hC.2 p D hSector with hOccupied | hEmpty
  · obtain ⟨a, _, _, hZero, _⟩ := hOccupied
    have hZeroAt :
        (N (PPL.shiftRight ring p 0)).sg = false :=
      hZero (⟨0, ring.hn⟩ : Fin n) (Nat.zero_le _)
    rw [grantDrainWeakDeathShiftRightZero ring p,
      hReady] at hZeroAt
    cases hZeroAt
  · obtain ⟨_, _, hReadyBody⟩ := hEmpty
    intro j hj
    have hArc :
        PPL.shiftLeft ring g j =
          PPL.shiftRight ring p (d - j) := by
      rw [hAt]
      exact grantDrainMarksArcShiftLeftRight
        ring p d j (by omega) hdshort
    rw [hArc]
    exact hReadyBody hReady
      (⟨d - j, show d - j < n by omega⟩ : Fin n)
      (show 1 ≤ d - j by omega)
      (show d - j < D.val by omega)

/-- In the ready/no-bullet branch the old terminal signal
run has maximal length, f=d-1. This follows from C_native,
not from a new post-step assumption about the run. -/
theorem grantDrainD6BirthReadyTerminalFull
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g : Fin n)
    (D : Fin (n + 1)) (d : Nat)
    (hC : C_native ring N)
    (hSector : sectorLength ring N p D)
    (hd : 1 ≤ d) (hInside : d < D.val)
    (hAt : g = PPL.shiftRight ring p d)
    (hReady : (N p).sg = true) :
    grantDrainTerminalRun ring N g d = d - 1 := by
  have hPrefix := grantDrainD6BirthReadySectorPrefix
    ring N p g D d hC hSector hd hInside hAt hReady
  have hSignal : (N g).sg = true := by
    have hzero := hPrefix 0 (by omega)
    rw [grantDrainWarmShiftLeftZero] at hzero
    exact hzero
  apply (grantDrainWarmTerminalCharacterization
    ring N g d (d - 1) hd hSignal).mpr
  refine ⟨by omega, ?_, Or.inl (by omega)⟩
  intro j hj
  exact hPrefix j (by omega)

/-- If the first bullet is strictly farther than the new
leader, the covered/gap scalar alternatives both pay at
most one birth unit with the true truncated signal run. -/
theorem grantDrainD6BirthAheadBulletArithmetic
    (p f w : Nat) (hw : 1 ≤ w) (hwp : w < p) :
    2 * w - Nat.min f (w - 1) + 1 ≤
      p + 2 * (p - (f + 1)) + 1 := by
  by_cases hgap : f + 1 < w
  · have hmin : Nat.min f (w - 1) = f := by
      show min f (w - 1) = f
      omega
    rw [hmin]
    have hbound :=
      grantDrainWarmBirthAheadGapArithmetic p f w hwp hgap
    omega
  · have hmin : Nat.min f (w - 1) = w - 1 := by
      show min f (w - 1) = w - 1
      omega
    rw [hmin]
    have hbound :=
      grantDrainWarmBirthAheadCoveredArithmetic p f w hw hwp
    omega

/-- A post-E-eligible actual birth site cannot itself be the
first old left bullet. This is exactly what excludes p=w:
the bare scalar inequality is false in that subcase. -/
theorem grantDrainD6BirthEligibleAvoidsFirstBullet
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (d p w : Nat)
    (hz : z = PPL.shiftLeft ring g w)
    (hBullet :
      grantDrainLeftBulletDistance ring N g d = some p)
    (hEligible : grantDrainEligible N z = true)
    (hwp : w ≤ p) :
    w < p := by
  have hZero : (N z).b.val = 0 := by
    by_cases hb : (N z).b.val = 0
    · exact hb
    · have hNoEligible : grantDrainEligible N z = false := by
        simp [grantDrainEligible, hb]
      rw [hNoEligible] at hEligible
      cases hEligible
  obtain ⟨_, _, hHit, _⟩ :=
    (grantDrainWarmBulletSomeCharacterization
      ring N g d p).mp hBullet
  have hneq : w ≠ p := by
    intro heq
    have hHitAtW :
        (N (PPL.shiftLeft ring g w)).b.val ≠ 0 := by
      rw [heq]
      exact hHit
    rw [← hz] at hHitAtW
    exact hHitAtW hZero
  omega

/-- f2b, the bullet-ahead case: a selected eligible birth
removes the old first bullet from its truncated scan, and
the no-bullet rank formula satisfies the one-birth budget. -/
theorem grantDrainD6BirthAheadBulletRankLe
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (d p f w : Nat)
    (hw : 1 ≤ w) (hwd : w < d) (hshort : d < n)
    (hz : z = PPL.shiftLeft ring g w)
    (hOldD : grantDrainLeftLeaderDistance ring N g = d)
    (hOldP : grantDrainLeftBulletDistance ring N g d = some p)
    (hwp : w ≤ p)
    (hSignal : (N g).sg = true)
    (hOldRun : grantDrainTerminalRun ring N g d = f)
    (hEligible : grantDrainEligible N z = true) :
    grantDrainWarmRank ring (canonicalBirth N z) g ≤
      grantDrainWarmRank ring N g + 1 := by
  have hNoOld := grantDrainD6BirthOldLeaderPrefix
    ring N g d (by omega) hshort hOldD
  have hNewD := grantDrainD6BirthFirstLeaderOfPrefix
    ring N g z w hw (by omega) hz
    (fun j hj hjw => hNoOld j hj (by omega))
  have hNewP := grantDrainD6BirthBulletAtOrBeyondRemoved
    ring N g z d p w hw (by omega) hz hOldP hwp
  have hNewRun := grantDrainD6BirthTerminalMin
    ring N g z d f w hw hwd (by omega) hz hSignal hOldRun
  have hNewFront :
      ((canonicalBirth N z) (PPL.shiftLeft ring g w)).sg =
        false := by
    rw [← hz]
    exact (grantDrainD6BirthNewFrontFields N z).2.2
  have hNewRank :
      grantDrainWarmRank ring (canonicalBirth N z) g =
        2 * w - Nat.min f (w - 1) + 1 := by
    simp [grantDrainWarmRank, hNewD, hNewP, hNewRun, hNewFront]
  have hOldRank :
      grantDrainWarmRank ring N g =
        p + 2 * (p - (f + 1)) := by
    simp [grantDrainWarmRank, hOldD, hOldP, hOldRun]
  have hp := grantDrainD6BirthEligibleAvoidsFirstBullet
    ring N g z d p w hz hOldP hEligible hwp
  rw [hOldRank, hNewRank]
  exact grantDrainD6BirthAheadBulletArithmetic p f w hw hp

/-- No-bullet scalar, quiet old front. The two original
D6 scalar inequalities cover both placements of the
terminal run relative to the new leader. -/
theorem grantDrainD6BirthNoBulletQuietArithmetic
    (d f w : Nat) (hw : 1 ≤ w)
    (hwd : w < d) (hf : f < d) :
    2 * w - Nat.min f (w - 1) + 1 ≤
      2 * d - f + 1 := by
  have hbound :=
    grantDrainWarmBirthNoBulletArithmetic d f w hwd hf
  by_cases hgap : f + 1 < w
  · have hmin : Nat.min f (w - 1) = f := by
      show min f (w - 1) = f
      omega
    rw [hmin]
    exact hbound.1
  · have hmin : Nat.min f (w - 1) = w - 1 := by
      show min f (w - 1) = w - 1
      omega
    rw [hmin]
    omega

/-- f2b, no old bullet: in the ready sector f=d-1,
while in the nonready sector the no-bullet arithmetic
proves the bound without a new scan hypothesis. -/
theorem grantDrainD6BirthNoBulletRankLe
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g z : Fin n)
    (D : Fin (n + 1)) (d f w : Nat)
    (hC : C_native ring N)
    (hSector : sectorLength ring N p D)
    (hd : 1 ≤ d) (hInside : d < D.val)
    (hAt : g = PPL.shiftRight ring p d)
    (hOldD : grantDrainLeftLeaderDistance ring N g = d)
    (hw : 1 ≤ w) (hwd : w < d)
    (hz : z = PPL.shiftLeft ring g w)
    (hOldP : grantDrainLeftBulletDistance ring N g d = none)
    (hSignal : (N g).sg = true)
    (hOldRun : grantDrainTerminalRun ring N g d = f) :
    grantDrainWarmRank ring (canonicalBirth N z) g ≤
      grantDrainWarmRank ring N g + 1 := by
  have hshort : d < n := by
    have hBound := D.isLt
    omega
  have hNoOld := grantDrainD6BirthOldLeaderPrefix
    ring N g d hd hshort hOldD
  have hNewD := grantDrainD6BirthFirstLeaderOfPrefix
    ring N g z w hw (by omega) hz
    (fun j hj hjw => hNoOld j hj (by omega))
  have hNewP := grantDrainD6BirthBulletNoneRemainsNone
    ring N g z d w hw hwd (by omega) hz hOldP
  have hNewRun := grantDrainD6BirthTerminalMin
    ring N g z d f w hw hwd (by omega) hz hSignal hOldRun
  have hNewFront :
      ((canonicalBirth N z) (PPL.shiftLeft ring g w)).sg =
        false := by
    rw [← hz]
    exact (grantDrainD6BirthNewFrontFields N z).2.2
  have hNewRank :
      grantDrainWarmRank ring (canonicalBirth N z) g =
        2 * w - Nat.min f (w - 1) + 1 := by
    simp [grantDrainWarmRank, hNewD, hNewP, hNewRun, hNewFront]
  have hFront :
      PPL.shiftLeft ring g d = p := by
    rw [hAt, grantDrainMarksArcShiftLeftRight
      ring p d d (Nat.le_refl _) hshort, Nat.sub_self]
    exact grantDrainWeakDeathShiftRightZero ring p
  by_cases hReady : (N p).sg = true
  · have hFull := grantDrainD6BirthReadyTerminalFull
      ring N p g D d hC hSector hd hInside hAt hReady
    have hf : f = d - 1 := hOldRun.symm.trans hFull
    have hmin : Nat.min f (w - 1) = w - 1 := by
      rw [hf]
      show min (d - 1) (w - 1) = w - 1
      omega
    have hOldRank :
        grantDrainWarmRank ring N g = 1 + d := by
      simp [grantDrainWarmRank, hOldD, hOldP, hOldRun,
        hFront, hReady]
    calc
      grantDrainWarmRank ring (canonicalBirth N z) g =
          2 * w - Nat.min f (w - 1) + 1 := hNewRank
      _ ≤ (1 + d) + 1 := by
        rw [hmin]
        omega
      _ = grantDrainWarmRank ring N g + 1 := by
        rw [hOldRank]
  · have hQuiet : (N p).sg = false := by
      cases hs : (N p).sg with
      | false => rfl
      | true => exact False.elim (hReady hs)
    have hOldRank :
        grantDrainWarmRank ring N g =
          2 * d - f + 1 := by
      simp [grantDrainWarmRank, hOldD, hOldP, hOldRun,
        hFront, hQuiet]
    have hf : f < d :=
      ((grantDrainWarmTerminalCharacterization
        ring N g d f hd hSignal).mp hOldRun).1
    have hbound := grantDrainD6BirthNoBulletQuietArithmetic
      d f w hw hwd hf
    calc
      grantDrainWarmRank ring (canonicalBirth N z) g =
          2 * w - Nat.min f (w - 1) + 1 := hNewRank
      _ ≤ 2 * d - f + 1 := hbound
      _ ≤ (2 * d - f + 1) + 1 := Nat.le_succ _
      _ = grantDrainWarmRank ring N g + 1 := by
        rw [hOldRank]

/-- The pure canonicalBirth rank lift for an eligible
interior site, from literal finite scans and the old
C_native sector. No rank inequality occurs in the guards. -/
theorem grantDrainD6BirthInteriorRankLift
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g z : Fin n)
    (D : Fin (n + 1)) (d f w : Nat)
    (hC : C_native ring N)
    (hSector : sectorLength ring N p D)
    (hd : 1 ≤ d) (hInside : d < D.val)
    (hAt : g = PPL.shiftRight ring p d)
    (hOldD : grantDrainLeftLeaderDistance ring N g = d)
    (hw : 1 ≤ w) (hwd : w < d)
    (hz : z = PPL.shiftLeft ring g w)
    (hSignal : (N g).sg = true)
    (hOldRun : grantDrainTerminalRun ring N g d = f)
    (hEligible : grantDrainEligible N z = true) :
    grantDrainWarmRank ring (canonicalBirth N z) g ≤
      grantDrainWarmRank ring N g + 1 := by
  have hshort : d < n := by
    have hBound := D.isLt
    omega
  cases hBullet : grantDrainLeftBulletDistance ring N g d with
  | none =>
      exact grantDrainD6BirthNoBulletRankLe
        ring N p g z D d f w hC hSector hd hInside
        hAt hOldD hw hwd hz hBullet hSignal hOldRun
  | some first =>
      by_cases hBefore : first < w
      · have hNoOld := grantDrainD6BirthOldLeaderPrefix
          ring N g d hd hshort hOldD
        have hRetained := grantDrainD6BirthRetainedBulletRankLe
          ring N g z d first f w hw hwd (by omega) hz
          (fun j hj hjw => hNoOld j hj (by omega))
          hOldD hBullet hBefore hSignal hOldRun
        exact Nat.le_trans hRetained (Nat.le_succ _)
      · exact grantDrainD6BirthAheadBulletRankLe
          ring N g z d first f w hw hwd hshort hz
          hOldD hBullet (by omega) hSignal hOldRun
          hEligible

/-- Eligibility plus true OLD first-leader evidence makes a
birth inside the inclusive old scan strictly interior.
The endpoint w=d is an old leader and cannot be eligible;
w=0 is the continuing warm host and is excluded. -/
theorem grantDrainD6BirthEligibleStrictInside
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g z : Fin n)
    (d w : Nat)
    (hd : 1 ≤ d) (hshort : d < n)
    (hOldD : grantDrainLeftLeaderDistance ring N g = d)
    (hwd : w ≤ d)
    (hz : z = PPL.shiftLeft ring g w)
    (hne : z ≠ g)
    (hEligible : grantDrainEligible N z = true) :
    1 ≤ w ∧ w < d := by
  have hwPositive : 1 ≤ w := by
    by_cases hwZero : w = 0
    · have hzg : z = g := by
        rw [hz, hwZero, grantDrainWarmShiftLeftZero]
      exact False.elim (hne hzg)
    · omega
  have hFront :=
    ((grantDrainWarmLeaderFirstCharacterization
      ring N g d hd hshort).mp hOldD).1
  have hFollower : (N z).l = false := by
    cases hl : (N z).l with
    | false => rfl
    | true =>
        have hNoEligible : grantDrainEligible N z = false := by
          simp [grantDrainEligible, hl]
        rw [hNoEligible] at hEligible
        cases hEligible
  have hwNotFront : w ≠ d := by
    intro heq
    have hHere : (N z).l = true := by
      rw [hz, heq]
      exact hFront
    rw [hHere] at hFollower
    cases hFollower
  exact ⟨hwPositive, by omega⟩

/-- f2: an eligible canonical birth either lies outside
the entire old inclusive scan (rank is equal) or at a
strictly interior offset (the assembled f2b/retained-bullet
proof applies). No artificial interior-offset hypothesis. -/
theorem grantDrainD6BirthSectorRankLift
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g z : Fin n)
    (D : Fin (n + 1)) (d f : Nat)
    (hC : C_native ring N)
    (hSector : sectorLength ring N p D)
    (hd : 1 ≤ d) (hInside : d < D.val)
    (hAt : g = PPL.shiftRight ring p d)
    (hOldD : grantDrainLeftLeaderDistance ring N g = d)
    (hSignal : (N g).sg = true)
    (hOldRun : grantDrainTerminalRun ring N g d = f)
    (hne : z ≠ g)
    (hEligible : grantDrainEligible N z = true) :
    grantDrainWarmRank ring (canonicalBirth N z) g ≤
      grantDrainWarmRank ring N g + 1 := by
  have hshort : d < n := by
    have hD := D.isLt
    omega
  by_cases hInScan :
      ∃ w : Nat, w ≤ d ∧ z = PPL.shiftLeft ring g w
  · obtain ⟨w, hwd, hz⟩ := hInScan
    obtain ⟨hw, hstrict⟩ :=
      grantDrainD6BirthEligibleStrictInside
        ring N g z d w hd hshort hOldD hwd hz hne hEligible
    exact grantDrainD6BirthInteriorRankLift
      ring N p g z D d f w
      hC hSector hd hInside hAt hOldD
      hw hstrict hz hSignal hOldRun hEligible
  · have hOutside :
        ∀ k : Nat,
          k ≤ grantDrainLeftLeaderDistance ring N g →
          PPL.shiftLeft ring g k ≠ z := by
      intro k hk heq
      apply hInScan
      exact ⟨k, by rw [← hOldD]; exact hk, heq.symm⟩
    have hSame := grantDrainWarmBirthOutsideScan
      ring N g z hOutside
    rw [hSame]
    exact Nat.le_succ _

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6BirthOldLeaderPrefix
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthReadySectorPrefix
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthReadyTerminalFull
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthAheadBulletArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthEligibleAvoidsFirstBullet
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthAheadBulletRankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthNoBulletQuietArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthNoBulletRankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthInteriorRankLift
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthEligibleStrictInside
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthSectorRankLift

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! S1n (h1): selected E+birth handoff.
All new proofs below are independent of private declarations in
GrantDrainDummy.lean. -/

/-- The literal first-match selector can return a firing branch only
when that branch's post-E site is eligible. This is a small, closed
Boolean table, before substituting the native configuration. -/
theorem grantDrainD6SelectRawEligibility
    (rx gx ry gy ex ey : Bool) :
    ((if rx && gx && ex then GrantDrainFire.leftLocal
      else if ry && gy && ey then GrantDrainFire.rightLocal
      else if rx && gy && ex then GrantDrainFire.cross
      else GrantDrainFire.none) = GrantDrainFire.leftLocal →
        ex = true) ∧
    ((if rx && gx && ex then GrantDrainFire.leftLocal
      else if ry && gy && ey then GrantDrainFire.rightLocal
      else if rx && gy && ex then GrantDrainFire.cross
      else GrantDrainFire.none) = GrantDrainFire.rightLocal →
        ey = true) ∧
    ((if rx && gx && ex then GrantDrainFire.leftLocal
      else if ry && gy && ey then GrantDrainFire.rightLocal
      else if rx && gy && ex then GrantDrainFire.cross
      else GrantDrainFire.none) = GrantDrainFire.cross →
        ex = true) := by
  cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases ex <;> cases ey <;> decide

/-- h1a: for each of the three actual firing selections, the
native step is exactly the canonical birth on the post-E state. -/
theorem grantDrainD6NativeNextIsBirth
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e z : Fin n)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e)) :
    grantDrainNativeNext ring s e =
      canonicalBirth (nativeE ring s.native e) z := by
  rcases hSelected with ⟨hf, hz⟩ | ⟨hf, hz⟩ | ⟨hf, hz⟩
  · rw [hz]
    simp only [grantDrainNativeNext, hf]
  · rw [hz]
    simp only [grantDrainNativeNext, hf]
  · rw [hz]
    simp only [grantDrainNativeNext, hf]

/-- h1b: unlike a post-step assumption, this eligibility is
derived solely from the OLD first-match selector. -/
theorem grantDrainD6SelectedEligible
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e z : Fin n)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e)) :
    grantDrainEligible (nativeE ring s.native e) z = true := by
  have hBool :=
    grantDrainD6SelectRawEligibility
      (s.request e) (s.grant e)
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainEligible (nativeE ring s.native e) e)
      (grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e))
  rcases hSelected with ⟨hf, hz⟩ | ⟨hf, hz⟩ | ⟨hf, hz⟩
  · rw [hz]
    exact hBool.1 hf
  · rw [hz]
    exact hBool.2.1 hf
  · rw [hz]
    exact hBool.2.2 hf

/-- Pack h1a/h1b into one existential physical FIRE-site witness. -/
theorem grantDrainD6SelectedBirthEligible
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e : Fin n)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    ∃ z : Fin n,
      (z = e ∨ z = ring.rightNeighbor e) ∧
      grantDrainNativeNext ring s e =
        canonicalBirth (nativeE ring s.native e) z ∧
      grantDrainEligible (nativeE ring s.native e) z = true := by
  cases hf : grantDrainSelect ring s e with
  | none =>
      exact False.elim (hFire hf)
  | leftLocal =>
      exact ⟨e, Or.inl rfl,
        grantDrainD6NativeNextIsBirth ring s e e
          (Or.inl ⟨hf, rfl⟩),
        grantDrainD6SelectedEligible ring s e e
          (Or.inl ⟨hf, rfl⟩)⟩
  | rightLocal =>
      exact ⟨ring.rightNeighbor e, Or.inr rfl,
        grantDrainD6NativeNextIsBirth ring s e
          (ring.rightNeighbor e)
          (Or.inr (Or.inl ⟨hf, rfl⟩)),
        grantDrainD6SelectedEligible ring s e
          (ring.rightNeighbor e)
          (Or.inr (Or.inl ⟨hf, rfl⟩))⟩
  | cross =>
      exact ⟨e, Or.inl rfl,
        grantDrainD6NativeNextIsBirth ring s e e
          (Or.inr (Or.inr ⟨hf, rfl⟩)),
        grantDrainD6SelectedEligible ring s e e
          (Or.inr (Or.inr ⟨hf, rfl⟩))⟩

/-- Unconditional available portion of h1c: the entire I factor,
including PPlus and the one-bullet/zero-prefix conditions, survives
native E when OLD C_native holds. No suffix closure is claimed. -/
theorem grantDrainD6NativeEI
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native) :
    I ring (nativeE ring s.native e) := by
  have hOldLocal : GrantDrainEntranceILocal ring s.native :=
    (grantDrainEntranceIffILocal ring s.native).mp hC.1
  have hNewLocal : GrantDrainEntranceILocal ring
      (nativeE ring s.native e) :=
    grantDrainEntranceILocalNativeEAll
      ring (by omega : 3 ≤ n) s.native e hOldLocal
  exact (grantDrainEntranceIffILocal
    ring (nativeE ring s.native e)).mpr hNewLocal

/-- h1c is already complete for the two established arbitrary-n
E rows: quiet empty source into a follower, or responder-leader
death. The other rows are NOT silently folded into this theorem. -/
theorem grantDrainD6NativeECNativeOfRows
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hRow :
      ((s.native (ring.rightNeighbor e)).l = false ∧
        (s.native e).b = (0 : Fin 3) ∧
        ((s.native e).l = false ∨ (s.native e).sg = false))
      ∨
      ((s.native (ring.rightNeighbor e)).l = true ∧
        (nativeE ring s.native e
          (ring.rightNeighbor e)).l = false)) :
    C_native ring (nativeE ring s.native e) := by
  rcases hRow with hQuiet | hDeath
  · exact grantDrainSettledSuffixQuietSourceNativeEPreservesC
      ring hn s.native e hC
      hQuiet.2.2 hQuiet.2.1 hQuiet.1
  · exact grantDrainSettledSuffixDeathNativeEPreservesC
      ring hn s.native e hC hDeath.1 hDeath.2

/-- The no-bullet case actually needs only a conditional
saturated terminal run, not the entire C_native predicate.
The condition is required only in the ready/no-bullet subcase. -/
theorem grantDrainD6BirthNoBulletRankLeWithReadyRun
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g z : Fin n)
    (D : Fin (n + 1)) (d f w : Nat)
    (hReadyRun :
      grantDrainLeftBulletDistance ring N g d = none →
      (N p).sg = true →
      grantDrainTerminalRun ring N g d = d - 1)
    (hd : 1 ≤ d) (hInside : d < D.val)
    (hAt : g = PPL.shiftRight ring p d)
    (hOldD : grantDrainLeftLeaderDistance ring N g = d)
    (hw : 1 ≤ w) (hwd : w < d)
    (hz : z = PPL.shiftLeft ring g w)
    (hOldP : grantDrainLeftBulletDistance ring N g d = none)
    (hSignal : (N g).sg = true)
    (hOldRun : grantDrainTerminalRun ring N g d = f) :
    grantDrainWarmRank ring (canonicalBirth N z) g ≤
      grantDrainWarmRank ring N g + 1 := by
  have hshort : d < n := by
    have hBound := D.isLt
    omega
  have hNoOld := grantDrainD6BirthOldLeaderPrefix
    ring N g d hd hshort hOldD
  have hNewD := grantDrainD6BirthFirstLeaderOfPrefix
    ring N g z w hw (by omega) hz
    (fun j hj hjw => hNoOld j hj (by omega))
  have hNewP := grantDrainD6BirthBulletNoneRemainsNone
    ring N g z d w hw hwd (by omega) hz hOldP
  have hNewRun := grantDrainD6BirthTerminalMin
    ring N g z d f w hw hwd (by omega) hz hSignal hOldRun
  have hNewFront :
      ((canonicalBirth N z) (PPL.shiftLeft ring g w)).sg =
      false := by
    rw [← hz]
    exact (grantDrainD6BirthNewFrontFields N z).2.2
  have hNewRank :
      grantDrainWarmRank ring (canonicalBirth N z) g =
        2 * w - Nat.min f (w - 1) + 1 := by
    simp [grantDrainWarmRank, hNewD, hNewP, hNewRun, hNewFront]
  have hFront :
      PPL.shiftLeft ring g d = p := by
    rw [hAt, grantDrainMarksArcShiftLeftRight
      ring p d d (Nat.le_refl _) hshort, Nat.sub_self]
    exact grantDrainWeakDeathShiftRightZero ring p
  by_cases hReady : (N p).sg = true
  · have hFull := hReadyRun hOldP hReady
    have hf : f = d - 1 := hOldRun.symm.trans hFull
    have hmin : Nat.min f (w - 1) = w - 1 := by
      rw [hf]
      show min (d - 1) (w - 1) = w - 1
      omega
    have hOldRank :
        grantDrainWarmRank ring N g = 1 + d := by
      simp [grantDrainWarmRank, hOldD, hOldP, hOldRun,
        hFront, hReady]
    calc
      grantDrainWarmRank ring (canonicalBirth N z) g =
          2 * w - Nat.min f (w - 1) + 1 := hNewRank
      _ ≤ (1 + d) + 1 := by
        rw [hmin]
        omega
      _ = grantDrainWarmRank ring N g + 1 := by
        rw [hOldRank]
  · have hQuiet : (N p).sg = false := by
      cases hs : (N p).sg with
      | false => rfl
      | true => exact False.elim (hReady hs)
    have hOldRank :
        grantDrainWarmRank ring N g =
          2 * d - f + 1 := by
      simp [grantDrainWarmRank, hOldD, hOldP, hOldRun,
        hFront, hQuiet]
    have hf : f < d :=
      ((grantDrainWarmTerminalCharacterization
        ring N g d f hd hSignal).mp hOldRun).1
    have hbound := grantDrainD6BirthNoBulletQuietArithmetic
      d f w hw hwd hf
    calc
      grantDrainWarmRank ring (canonicalBirth N z) g =
          2 * w - Nat.min f (w - 1) + 1 := hNewRank
      _ ≤ 2 * d - f + 1 := hbound
      _ ≤ (2 * d - f + 1) + 1 := Nat.le_succ _
      _ = grantDrainWarmRank ring N g + 1 := by
        rw [hOldRank]

/-- The interior birth comparison, retaining exactly the single
conditional ready-run fact from the no-bullet branch. -/
theorem grantDrainD6BirthInteriorRankLiftWithReadyRun
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g z : Fin n)
    (D : Fin (n + 1)) (d f w : Nat)
    (hReadyRun :
      grantDrainLeftBulletDistance ring N g d = none →
      (N p).sg = true →
      grantDrainTerminalRun ring N g d = d - 1)
    (hd : 1 ≤ d) (hInside : d < D.val)
    (hAt : g = PPL.shiftRight ring p d)
    (hOldD : grantDrainLeftLeaderDistance ring N g = d)
    (hw : 1 ≤ w) (hwd : w < d)
    (hz : z = PPL.shiftLeft ring g w)
    (hSignal : (N g).sg = true)
    (hOldRun : grantDrainTerminalRun ring N g d = f)
    (hEligible : grantDrainEligible N z = true) :
    grantDrainWarmRank ring (canonicalBirth N z) g ≤
      grantDrainWarmRank ring N g + 1 := by
  have hshort : d < n := by
    have hBound := D.isLt
    omega
  cases hBullet : grantDrainLeftBulletDistance ring N g d with
  | none =>
      exact grantDrainD6BirthNoBulletRankLeWithReadyRun
        ring N p g z D d f w hReadyRun hd hInside
        hAt hOldD hw hwd hz hBullet hSignal hOldRun
  | some first =>
      by_cases hBefore : first < w
      · have hNoOld := grantDrainD6BirthOldLeaderPrefix
          ring N g d hd hshort hOldD
        have hRetained := grantDrainD6BirthRetainedBulletRankLe
          ring N g z d first f w hw hwd (by omega) hz
          (fun j hj hjw => hNoOld j hj (by omega))
          hOldD hBullet hBefore hSignal hOldRun
        exact Nat.le_trans hRetained (Nat.le_succ _)
      · exact grantDrainD6BirthAheadBulletRankLe
          ring N g z d first f w hw hwd hshort hz
          hOldD hBullet (by omega) hSignal hOldRun
          hEligible

/-- The earlier sector lift with C_native and sectorLength eliminated
from the hypotheses. The one genuinely needed suffix consequence
is precisely hReadyRun; the other inputs are raw scan facts. -/
theorem grantDrainD6BirthSectorRankLiftWithReadyRun
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g z : Fin n)
    (D : Fin (n + 1)) (d f : Nat)
    (hReadyRun :
      grantDrainLeftBulletDistance ring N g d = none →
      (N p).sg = true →
      grantDrainTerminalRun ring N g d = d - 1)
    (hd : 1 ≤ d) (hInside : d < D.val)
    (hAt : g = PPL.shiftRight ring p d)
    (hOldD : grantDrainLeftLeaderDistance ring N g = d)
    (hSignal : (N g).sg = true)
    (hOldRun : grantDrainTerminalRun ring N g d = f)
    (hne : z ≠ g)
    (hEligible : grantDrainEligible N z = true) :
    grantDrainWarmRank ring (canonicalBirth N z) g ≤
      grantDrainWarmRank ring N g + 1 := by
  have hshort : d < n := by
    have hD := D.isLt
    omega
  by_cases hInScan :
      ∃ w : Nat, w ≤ d ∧ z = PPL.shiftLeft ring g w
  · obtain ⟨w, hwd, hz⟩ := hInScan
    obtain ⟨hw, hstrict⟩ :=
      grantDrainD6BirthEligibleStrictInside
        ring N g z d w hd hshort hOldD hwd hz hne hEligible
    exact grantDrainD6BirthInteriorRankLiftWithReadyRun
      ring N p g z D d f w
      hReadyRun hd hInside hAt hOldD
      hw hstrict hz hSignal hOldRun hEligible
  · have hOutside :
        ∀ k : Nat,
          k ≤ grantDrainLeftLeaderDistance ring N g →
          PPL.shiftLeft ring g k ≠ z := by
      intro k hk heq
      apply hInScan
      exact ⟨k, by rw [← hOldD]; exact hk, heq.symm⟩
    have hSame := grantDrainWarmBirthOutsideScan
      ring N g z hOutside
    rw [hSame]
    exact Nat.le_succ _

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6SelectRawEligibility
#print axioms L3.GrantDrainEntrance.grantDrainD6NativeNextIsBirth
#print axioms L3.GrantDrainEntrance.grantDrainD6SelectedEligible
#print axioms L3.GrantDrainEntrance.grantDrainD6SelectedBirthEligible
#print axioms L3.GrantDrainEntrance.grantDrainD6NativeEI
#print axioms L3.GrantDrainEntrance.grantDrainD6NativeECNativeOfRows
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthNoBulletRankLeWithReadyRun
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthInteriorRankLiftWithReadyRun
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthSectorRankLiftWithReadyRun

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! S1n continuation.
The following uses the already-proved public R8e pointwise backward
theorem to control the E signal suffix. No private declaration from
GrantDrainDummy.lean or GrantDrainEntrance.lean is referenced. -/

/-- OLD C_native prohibits each signal defect after native E.
This uses all three proved literal E rows of the R8e backward
theorem, not an assumed C_native closure theorem. -/
theorem grantDrainD6NativeENoSignalDefects
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native) :
    ∀ v : Fin n,
      ¬ GrantDrainEntranceSignalDefect ring
        (nativeE ring s.native e) v := by
  intro v hNew
  have hBack :=
    (grantDrainEntranceR8eDefectBackward
      ring (by omega : 3 ≤ n) s.native e hC.1 v).1
  exact (grantDrainEntranceCleanNoSignalDefect
    ring s.native hC v) (hBack hNew)

theorem grantDrainD6ReadySectorSignalOnes
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (D : Fin (n + 1))
    (hI : I ring N)
    (hNoDefect :
      ∀ v : Fin n,
        ¬ GrantDrainEntranceSignalDefect ring N v)
    (hSector : sectorLength ring N p D)
    (hReady : (N p).sg = true) :
    ∀ k : Fin n, 1 ≤ k.val → k.val < D.val →
      (N (PPL.shiftRight ring p k.val)).sg = true := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hI
  have hNoBullet :=
    grantDrainEntranceReadyLeaderSectorBulletFree
      ring N p D hLocal hSector hReady
  intro k hkPos hkInside
  have hOneInRing : 1 < n := by
    have hkBound := k.isLt
    omega
  have hGap : 1 < D.val := by omega
  have hFirst :
      (N (ring.rightNeighbor p)).sg = true := by
    cases hFirstSignal : (N (ring.rightNeighbor p)).sg with
    | true => rfl
    | false =>
        have hMismatch :
            GrantDrainEntranceReadyMismatch ring N
              (ring.rightNeighbor p) := by
          exact ⟨p, D, hSector, hGap, rfl,
            hNoBullet, hReady, hFirstSignal⟩
        exact False.elim
          ((hNoDefect (ring.rightNeighbor p))
            (Or.inr hMismatch))
  by_cases hkFirst : k.val = 1
  · rw [hkFirst]
    change (N (ring.rightNeighbor p)).sg = true
    exact hFirst
  · cases hAtK : (N (PPL.shiftRight ring p k.val)).sg with
    | true => rfl
    | false =>
        have hSuffix :
            GrantDrainEntranceSignalSuffixSite ring N p D
              (⟨1, hOneInRing⟩ : Fin n) := by
          refine ⟨hSector, Nat.le_refl 1, hGap, ?_⟩
          intro j hj hBullet
          exact False.elim (hNoBullet j hj hBullet)
        have hCounted :
            GrantDrainEntranceCountedZero ring N
              (PPL.shiftRight ring p k.val) := by
          refine ⟨p, D, (⟨1, hOneInRing⟩ : Fin n), k,
            hSuffix, rfl, ?_, hkInside, hAtK, ?_⟩
          · change 1 < k.val
            omega
          · change (N (ring.rightNeighbor p)).sg = true
            exact hFirst
        exact False.elim
          ((hNoDefect (PPL.shiftRight ring p k.val))
            (Or.inl hCounted))


theorem grantDrainD6ReadySectorTerminalRun
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p g : Fin n) (D : Fin (n + 1)) (d : Nat)
    (hI : I ring N)
    (hNoDefect :
      ∀ v : Fin n,
        ¬ GrantDrainEntranceSignalDefect ring N v)
    (hSector : sectorLength ring N p D)
    (hd : 1 ≤ d) (hInside : d < D.val)
    (hAt : g = PPL.shiftRight ring p d)
    (hReady : (N p).sg = true) :
    grantDrainTerminalRun ring N g d = d - 1 := by
  have hDlt : d < n := by
    have hMax := D.isLt
    omega
  have hTail :=
    grantDrainD6ReadySectorSignalOnes
      ring N p D hI hNoDefect hSector hReady
  have hGSignal : (N g).sg = true := by
    rw [hAt]
    exact hTail (⟨d, hDlt⟩ : Fin n) hd hInside
  apply (grantDrainWarmTerminalCharacterization
    ring N g d (d - 1) hd hGSignal).mpr
  refine ⟨by omega, ?_, Or.inl (by omega)⟩
  intro j hj
  have hLeft :
      PPL.shiftLeft ring g j =
        PPL.shiftRight ring p (d - j) := by
    rw [hAt]
    exact grantDrainMarksArcShiftLeftRight
      ring p d j (by omega) hDlt
  rw [hLeft]
  have hjStrict : j < d := by
    have hdPositive : 1 ≤ d := hd
    omega
  have hBackPos : 1 ≤ d - j := by omega
  have hBackInside : d - j < D.val := by omega
  have hBackBound : d - j < n := by omega
  exact hTail
    (⟨d - j, hBackBound⟩ : Fin n)
    hBackPos hBackInside


/-- (r), with exactly the ready-run implication requested for
N = nativeE ring s.native e. The no-bullet hypothesis is accepted
at the interface but turns out unnecessary: I plus a ready leader
already excludes every bullet in its complete sector. -/
theorem grantDrainD6NativeEReadyRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (p g : Fin n) (D : Fin (n + 1)) (d : Nat)
    (hC : C_native ring s.native)
    (hSector :
      sectorLength ring (nativeE ring s.native e) p D)
    (hd : 1 ≤ d) (hInside : d < D.val)
    (hAt : g = PPL.shiftRight ring p d) :
    grantDrainLeftBulletDistance ring
        (nativeE ring s.native e) g d = none →
    (nativeE ring s.native e p).sg = true →
    grantDrainTerminalRun ring
      (nativeE ring s.native e) g d = d - 1 := by
  intro _hNoBullet hReady
  exact grantDrainD6ReadySectorTerminalRun
    ring (nativeE ring s.native e) p g D d
    (grantDrainD6NativeEI ring hn s e hC)
    (grantDrainD6NativeENoSignalDefects ring hn s e hC)
    hSector hd hInside hAt hReady

theorem grantDrainD6PostESectorWitness
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hFollower : (nativeE ring s.native e g).l = false) :
    ∃ (p : Fin n) (D : Fin (n + 1)) (d : Nat),
      sectorLength ring (nativeE ring s.native e) p D ∧
      1 ≤ d ∧ d < D.val ∧
      g = PPL.shiftRight ring p d ∧
      grantDrainLeftLeaderDistance ring
        (nativeE ring s.native e) g = d := by
  have hRoot : PPlus ring (nativeE ring s.native e) :=
    nativeE_preserves_PPlus
      (by omega : 3 ≤ n) ring s.native e hC.1.1
  obtain ⟨p, D, a, hSector, haInside, hAt⟩ :=
    grantDrainEntranceSectorCoverOfRoot
      ring (nativeE ring s.native e) hRoot.1 g
  have haPos : 1 ≤ a.val := by
    by_cases haZero : a.val = 0
    · have hSame : g = p := by
        calc
          g = PPL.shiftRight ring p a.val := hAt
          _ = PPL.shiftRight ring p 0 := by rw [haZero]
          _ = p := grantDrainWeakDeathShiftRightZero ring p
      rw [hSame, hSector.2.1] at hFollower
      cases hFollower
    · omega
  have hLeader :
      (nativeE ring s.native e
        (PPL.shiftLeft ring g a.val)).l = true := by
    rw [hAt, grantDrainMarksArcShiftLeftRight
      ring p a.val a.val (Nat.le_refl _) a.isLt,
      Nat.sub_self, grantDrainWeakDeathShiftRightZero ring p]
    exact hSector.2.1
  have hNoEarlier :
      ∀ k : Nat, 1 ≤ k → k < a.val →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g k)).l = false := by
    intro k hk hkEarlier
    have hLeft :
        PPL.shiftLeft ring g k =
          PPL.shiftRight ring p (a.val - k) := by
      rw [hAt]
      exact grantDrainMarksArcShiftLeftRight
        ring p a.val k (by omega) a.isLt
    rw [hLeft]
    have hIndexPos : 0 < a.val - k := by omega
    have hIndexInside : a.val - k < D.val := by omega
    have hIndexBound : a.val - k < n := by omega
    exact hSector.2.2.2
      (⟨a.val - k, hIndexBound⟩ : Fin n)
      hIndexPos hIndexInside
  have hDistance :
      grantDrainLeftLeaderDistance ring
        (nativeE ring s.native e) g = a.val := by
    exact (grantDrainWarmLeaderFirstCharacterization
      ring (nativeE ring s.native e) g a.val
      haPos a.isLt).mpr ⟨hLeader, hNoEarlier⟩
  exact ⟨p, D, a.val, hSector, haPos, haInside, hAt, hDistance⟩


/-- A surviving warm physical host different from the selected
birth site was already a signal-one follower after native E.
No request/grant assumptions are folded into this native fact. -/
theorem grantDrainD6PostENativeStillWarm
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hBirth :
      grantDrainNativeNext ring s e =
        canonicalBirth (nativeE ring s.native e) z)
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true) :
    (nativeE ring s.native e g).l = false ∧
    (nativeE ring s.native e g).sg = true := by
  have hAtG :
      (grantDrainStep ring fresh update s e).native g =
        nativeE ring s.native e g := by
    change grantDrainNativeNext ring s e g =
      nativeE ring s.native e g
    rw [hBirth]
    simp [canonicalBirth, Ne.symm hz]
  have hFollower :
      ((grantDrainStep ring fresh update s e).native g).l =
        false := by
    cases hl :
        ((grantDrainStep ring fresh update s e).native g).l with
    | false => rfl
    | true =>
        simp [grantDrainWarmAt, hl] at hStillWarm
  have hSignal :
      ((grantDrainStep ring fresh update s e).native g).sg =
        true := by
    cases hs :
        ((grantDrainStep ring fresh update s e).native g).sg with
    | true => rfl
    | false =>
        simp [grantDrainWarmAt, hs] at hStillWarm
  rw [hAtG] at hFollower hSignal
  exact ⟨hFollower, hSignal⟩

/-- The full BIRTH portion of s1n, leaving exactly the separate
E-to-OLD rank comparison as an explicit hypothesis. The sector,
post-E eligibility, ready run, and birth identity are all derived
from OLD C_native and the actual selector and warm host. -/
theorem grantDrainD6NonExceptionalBirthRankLiftOfERank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (_hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hERank :
      grantDrainWarmRank ring (nativeE ring s.native e) g ≤
        grantDrainWarmRank ring s.native g) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g + 1 := by
  have hBirth :=
    grantDrainD6NativeNextIsBirth ring s e z hSelected
  have hEligible :=
    grantDrainD6SelectedEligible ring s e z hSelected
  have hPostWarm :=
    grantDrainD6PostENativeStillWarm
      ring fresh update s e g z hBirth hz hStillWarm
  obtain ⟨p, D, d, hSector, hd, hInside,
      hAt, hDistance⟩ :=
    grantDrainD6PostESectorWitness
      ring hn s e g hC hPostWarm.1
  have hReadyRun :=
    grantDrainD6NativeEReadyRun
      ring hn s e p g D d hC hSector hd hInside hAt
  have hLift :=
    grantDrainD6BirthSectorRankLiftWithReadyRun
      ring (nativeE ring s.native e) p g z D d
      (grantDrainTerminalRun ring (nativeE ring s.native e) g d)
      hReadyRun hd hInside hAt hDistance hPostWarm.2
      rfl hz hEligible
  calc
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g =
        grantDrainWarmRank ring
          (canonicalBirth (nativeE ring s.native e) z) g := by
            rw [hBirth]
    _ ≤ grantDrainWarmRank ring
          (nativeE ring s.native e) g + 1 := hLift
    _ ≤ grantDrainWarmRank ring s.native g + 1 :=
      Nat.add_le_add_right hERank 1

/-- Closed s1n outside the whole inclusive OLD scan: the E rank
is exactly unchanged, and no interaction with the scanned birth
site is possible. The OLD nonexceptional guard is retained. -/
theorem grantDrainD6NonExceptionalBirthRankLiftOutsidePair
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hOutside :
      ∀ k : Nat,
        k ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g k ≠ e ∧
        PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g + 1 := by
  have hRank :=
    grantDrainD6EScanOutsidePair
      ring s.native e g hOutside
  exact grantDrainD6NonExceptionalBirthRankLiftOfERank
    ring hn fresh update s e g z hC hNonExceptional
    hSelected hz hStillWarm (Nat.le_of_eq hRank)

/-- Closed s1n on the empty-follower/empty-follower E row,
including both FIRE ports. The known physical E-scan expansion
comparison supplies the missing E-rank premise here. -/
theorem grantDrainD6NonExceptionalBirthRankLiftEmptyPair
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hyEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hOldFront :
      (s.native (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))).l =
          true) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g + 1 := by
  have hERank :=
    grantDrainD6EScanEmptyFollowerPair
      ring s.native e g hxFollower hxEmpty
      hyFollower hyEmpty hOldFront
  exact grantDrainD6NonExceptionalBirthRankLiftOfERank
    ring hn fresh update s e g z hC hNonExceptional
    hSelected hz hStillWarm hERank

end L3.GrantDrainEntrance




namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false

/-- Boolean warm-host fields used by the exceptional E scan. -/
theorem grantDrainD6ExceptionalDeathHostFields
    {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hWarm : grantDrainWarmAt s g = true) :
    (s.native g).l = false ∧
    (s.native g).b = (0 : Fin 3) ∧
    (s.native g).sg = true := by
  have hL : (s.native g).l = false := by
    cases hl : (s.native g).l with
    | false => rfl
    | true => simp [grantDrainWarmAt, hl] at hWarm
  have hB : (s.native g).b = (0 : Fin 3) := by
    by_cases hb : (s.native g).b = (0 : Fin 3)
    · exact hb
    · have hCold := grantDrainWarmPhysicalBulletEndsWarm s g hb
      rw [hWarm] at hCold
      cases hCold
  have hS : (s.native g).sg = true := by
    cases hs : (s.native g).sg with
    | true => rfl
    | false => simp [grantDrainWarmAt, hs] at hWarm
  exact ⟨hL, hB, hS⟩

/-- The literal nearest-leader observer, including the getD fallback,
always returns a number in [1,n] on a nonempty ring. -/
theorem grantDrainD6ExceptionalDistanceRange
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (g : Fin n) :
    1 ≤ grantDrainLeftLeaderDistance ring N g ∧
    grantDrainLeftLeaderDistance ring N g ≤ n := by
  have hScan :
      grantDrainLeftLeaderDistance ring N g =
        ((List.range' 1 n).find?
          (fun j => (N (PPL.shiftLeft ring g j)).l)).getD n := by
    unfold grantDrainLeftLeaderDistance
    rw [grantDrainD6DeathPositiveRange]
  simp only [hScan]
  cases hf : (List.range' 1 n).find?
      (fun j => (N (PPL.shiftLeft ring g j)).l) with
  | none =>
      simpa [hf] using (show 1 ≤ n ∧ n ≤ n by omega)
  | some p =>
      obtain ⟨hp, hUpper, _, _⟩ :=
        grantDrainD6DeathFindConverse
          (fun j => (N (PPL.shiftLeft ring g j)).l)
          n 1 p hf
      simpa [hf] using (show 1 ≤ p ∧ p ≤ n by omega)

/-- An entire counterclockwise circuit returns to its starting site. -/
theorem grantDrainD6ExceptionalFullShift
    {n : Nat} (ring : DirectedRing n) (g : Fin n) :
    PPL.shiftLeft ring g n = g := by
  apply Fin.ext
  change (g.val + n - n % n) % n = g.val
  simp [Nat.mod_eq_of_lt g.isLt]

/-- A true exceptional guard at a genuine warm follower cannot use
the full-circuit fallback as its OLD preceding leader. -/
theorem grantDrainD6ExceptionalDeathOldDistanceShort
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    1 ≤ grantDrainLeftLeaderDistance ring s.native g ∧
    grantDrainLeftLeaderDistance ring s.native g < n := by
  have hRange :=
    grantDrainD6ExceptionalDistanceRange ring hn s.native g
  have hLeader :=
    (grantDrainD6MergeExceptionalFields
      ring s e g hExceptional).1
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l = true
    at hLeader
  have hFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  have hNotFull :
      grantDrainLeftLeaderDistance ring s.native g ≠ n := by
    intro hFull
    rw [hFull, grantDrainD6ExceptionalFullShift ring g] at hLeader
    rw [hFollower] at hLeader
    cases hLeader
  exact ⟨hRange.1, by omega⟩

/-- Exact OLD no-bullet, quiet-front rank; no post-E scan result
is assumed here. -/
theorem grantDrainD6ExceptionalDeathOldRankExact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    grantDrainWarmRank ring s.native g =
      2 * grantDrainLeftLeaderDistance ring s.native g -
        grantDrainTerminalRun ring s.native g
          (grantDrainLeftLeaderDistance ring s.native g) + 1 := by
  obtain ⟨_, _, hQuiet, hNoBullet, _⟩ :=
    grantDrainD6MergeExceptionalFields
      ring s e g hExceptional
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).sg = false
    at hQuiet
  simp [grantDrainWarmRank, hNoBullet, hQuiet]

/-- The killed responder was already bullet-free by the INCLUSIVE
old bullet scan, and its literal E image remains bullet-free. -/
theorem grantDrainD6ExceptionalDeathFrontBulletZeroAfterE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    (nativeE ring s.native e (ring.rightNeighbor e)).b =
      (0 : Fin 3) := by
  have hPos :=
    (grantDrainD6ExceptionalDistanceRange
      ring hn s.native g).1
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  obtain ⟨hLeader, _, hQuiet, hNoBullet, _⟩ :=
    grantDrainD6MergeExceptionalFields
      ring s e g hExceptional
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l = true
    at hLeader
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).sg = false
    at hQuiet
  rw [hResponder] at hLeader hQuiet
  have hOldVal :=
    ((grantDrainWarmBulletNoneCharacterization
      ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)).mp
      hNoBullet)
        (grantDrainLeftLeaderDistance ring s.native g)
        hPos (Nat.le_refl _)
  rw [hResponder] at hOldVal
  have hOldZero :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) := by
    apply Fin.ext
    change (s.native (ring.rightNeighbor e)).b.val = 0
    exact hOldVal
  simpa [hQuiet, hOldZero] using
    (grantDrainEntranceNativeELeaderBulletAfter
      ring (by omega : 2 ≤ n) s.native e hLeader).1

/-- Every STRICT interior site of the old positive scan is outside
both physical E endpoints. This is proved from the OLD first-hit
observer and the literal responder-death location. -/
theorem grantDrainD6ExceptionalDeathInteriorFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    ∀ k : Nat,
      1 ≤ k →
      k < grantDrainLeftLeaderDistance ring s.native g →
      nativeE ring s.native e (PPL.shiftLeft ring g k) =
        s.native (PPL.shiftLeft ring g k) := by
  obtain ⟨hPos, hShort⟩ :=
    grantDrainD6ExceptionalDeathOldDistanceShort
      ring hn s e g hWarm hExceptional
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  have hAt :
      g = PPL.shiftRight ring (ring.rightNeighbor e)
        (grantDrainLeftLeaderDistance ring s.native g) := by
    calc
      g = PPL.shiftRight ring
          (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g))
          (grantDrainLeftLeaderDistance ring s.native g) :=
            (grantDrainD6BirthShiftCancel ring g
              (grantDrainLeftLeaderDistance ring s.native g)
              hShort).symm
      _ = PPL.shiftRight ring (ring.rightNeighbor e)
          (grantDrainLeftLeaderDistance ring s.native g) := by
            rw [hResponder]
  have hOldLeader :
      (s.native (ring.rightNeighbor e)).l = true := by
    have hLeader :=
      (grantDrainD6MergeExceptionalFields
        ring s e g hExceptional).1
    change (s.native (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).l = true
      at hLeader
    rw [hResponder] at hLeader
    exact hLeader
  have hOldNoLeader :=
    ((grantDrainWarmLeaderFirstCharacterization
      ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        hPos hShort).mp rfl).2
  intro k hk hBefore
  have hNotY :
      PPL.shiftLeft ring g k ≠ ring.rightNeighbor e := by
    intro hAtY
    have hMiss := hOldNoLeader k hk hBefore
    rw [hAtY, hOldLeader] at hMiss
    cases hMiss
  have hNotE : PPL.shiftLeft ring g k ≠ e :=
    grantDrainD6DeathSourceOutsidePositive
      ring hn e (ring.rightNeighbor e) g
      (grantDrainLeftLeaderDistance ring s.native g)
      hShort hAt rfl k hk (by omega)
  exact grantDrainEntranceNativeEFrame
    ring s.native e (PPL.shiftLeft ring g k)
    hNotE hNotY

/-- Once the old front dies, the NEW first-leader distance strictly
exceeds the OLD one. This includes the getD n fallback and does not
claim that the new distance is strictly less than n. -/
theorem grantDrainD6ExceptionalDeathNewLeaderFarther
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    grantDrainLeftLeaderDistance ring s.native g <
      grantDrainLeftLeaderDistance ring
        (nativeE ring s.native e) g := by
  obtain ⟨hPos, hShort⟩ :=
    grantDrainD6ExceptionalDeathOldDistanceShort
      ring hn s e g hWarm hExceptional
  have hOldNoLeader :=
    ((grantDrainWarmLeaderFirstCharacterization
      ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        hPos hShort).mp rfl).2
  obtain ⟨_, _, _, _, hDead⟩ :=
    grantDrainD6MergeExceptionalFields
      ring s e g hExceptional
  change (nativeE ring s.native e (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l = false
    at hDead
  have hFrame :=
    grantDrainD6ExceptionalDeathInteriorFrame
      ring hn s e g hWarm hExceptional
  have hNewNoLeader :
      ∀ k : Nat, 1 ≤ k →
        k < grantDrainLeftLeaderDistance ring s.native g + 1 →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g k)).l = false := by
    intro k hk hBefore
    by_cases hAtEnd :
        k = grantDrainLeftLeaderDistance ring s.native g
    · subst k
      exact hDead
    · have hInterior :
          k < grantDrainLeftLeaderDistance ring s.native g := by
        omega
      rw [hFrame k hk hInterior]
      exact hOldNoLeader k hk hInterior
  have hBound :=
    grantDrainD6DeathLeaderPrefixLowerBound
      ring (nativeE ring s.native e) g
      (grantDrainLeftLeaderDistance ring s.native g + 1)
      (by omega) hNewNoLeader
  omega

/-- The literal E image contains NO bullet on 1..d_OLD, including
the killed old front. The yet-unscanned interval (d_OLD,d_NEW]
is deliberately not covered by this theorem. -/
theorem grantDrainD6ExceptionalDeathOldBulletPrefixE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    ∀ k : Nat,
      1 ≤ k →
      k ≤ grantDrainLeftLeaderDistance ring s.native g →
      (nativeE ring s.native e
        (PPL.shiftLeft ring g k)).b = (0 : Fin 3) := by
  obtain ⟨_, _, _, hNoBullet, _⟩ :=
    grantDrainD6MergeExceptionalFields
      ring s e g hExceptional
  have hOldZero :=
    (grantDrainWarmBulletNoneCharacterization
      ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)).mp
      hNoBullet
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  have hFrontZero :=
    grantDrainD6ExceptionalDeathFrontBulletZeroAfterE
      ring hn s e g hExceptional
  have hFrame :=
    grantDrainD6ExceptionalDeathInteriorFrame
      ring hn s e g hWarm hExceptional
  intro k hk hBound
  by_cases hAtFront :
      k = grantDrainLeftLeaderDistance ring s.native g
  · subst k
    rw [hResponder]
    exact hFrontZero
  · have hInterior :
        k < grantDrainLeftLeaderDistance ring s.native g := by
      omega
    rw [hFrame k hk hInterior]
    have hVal := hOldZero k hk hBound
    apply Fin.ext
    change (s.native (PPL.shiftLeft ring g k)).b.val = 0
    exact hVal

/-- The exceptional OLD responder cannot be killed by the empty
warm grant site itself: a quiet bullet-free follower does not kill. -/
theorem grantDrainD6ExceptionalDeathSourceNotHost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    e ≠ g := by
  intro hEq
  have hWarmFields :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hFollower : (s.native e).l = false := by
    rw [hEq]
    exact hWarmFields.1
  have hEmpty : (s.native e).b = (0 : Fin 3) := by
    rw [hEq]
    exact hWarmFields.2.1
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  obtain ⟨hLeader, hUnshielded, hQuiet, _, hDeath⟩ :=
    grantDrainD6MergeExceptionalFields
      ring s e g hExceptional
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l = true
    at hLeader
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).sh = false
    at hUnshielded
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).sg = false
    at hQuiet
  change (nativeE ring s.native e (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l = false
    at hDeath
  rw [hResponder] at hLeader hUnshielded hQuiet hDeath
  have hPair :=
    grantDrainD6DeathEmptyFollowerCannotKill
      (s.native e) (s.native (ring.rightNeighbor e))
      hFollower hEmpty hLeader hUnshielded hQuiet
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hAlive :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        true := by
    simpa [nativeE, hDistinct] using hPair
  rw [hAlive] at hDeath
  cases hDeath

/-- E preserves the signal word on offsets 0..d_OLD. At d_OLD
the old signal was false and the killed responder's new signal
is false; distance zero uses source-not-host. -/
theorem grantDrainD6ExceptionalDeathSignalPrefixE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g →
      (nativeE ring s.native e
        (PPL.shiftLeft ring g k)).sg =
      (s.native (PPL.shiftLeft ring g k)).sg := by
  have hWarmFields :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hNotE : g ≠ e :=
    (grantDrainD6ExceptionalDeathSourceNotHost
      ring hn s e g hWarm hExceptional).symm
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  obtain ⟨hLeader, _, hQuiet, _, _⟩ :=
    grantDrainD6MergeExceptionalFields
      ring s e g hExceptional
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l = true
    at hLeader
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).sg = false
    at hQuiet
  rw [hResponder] at hLeader hQuiet
  have hNotY : g ≠ ring.rightNeighbor e := by
    intro hEq
    have hFollower := hWarmFields.1
    rw [hEq, hLeader] at hFollower
    cases hFollower
  have hNewQuiet :=
    (grantDrainEntranceNativeELeaderBulletAfter
      ring (by omega : 2 ≤ n) s.native e hLeader).2
  intro k hk
  by_cases hZero : k = 0
  · subst k
    rw [grantDrainWarmShiftLeftZero]
    exact congrArg (fun c : CertNative => c.sg)
      (grantDrainEntranceNativeEFrame
        ring s.native e g hNotE hNotY)
  · by_cases hAtFront :
        k = grantDrainLeftLeaderDistance ring s.native g
    · subst k
      rw [hResponder, hNewQuiet, hQuiet]
    · have hInterior :
          k < grantDrainLeftLeaderDistance ring s.native g := by
        omega
      exact congrArg (fun c : CertNative => c.sg)
        (grantDrainD6ExceptionalDeathInteriorFrame
          ring hn s e g hWarm hExceptional
          k (by omega) hInterior)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6NativeENoSignalDefects
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadySectorSignalOnes
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadySectorTerminalRun
#print axioms L3.GrantDrainEntrance.grantDrainD6NativeEReadyRun
#print axioms L3.GrantDrainEntrance.grantDrainD6PostESectorWitness
#print axioms L3.GrantDrainEntrance.grantDrainD6PostENativeStillWarm
#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalBirthRankLiftOfERank
#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalBirthRankLiftOutsidePair
#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalBirthRankLiftEmptyPair
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathHostFields
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDistanceRange
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalFullShift
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathOldDistanceShort
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathOldRankExact
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathFrontBulletZeroAfterE
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathInteriorFrame
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathNewLeaderFarther
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathOldBulletPrefixE
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathSourceNotHost
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathSignalPrefixE

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! S1x(a). All E facts below are derived
from the OLD C_native configuration and the literal nativeE row. -/

/-- A true exceptional responder death does not change the old
warm follower's native leader bit. The OLD front is the responder,
whereas the host is a different, non-source follower. -/
theorem grantDrainD6ExceptionalDeathPostFollower
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    (nativeE ring s.native e g).l = false := by
  have hOldFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  have hNotSource : g ≠ e :=
    (grantDrainD6ExceptionalDeathSourceNotHost
      ring hn s e g hWarm hExceptional).symm
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  have hOldLeader :=
    (grantDrainD6MergeExceptionalFields
      ring s e g hExceptional).1
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l =
      true at hOldLeader
  rw [hResponder] at hOldLeader
  have hNotResponder : g ≠ ring.rightNeighbor e := by
    intro hg
    have hOldResponderFollower :
        (s.native (ring.rightNeighbor e)).l = false := by
      rw [← hg]
      exact hOldFollower
    rw [hOldLeader] at hOldResponderFollower
    cases hOldResponderFollower
  rw [grantDrainEntranceNativeEFrame
    ring s.native e g hNotSource hNotResponder]
  exact hOldFollower

/-- s1x(i). Since the actual post-E host remains a follower
and the post-E state is rooted, its nearest counterclockwise
leader occurs at a strictly sub-circuit distance. -/
theorem grantDrainD6ExceptionalDeathNewDistanceShort
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    1 ≤ grantDrainLeftLeaderDistance ring
          (nativeE ring s.native e) g ∧
    grantDrainLeftLeaderDistance ring
        (nativeE ring s.native e) g ≤ n - 1 := by
  have hFollower :=
    grantDrainD6ExceptionalDeathPostFollower
      ring hn s e g hWarm hExceptional
  obtain ⟨p, D, dNew, hSector, hdPos, hdInside,
      hAt, hDistance⟩ :=
    grantDrainD6PostESectorWitness
      ring hn s e g hC hFollower
  have hBound := D.isLt
  rw [hDistance]
  exact ⟨hdPos, by omega⟩

/-- Core of s1x(ii), with the OLD leader distance abstracted as d.
For k ≤ d use the already-proved bullet prefix. For
d < k ≤ d_NEW, the E-death sector partition identifies the site
with the OLD source-sector prefix. Its entire post-E bullet
field is zero by the proved death-source-prefix theorem. -/
theorem grantDrainD6ExceptionalDeathNewBulletNoneAt
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (d : Nat)
    (hOldDistance :
      grantDrainLeftLeaderDistance ring s.native g = d)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    grantDrainLeftBulletDistance ring
        (nativeE ring s.native e) g
        (grantDrainLeftLeaderDistance ring
          (nativeE ring s.native e) g) = none := by
  have hPostFollower :=
    grantDrainD6ExceptionalDeathPostFollower
      ring hn s e g hWarm hExceptional
  obtain ⟨p, D, a, hSector, haPos, haInside,
      hAt, hDistance⟩ :=
    grantDrainD6PostESectorWitness
      ring hn s e g hC hPostFollower
  have hAShort : a < n := by
    have hDbound := D.isLt
    omega
  have hFar :=
    grantDrainD6ExceptionalDeathNewLeaderFarther
      ring hn s e g hWarm hExceptional
  rw [hOldDistance, hDistance] at hFar
  have hLocal : GrantDrainEntranceILocal ring s.native :=
    (grantDrainEntranceIffILocal ring s.native).mp hC.1
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  rw [hOldDistance] at hResponder
  obtain ⟨hOldLeader, _, _, _, hDead⟩ :=
    grantDrainD6MergeExceptionalFields
      ring s e g hExceptional
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l =
      true at hOldLeader
  change (nativeE ring s.native e
    (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).l =
      false at hDead
  rw [hOldDistance, hResponder] at hOldLeader hDead
  have hYoffset :
      PPL.shiftRight ring p (a - d) =
        ring.rightNeighbor e := by
    calc
      PPL.shiftRight ring p (a - d) =
          PPL.shiftLeft ring
            (PPL.shiftRight ring p a) d :=
        (grantDrainMarksArcShiftLeftRight
          ring p a d (by omega) hAShort).symm
      _ = PPL.shiftLeft ring g d := by rw [hAt]
      _ = ring.rightNeighbor e := hResponder
  have hOffsetPos : 0 < a - d := by omega
  have hOffsetInside : a - d < D.val := by omega
  have hOffsetShort : a - d < n := by omega
  have hPartition :=
    grantDrainEntranceDeathSectorPartition
      ring (by omega : 2 ≤ n) s.native e hLocal
      hOldLeader hDead p D hSector
  have hOldBulletPrefix :=
    grantDrainD6ExceptionalDeathOldBulletPrefixE
      ring hn s e g hWarm hExceptional
  rw [hOldDistance] at hOldBulletPrefix
  rw [hDistance]
  apply (grantDrainWarmBulletNoneCharacterization
    ring (nativeE ring s.native e) g a).mpr
  intro k hk hka
  by_cases hkOld : k ≤ d
  · have hZero := hOldBulletPrefix k hk hkOld
    rw [hZero]
    rfl
  · have hLeft :
        PPL.shiftLeft ring g k =
          PPL.shiftRight ring p (a - k) := by
      rw [hAt]
      exact grantDrainMarksArcShiftLeftRight
        ring p a k (by omega) hAShort
    rcases hPartition with hFramed | hMerged
    · have hFalse :
          (s.native (ring.rightNeighbor e)).l = false := by
        have hAtInterior :=
          hFramed.1.2.2.2
            (⟨a - d, hOffsetShort⟩ : Fin n)
            hOffsetPos hOffsetInside
        rw [hYoffset] at hAtInterior
        exact hAtInterior
      rw [hOldLeader] at hFalse
      cases hFalse
    · obtain ⟨t, htPos, htInside, htY, htSource,
        hOldSourceSector, _⟩ := hMerged
      have htShort : t.val < n := by
        have hDbound := D.isLt
        omega
      have htEq : t.val = a - d :=
        grantDrainEntranceR8eShiftIndexInjective
          ring p t.val (a - d) htShort hOffsetShort
          (htY.trans hYoffset.symm)
      have hIndex : a - k < t.val := by omega
      have hPrefix :=
        grantDrainEntranceDeathSourcePrefixClean
          ring (by omega : 2 ≤ n)
          s.native e hLocal hOldLeader hDead
          p t htPos htShort htY htSource hOldSourceSector
      have hFields :=
        grantDrainEntranceNativeEDeathFields
          ring (by omega : 2 ≤ n)
          s.native e hLocal hOldLeader hDead
          (PPL.shiftRight ring p (a - k))
      rw [hLeft, hFields.2.1]
      exact congrArg Fin.val (hPrefix (a - k) hIndex).1

/-- s1x(ii), with the OLD scan index instantiated rather than
provided as an additional hypothesis. -/
theorem grantDrainD6ExceptionalDeathNewBulletNone
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    grantDrainLeftBulletDistance ring
        (nativeE ring s.native e) g
        (grantDrainLeftLeaderDistance ring
          (nativeE ring s.native e) g) = none := by
  exact grantDrainD6ExceptionalDeathNewBulletNoneAt
    ring hn s e g
    (grantDrainLeftLeaderDistance ring s.native g)
    rfl hC hWarm hExceptional

/-- A first false signal at or before the OLD scan endpoint fixes
the terminal 1-run across any extension of the scan window.
Only the signal frame, not a new C_native predicate, is needed. -/
theorem grantDrainD6TerminalRunPreservedByFrame
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (g : Fin n)
    (d dNew f : Nat)
    (hd : 1 ≤ d)
    (hSignal : (N g).sg = true)
    (hFar : d < dNew)
    (hOldRun : grantDrainTerminalRun ring N g d = f)
    (hFrame : ∀ k : Nat, k ≤ d →
      (M (PPL.shiftLeft ring g k)).sg =
        (N (PPL.shiftLeft ring g k)).sg)
    (hOldEnd :
      (N (PPL.shiftLeft ring g d)).sg = false) :
    grantDrainTerminalRun ring M g dNew = f := by
  obtain ⟨hf, hPrefix, hStop⟩ :=
    (grantDrainWarmTerminalCharacterization
      ring N g d f hd hSignal).mp hOldRun
  have hNewSignal : (M g).sg = true := by
    have hZero := hFrame 0 (by omega)
    rw [grantDrainWarmShiftLeftZero] at hZero
    exact hZero.trans hSignal
  have hNewStop :
      (M (PPL.shiftLeft ring g (f + 1))).sg = false := by
    rw [hFrame (f + 1) (by omega)]
    rcases hStop with hEnd | hStopHere
    · rw [hEnd]
      exact hOldEnd
    · exact hStopHere
  apply (grantDrainWarmTerminalCharacterization
    ring M g dNew f (by omega) hNewSignal).mpr
  refine ⟨by omega, ?_, Or.inr hNewStop⟩
  intro k hk
  rw [hFrame k (by omega)]
  exact hPrefix k hk

/-- s1x(iii): the OLD terminal run has already met the quiet
doomed leader by distance d. The earlier framing lemma covers every signal in 0..d,
so extending the new leader scan cannot extend its true prefix. -/
theorem grantDrainD6ExceptionalDeathTerminalRunPreserved
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    grantDrainTerminalRun ring (nativeE ring s.native e) g
        (grantDrainLeftLeaderDistance ring
          (nativeE ring s.native e) g) =
      grantDrainTerminalRun ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) := by
  have hOldDistance :=
    grantDrainD6ExceptionalDeathOldDistanceShort
      ring hn s e g hWarm hExceptional
  have hFar :=
    grantDrainD6ExceptionalDeathNewLeaderFarther
      ring hn s e g hWarm hExceptional
  have hSignal :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).2.2
  obtain ⟨_, _, hQuiet, _, _⟩ :=
    grantDrainD6MergeExceptionalFields
      ring s e g hExceptional
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).sg =
      false at hQuiet
  exact grantDrainD6TerminalRunPreservedByFrame
    ring s.native (nativeE ring s.native e) g
    (grantDrainLeftLeaderDistance ring s.native g)
    (grantDrainLeftLeaderDistance ring
      (nativeE ring s.native e) g)
    (grantDrainTerminalRun ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g))
    hOldDistance.1 hSignal hFar rfl
    (grantDrainD6ExceptionalDeathSignalPrefixE
      ring hn s e g hWarm hExceptional)
    hQuiet

/-- The numerical cost of a single genuine exceptional merge.
This is stated on opaque natural-number indices and does not
unfold any protocol observer. -/
theorem grantDrainD6ExceptionalMergeBudgetArithmetic
    (n d dNew f : Nat)
    (hn : 5 ≤ n) (hd : 1 ≤ d)
    (hFar : d < dNew) (hNewBound : dNew ≤ n - 1)
    (hf : f < d) :
    2 * dNew - f + 1 ≤
      (2 * d - f + 1) + 2 * (n - 2) := by
  omega

/-- s1x(a): OLD quiet front, no OLD bullet, literal responder
death, bounded new leader, bullet-free extended new scan, and
unchanged terminal run give the prepaid exceptional allowance. -/
theorem grantDrainD6ExceptionalDeathERank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g + 2 * (n - 2) := by
  have hOldRange :=
    grantDrainD6ExceptionalDeathOldDistanceShort
      ring hn s e g hWarm hExceptional
  have hNewRange :=
    grantDrainD6ExceptionalDeathNewDistanceShort
      ring hn s e g hC hWarm hExceptional
  have hFar :=
    grantDrainD6ExceptionalDeathNewLeaderFarther
      ring hn s e g hWarm hExceptional
  have hBullet :=
    grantDrainD6ExceptionalDeathNewBulletNone
      ring hn s e g hC hWarm hExceptional
  have hRun :=
    grantDrainD6ExceptionalDeathTerminalRunPreserved
      ring hn s e g hWarm hExceptional
  have hOldRank :=
    grantDrainD6ExceptionalDeathOldRankExact
      ring s e g hExceptional
  have hOldSignal :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).2.2
  have hRunBound :
      grantDrainTerminalRun ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) <
      grantDrainLeftLeaderDistance ring s.native g :=
    ((grantDrainWarmTerminalCharacterization
      ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        (grantDrainTerminalRun ring s.native g
          (grantDrainLeftLeaderDistance ring s.native g))
        hOldRange.1 hOldSignal).mp rfl).1
  have hNewRankUpper :
      grantDrainWarmRank ring (nativeE ring s.native e) g ≤
        2 * grantDrainLeftLeaderDistance ring
              (nativeE ring s.native e) g -
            grantDrainTerminalRun ring s.native g
              (grantDrainLeftLeaderDistance ring s.native g) +
            1 := by
    cases hNewFront :
        (nativeE ring s.native e
          (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring
              (nativeE ring s.native e) g))).sg with
    | true =>
        have hExact :
            grantDrainWarmRank ring
              (nativeE ring s.native e) g =
            1 + grantDrainLeftLeaderDistance ring
              (nativeE ring s.native e) g := by
          simp [grantDrainWarmRank, hBullet, hRun, hNewFront]
        rw [hExact]
        omega
    | false =>
        have hExact :
            grantDrainWarmRank ring
              (nativeE ring s.native e) g =
            2 * grantDrainLeftLeaderDistance ring
                (nativeE ring s.native e) g -
              grantDrainTerminalRun ring s.native g
                (grantDrainLeftLeaderDistance ring s.native g) +
              1 := by
          simp [grantDrainWarmRank, hBullet, hRun, hNewFront]
        exact Nat.le_of_eq hExact
  calc
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
        2 * grantDrainLeftLeaderDistance ring
              (nativeE ring s.native e) g -
          grantDrainTerminalRun ring s.native g
            (grantDrainLeftLeaderDistance ring s.native g) +
          1 := hNewRankUpper
    _ ≤
        (2 * grantDrainLeftLeaderDistance ring s.native g -
          grantDrainTerminalRun ring s.native g
            (grantDrainLeftLeaderDistance ring s.native g) + 1) +
        2 * (n - 2) :=
      grantDrainD6ExceptionalMergeBudgetArithmetic
        n
        (grantDrainLeftLeaderDistance ring s.native g)
        (grantDrainLeftLeaderDistance ring
          (nativeE ring s.native e) g)
        (grantDrainTerminalRun ring s.native g
          (grantDrainLeftLeaderDistance ring s.native g))
        hn hOldRange.1 hFar hNewRange.2 hRunBound
    _ = grantDrainWarmRank ring s.native g + 2 * (n - 2) := by
      rw [hOldRank]

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathPostFollower
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathNewDistanceShort
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathNewBulletNoneAt
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathNewBulletNone
#print axioms L3.GrantDrainEntrance.grantDrainD6TerminalRunPreservedByFrame
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathTerminalRunPreserved
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalMergeBudgetArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalDeathERank

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
S1n: counterexample to the proposed
unqualified E-only rank transfer.

The serviced pair is 0 -> 1 on a five-site ring.
OLD 0 is the only leader, ready (sg = true), with no bullet.
All OLD followers have sg = true. The OLD warm grant at 1 is
an actual grant, with request = false. Native E emits the
ready leader's LIVE to follower 1, resetting both signals.
There is no old exceptional leader death and no selected FIRE.
-/

def grantDrainD6NonExceptionalCounterRing : DirectedRing 5 :=
  ⟨by decide⟩

def grantDrainD6NonExceptionalCounterNative
    (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (0 : Fin 3), sh := false, sg := true }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := true }

def grantDrainD6NonExceptionalCounterState :
    GrantDrainState 5 Unit :=
  { native := grantDrainD6NonExceptionalCounterNative
    request := fun _ => false
    grant := fun i => i.val == 1
    scratch := ()
    history := [] }

/-- The concrete OLD state satisfies the exact paper settled
native predicate and NoBadLive; its tracked grant is truly warm.
The offending E edge intersects the inclusive OLD scan at its
leader endpoint, without triggering exceptional death. -/
theorem grantDrainD6NonExceptionalCounterAdmissible :
    C_native grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState.native ∧
    PPlus grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState.native ∧
    GrantDrainEntranceNoBadLive
      grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState ∧
    grantDrainWarmAt
      grantDrainD6NonExceptionalCounterState
      (1 : Fin 5) = true ∧
    grantDrainD6NonExceptionalCounterState.grant
      (1 : Fin 5) = true ∧
    grantDrainExceptionalDeath
      grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState
      (0 : Fin 5) (1 : Fin 5) = false ∧
    grantDrainSelect
      grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState
      (0 : Fin 5) = .none ∧
    PPL.shiftLeft grantDrainD6NonExceptionalCounterRing
      (1 : Fin 5)
      (grantDrainLeftLeaderDistance
        grantDrainD6NonExceptionalCounterRing
        grantDrainD6NonExceptionalCounterState.native
        (1 : Fin 5)) = (0 : Fin 5) := by
  have hC :
      C_native grantDrainD6NonExceptionalCounterRing
        grantDrainD6NonExceptionalCounterState.native := by
    decide
  refine ⟨hC, hC.1.1, ?_, by decide, by decide,
    by decide, by decide, by decide⟩
  intro b
  unfold SharedPaperNonleftmostLiveExact
  revert b
  decide

/-- The E row preserves the old front leader but places a new LIVE
bullet at the responder; the responder ceases to be warm.
The literal rank changes 2 -> 3, not a nonincreasing step. -/
theorem grantDrainD6NonExceptionalCounterTrace :
    grantDrainLeftLeaderDistance
      grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState.native
      (1 : Fin 5) = 1 ∧
    grantDrainLeftLeaderDistance
      grantDrainD6NonExceptionalCounterRing
      (nativeE grantDrainD6NonExceptionalCounterRing
        grantDrainD6NonExceptionalCounterState.native (0 : Fin 5))
      (1 : Fin 5) = 1 ∧
    (nativeE grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState.native (0 : Fin 5)
      (0 : Fin 5)).l = true ∧
    (nativeE grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState.native (0 : Fin 5)
      (1 : Fin 5)).b = (2 : Fin 3) ∧
    (nativeE grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState.native (0 : Fin 5)
      (1 : Fin 5)).sg = false ∧
    grantDrainWarmRank
      grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState.native
      (1 : Fin 5) = 2 ∧
    grantDrainWarmRank
      grantDrainD6NonExceptionalCounterRing
      (nativeE grantDrainD6NonExceptionalCounterRing
        grantDrainD6NonExceptionalCounterState.native (0 : Fin 5))
      (1 : Fin 5) = 3 ∧
    ¬ (grantDrainWarmRank
        grantDrainD6NonExceptionalCounterRing
        (nativeE grantDrainD6NonExceptionalCounterRing
          grantDrainD6NonExceptionalCounterState.native (0 : Fin 5))
        (1 : Fin 5) ≤
      grantDrainWarmRank
        grantDrainD6NonExceptionalCounterRing
        grantDrainD6NonExceptionalCounterState.native
        (1 : Fin 5)) := by
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- The requested E-rank transfer, quantified over OLD C_native,
OLD warm hosts and an OLD false exceptional guard, is false already
at n=5. This does not refute a version restricted to an ACTUAL
continuing post-E warm host. -/
theorem grantDrainD6NonExceptionalERankLeRefuted :
    ¬ (∀ (ring : DirectedRing 5)
        (s : GrantDrainState 5 Unit) (e g : Fin 5),
      C_native ring s.native →
      grantDrainExceptionalDeath ring s e g = false →
      grantDrainWarmAt s g = true →
      grantDrainWarmRank ring (nativeE ring s.native e) g ≤
        grantDrainWarmRank ring s.native g) := by
  intro hTransfer
  have hC :=
    grantDrainD6NonExceptionalCounterAdmissible.1
  have hGuard :
      grantDrainExceptionalDeath
        grantDrainD6NonExceptionalCounterRing
        grantDrainD6NonExceptionalCounterState
        (0 : Fin 5) (1 : Fin 5) = false := by
    decide
  have hWarm :
      grantDrainWarmAt
        grantDrainD6NonExceptionalCounterState
        (1 : Fin 5) = true := by
    decide
  have hFailure :
      ¬ (grantDrainWarmRank
          grantDrainD6NonExceptionalCounterRing
          (nativeE grantDrainD6NonExceptionalCounterRing
            grantDrainD6NonExceptionalCounterState.native
            (0 : Fin 5))
          (1 : Fin 5) ≤
        grantDrainWarmRank
          grantDrainD6NonExceptionalCounterRing
          grantDrainD6NonExceptionalCounterState.native
          (1 : Fin 5)) :=
    grantDrainD6NonExceptionalCounterTrace.2.2.2.2.2.2.2
  exact hFailure
    (hTransfer grantDrainD6NonExceptionalCounterRing
      grantDrainD6NonExceptionalCounterState
      (0 : Fin 5) (1 : Fin 5) hC hGuard hWarm)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalCounterAdmissible
#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalCounterTrace
#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalERankLeRefuted

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- An exceptional front is the OLD responder leader.  The warm
tracked site is an OLD follower, so it cannot be that responder. -/
theorem grantDrainD6ExceptionalBirthResponderAway
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    ring.rightNeighbor e ≠ g := by
  have hLeader :=
    (grantDrainD6MergeExceptionalFields
      ring s e g hExceptional).1
  change (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l = true
    at hLeader
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  rw [hResponder] at hLeader
  intro hEq
  rw [hEq] at hLeader
  have hFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  rw [hFollower] at hLeader
  cases hLeader

/-- s1x(b), in fact stronger than the continuing-warm formulation:
for every genuine exceptional OLD front and every selected FIRE,
the selected canonical birth site is automatically different from g.
supplies the E signal at g; the earlier post-E lemma supplies the post-E follower,
bounded leader scan, no-bullet scan and preserved terminal run.
The generic ready-run sector lift needs no post-E C_native premise. -/
theorem grantDrainD6ExceptionalBirthRankLift
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring (nativeE ring s.native e) g + 1 := by
  obtain ⟨z, hSite, hBirth, hEligible⟩ :=
    grantDrainD6SelectedBirthEligible ring s e hFire
  have hAwaySource : e ≠ g :=
    grantDrainD6ExceptionalDeathSourceNotHost
      ring hn s e g hWarm hExceptional
  have hAwayResponder : ring.rightNeighbor e ≠ g :=
    grantDrainD6ExceptionalBirthResponderAway
      ring s e g hWarm hExceptional
  have hz : z ≠ g := by
    rcases hSite with hAtSource | hAtResponder
    · rw [hAtSource]
      exact hAwaySource
    · rw [hAtResponder]
      exact hAwayResponder
  have hPostFollower :=
    grantDrainD6ExceptionalDeathPostFollower
      ring hn s e g hWarm hExceptional
  have hZero :
      (nativeE ring s.native e g).sg = (s.native g).sg := by
    simpa only [grantDrainWarmShiftLeftZero] using
      (grantDrainD6ExceptionalDeathSignalPrefixE
        ring hn s e g hWarm hExceptional
        0 (Nat.zero_le _))
  have hPostSignal : (nativeE ring s.native e g).sg = true :=
    hZero.trans
      ((grantDrainD6ExceptionalDeathHostFields s g hWarm).2.2)
  obtain ⟨p, D, d, hSector, _hd, hInside, hAt, hDistance⟩ :=
    grantDrainD6PostESectorWitness
      ring hn s e g hC hPostFollower
  have hRange :=
    grantDrainD6ExceptionalDeathNewDistanceShort
      ring hn s e g hC hWarm hExceptional
  rw [hDistance] at hRange
  have hNoBullet :=
    grantDrainD6ExceptionalDeathNewBulletNone
      ring hn s e g hC hWarm hExceptional
  rw [hDistance] at hNoBullet
  have hTerminal :=
    grantDrainD6ExceptionalDeathTerminalRunPreserved
      ring hn s e g hWarm hExceptional
  rw [hDistance] at hTerminal
  have hReadyRun :
      grantDrainLeftBulletDistance ring
          (nativeE ring s.native e) g d = none →
      (nativeE ring s.native e p).sg = true →
      grantDrainTerminalRun ring
        (nativeE ring s.native e) g d = d - 1 := by
    intro _hNoBullet hReady
    exact grantDrainD6NativeEReadyRun
      ring hn s e p g D d hC hSector hRange.1 hInside hAt
      hNoBullet hReady
  have hLift :=
    grantDrainD6BirthSectorRankLiftWithReadyRun
      ring (nativeE ring s.native e) p g z D d
      (grantDrainTerminalRun ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g))
      hReadyRun hRange.1 hInside hAt hDistance
      hPostSignal hTerminal hz hEligible
  calc
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g =
        grantDrainWarmRank ring
          (canonicalBirth (nativeE ring s.native e) z) g := by
            rw [hBirth]
    _ ≤ grantDrainWarmRank ring
          (nativeE ring s.native e) g + 1 := hLift

/-- s1x: the exceptional E charge from s1x(a), followed by the
selected canonical birth charge from s1x(b). -/
theorem grantDrainD6ExceptionalBirthRankCharge
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g + 2 * (n - 2) + 1 := by
  have hE :=
    grantDrainD6ExceptionalDeathERank
      ring hn s e g hC hWarm hExceptional
  have hBirth :=
    grantDrainD6ExceptionalBirthRankLift
      ring hn s e g hC hWarm hExceptional hFire
  exact Nat.le_trans hBirth (Nat.add_le_add_right hE 1)

/-- The same physical exceptional FIRE simultaneously incurs
the above numeric charge and spends the one-time exceptional
reserve and one birth credit.  This does not assert full charged
monotonicity without a positive remaining birth allowance and
a continuing physical/ghost host. -/
theorem grantDrainD6ExceptionalBirthRankChargeAndCredits
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hWarmAt : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true)
    (hFire : grantDrainSelect ring s e ≠ .none)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hLabelWarm : label.warm = true)
    (hHost : label.host = some g) :
    (grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
       grantDrainWarmRank ring s.native g + 2 * (n - 2) + 1) ∧
    label.exceptionalLeft = true ∧
    (grantDrainWarmLabelStep ring fresh update s e
      label).exceptionalLeft = false ∧
    (grantDrainWarmLabelStep ring fresh update s e
      label).birthsLeft = label.birthsLeft - 1 := by
  have hRank :=
    grantDrainD6ExceptionalBirthRankCharge
      ring hn s e g hC hWarmAt hExceptional hFire
  have hCredits :=
    grantDrainD6ExceptionalBirthCredits
      ring fresh update s e g label
      hInv hLabelWarm hHost hExceptional hFire
  exact ⟨hRank, hCredits.1, hCredits.2.1, hCredits.2.2⟩

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalBirthResponderAway
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalBirthRankLift
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalBirthRankCharge
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalBirthRankChargeAndCredits

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! S1n: an interacting source-follower/
empty-source E-row closure. The remaining row families are named
after the code. No purported unconditional all-row theorem is given. -/

/-- A real C_native OLD warm follower always has a genuine
preceding leader in the nearest-left-leader scan. -/
theorem grantDrainD6OldWarmFrontLeader
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true) :
    (s.native (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).l =
        true := by
  have hFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  obtain ⟨p, D, a, hSector, haInside, hAt⟩ :=
    grantDrainEntranceSectorCoverOfRoot
      ring s.native hC.1.1.1 g
  have haPos : 1 ≤ a.val := by
    by_cases haZero : a.val = 0
    · have hSame : g = p := by
        calc
          g = PPL.shiftRight ring p a.val := hAt
          _ = PPL.shiftRight ring p 0 := by rw [haZero]
          _ = p := grantDrainWeakDeathShiftRightZero ring p
      rw [hSame, hSector.2.1] at hFollower
      cases hFollower
    · omega
  have hLeader :
      (s.native (PPL.shiftLeft ring g a.val)).l = true := by
    rw [hAt, grantDrainMarksArcShiftLeftRight
      ring p a.val a.val (Nat.le_refl _) a.isLt,
      Nat.sub_self, grantDrainWeakDeathShiftRightZero ring p]
    exact hSector.2.1
  have hNoEarlier :
      ∀ k : Nat, 1 ≤ k → k < a.val →
        (s.native (PPL.shiftLeft ring g k)).l = false := by
    intro k hk hkEarlier
    have hLeft :
        PPL.shiftLeft ring g k =
          PPL.shiftRight ring p (a.val - k) := by
      rw [hAt]
      exact grantDrainMarksArcShiftLeftRight
        ring p a.val k (by omega) a.isLt
    rw [hLeft]
    have hIndexPos : 0 < a.val - k := by omega
    have hIndexInside : a.val - k < D.val := by omega
    have hIndexBound : a.val - k < n := by omega
    exact hSector.2.2.2
      (⟨a.val - k, hIndexBound⟩ : Fin n)
      hIndexPos hIndexInside
  have hDistance :
      grantDrainLeftLeaderDistance ring s.native g = a.val :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g a.val haPos a.isLt).mpr
      ⟨hLeader, hNoEarlier⟩
  rw [hDistance]
  exact hLeader

/-- A quiet responder leader and a source with no bullet and
no leader preserve all leader/bullet flags; only the source
signal may increase. The source-signal-zero case uses the
public complete E row, while source-signal-one is literally
the existing native-E identity row. -/
theorem grantDrainD6QuietResponderSignalExpansionFields
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hxFollower : (N e).l = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyQuiet : (N (ring.rightNeighbor e)).sg = false) :
    ∀ i : Fin n,
      (nativeE ring N e i).l = (N i).l ∧
      (nativeE ring N e i).b = (N i).b ∧
      ((N i).sg = true → (nativeE ring N e i).sg = true) ∧
      ((N i).l = true →
        (nativeE ring N e i).sg = (N i).sg) := by
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  by_cases hxOne : (N e).sg = true
  · have hIdentity :=
      grantDrainEntranceR8eQuietLeaderSilentNativeIdentity
        ring hn N e hxFollower hxEmpty hxOne hyLeader hyQuiet
    intro i
    rw [hIdentity]
    exact ⟨rfl, rfl, (fun h => h), (fun _ => rfl)⟩
  · have hxZero : (N e).sg = false := by
      cases hs : (N e).sg with
      | false => rfl
      | true => exact False.elim (hxOne hs)
    obtain ⟨hXL, hXB, hXS, hYL, hYB, hYS⟩ :=
      grantDrainEntranceR8eQuietLeaderEmptyPair
        (N e) (N (ring.rightNeighbor e))
        hxEmpty hxZero hyLeader hyQuiet
    have hSourceL :
        (nativeE ring N e e).l = (N e).l := by
      simpa [nativeE] using hXL
    have hSourceB :
        (nativeE ring N e e).b = (N e).b := by
      simpa [nativeE] using hXB
    have hSourceS :
        (nativeE ring N e e).sg = true := by
      simpa [nativeE] using hXS
    have hTargetL :
        (nativeE ring N e (ring.rightNeighbor e)).l =
          (N (ring.rightNeighbor e)).l := by
      simpa [nativeE, hDistinct] using hYL
    have hTargetB :
        (nativeE ring N e (ring.rightNeighbor e)).b =
          (N (ring.rightNeighbor e)).b := by
      simpa [nativeE, hDistinct] using hYB
    have hTargetS :
        (nativeE ring N e (ring.rightNeighbor e)).sg =
          (N (ring.rightNeighbor e)).sg := by
      simpa [nativeE, hDistinct] using hYS
    intro i
    by_cases hi : i = e
    · subst i
      refine ⟨hSourceL, hSourceB, ?_, ?_⟩
      · intro _
        exact hSourceS
      · intro hl
        rw [hxFollower] at hl
        cases hl
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        refine ⟨hTargetL, hTargetB, ?_, ?_⟩
        · intro hs
          rw [hTargetS]
          exact hs
        · intro _
          exact hTargetS
      · rw [grantDrainEntranceNativeEFrame ring N e i hi hj]
        exact ⟨rfl, rfl, (fun h => h), (fun _ => rfl)⟩

/-- The signal-expansion rank theorem now applies to an actual
quiet responder leader, even when the pair intersects the OLD
warm-host scan. -/
theorem grantDrainD6QuietResponderSignalExpansionRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxFollower : (s.native e).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hyQuiet : (s.native (ring.rightNeighbor e)).sg = false) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hRows :=
    grantDrainD6QuietResponderSignalExpansionFields
      ring (by omega : 2 ≤ n) s.native e
      hxFollower hxEmpty hyLeader hyQuiet
  have hOldFront :=
    grantDrainD6OldWarmFrontLeader ring hn s g hC hWarm
  exact grantDrainWarmSignalExpansionRank
    ring s.native (nativeE ring s.native e) g
    (fun i => (hRows i).1)
    (fun i => (hRows i).2.1)
    ((hRows (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).2.2.2
      hOldFront)
    (fun i hs => (hRows i).2.2.1 hs)

/-- A follower with no bullet, serving a follower with a
resident LIVE/DUMMY, does not change the native word at all:
C_native makes the responder's OLD signal zero. -/
theorem grantDrainD6StationaryBulletResponderNativeE
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hC : C_native ring N)
    (hxFollower : (N e).l = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hyBullet : HasBullet N (ring.rightNeighbor e)) :
    nativeE ring N e = N := by
  have hyZero :=
    grantDrainD6CleanBulletOwnSignalZero
      ring N hC (ring.rightNeighbor e) hyBullet
  have hPair :
      certLiteralEPair (N e) (N (ring.rightNeighbor e)) =
        (N e, N (ring.rightNeighbor e)) := by
    generalize N e = X at hxFollower hxEmpty ⊢
    generalize N (ring.rightNeighbor e) = Y at hyFollower hyZero ⊢
    rcases X with ⟨xl, xb, xsh, xsg⟩
    rcases Y with ⟨yl, yb, ysh, ysg⟩
    change xl = false at hxFollower
    change xb = (0 : Fin 3) at hxEmpty
    change yl = false at hyFollower
    change ysg = false at hyZero
    subst xl
    subst xb
    subst yl
    subst ysg
    rcases grantDrainEntranceLocalFinThreeCases yb with hb | hb | hb <;>
      rw [hb] <;>
      simp [certLiteralEPair, certFinThree]
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  funext i
  by_cases hi : i = e
  · subst i
    simpa [nativeE] using congrArg Prod.fst hPair
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa [nativeE, hDistinct] using congrArg Prod.snd hPair
    · exact grantDrainEntranceNativeEFrame ring N e i hi hj

/-- All E rows with an OLD empty follower source and a NOT-ready
responder now have a derived W nonincrease: empty follower target
, stationary follower bullet (above), or quiet leader
(signal-copy row above). No hERank assumption occurs. -/
theorem grantDrainD6EmptyFollowerNotReadyResponderERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxFollower : (s.native e).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyNotReady :
      (s.native (ring.rightNeighbor e)).l = false ∨
      (s.native (ring.rightNeighbor e)).sg = false) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  by_cases hyLeader :
      (s.native (ring.rightNeighbor e)).l = true
  · have hyQuiet :
        (s.native (ring.rightNeighbor e)).sg = false := by
      rcases hyNotReady with hyFollower | hyQuiet
      · rw [hyLeader] at hyFollower
        cases hyFollower
      · exact hyQuiet
    exact grantDrainD6QuietResponderSignalExpansionRank
      ring hn s e g hC hWarm
      hxFollower hxEmpty hyLeader hyQuiet
  · have hyFollower :
        (s.native (ring.rightNeighbor e)).l = false := by
      cases hl : (s.native (ring.rightNeighbor e)).l with
      | false => rfl
      | true => exact False.elim (hyLeader hl)
    by_cases hyEmpty :
        (s.native (ring.rightNeighbor e)).b = (0 : Fin 3)
    · have hFront :=
        grantDrainD6OldWarmFrontLeader ring hn s g hC hWarm
      exact grantDrainD6EScanEmptyFollowerPair
        ring s.native e g hxFollower hxEmpty
        hyFollower hyEmpty hFront
    · have hIdentity :=
        grantDrainD6StationaryBulletResponderNativeE
          ring (by omega : 2 ≤ n) s.native e hC
          hxFollower hxEmpty hyFollower hyEmpty
      rw [hIdentity]
      exact Nat.le_refl _

/-- Consequent selected-FIRE s1n result for the newly completed
source-empty / responder-not-ready E family. The birth lift uses
the existing, proved conditional bridge only after its E-rank
premise has been discharged by the preceding theorem. -/
theorem grantDrainD6NonExceptionalBirthRankLiftEmptySourceNotReady
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyNotReady :
      (s.native (ring.rightNeighbor e)).l = false ∨
      (s.native (ring.rightNeighbor e)).sg = false) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g + 1 := by
  have hERank :=
    grantDrainD6EmptyFollowerNotReadyResponderERankLe
      ring hn s e g hC hWarm
      hxFollower hxEmpty hyNotReady
  exact grantDrainD6NonExceptionalBirthRankLiftOfERank
    ring hn fresh update s e g z hC hNonExceptional
    hSelected hz hStillWarm hERank

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6OldWarmFrontLeader
#print axioms L3.GrantDrainEntrance.grantDrainD6QuietResponderSignalExpansionFields
#print axioms L3.GrantDrainEntrance.grantDrainD6QuietResponderSignalExpansionRank
#print axioms L3.GrantDrainEntrance.grantDrainD6StationaryBulletResponderNativeE
#print axioms L3.GrantDrainEntrance.grantDrainD6EmptyFollowerNotReadyResponderERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalBirthRankLiftEmptySourceNotReady

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Source-leader/follower and
ready-responder/front E rank subrows. No private imported declarations. -/

/-- Turning additional Bool entries true cannot shorten takeWhile. -/
theorem grantDrainD6TakeWhileLengthMono
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

/-- Removing the fixed-front-signal premise of the previous signal
expansion rank lemma is valid for a signal-one OLD host: turning its
front leader from quiet to ready can only LOWER its no-bullet rank. -/
theorem grantDrainD6WarmSignalExpansionRank
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N M : Fin n → CertNative) (g : Fin n)
    (hWarm : (N g).sg = true)
    (hLeaders : ∀ i : Fin n, (M i).l = (N i).l)
    (hBullets : ∀ i : Fin n, (M i).b = (N i).b)
    (hSignals : ∀ i : Fin n, (N i).sg = true →
      (M i).sg = true) :
    grantDrainWarmRank ring M g ≤
      grantDrainWarmRank ring N g := by
  have hD :
      grantDrainLeftLeaderDistance ring M g =
        grantDrainLeftLeaderDistance ring N g := by
    simp [grantDrainLeftLeaderDistance, hLeaders]
  have hB (d : Nat) :
      grantDrainLeftBulletDistance ring M g d =
        grantDrainLeftBulletDistance ring N g d := by
    simp [grantDrainLeftBulletDistance, hBullets]
  have hF (d : Nat) :
      grantDrainTerminalRun ring N g d ≤
        grantDrainTerminalRun ring M g d := by
    unfold grantDrainTerminalRun
    have hLen :=
      grantDrainD6TakeWhileLengthMono
        (List.range d)
        (fun k => (N (PPL.shiftLeft ring g k)).sg)
        (fun k => (M (PPL.shiftLeft ring g k)).sg)
        (by
          intro k _ hk
          exact hSignals (PPL.shiftLeft ring g k) hk)
    omega
  have hPos :=
    (grantDrainD6ExceptionalDistanceRange ring hn N g).1
  have hFBound :
      grantDrainTerminalRun ring N g
        (grantDrainLeftLeaderDistance ring N g) <
      grantDrainLeftLeaderDistance ring N g :=
    ((grantDrainWarmTerminalCharacterization
      ring N g
      (grantDrainLeftLeaderDistance ring N g)
      (grantDrainTerminalRun ring N g
        (grantDrainLeftLeaderDistance ring N g))
      hPos hWarm).mp rfl).1
  have hRun :=
    hF (grantDrainLeftLeaderDistance ring N g)
  simp only [grantDrainWarmRank, hD, hB]
  cases hBullet :
      grantDrainLeftBulletDistance ring N g
        (grantDrainLeftLeaderDistance ring N g) with
  | some p =>
      simp [hBullet]
      omega
  | none =>
      cases hOldFront :
          (N (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring N g))).sg with
      | true =>
          have hNewFront :=
            hSignals
              (PPL.shiftLeft ring g
                (grantDrainLeftLeaderDistance ring N g))
              hOldFront
          simp [hBullet, hOldFront, hNewFront]
      | false =>
          cases hNewFront :
              (M (PPL.shiftLeft ring g
                (grantDrainLeftLeaderDistance ring N g))).sg with
          | false =>
              simp [hBullet, hOldFront, hNewFront]
              omega
          | true =>
              simp [hBullet, hOldFront, hNewFront]
              omega

/-- A source that is an OLD leader, serving an OLD follower,
cannot leave an eligible empty responder unless the OLD source
was quiet and empty and the responder itself was empty. -/
theorem grantDrainD6SourceLeaderFollowerEligibleRow
    (x y : CertNative)
    (hxLeader : x.l = true)
    (hyFollower : y.l = false)
    (hAfterEmpty :
      (certLiteralEPair x y).2.b = (0 : Fin 3)) :
    x.b = (0 : Fin 3) ∧ x.sg = false ∧
      y.b = (0 : Fin 3) := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with rfl | rfl | rfl <;>
    rcases grantDrainEntranceLocalFinThreeCases yb with rfl | rfl | rfl <;>
    cases xl <;> cases yl <;> cases xsh <;>
    cases ysh <;> cases xsg <;> cases ysg <;>
    simp [certLiteralEPair, certFinThree] at *

/-- Under an OLD source-leader and OLD follower-responder pair,
any selected FIRE is rightLocal. Eligibility then forces precisely
the quiet, bullet-free source and empty follower row above. -/
theorem grantDrainD6SourceLeaderSelectedFollowerFields
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e z : Fin n)
    (hxLeader : (s.native e).l = true)
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e)) :
    z = ring.rightNeighbor e ∧
    (s.native e).b = (0 : Fin 3) ∧
    (s.native e).sg = false ∧
    (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) := by
  have hSourceLeader :
      (nativeE ring s.native e e).l = true := by
    have hSource :=
      grantDrainEntranceLiteralESourceLeaderFixed
        (s.native e) (s.native (ring.rightNeighbor e))
    simpa [nativeE] using hSource.trans hxLeader
  have hRight : grantDrainSelect ring s e = .rightLocal := by
    rcases hSelected with hLeft | hRight | hCross
    · have hEligible :=
        grantDrainD6SelectedEligible ring s e z
          (Or.inl hLeft)
      rw [hLeft.2] at hEligible
      simp [grantDrainEligible, hSourceLeader] at hEligible
    · exact hRight.1
    · have hEligible :=
        grantDrainD6SelectedEligible ring s e z
          (Or.inr (Or.inr hCross))
      rw [hCross.2] at hEligible
      simp [grantDrainEligible, hSourceLeader] at hEligible
  have hz :
      z = ring.rightNeighbor e := by
    rcases hSelected with hLeft | hSelectedRight | hCross
    · rw [hRight] at hLeft
      cases hLeft.1
    · exact hSelectedRight.2
    · rw [hRight] at hCross
      cases hCross.1
  have hEligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = true :=
    grantDrainD6SelectedEligible ring s e
      (ring.rightNeighbor e)
      (Or.inr (Or.inl ⟨hRight, rfl⟩))
  have hPostVal :
      (nativeE ring s.native e (ring.rightNeighbor e)).b.val =
        0 := by
    by_cases hb :
        (nativeE ring s.native e
          (ring.rightNeighbor e)).b.val = 0
    · exact hb
    · have hBad :
          grantDrainEligible (nativeE ring s.native e)
            (ring.rightNeighbor e) = false := by
        simp [grantDrainEligible, hb]
      rw [hBad] at hEligible
      cases hEligible
  have hPostEmpty :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (0 : Fin 3) := by
    apply Fin.ext
    exact hPostVal
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPairEmpty :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.b =
          (0 : Fin 3) := by
    simpa [nativeE, hDistinct] using hPostEmpty
  obtain ⟨hxEmpty, hxQuiet, hyEmpty⟩ :=
    grantDrainD6SourceLeaderFollowerEligibleRow
      (s.native e) (s.native (ring.rightNeighbor e))
      hxLeader hyFollower hPairEmpty
  exact ⟨hz, hxEmpty, hxQuiet, hyEmpty⟩

/-- (A), the complete source-leader/OLD follower-responder family.
The selected post-E FIRE eligibility derives the quiet-empty
source row; this is not an unproved row hypothesis. -/
theorem grantDrainD6SourceLeaderFollowerERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (_hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (_hz : z ≠ g)
    (_hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxLeader : (s.native e).l = true)
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  obtain ⟨_, hxEmpty, hxQuiet, _⟩ :=
    grantDrainD6SourceLeaderSelectedFollowerFields
      ring hn s e z hxLeader hyFollower hSelected
  have hRows :=
    grantDrainEntranceQuietEmptySourceNativeERows
      ring (by omega : 2 ≤ n) s.native e
      (Or.inr hxQuiet) hxEmpty hyFollower
  have hSignals :
      ∀ i : Fin n, (s.native i).sg = true →
        (nativeE ring s.native e i).sg = true := by
    intro i hi
    by_cases he : i = e
    · subst i
      rw [hRows.2.1, hi]
      simp
    · by_cases hy : i = ring.rightNeighbor e
      · subst i
        rw [hRows.2.2]
        exact hi
      · rw [grantDrainEntranceNativeEFrame
          ring s.native e i he hy]
        exact hi
  exact grantDrainD6WarmSignalExpansionRank
    ring hn s.native (nativeE ring s.native e) g
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).2.2
    (fun i => (hRows.1 i).1)
    (fun i => (hRows.1 i).2)
    hSignals

/-- An actual selected FIRE at a ready old responder must
take place at the source e, never at the DUMMY-emitting
responder. Its birth site differs from g, so g differs from e. -/
theorem grantDrainD6ReadyResponderSelectedAway
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g) :
    z = e ∧ g ≠ e := by
  have hNoRight :=
    grantDrainD6CompositeReadyResponderNotRightFire
      ring hn s e hyLeader hyReady
  have hSite : z = e := by
    rcases hSelected with hLeft | hRight | hCross
    · exact hLeft.2
    · exact False.elim (hNoRight hRight.1)
    · exact hCross.2
  refine ⟨hSite, ?_⟩
  intro hGE
  exact hz (hSite.trans hGE.symm)

/-- (B) ready old responder p as the actual preceding leader
of the old warm host g. The source is an empty follower, hence
the ready responder survives and emits exactly one DUMMY at
distance a. The signal-one prefix is framed and W falls from
1+a to a. This is an E-only fact. -/
theorem grantDrainD6ReadyResponderFrontERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hSector : sectorLength ring s.native p D)
    (hAt : g = PPL.shiftRight ring p a)
    (ha : 1 ≤ a) (haInside : a < D.val)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = a)
    (hTo : ring.rightNeighbor e = p)
    (hxFollower : (s.native e).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hReady : (s.native p).sg = true)
    (hNotHostSource : g ≠ e) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have haN : a < n := by
    have hBound := D.isLt
    omega
  have hOldScan :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g a ha haN).mp hDistance
  have hFront : PPL.shiftLeft ring g a = p := by
    rw [hAt, grantDrainMarksArcShiftLeftRight
      ring p a a (Nat.le_refl _) haN,
      Nat.sub_self, grantDrainWeakDeathShiftRightZero ring p]
  have hOldFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  have hNotP :
      ∀ j : Nat, j < a →
        PPL.shiftLeft ring g j ≠ p := by
    intro j hj heq
    by_cases hjZero : j = 0
    · subst j
      rw [grantDrainWarmShiftLeftZero] at heq
      rw [heq, hSector.2.1] at hOldFollower
      cases hOldFollower
    · have hF := hOldScan.2 j (by omega) hj
      rw [heq, hSector.2.1] at hF
      cases hF
  have hNotE :
      ∀ j : Nat, j < a →
        PPL.shiftLeft ring g j ≠ e := by
    intro j hj
    by_cases hjZero : j = 0
    · subst j
      simpa only [grantDrainWarmShiftLeftZero] using
        hNotHostSource
    · exact grantDrainD6DeathSourceOutsidePositive
        ring hn e p g a haN hAt hTo
        j (by omega) (by omega)
  have hFrame :
      ∀ j : Nat, j < a →
        nativeE ring s.native e (PPL.shiftLeft ring g j) =
          s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    exact grantDrainEntranceNativeEFrame
      ring s.native e (PPL.shiftLeft ring g j)
      (hNotE j hj)
      (by rw [hTo]; exact hNotP j hj)
  have hyLeader :
      (s.native (ring.rightNeighbor e)).l = true := by
    rw [hTo]
    exact hSector.2.1
  have hyReady :
      (s.native (ring.rightNeighbor e)).sg = true := by
    rw [hTo]
    exact hReady
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hYFixed :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l =
        (s.native (ring.rightNeighbor e)).l := by
    have hPair :
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).2.l =
            (s.native (ring.rightNeighbor e)).l := by
      simp [certLiteralEPair, hxFollower, hxEmpty, hyLeader]
    simpa [nativeE, hDistinct] using hPair
  have hLeaders :=
    grantDrainEntranceNativeELeadersFixed
      ring (by omega : 2 ≤ n) s.native e hYFixed
  have hNewDistance :
      grantDrainLeftLeaderDistance
        ring (nativeE ring s.native e) g = a := by
    have hSame :
        grantDrainLeftLeaderDistance
          ring (nativeE ring s.native e) g =
          grantDrainLeftLeaderDistance ring s.native g := by
      simp [grantDrainLeftLeaderDistance, hLeaders]
    exact hSame.trans hDistance
  have hOldPrefix :=
    grantDrainD6ReadyResponderWarmPrefix
      ring s.native p g D a hC hSector ha haInside hAt hReady
  have hOldNone :
      grantDrainLeftBulletDistance ring s.native g a = none := by
    apply (grantDrainWarmBulletNoneCharacterization
      ring s.native g a).mpr
    intro j _ hj
    rw [hOldPrefix.2 j hj]
    rfl
  have hNewYBullet :
      (nativeE ring s.native e p).b = (1 : Fin 3) := by
    rw [← hTo]
    exact grantDrainEntranceNativeEReadyVictimBulletDummy
      ring (by omega : 2 ≤ n) s.native e
      hyLeader hyReady
  have hNewFirst :
      grantDrainLeftBulletDistance ring
        (nativeE ring s.native e) g a = some a := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring (nativeE ring s.native e) g a a).mpr
    refine ⟨ha, Nat.le_refl _, ?_, ?_⟩
    · rw [hFront, hNewYBullet]
      decide
    · intro j hj hja
      rw [hFrame j hja, hOldPrefix.2 j (by omega)]
      rfl
  have hNewGSignal :
      (nativeE ring s.native e g).sg = true := by
    have hHead := hFrame 0 (by omega)
    rw [grantDrainWarmShiftLeftZero] at hHead
    rw [hHead]
    exact (grantDrainD6ExceptionalDeathHostFields s g hWarm).2.2
  have hNewTerminal :
      grantDrainTerminalRun ring (nativeE ring s.native e) g a =
        a - 1 := by
    apply (grantDrainWarmTerminalCharacterization
      ring (nativeE ring s.native e) g a (a - 1)
      ha hNewGSignal).mpr
    refine ⟨by omega, ?_, Or.inl (by omega)⟩
    intro j hj
    rw [hFrame j (by omega)]
    exact hOldPrefix.1 j (by omega)
  have hOldRank :
      grantDrainWarmRank ring s.native g = 1 + a := by
    simp [grantDrainWarmRank, hDistance, hOldNone,
      hFront, hReady]
  have hNewRank :
      grantDrainWarmRank ring (nativeE ring s.native e) g =
        a := by
    simp [grantDrainWarmRank, hNewDistance,
      hNewFirst, hNewTerminal]
    omega
  rw [hOldRank, hNewRank]
  omega

/-- (B), selected-FIRE specialization of the ready responder's
own-sector subrow. The source-host separation is derived from
the actual first-match selector, not assumed. -/
theorem grantDrainD6ReadyResponderSelectedFrontERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g z : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (_hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (_hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hSector : sectorLength ring s.native p D)
    (hAt : g = PPL.shiftRight ring p a)
    (ha : 1 ≤ a) (haInside : a < D.val)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = a)
    (hTo : ring.rightNeighbor e = p)
    (hxFollower : (s.native e).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyReady : (s.native p).sg = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hyLeader :
      (s.native (ring.rightNeighbor e)).l = true := by
    rw [hTo]
    exact hSector.2.1
  have hySignal :
      (s.native (ring.rightNeighbor e)).sg = true := by
    rw [hTo]
    exact hyReady
  have hNotG :=
    (grantDrainD6ReadyResponderSelectedAway
      ring hn s e g z hyLeader hySignal hSelected hz).2
  exact grantDrainD6ReadyResponderFrontERankLe
    ring hn s e p g D a hC hWarm hSector
    hAt ha haInside hDistance hTo hxFollower hxEmpty
    hyReady hNotG

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! D6-PAIR-SCAN: literal outgoing follower LIVE/DUMMY rows.
No unconditional warm-rank transfer is assumed here. -/

/-- A C_native OLD bullet site necessarily has a zero signal. -/
theorem grantDrainD6OutgoingBulletSourceQuiet
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hC : C_native ring N) (e : Fin n)
    (hxBullet : (N e).b ≠ (0 : Fin 3)) :
    (N e).sg = false := by
  exact grantDrainD6CleanBulletOwnSignalZero
    ring N hC e hxBullet

/-- C_native prevents a second bullet at a follower responder.
The source LIVE/DUMMY moves and both endpoint signals are zero. -/
theorem grantDrainD6OutgoingBulletFollowerEFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hC : C_native ring N)
    (hxFollower : (N e).l = false)
    (hxBullet : (N e).b ≠ (0 : Fin 3))
    (hyFollower : (N (ring.rightNeighbor e)).l = false) :
    (N (ring.rightNeighbor e)).b = (0 : Fin 3) ∧
    (N e).sg = false ∧
    (nativeE ring N e e).b = (0 : Fin 3) ∧
    (nativeE ring N e e).sg = false ∧
    (nativeE ring N e (ring.rightNeighbor e)).b = (N e).b ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hC.1
  have hyEmpty :=
    grantDrainEntranceILocalFollowerBulletNextEmpty
      ring N e hLocal hxBullet hyFollower
  have hxQuiet :=
    grantDrainD6OutgoingBulletSourceQuiet ring N hC e hxBullet
  have hRows :=
    grantDrainEntranceNonleaderBulletNativeE
      ring (by omega : 2 ≤ n) N e
      hxFollower hyFollower hxBullet hyEmpty hxQuiet
  exact ⟨hyEmpty, hxQuiet, hRows.1, hRows.2.1,
    hRows.2.2.1, hRows.2.2.2⟩

/-- This follower-to-follower E row does not change the leader
flags at any site, although the bullet actually moves. -/
theorem grantDrainD6OutgoingBulletFollowerELeaders
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (_hxFollower : (N e).l = false)
    (hyFollower : (N (ring.rightNeighbor e)).l = false) :
    ∀ i : Fin n, (nativeE ring N e i).l = (N i).l := by
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hLocal :=
    grantDrainEntranceLiteralEFollowerResponderRemains
      (N e) (N (ring.rightNeighbor e)) hyFollower
  have hResponder :
      (nativeE ring N e (ring.rightNeighbor e)).l =
        (N (ring.rightNeighbor e)).l := by
    simpa [nativeE, hDistinct, hyFollower] using hLocal
  exact grantDrainEntranceNativeELeadersFixed
    ring (by omega : 2 ≤ n) N e hResponder

/-- When the moving bullet is the OLD first bullet in the
inclusive scan at offset k+1 and moves to offset k >= 1,
settlement bounds any terminal-run loss to one position. -/
theorem grantDrainD6OutgoingBulletFirstInScanERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (d k : Nat)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = d)
    (hDShort : d < n)
    (hk : 1 ≤ k) (hInside : k + 1 ≤ d)
    (hFirst :
      grantDrainLeftBulletDistance ring s.native g d =
        some (k + 1))
    (hSource : e = PPL.shiftLeft ring g (k + 1))
    (hTarget : ring.rightNeighbor e =
      PPL.shiftLeft ring g k) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hRows :=
    grantDrainD6OutgoingBulletFollowerEFields
      ring hn s.native e hC hxFollower hxBullet hyFollower
  have hLeaders :=
    grantDrainD6OutgoingBulletFollowerELeaders
      ring hn s.native e hxFollower hyFollower
  have hWarmSignal :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).2.2
  have hkN : k + 1 < n := by omega
  have hPrefix :
      ∀ j : Nat, j < k →
        nativeE ring s.native e (PPL.shiftLeft ring g j) =
        s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    have hjN : j < n := by omega
    have he : PPL.shiftLeft ring g j ≠ e := by
      rw [hSource]
      exact grantDrainD6BirthLeftOffsetsDistinct
        ring g j (k + 1) hjN hkN (by omega)
    have hy :
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
      rw [hTarget]
      exact grantDrainD6BirthLeftOffsetsDistinct
        ring g j k hjN (by omega) (by omega)
    exact grantDrainEntranceNativeEFrame
      ring s.native e _ he hy
  have hSignals :
      ∀ j : Nat, j < k →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).sg =
        (s.native (PPL.shiftLeft ring g j)).sg := by
    intro j hj
    exact congrArg CertNative.sg (hPrefix j hj)
  have hBullets :
      ∀ j : Nat, 1 ≤ j → j < k →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).b.val =
        (s.native (PPL.shiftLeft ring g j)).b.val := by
    intro j _ hj
    exact congrArg (fun x : CertNative => x.b.val)
      (hPrefix j hj)
  have hNonzero : (s.native e).b.val ≠ 0 := by
    intro hz
    apply hxBullet
    apply Fin.ext
    exact hz
  have hNewNear :
      (nativeE ring s.native e
        (PPL.shiftLeft ring g k)).b.val ≠ 0 := by
    rw [← hTarget, hRows.2.2.2.2.1]
    exact hNonzero
  have hNewFar :
      (nativeE ring s.native e
        (PPL.shiftLeft ring g (k + 1))).b.val = 0 := by
    rw [← hSource, hRows.2.2.1]
    rfl
  have hMove :=
    grantDrainD6PairFirstBulletMoveRankSignal
      ring s.native (nativeE ring s.native e)
      g d k hk hInside hC hWarmSignal
      hLeaders hSignals hBullets hDistance hFirst
      hNewNear hNewFar
  exact Nat.le_trans (Nat.le_succ _) hMove.2.2.2

/-- If the pair is entirely outside the inclusive OLD scan,
native E leaves the scanned rank exactly unchanged. -/
theorem grantDrainD6OutgoingBulletOutsideScanERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (_hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (_hC : C_native ring s.native)
    (_hWarm : grantDrainWarmAt s g = true)
    (_hxFollower : (s.native e).l = false)
    (_hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hOutside : ∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g j ≠ e ∧
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  exact Nat.le_of_eq
    (grantDrainD6EScanOutsidePair ring s.native e g hOutside)

/-- For a leader responder, literal E consumes the source bullet.
LIVE kills the leader exactly when the ready-reset or unshielded
condition makes its shield false; DUMMY cannot kill it. -/
theorem grantDrainD6OutgoingBulletLeaderDeathIff
    (x y : CertNative)
    (hxFollower : x.l = false)
    (hxBullet : x.b ≠ (0 : Fin 3))
    (hxQuiet : x.sg = false)
    (hyLeader : y.l = true) :
    (certLiteralEPair x y).2.l = false ↔
      x.b = (2 : Fin 3) ∧
        (y.sg = true ∨ y.sh = false) := by
  rcases grantDrainEntranceNonzeroBulletKind x.b hxBullet with hb | hb
  · cases hs : y.sg <;> cases hh : y.sh <;>
      simp [certLiteralEPair, certFinThree, hxFollower,
        hxQuiet, hyLeader, hb, hs, hh]
  · cases hs : y.sg <;> cases hh : y.sh <;>
      simp [certLiteralEPair, certFinThree, hxFollower,
        hxQuiet, hyLeader, hb, hs, hh]

/-- Post-step warmness excludes an incoming moving bullet from
entering the tracked warm host. This handles the k=0 contact
case without treating a future comparison as an assumption. -/
theorem grantDrainD6OutgoingBulletFollowerWarmOutsideEndpoints
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false) :
    e ≠ g ∧ ring.rightNeighbor e ≠ g := by
  have hHost :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have he : e ≠ g := by
    intro heq
    rw [heq] at hxBullet
    exact hxBullet hHost.2.1
  have hRows :=
    grantDrainD6OutgoingBulletFollowerEFields
      ring hn s.native e hC hxFollower hxBullet hyFollower
  have hBirth :=
    grantDrainD6NativeNextIsBirth ring s e z hSelected
  have hPost :=
    grantDrainD6PostENativeStillWarm
      ring fresh update s e g z hBirth hz hStillWarm
  have hy : ring.rightNeighbor e ≠ g := by
    intro hyEq
    have hAt :
        (nativeE ring s.native e
          (ring.rightNeighbor e)).sg = true := by
      rw [hyEq]
      exact hPost.2
    rw [hRows.2.2.2.2.2] at hAt
    cases hAt
  exact ⟨he, hy⟩

/-- Combining the proved first-left-bullet E inequality with the
existing selected-FIRE bridge yields the desired +1 rank lift
for this concrete overlapping interior family. -/
theorem grantDrainD6OutgoingBulletFirstInScanBirthRankLift
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (d k : Nat)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = d)
    (hDShort : d < n)
    (hk : 1 ≤ k) (hInside : k + 1 ≤ d)
    (hFirst :
      grantDrainLeftBulletDistance ring s.native g d =
        some (k + 1))
    (hSource : e = PPL.shiftLeft ring g (k + 1))
    (hTarget : ring.rightNeighbor e =
      PPL.shiftLeft ring g k) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g + 1 := by
  have hERank := grantDrainD6OutgoingBulletFirstInScanERankLe
    ring hn s e g hC hWarm hxFollower hxBullet
    hyFollower d k hDistance hDShort hk hInside hFirst
    hSource hTarget
  exact grantDrainD6NonExceptionalBirthRankLiftOfERank
    ring hn fresh update s e g z hC hNonExceptional
    hSelected hz hStillWarm hERank

/-- The selected-FIRE rank lift on the unscanned outgoing bullet
family, independent of how the local E bullet is consumed. -/
theorem grantDrainD6OutgoingBulletOutsideScanBirthRankLift
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hOutside : ∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g j ≠ e ∧
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g + 1 := by
  have hERank := grantDrainD6OutgoingBulletOutsideScanERankLe
    ring hn s e g hC hWarm hxFollower hxBullet hOutside
  exact grantDrainD6NonExceptionalBirthRankLiftOfERank
    ring hn fresh update s e g z hC hNonExceptional
    hSelected hz hStillWarm hERank

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6WarmSignalExpansionRank
#print axioms L3.GrantDrainEntrance.grantDrainD6SourceLeaderFollowerEligibleRow
#print axioms L3.GrantDrainEntrance.grantDrainD6SourceLeaderSelectedFollowerFields
#print axioms L3.GrantDrainEntrance.grantDrainD6SourceLeaderFollowerERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderSelectedAway
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderFrontERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderSelectedFrontERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletSourceQuiet
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletFollowerEFields
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletFollowerELeaders
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletFirstInScanERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletOutsideScanERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletLeaderDeathIff
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletFollowerWarmOutsideEndpoints
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletFirstInScanBirthRankLift
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletOutsideScanBirthRankLift

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Genuine C_native source-bullet geometry. -/

/-- Successor of a positive backward offset p is offset p-1. -/
theorem grantDrainD6OutgoingBulletSuccessorAtOffset
    {n : Nat} (ring : DirectedRing n)
    (g e : Fin n) (p : Nat)
    (hp : 1 ≤ p) (hpShort : p < n)
    (hSource : e = PPL.shiftLeft ring g p) :
    ring.rightNeighbor e = PPL.shiftLeft ring g (p - 1) := by
  have hG : PPL.shiftRight ring e p = g := by
    rw [hSource]
    exact grantDrainD6BirthShiftCancel ring g p hpShort
  have hArc := grantDrainMarksArcShiftLeftRight
    ring e p (p - 1) (by omega) hpShort
  rw [hG] at hArc
  have hUnit : p - (p - 1) = 1 := by omega
  rw [hUnit] at hArc
  have hRight :
      PPL.shiftRight ring e 1 = ring.rightNeighbor e := by
    apply Fin.ext
    rfl
  rw [hRight] at hArc
  exact hArc.symm

/-- A warm OLD follower has its actual preceding leader at d<n. -/
theorem grantDrainD6OutgoingBulletOldDistanceShort
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true) :
    1 ≤ grantDrainLeftLeaderDistance ring s.native g ∧
      grantDrainLeftLeaderDistance ring s.native g < n := by
  have hRange :=
    grantDrainD6ExceptionalDistanceRange ring hn s.native g
  have hFront :=
    grantDrainD6OldWarmFrontLeader ring hn s g hC hWarm
  have hFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  have hNotFull :
      grantDrainLeftLeaderDistance ring s.native g ≠ n := by
    intro hFull
    rw [hFull, grantDrainD6ExceptionalFullShift ring g]
      at hFront
    rw [hFollower] at hFront
    cases hFront
  exact ⟨hRange.1, by omega⟩

/-- Sector ownership converts the local clockwise coordinate a
of an OLD follower into the nearest-left leader distance. -/
theorem grantDrainD6OutgoingBulletSectorDistance
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (g p : Fin n)
    (D : Fin (n + 1)) (a : Fin n)
    (hSector : sectorLength ring N p D)
    (haInside : a.val < D.val)
    (hAt : g = PPL.shiftRight ring p a.val)
    (hFollower : (N g).l = false) :
    1 ≤ a.val ∧
      grantDrainLeftLeaderDistance ring N g = a.val := by
  have haPos : 1 ≤ a.val := by
    by_cases haZero : a.val = 0
    · have hSame : g = p := by
        calc
          g = PPL.shiftRight ring p a.val := hAt
          _ = PPL.shiftRight ring p 0 := by rw [haZero]
          _ = p := grantDrainWeakDeathShiftRightZero ring p
      rw [hSame, hSector.2.1] at hFollower
      cases hFollower
    · omega
  have hLeader :
      (N (PPL.shiftLeft ring g a.val)).l = true := by
    rw [hAt, grantDrainMarksArcShiftLeftRight
      ring p a.val a.val (Nat.le_refl _) a.isLt,
      Nat.sub_self, grantDrainWeakDeathShiftRightZero ring p]
    exact hSector.2.1
  have hNoEarlier :
      ∀ k : Nat, 1 ≤ k → k < a.val →
        (N (PPL.shiftLeft ring g k)).l = false := by
    intro k hk hkEarlier
    have hShift :
        PPL.shiftLeft ring g k =
          PPL.shiftRight ring p (a.val - k) := by
      rw [hAt]
      exact grantDrainMarksArcShiftLeftRight
        ring p a.val k (by omega) a.isLt
    rw [hShift]
    exact hSector.2.2.2
      (⟨a.val - k, show a.val - k < n by omega⟩ : Fin n)
      (by dsimp only; omega) (by dsimp only; omega)
  have hd :=
    (grantDrainWarmLeaderFirstCharacterization
      ring N g a.val haPos a.isLt).mpr
      ⟨hLeader, hNoEarlier⟩
  exact ⟨haPos, hd⟩

/-- Within the OLD scan, C_native sector uniqueness makes the
source's LIVE/DUMMY the FIRST bullet, not an arbitrary bullet. -/
theorem grantDrainD6OutgoingBulletInScanIsFirst
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (_hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (p : Nat) (hp : 1 ≤ p)
    (hpBefore : p < grantDrainLeftLeaderDistance
      ring s.native g)
    (hSource : e = PPL.shiftLeft ring g p) :
    grantDrainLeftBulletDistance ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g) =
        some p := by
  obtain ⟨q, D, a, hSector, haInside, hAt⟩ :=
    grantDrainEntranceSectorCoverOfRoot
      ring s.native hC.1.1.1 g
  have hFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  have hDist :=
    (grantDrainD6OutgoingBulletSectorDistance
      ring s.native g q D a hSector haInside hAt hFollower).2
  have hpLt : p < a.val := by
    rw [← hDist]
    exact hpBefore
  have hSourceAt :
      PPL.shiftLeft ring g p =
        PPL.shiftRight ring q (a.val - p) := by
    rw [hAt]
    exact grantDrainMarksArcShiftLeftRight
      ring q a.val p (by omega) a.isLt
  have hSiteBullet :
      HasBullet s.native (PPL.shiftRight ring q (a.val - p)) := by
    rw [← hSourceAt, ← hSource]
    exact hxBullet
  have hUnique := (hC.1.2 q D hSector).1
  apply (grantDrainWarmBulletSomeCharacterization
    ring s.native g
    (grantDrainLeftLeaderDistance ring s.native g) p).mpr
  refine ⟨hp, by omega, ?_, ?_⟩
  · rw [← hSource]
    intro hZero
    apply hxBullet
    apply Fin.ext
    exact hZero
  · intro j hj hjBefore
    have hjLt : j < a.val := by omega
    have hJAt :
        PPL.shiftLeft ring g j =
          PPL.shiftRight ring q (a.val - j) := by
      rw [hAt]
      exact grantDrainMarksArcShiftLeftRight
        ring q a.val j (by omega) a.isLt
    by_cases hJEmpty :
        (s.native (PPL.shiftLeft ring g j)).b =
          (0 : Fin 3)
    · rw [hJEmpty]
      rfl
    · have hJBullet :
          HasBullet s.native
            (PPL.shiftRight ring q (a.val - j)) := by
        rw [← hJAt]
        exact hJEmpty
      have hEq :
          (⟨a.val - p, show a.val - p < n by omega⟩ : Fin n) =
          (⟨a.val - j, show a.val - j < n by omega⟩ : Fin n) :=
        hUnique
          (⟨a.val - p, show a.val - p < n by omega⟩ : Fin n)
          (⟨a.val - j, show a.val - j < n by omega⟩ : Fin n)
          (by dsimp only; omega) (by dsimp only; omega) hSiteBullet hJBullet
      have hv := congrArg Fin.val hEq
      dsimp only at hv
      omega

/-- For a moving OLD follower bullet, once the responder is
known different from the still-warm host, either the entire
selected pair misses the OLD inclusive scan, or the source is
the unique first bullet in that scan and its successor is the
previous offset. This is derived from C_native and ring geometry. -/
theorem grantDrainD6OutgoingBulletFollowerScanDichotomy
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (_hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hNotResponder : ring.rightNeighbor e ≠ g) :
    (∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g j ≠ e ∧
      PPL.shiftLeft ring g j ≠ ring.rightNeighbor e) ∨
    (∃ k : Nat,
      1 ≤ k ∧
      k + 1 ≤ grantDrainLeftLeaderDistance ring s.native g ∧
      grantDrainLeftLeaderDistance ring s.native g < n ∧
      grantDrainLeftBulletDistance ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) =
        some (k + 1) ∧
      e = PPL.shiftLeft ring g (k + 1) ∧
      ring.rightNeighbor e = PPL.shiftLeft ring g k) := by
  have hWarmEmpty :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).2.1
  have hDist :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hOldFront :=
    grantDrainD6OldWarmFrontLeader ring hn s g hC hWarm
  have hpShort :
      PPL.cyclicOffset ring e g < n :=
    grantDrainEntranceArcOffsetLt ring e g
  have hSource :
      e = PPL.shiftLeft ring g (PPL.cyclicOffset ring e g) :=
    (grantDrainEntranceLeftOffset ring e g).symm
  have hpPositive : 1 ≤ PPL.cyclicOffset ring e g := by
    by_cases hZero : PPL.cyclicOffset ring e g = 0
    · have hAt := grantDrainEntranceLeftOffset ring e g
      rw [hZero, grantDrainWarmShiftLeftZero ring g] at hAt
      have hEG : e = g := hAt.symm
      rw [hEG] at hxBullet
      exact False.elim (hxBullet hWarmEmpty)
    · omega
  have hNeighbor :=
    grantDrainD6OutgoingBulletSuccessorAtOffset
      ring g e (PPL.cyclicOffset ring e g)
      hpPositive hpShort hSource
  by_cases hWithin :
      PPL.cyclicOffset ring e g ≤
        grantDrainLeftLeaderDistance ring s.native g
  · have hNotFront :
        PPL.cyclicOffset ring e g ≠
          grantDrainLeftLeaderDistance ring s.native g := by
      intro hEq
      have hAt : e = PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g) := by
        rw [hEq] at hSource
        exact hSource
      have hFollower : (s.native e).l = false := by
        exact _hxFollower
      rw [hAt, hOldFront] at hFollower
      cases hFollower
    have hBefore :
        PPL.cyclicOffset ring e g <
          grantDrainLeftLeaderDistance ring s.native g := by
      omega
    have hNotOne :
        PPL.cyclicOffset ring e g ≠ 1 := by
      intro hOne
      have hNear := hNeighbor
      rw [hOne] at hNear
      have hOneSub : 1 - 1 = 0 := by omega
      rw [hOneSub, grantDrainWarmShiftLeftZero ring g] at hNear
      exact hNotResponder hNear
    have hFirst :=
      grantDrainD6OutgoingBulletInScanIsFirst
        ring hn s e g hC hWarm hxBullet
        (PPL.cyclicOffset ring e g)
        hpPositive hBefore hSource
    have hK :
        PPL.cyclicOffset ring e g - 1 + 1 =
          PPL.cyclicOffset ring e g := by omega
    right
    refine ⟨PPL.cyclicOffset ring e g - 1,
      by omega, by omega, hDist.2, ?_, ?_, hNeighbor⟩
    · simpa only [hK] using hFirst
    · simpa only [hK] using hSource
  · have hNotAdjacent :
        PPL.cyclicOffset ring e g ≠
          grantDrainLeftLeaderDistance ring s.native g + 1 := by
      intro hEq
      have hNear := hNeighbor
      rw [hEq] at hNear
      have hUnit :
          grantDrainLeftLeaderDistance ring s.native g + 1 - 1 =
            grantDrainLeftLeaderDistance ring s.native g := by
        omega
      rw [hUnit] at hNear
      have hYL : (s.native (ring.rightNeighbor e)).l = false :=
        hyFollower
      rw [hNear, hOldFront] at hYL
      cases hYL
    have hFar :
        grantDrainLeftLeaderDistance ring s.native g + 2 ≤
          PPL.cyclicOffset ring e g := by
      omega
    left
    intro j hj
    have hjShort : j < n := by omega
    constructor
    · rw [hSource]
      exact grantDrainD6BirthLeftOffsetsDistinct
        ring g j (PPL.cyclicOffset ring e g)
        hjShort hpShort (by omega)
    · rw [hNeighbor]
      exact grantDrainD6BirthLeftOffsetsDistinct
        ring g j (PPL.cyclicOffset ring e g - 1)
        hjShort (by omega) (by omega)

/-- Complete E-rank comparison for an outgoing LIVE/DUMMY
follower-to-follower service under the genuine continuing FIRE.
The old first bullet or outside-scan case is derived rather than
supplied as a disjunctive row assumption. -/
theorem grantDrainD6OutgoingBulletFollowerERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (_hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hNotResponder :=
    (grantDrainD6OutgoingBulletFollowerWarmOutsideEndpoints
      ring hn fresh update s e g z
      hC hWarm hSelected hz hStillWarm
      hxFollower hxBullet hyFollower).2
  rcases grantDrainD6OutgoingBulletFollowerScanDichotomy
      ring hn s e g hC hWarm hxFollower hxBullet
      hyFollower hNotResponder with
    hOutside | ⟨k, hk, hInside, hDShort,
      hFirst, hSource, hTarget⟩
  · exact grantDrainD6OutgoingBulletOutsideScanERankLe
      ring hn s e g hC hWarm hxFollower hxBullet hOutside
  · exact grantDrainD6OutgoingBulletFirstInScanERankLe
      ring hn s e g hC hWarm
      hxFollower hxBullet hyFollower
      (grantDrainLeftLeaderDistance ring s.native g) k
      rfl hDShort hk hInside hFirst hSource hTarget

/-- A physical outgoing OLD follower bullet meeting a leader
responder can affect the inclusive OLD host scan only when that
responder IS the first old left leader. All other such services
are completely outside the scan; this is the literal ring-edge
classification without relying on an abstract pair classifier. -/
theorem grantDrainD6OutgoingBulletLeaderOutsideOrFront
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true) :
    (∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g j ≠ e ∧
      PPL.shiftLeft ring g j ≠ ring.rightNeighbor e) ∨
    ring.rightNeighbor e =
      PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g) := by
  have hWarmFields :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hDist :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hDist.1 hDist.2).mp rfl
  have hpShort :=
    grantDrainEntranceArcOffsetLt ring e g
  have hSource :
      e = PPL.shiftLeft ring g
        (PPL.cyclicOffset ring e g) :=
    (grantDrainEntranceLeftOffset ring e g).symm
  have hpPositive : 1 ≤ PPL.cyclicOffset ring e g := by
    by_cases hpZero : PPL.cyclicOffset ring e g = 0
    · have hAt := grantDrainEntranceLeftOffset ring e g
      rw [hpZero, grantDrainWarmShiftLeftZero ring g] at hAt
      have hEG : e = g := hAt.symm
      rw [hEG] at hxBullet
      exact False.elim (hxBullet hWarmFields.2.1)
    · omega
  have hNeighbor :=
    grantDrainD6OutgoingBulletSuccessorAtOffset
      ring g e (PPL.cyclicOffset ring e g)
      hpPositive hpShort hSource
  by_cases hWithin :
      PPL.cyclicOffset ring e g ≤
        grantDrainLeftLeaderDistance ring s.native g
  · have hNotAtFront :
        PPL.cyclicOffset ring e g ≠
          grantDrainLeftLeaderDistance ring s.native g := by
      intro hEqual
      have he := hSource
      rw [hEqual] at he
      rw [he, hFirst.1] at hxFollower
      cases hxFollower
    have hBefore :
        PPL.cyclicOffset ring e g <
          grantDrainLeftLeaderDistance ring s.native g := by
      omega
    by_cases hAtOne : PPL.cyclicOffset ring e g = 1
    · have hy := hNeighbor
      rw [hAtOne] at hy
      have hOne : 1 - 1 = 0 := by omega
      rw [hOne, grantDrainWarmShiftLeftZero ring g] at hy
      rw [hy, hWarmFields.1] at hyLeader
      cases hyLeader
    · have hPrevious : 1 ≤ PPL.cyclicOffset ring e g - 1 ∧
          PPL.cyclicOffset ring e g - 1 <
            grantDrainLeftLeaderDistance ring s.native g := by
        omega
      have hFollowerAt :=
        hFirst.2 (PPL.cyclicOffset ring e g - 1)
          hPrevious.1 hPrevious.2
      rw [hNeighbor, hFollowerAt] at hyLeader
      cases hyLeader
  · by_cases hAtFront :
        PPL.cyclicOffset ring e g =
          grantDrainLeftLeaderDistance ring s.native g + 1
    · right
      have hAt := hNeighbor
      rw [hAtFront] at hAt
      have hOne :
          grantDrainLeftLeaderDistance ring s.native g + 1 - 1 =
            grantDrainLeftLeaderDistance ring s.native g := by
        omega
      rw [hOne] at hAt
      exact hAt
    · have hFar :
          grantDrainLeftLeaderDistance ring s.native g + 2 ≤
            PPL.cyclicOffset ring e g := by
        omega
      left
      intro j hj
      have hjShort : j < n := by omega
      constructor
      · rw [hSource]
        exact grantDrainD6BirthLeftOffsetsDistinct
          ring g j (PPL.cyclicOffset ring e g)
          hjShort hpShort (by omega)
      · rw [hNeighbor]
        exact grantDrainD6BirthLeftOffsetsDistinct
          ring g j (PPL.cyclicOffset ring e g - 1)
          hjShort (by omega) (by omega)

/-- For a leader responder outside the OLD inclusive scan,
the desired E-rank inequality is already exact equality.
The only remaining leader branch is its first-leader boundary. -/
theorem grantDrainD6OutgoingBulletLeaderOutsideOrBoundaryRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g ∨
    ring.rightNeighbor e =
      PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g) := by
  rcases grantDrainD6OutgoingBulletLeaderOutsideOrFront
      ring hn s e g hC hWarm hxFollower hxBullet hyLeader with
    hOutside | hFront
  · exact Or.inl
      (grantDrainD6OutgoingBulletOutsideScanERankLe
        ring hn s e g hC hWarm hxFollower hxBullet hOutside)
  · exact Or.inr hFront

/-- When the OLD leader responder is the nearest scanned leader,
the outgoing source lies just behind the OLD boundary and every
strictly earlier scan site is outside the physical E pair. -/
theorem grantDrainD6OutgoingBulletLeaderBoundaryPrefixFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)) :
    ∀ j : Nat,
      j < grantDrainLeftLeaderDistance ring s.native g →
      nativeE ring s.native e (PPL.shiftLeft ring g j) =
        s.native (PPL.shiftLeft ring g j) := by
  have hDist :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hOldFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hDist.1 hDist.2).mp rfl
  have hAt :
      g = PPL.shiftRight ring (ring.rightNeighbor e)
        (grantDrainLeftLeaderDistance ring s.native g) := by
    calc
      g = PPL.shiftRight ring
            (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))
            (grantDrainLeftLeaderDistance ring s.native g) :=
            (grantDrainD6BirthShiftCancel ring g
              (grantDrainLeftLeaderDistance ring s.native g)
              hDist.2).symm
      _ = PPL.shiftRight ring (ring.rightNeighbor e)
            (grantDrainLeftLeaderDistance ring s.native g) := by
            rw [← hFront]
  have hNotG : g ≠ e := by
    intro hg
    have hEmpty :=
      (grantDrainD6ExceptionalDeathHostFields s g hWarm).2.1
    rw [hg] at hEmpty
    exact hxBullet hEmpty
  intro j hj
  have hNotX : PPL.shiftLeft ring g j ≠ e := by
    by_cases hjZero : j = 0
    · subst j
      simpa only [grantDrainWarmShiftLeftZero] using hNotG
    · exact grantDrainD6DeathSourceOutsidePositive
        ring hn e (ring.rightNeighbor e) g
        (grantDrainLeftLeaderDistance ring s.native g)
        hDist.2 hAt rfl j (by omega) (by omega)
  have hNotY :
      PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
    by_cases hjZero : j = 0
    · subst j
      have hgFollower :=
        (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
      rw [grantDrainWarmShiftLeftZero]
      intro hEq
      rw [hEq, hyLeader] at hgFollower
      cases hgFollower
    · have hFollower := hOldFirst.2 j (by omega) hj
      intro hEq
      rw [hEq, hyLeader] at hFollower
      cases hFollower
  exact grantDrainEntranceNativeEFrame
    ring s.native e _ hNotX hNotY

/-- A READY OLD front emits a DUMMY on the leader boundary even
if the incoming OLD follower carries LIVE and deletes the leader.
The new first bullet is at old distance d, the terminal run is
d-1, and W'=d < 1+d=W. No source-emptiness assumption. -/
theorem grantDrainD6OutgoingBulletReadyFrontERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (_hxFollower : (s.native e).l = false)
    (_hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  obtain ⟨p, D, a, hSector, haInside, hAt⟩ :=
    grantDrainEntranceSectorCoverOfRoot
      ring s.native hC.1.1.1 g
  have hG :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  obtain ⟨haPos, hDA⟩ :=
    grantDrainD6OutgoingBulletSectorDistance
      ring s.native g p D a
      hSector haInside hAt hG
  have hPFront :
      PPL.shiftLeft ring g a.val = p := by
    rw [hAt, grantDrainMarksArcShiftLeftRight
      ring p a.val a.val (Nat.le_refl _) a.isLt,
      Nat.sub_self, grantDrainWeakDeathShiftRightZero ring p]
  have hYp : ring.rightNeighbor e = p := by
    calc
      ring.rightNeighbor e =
          PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g) :=
            hFront
      _ = PPL.shiftLeft ring g a.val := by rw [hDA]
      _ = p := hPFront
  have hReadyP : (s.native p).sg = true := by
    rw [← hYp]
    exact hyReady
  have hOldPrefix :=
    grantDrainD6ReadyResponderWarmPrefix
      ring s.native p g D a.val
      hC hSector haPos haInside hAt hReadyP
  have hOldNone :
      grantDrainLeftBulletDistance ring s.native g a.val =
        none := by
    apply (grantDrainWarmBulletNoneCharacterization
      ring s.native g a.val).mpr
    intro j _ hj
    rw [hOldPrefix.2 j hj]
    rfl
  have hOldRank :
      grantDrainWarmRank ring s.native g = 1 + a.val := by
    simp [grantDrainWarmRank, hDA,
      hOldNone, hPFront, hReadyP]
  have hFrame :=
    grantDrainD6OutgoingBulletLeaderBoundaryPrefixFrame
      ring hn s e g hC hWarm _hxBullet
      hyLeader hFront
  have hFrameA : ∀ j : Nat, j < a.val →
      nativeE ring s.native e (PPL.shiftLeft ring g j) =
        s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    exact hFrame j (by rw [hDA]; exact hj)
  have hOldFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g a.val haPos a.isLt).mp hDA
  have hNewNoLeader :
      ∀ j : Nat, 1 ≤ j → j < a.val →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).l = false := by
    intro j hj hjBefore
    rw [hFrameA j hjBefore]
    exact hOldFirst.2 j hj hjBefore
  have hNewDistance :
      a.val ≤ grantDrainLeftLeaderDistance
        ring (nativeE ring s.native e) g :=
    grantDrainD6DeathLeaderPrefixLowerBound
      ring (nativeE ring s.native e) g a.val
      (by omega) hNewNoLeader
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hDummy :=
    grantDrainD6MergeReadyResponderDummyPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hyLeader hyReady
  have hNewPBullet :
      (nativeE ring s.native e p).b = (1 : Fin 3) := by
    rw [← hYp]
    simpa [nativeE, hDistinct] using hDummy.2.1
  have hNewPSignal :
      (nativeE ring s.native e p).sg = false := by
    rw [← hYp]
    simpa [nativeE, hDistinct] using hDummy.2.2
  have hNewBullet :
      grantDrainLeftBulletDistance ring
        (nativeE ring s.native e) g
        (grantDrainLeftLeaderDistance ring
          (nativeE ring s.native e) g) = some a.val := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring (nativeE ring s.native e) g
      (grantDrainLeftLeaderDistance ring
        (nativeE ring s.native e) g) a.val).mpr
    refine ⟨haPos, hNewDistance, ?_, ?_⟩
    · rw [hPFront, hNewPBullet]
      decide
    · intro j hj hjBefore
      rw [hFrameA j hjBefore, hOldPrefix.2 j (by omega)]
      rfl
  have hNewSignals :
      ∀ j : Nat, j < a.val →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).sg = true := by
    intro j hj
    rw [hFrameA j hj]
    exact hOldPrefix.1 j hj
  have hNewWarm :
      (nativeE ring s.native e g).sg = true := by
    have h := hNewSignals 0 (by omega)
    simpa only [grantDrainWarmShiftLeftZero] using h
  have hNewTerminal :
      grantDrainTerminalRun ring
        (nativeE ring s.native e) g
        (grantDrainLeftLeaderDistance ring
          (nativeE ring s.native e) g) = a.val - 1 := by
    apply (grantDrainWarmTerminalCharacterization
      ring (nativeE ring s.native e) g
      (grantDrainLeftLeaderDistance ring
        (nativeE ring s.native e) g)
      (a.val - 1) (by omega) hNewWarm).mpr
    refine ⟨by omega, ?_, ?_⟩
    · intro j hj
      exact hNewSignals j (by omega)
    · by_cases hdEq :
          grantDrainLeftLeaderDistance ring
            (nativeE ring s.native e) g = a.val
      · exact Or.inl (by omega)
      · right
        have hIdx : a.val - 1 + 1 = a.val := by omega
        rw [hIdx, hPFront]
        exact hNewPSignal
  have hNewRank :
      grantDrainWarmRank ring (nativeE ring s.native e) g =
        a.val := by
    simp [grantDrainWarmRank, hNewBullet,
      hNewTerminal]
    omega
  rw [hOldRank, hNewRank]
  omega

/-- At a quiet OLD responder leader, any incoming LIVE/DUMMY
preserves the responder's bullet and signal fields. Its leader
bit may still die if a LIVE meets an unshielded leader. -/
theorem grantDrainD6OutgoingBulletQuietLeaderFields
    (x y : CertNative)
    (hxFollower : x.l = false)
    (hxBullet : x.b ≠ (0 : Fin 3))
    (hxQuiet : x.sg = false)
    (hyLeader : y.l = true)
    (hyQuiet : y.sg = false) :
    (certLiteralEPair x y).2.b = y.b ∧
      (certLiteralEPair x y).2.sg = y.sg := by
  rcases grantDrainEntranceNonzeroBulletKind x.b hxBullet with hb | hb
  · cases hsh : y.sh <;>
      simp [certLiteralEPair, certFinThree,
        hxFollower, hxQuiet, hyLeader, hyQuiet, hb, hsh]
  · cases hsh : y.sh <;>
      simp [certLiteralEPair, certFinThree,
        hxFollower, hxQuiet, hyLeader, hyQuiet, hb, hsh]

/-- In the quiet responder branch, if the old leader survives,
its complete record is unchanged by an incoming follower bullet. -/
theorem grantDrainD6OutgoingBulletQuietLeaderSurvivorPair
    (x y : CertNative)
    (hxFollower : x.l = false)
    (hxBullet : x.b ≠ (0 : Fin 3))
    (hxQuiet : x.sg = false)
    (hyLeader : y.l = true)
    (hyQuiet : y.sg = false)
    (hAlive : (certLiteralEPair x y).2.l = true) :
    (certLiteralEPair x y).2 = y := by
  rcases y with ⟨yl, yb, ysh, ysg⟩
  change yl = true at hyLeader
  change ysg = false at hyQuiet
  subst yl
  subst ysg
  rcases grantDrainEntranceNonzeroBulletKind x.b hxBullet with hb | hb
  · cases ysh <;>
      simp [certLiteralEPair, certFinThree,
        hxFollower, hxQuiet, hb]
        at hAlive ⊢
  · cases ysh <;>
      simp [certLiteralEPair, certFinThree,
        hxFollower, hxQuiet, hb]
        at hAlive ⊢

/-- The QUIET OLD boundary leader survives: the source is outside
the old scan and the responder is unchanged, hence the whole
inclusive scan, not just its rank, is identical after native E. -/
theorem grantDrainD6OutgoingBulletQuietFrontSurvivesERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyQuiet :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))
    (hAlive :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hxQuiet :=
    grantDrainD6OutgoingBulletSourceQuiet
      ring s.native hC e hxBullet
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPairAlive :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.l = true := by
    simpa [nativeE, hDistinct] using hAlive
  have hPair :=
    grantDrainD6OutgoingBulletQuietLeaderSurvivorPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hxFollower hxBullet hxQuiet hyLeader hyQuiet hPairAlive
  have hY :
      nativeE ring s.native e (ring.rightNeighbor e) =
        s.native (ring.rightNeighbor e) := by
    simpa [nativeE, hDistinct] using hPair
  have hPrefix :=
    grantDrainD6OutgoingBulletLeaderBoundaryPrefixFrame
      ring hn s e g hC hWarm hxBullet hyLeader hFront
  have hFull : ∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native g →
      nativeE ring s.native e (PPL.shiftLeft ring g j) =
        s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    by_cases hBefore :
        j < grantDrainLeftLeaderDistance ring s.native g
    · exact hPrefix j hBefore
    · have hAt :
          j = grantDrainLeftLeaderDistance ring s.native g := by
        omega
      rw [hAt, ← hFront]
      exact hY
  exact Nat.le_of_eq
    (grantDrainWarmFullScanFrame
      ring s.native (nativeE ring s.native e) g hFull).2.2.2

/-- If the QUIET old boundary leader dies while an OLD scanned
bullet exists, the first bullet and the terminal-run observer are
unchanged even though the nearest-leader distance grows. -/
theorem grantDrainD6OutgoingBulletQuietFrontDeathOldBulletERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyQuiet :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))
    (k : Nat)
    (hOldBullet :
      grantDrainLeftBulletDistance ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) =
          some k) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hxQuiet :=
    grantDrainD6OutgoingBulletSourceQuiet
      ring s.native hC e hxBullet
  have hPair :=
    grantDrainD6OutgoingBulletQuietLeaderFields
      (s.native e) (s.native (ring.rightNeighbor e))
      hxFollower hxBullet hxQuiet hyLeader hyQuiet
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hYBullet :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (s.native (ring.rightNeighbor e)).b := by
    simpa [nativeE, hDistinct] using hPair.1
  have hYSignal :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        (s.native (ring.rightNeighbor e)).sg := by
    simpa [nativeE, hDistinct] using hPair.2
  have hDist :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hOldFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hDist.1 hDist.2).mp rfl
  have hPrefix :=
    grantDrainD6OutgoingBulletLeaderBoundaryPrefixFrame
      ring hn s e g hC hWarm hxBullet hyLeader hFront
  have hNewDist :
      grantDrainLeftLeaderDistance ring s.native g ≤
        grantDrainLeftLeaderDistance
          ring (nativeE ring s.native e) g := by
    apply grantDrainD6DeathLeaderPrefixLowerBound
      ring (nativeE ring s.native e) g
      (grantDrainLeftLeaderDistance ring s.native g)
      (by omega)
    intro j hj hjBefore
    rw [hPrefix j hjBefore]
    exact hOldFirst.2 j hj hjBefore
  have hBulletPrefix :
      ∀ j : Nat, 1 ≤ j →
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).b.val =
        (s.native (PPL.shiftLeft ring g j)).b.val := by
    intro j hj hjLe
    by_cases hBefore :
        j < grantDrainLeftLeaderDistance ring s.native g
    · rw [hPrefix j hBefore]
    · have hAt :
          j = grantDrainLeftLeaderDistance ring s.native g := by
        omega
      rw [hAt, ← hFront, hYBullet]
  have hSignalPrefix :
      ∀ j : Nat,
        j < grantDrainLeftLeaderDistance ring s.native g →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).sg =
        (s.native (PPL.shiftLeft ring g j)).sg := by
    intro j hj
    rw [hPrefix j hj]
  have hNewFrontQuiet :
      (nativeE ring s.native e
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))).sg =
          false := by
    rw [← hFront, hYSignal]
    exact hyQuiet
  have hEq :=
    (grantDrainD6DeathBulletRankPrefix
      ring s.native (nativeE ring s.native e) g
      (grantDrainLeftLeaderDistance ring s.native g) k
      hDist.1 rfl hNewDist hOldBullet
      (grantDrainD6ExceptionalDeathHostFields s g hWarm).2.2
      hSignalPrefix hBulletPrefix hNewFrontQuiet).2.2
  exact Nat.le_of_eq hEq

/-- A quiet OLD leader can die from an incoming follower LIVE
only if it is unshielded. If the OLD inclusive scan were
bullet-free too, this would be exactly the prohibited exceptional
death, so nonexceptionality forces an OLD scanned bullet. -/
theorem grantDrainD6OutgoingBulletQuietFrontDeathHasOldBullet
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (_hWarm : grantDrainWarmAt s g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyQuiet :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))
    (hDeath :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = false)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false) :
    ∃ k : Nat,
      grantDrainLeftBulletDistance ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) =
          some k := by
  cases hBullet :
      grantDrainLeftBulletDistance ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) with
  | some k =>
      exact ⟨k, rfl⟩
  | none =>
      have hxQuiet :=
        grantDrainD6OutgoingBulletSourceQuiet
          ring s.native hC e hxBullet
      have hDistinct :=
        grantDrainEntranceRightNeighborDistinct
          ring (by omega : 2 ≤ n) e
      have hPairDeath :
          (certLiteralEPair (s.native e)
            (s.native (ring.rightNeighbor e))).2.l =
              false := by
        simpa [nativeE, hDistinct] using hDeath
      have hReason :=
        (grantDrainD6OutgoingBulletLeaderDeathIff
          (s.native e) (s.native (ring.rightNeighbor e))
          hxFollower hxBullet hxQuiet hyLeader).mp hPairDeath
      have hUnshield :
          (s.native (ring.rightNeighbor e)).sh = false := by
        rcases hReason.2 with hReady | hUnshield
        · rw [hyQuiet] at hReady
          cases hReady
        · exact hUnshield
      have hFrontLeader :
          (s.native (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g))).l =
              true := by
        rw [← hFront]
        exact hyLeader
      have hFrontShield :
          (s.native (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g))).sh =
              false := by
        rw [← hFront]
        exact hUnshield
      have hFrontSignal :
          (s.native (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g))).sg =
              false := by
        rw [← hFront]
        exact hyQuiet
      have hFrontDead :
          (nativeE ring s.native e
            (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))).l =
              false := by
        rw [← hFront]
        exact hDeath
      have hExceptional :
          grantDrainExceptionalDeath ring s e g = true := by
        simp [grantDrainExceptionalDeath,
          hFrontLeader, hFrontShield, hFrontSignal,
          hBullet, hFrontDead]
      rw [hNonExceptional] at hExceptional
      cases hExceptional

/-- The requested all-row corrected E-rank theorem for the
outgoing LIVE/DUMMY follower source. The only additional split
is the literal OLD responder leader flag, its ready flag, and
whether the quiet front survives. In the sole death/no-bullet
case, the real nonexceptional guard gives a contradiction. -/
theorem grantDrainD6OutgoingBulletERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3)) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  cases hyLeader :
      (s.native (ring.rightNeighbor e)).l with
  | false =>
      exact grantDrainD6OutgoingBulletFollowerERankLe
        ring hn fresh update s e g z hC hWarm
        hNonExceptional hSelected hz hStillWarm
        hxFollower hxBullet hyLeader
  | true =>
      rcases grantDrainD6OutgoingBulletLeaderOutsideOrBoundaryRank
          ring hn s e g hC hWarm hxFollower hxBullet hyLeader with
        hOutsideRank | hFront
      · exact hOutsideRank
      · cases hyReady :
            (s.native (ring.rightNeighbor e)).sg with
        | true =>
            exact grantDrainD6OutgoingBulletReadyFrontERankLe
              ring hn s e g hC hWarm hxFollower hxBullet
              hyLeader hyReady hFront
        | false =>
            cases hNewLeader :
                (nativeE ring s.native e
                  (ring.rightNeighbor e)).l with
            | true =>
                exact grantDrainD6OutgoingBulletQuietFrontSurvivesERankLe
                  ring hn s e g hC hWarm
                  hxFollower hxBullet hyLeader hyReady
                  hFront hNewLeader
            | false =>
                obtain ⟨k, hOldBullet⟩ :=
                  grantDrainD6OutgoingBulletQuietFrontDeathHasOldBullet
                    ring hn s e g hC hWarm hxFollower hxBullet
                    hyLeader hyReady hFront hNewLeader hNonExceptional
                exact grantDrainD6OutgoingBulletQuietFrontDeathOldBulletERankLe
                  ring hn s e g hC hWarm
                  hxFollower hxBullet hyLeader hyReady
                  hFront k hOldBullet

/-- The corresponding s1n birth rank lift is now available
directly for the whole outgoing LIVE/DUMMY source family. -/
theorem grantDrainD6OutgoingBulletSelectedBirthRankLift
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3)) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g + 1 := by
  have hERank :=
    grantDrainD6OutgoingBulletERankLe
      ring hn fresh update s e g z
      hC hWarm hNonExceptional hSelected hz hStillWarm
      hxFollower hxBullet
  exact grantDrainD6NonExceptionalBirthRankLiftOfERank
    ring hn fresh update s e g z hC hNonExceptional
    hSelected hz hStillWarm hERank

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletSuccessorAtOffset
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletOldDistanceShort
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletSectorDistance
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletInScanIsFirst
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletFollowerScanDichotomy
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletFollowerERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletLeaderOutsideOrFront
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletLeaderOutsideOrBoundaryRank
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletLeaderBoundaryPrefixFrame
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletReadyFrontERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletQuietLeaderFields
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletQuietLeaderSurvivorPair
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletQuietFrontSurvivesERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletQuietFrontDeathOldBulletERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletQuietFrontDeathHasOldBullet
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6OutgoingBulletSelectedBirthRankLift

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Selected source-leader/leader-responder row. -/

/-- Two consecutive OLD leaders cannot have their service source
in the inclusive nearest-left-leader scan of a warm follower.
At positive offsets, its right neighbor would be an OLD follower;
at offset zero the source would be the warm follower itself. -/
theorem grantDrainD6SourceLeaderLeaderNoSourceInScan
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxLeader : (s.native e).l = true)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true) :
    ∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g j ≠ e := by
  have hHost :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hDistance :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hDistance.1 hDistance.2).mp rfl
  intro j hj hEq
  by_cases hjZero : j = 0
  · subst j
    rw [grantDrainWarmShiftLeftZero] at hEq
    have hBad : (s.native g).l = true := by
      rw [hEq]
      exact hxLeader
    rw [hHost.1] at hBad
    cases hBad
  · have hNext :=
      grantDrainD6OutgoingBulletSuccessorAtOffset
        ring g e j (by omega) (by omega) hEq.symm
    have hPrevious :
        (s.native (PPL.shiftLeft ring g (j - 1))).l =
          false := by
      by_cases hjOne : j = 1
      · have hZero : j - 1 = 0 := by omega
        rw [hZero, grantDrainWarmShiftLeftZero]
        exact hHost.1
      · exact hFirst.2 (j - 1) (by omega) (by omega)
    rw [← hNext, hyLeader] at hPrevious
    cases hPrevious

/-- A leader/leader OLD pair either misses the entire inclusive
warm scan or has its responder at the unique OLD front leader.
This uses the actual cyclic predecessor relation, not a proposed
pair-position classifier. -/
theorem grantDrainD6SourceLeaderLeaderOutsideOrFront
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxLeader : (s.native e).l = true)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true) :
    (∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g j ≠ e ∧
      PPL.shiftLeft ring g j ≠ ring.rightNeighbor e) ∨
    ring.rightNeighbor e =
      PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g) := by
  have hNoSource :=
    grantDrainD6SourceLeaderLeaderNoSourceInScan
      ring hn s e g hC hWarm hxLeader hyLeader
  have hHost :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hDistance :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hDistance.1 hDistance.2).mp rfl
  by_cases hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)
  · exact Or.inr hFront
  · left
    intro j hj
    refine ⟨hNoSource j hj, ?_⟩
    intro hEq
    by_cases hjZero : j = 0
    · subst j
      rw [grantDrainWarmShiftLeftZero] at hEq
      have hBad : (s.native g).l = true := by
        rw [hEq]
        exact hyLeader
      rw [hHost.1] at hBad
      cases hBad
    · by_cases hjBefore :
          j < grantDrainLeftLeaderDistance ring s.native g
      · have hOldFollower := hFirst.2 j (by omega) hjBefore
        rw [hEq, hyLeader] at hOldFollower
        cases hOldFollower
      · have hjAt :
            j = grantDrainLeftLeaderDistance ring s.native g := by
          omega
        rw [hjAt] at hEq
        exact hFront hEq.symm

/-- A selected FIRE on an OLD leader/leader pair can only be
rightLocal after E has deleted the OLD responder. Its empty
post-E bullet implies that the responder was quiet and had no
resident bullet; actual leader death then implies open shield. -/
theorem grantDrainD6SourceLeaderLeaderSelectedFields
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e z : Fin n)
    (hxLeader : (s.native e).l = true)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e)) :
    z = ring.rightNeighbor e ∧
    (nativeE ring s.native e
      (ring.rightNeighbor e)).l = false ∧
    (nativeE ring s.native e
      (ring.rightNeighbor e)).b = (0 : Fin 3) ∧
    (s.native (ring.rightNeighbor e)).sg = false ∧
    (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) ∧
    (s.native (ring.rightNeighbor e)).sh = false := by
  have hSourceLeader :
      (nativeE ring s.native e e).l = true := by
    have hSource :=
      grantDrainEntranceLiteralESourceLeaderFixed
        (s.native e) (s.native (ring.rightNeighbor e))
    simpa [nativeE] using hSource.trans hxLeader
  have hRight : grantDrainSelect ring s e = .rightLocal := by
    rcases hSelected with hLeft | hSelectedRight | hCross
    · have hEligible :=
        grantDrainD6SelectedEligible ring s e z
          (Or.inl hLeft)
      rw [hLeft.2] at hEligible
      simp [grantDrainEligible, hSourceLeader] at hEligible
    · exact hSelectedRight.1
    · have hEligible :=
        grantDrainD6SelectedEligible ring s e z
          (Or.inr (Or.inr hCross))
      rw [hCross.2] at hEligible
      simp [grantDrainEligible, hSourceLeader] at hEligible
  have hz : z = ring.rightNeighbor e := by
    rcases hSelected with hLeft | hSelectedRight | hCross
    · rw [hRight] at hLeft
      cases hLeft.1
    · exact hSelectedRight.2
    · rw [hRight] at hCross
      cases hCross.1
  have hEligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = true :=
    grantDrainD6SelectedEligible ring s e
      (ring.rightNeighbor e)
      (Or.inr (Or.inl ⟨hRight, rfl⟩))
  have hDead :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = false := by
    cases hl :
        (nativeE ring s.native e
          (ring.rightNeighbor e)).l with
    | false => rfl
    | true =>
        simp [grantDrainEligible, hl] at hEligible
  have hPostVal :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).b.val = 0 := by
    by_cases hb :
        (nativeE ring s.native e
          (ring.rightNeighbor e)).b.val = 0
    · exact hb
    · have hBad :
          grantDrainEligible (nativeE ring s.native e)
            (ring.rightNeighbor e) = false := by
        simp [grantDrainEligible, hb]
      rw [hBad] at hEligible
      cases hEligible
  have hPostEmpty :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).b = (0 : Fin 3) := by
    apply Fin.ext
    exact hPostVal
  have hAfter :=
    grantDrainEntranceNativeELeaderBulletAfter
      ring (by omega : 2 ≤ n) s.native e hyLeader
  have hyQuiet :
      (s.native (ring.rightNeighbor e)).sg = false := by
    cases hs : (s.native (ring.rightNeighbor e)).sg with
    | false => rfl
    | true =>
        have hDummy :
            (nativeE ring s.native e
              (ring.rightNeighbor e)).b = (1 : Fin 3) := by
          simpa [hs] using hAfter.1
        rw [hPostEmpty] at hDummy
        cases hDummy
  have hyEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) := by
    have hSame :
        (nativeE ring s.native e
          (ring.rightNeighbor e)).b =
          (s.native (ring.rightNeighbor e)).b := by
      simpa [hyQuiet] using hAfter.1
    exact hSame.symm.trans hPostEmpty
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPairDead :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.l = false := by
    simpa [nativeE, hDistinct] using hDead
  have hReason :=
    (grantDrainEntranceLiteralELeaderDeathCases
      (s.native e) (s.native (ring.rightNeighbor e))
      hyLeader).mp hPairDead
  have hyOpen :
      (s.native (ring.rightNeighbor e)).sh = false := by
    rcases hReason.2 with hReady | hOpen
    · rw [hyQuiet] at hReady
      cases hReady
    · exact hOpen
  exact ⟨hz, hDead, hPostEmpty, hyQuiet, hyEmpty, hyOpen⟩

/-- A2: selected source leader and OLD responder leader.
An outside pair is rank-neutral by the OLD scan frame.
At the old front, post-E eligibility forces a quiet, empty,
unshielded leader death. Nonexceptionality forces an earlier
OLD bullet; the generic retained-bullet front-death transport
therefore makes the E rank exactly unchanged. -/
theorem grantDrainD6SourceLeaderLeaderERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (_hz : z ≠ g)
    (_hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxLeader : (s.native e).l = true)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  obtain ⟨_, hDead, _, hyQuiet, _, hyOpen⟩ :=
    grantDrainD6SourceLeaderLeaderSelectedFields
      ring hn s e z hxLeader hyLeader hSelected
  rcases grantDrainD6SourceLeaderLeaderOutsideOrFront
      ring hn s e g hC hWarm hxLeader hyLeader with
    hOutside | hFront
  · exact Nat.le_of_eq
      (grantDrainD6EScanOutsidePair
        ring s.native e g hOutside)
  · have hHost :=
      grantDrainD6ExceptionalDeathHostFields s g hWarm
    have hDistance :=
      grantDrainD6OutgoingBulletOldDistanceShort
        ring hn s g hC hWarm
    have hFirst :=
      (grantDrainWarmLeaderFirstCharacterization
        ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        hDistance.1 hDistance.2).mp rfl
    have hNoSource :=
      grantDrainD6SourceLeaderLeaderNoSourceInScan
        ring hn s e g hC hWarm hxLeader hyLeader
    have hFrame :
        ∀ j : Nat,
          j < grantDrainLeftLeaderDistance ring s.native g →
          nativeE ring s.native e
            (PPL.shiftLeft ring g j) =
          s.native (PPL.shiftLeft ring g j) := by
      intro j hj
      have hNoResponder :
          PPL.shiftLeft ring g j ≠
            ring.rightNeighbor e := by
        by_cases hjZero : j = 0
        · subst j
          rw [grantDrainWarmShiftLeftZero]
          intro hEq
          have hBad : (s.native g).l = true := by
            rw [hEq]
            exact hyLeader
          rw [hHost.1] at hBad
          cases hBad
        · intro hEq
          have hOldFollower := hFirst.2 j (by omega) hj
          rw [hEq, hyLeader] at hOldFollower
          cases hOldFollower
      exact grantDrainEntranceNativeEFrame
        ring s.native e _
        (hNoSource j (by omega)) hNoResponder
    have hAfter :=
      grantDrainEntranceNativeELeaderBulletAfter
        ring (by omega : 2 ≤ n) s.native e hyLeader
    have hResponderBullet :
        (nativeE ring s.native e
          (ring.rightNeighbor e)).b =
          (s.native (ring.rightNeighbor e)).b := by
      simpa [hyQuiet] using hAfter.1
    have hNewDistance :
        grantDrainLeftLeaderDistance ring s.native g ≤
          grantDrainLeftLeaderDistance
            ring (nativeE ring s.native e) g := by
      apply grantDrainD6DeathLeaderPrefixLowerBound
        ring (nativeE ring s.native e) g
        (grantDrainLeftLeaderDistance ring s.native g)
        (by omega)
      intro j hj hjBefore
      rw [hFrame j hjBefore]
      exact hFirst.2 j hj hjBefore
    have hBulletPrefix :
        ∀ j : Nat, 1 ≤ j →
          j ≤ grantDrainLeftLeaderDistance ring s.native g →
          (nativeE ring s.native e
            (PPL.shiftLeft ring g j)).b.val =
          (s.native (PPL.shiftLeft ring g j)).b.val := by
      intro j _ hjLe
      by_cases hjBefore :
          j < grantDrainLeftLeaderDistance ring s.native g
      · rw [hFrame j hjBefore]
      · have hjAt :
            j = grantDrainLeftLeaderDistance ring s.native g := by
          omega
        rw [hjAt, ← hFront, hResponderBullet]
    have hSignalPrefix :
        ∀ j : Nat,
          j < grantDrainLeftLeaderDistance ring s.native g →
          (nativeE ring s.native e
            (PPL.shiftLeft ring g j)).sg =
          (s.native (PPL.shiftLeft ring g j)).sg := by
      intro j hj
      exact congrArg CertNative.sg (hFrame j hj)
    have hNewFrontQuiet :
        (nativeE ring s.native e
          (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g))).sg =
          false := by
      rw [← hFront]
      exact hAfter.2
    cases hBullet :
        grantDrainLeftBulletDistance ring s.native g
          (grantDrainLeftLeaderDistance ring s.native g) with
    | none =>
        have hFrontLeader :
            (s.native (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))).l =
              true := by
          rw [← hFront]
          exact hyLeader
        have hFrontShield :
            (s.native (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))).sh =
              false := by
          rw [← hFront]
          exact hyOpen
        have hFrontSignal :
            (s.native (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))).sg =
              false := by
          rw [← hFront]
          exact hyQuiet
        have hSurvive :=
          grantDrainD6NonExceptionalQuietFrontSurvivesE
            ring s e g hNonExceptional hFrontLeader
            hFrontShield hFrontSignal hBullet
        rw [← hFront, hDead] at hSurvive
        cases hSurvive
    | some k =>
        exact Nat.le_of_eq
          (grantDrainD6DeathBulletRankPrefix
            ring s.native (nativeE ring s.native e) g
            (grantDrainLeftLeaderDistance ring s.native g)
            k hDistance.1 rfl hNewDistance hBullet
            hHost.2.2 hSignalPrefix hBulletPrefix
            hNewFrontQuiet).2.2

/-- The entire selected source-leader E family follows by
splitting only the OLD responder leader bit. -/
theorem grantDrainD6SourceLeaderERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxLeader : (s.native e).l = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  by_cases hyLeader :
      (s.native (ring.rightNeighbor e)).l = true
  · exact grantDrainD6SourceLeaderLeaderERankLe
      ring hn fresh update s e g z hC hWarm
      hNonExceptional hSelected hz hStillWarm
      hxLeader hyLeader
  · have hyFollower :
        (s.native (ring.rightNeighbor e)).l = false := by
      cases hl : (s.native (ring.rightNeighbor e)).l with
      | false => rfl
      | true => exact False.elim (hyLeader hl)
    exact grantDrainD6SourceLeaderFollowerERankLe
      ring hn fresh update s e g z hC hWarm
      hNonExceptional hSelected hz hStillWarm
      hxLeader hyFollower

/-- Apply the already-proved selected-birth bridge only after
discharging its E-rank input for all source-leader rows. -/
theorem grantDrainD6SourceLeaderSelectedBirthRankLift
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxLeader : (s.native e).l = true) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g + 1 := by
  have hERank :=
    grantDrainD6SourceLeaderERankLe
      ring hn fresh update s e g z hC hWarm
      hNonExceptional hSelected hz hStillWarm hxLeader
  exact grantDrainD6NonExceptionalBirthRankLiftOfERank
    ring hn fresh update s e g z hC hNonExceptional
    hSelected hz hStillWarm hERank

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6SourceLeaderLeaderNoSourceInScan
#print axioms L3.GrantDrainEntrance.grantDrainD6SourceLeaderLeaderOutsideOrFront
#print axioms L3.GrantDrainEntrance.grantDrainD6SourceLeaderLeaderSelectedFields
#print axioms L3.GrantDrainEntrance.grantDrainD6SourceLeaderLeaderERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6SourceLeaderERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6SourceLeaderSelectedBirthRankLift

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Charged-step case table.

The requested unrestricted theorem is FALSE under only C_native and
GrantDrainWarmMergeSpent, even if the OLD label is warm, its host is
warm and holds a grant, the FIRE is selected away from that host,
the OLD exceptional guard is false, and the NEW host remains warm
with a grant.  The counterexample below is a public restatement of
the genuine eight-site remote-birth row in GrantDrain.lean, with
birthsLeft = 0.  It therefore cannot be repaired by assuming the
pending ready-responder E-rank comparison.

COMPLETE ASSEMBLY CASE TABLE (no hidden rank assumptions):

(0) OLD label cold:
    grantDrainD6MergeColdLabelRemainsCold.  New charged quota = 0.
    Proved below by grantDrainD6ChargedColdStep.

(1) OLD label hostless:
    grantDrainWarmLabelStep preserves host = none by definition.
    New charged quota = 0.
    Proved below by grantDrainD6ChargedHostlessStep.

(2) NEW label hostless or cold, regardless of OLD host:
    grantDrainChargedWarmRank gives new quota = 0.
    Proved below by grantDrainD6ChargedRetiredStep.

(3) OLD active host g, NEW active host g, no FIRE:
    Outside the OLD inclusive scan:
      grantDrainD6WarmOutsidePairCase (exact charged bound).
    Inside the scan, only individual rows are merged:
      grantDrainD6ContactNoBirthPairFrame,
      grantDrainD6ContactEmptyFollowersNoChange,
      grantDrainD6ContactFirstBulletInterior,
      grantDrainD6CompositeReadySourceRank,
      grantDrainD6FireReadyResponderKilledRank,
      grantDrainD6FireReadyResponderSurvivingRank,
      grantDrainD6ExceptionalDeathERank,
      grantDrainD6EmptyFollowerNotReadyResponderERankLe.
    There is no merged complete ALL-ROW no-FIRE/continuing-warm
    rank comparison for the remaining inside-scan cases.
    Exceptional no-FIRE costs at most 2*(n-2) by
      grantDrainD6ExceptionalDeathERank; the spent invariant
    forces the available reserve by
      grantDrainD6MergeExceptionalRequiresReserve.

(4) OLD active host g, selected FIRE at z != g, nonexceptional:
    E-then-FIRE bridge:
      grantDrainD6NonExceptionalBirthRankLiftOfERank.
    Source leader:
      grantDrainD6SourceLeaderSelectedBirthRankLift.
    Follower with outgoing LIVE/DUMMY:
      grantDrainD6OutgoingBulletSelectedBirthRankLift.
    Empty follower, responder not ready:
      grantDrainD6NonExceptionalBirthRankLiftEmptySourceNotReady.
    Empty follower, ready leader responder:
      grantDrainD6ReadyResponderERankLe (PENDING in another tab).
    If the latter E-rank row is supplied, the bridge gives
      W(new,g) <= W(old,g)+1.
    The ghost credit is
      grantDrainD6ContactPhysicalBirthBudget:
      b' = b-1.
    To pay the increment one MUST ALSO HAVE 1 <= b.
    Neither C_native nor GrantDrainWarmMergeSpent implies it.
    The closed counterexample below is precisely this case.

(5) OLD active host g, selected FIRE at z != g, exceptional:
      grantDrainD6ExceptionalBirthRankChargeAndCredits
    proves W(new,g) <= W(old,g)+2*(n-2)+1 and spends
    exceptionalLeft, plus b' = b-1.
    To charge the additional +1 one STILL needs 1 <= b.
    The other credit is available from the spent invariant.

(6) FIRE selected at the actual tracked host z = g:
      grantDrainD6CompositeSourceBirthEndsWarm and
      grantDrainD6CompositeResponderBirthEndsWarm
    show the birth site becomes physically cold.  The label
    routing is given by grantDrainD6ContactHostAtSource and
    grantDrainD6ContactHostAtResponder.  If the label stays at
    the birth site it becomes cold; if it retires use (2).
    No general consolidated charged lemma for this logical row
    is merged, although its physical ingredients are.

(7) Host moves from OLD y = rightNeighbor e to NEW e:
      grantDrainD6ContactIncomingGrantMovesHost gives a
    concrete no-FIRE movement under its hypotheses.
      grantDrainD6MovingHostEmptyFollowerRank
    gives W(new,e)+1 <= W(old,y), but ONLY for the old
    empty-follower pair, OLD d >= 2, and no FIRE.
    The complete derivation of these hypotheses from arbitrary
    continuing-warm ghost routing is NOT a merged theorem.
    There is no host e -> y transition in the literal label step.

(8) OLD label warm/hosted but OLD host has no grant:
    The OLD charged expression is zero.  There is no merged
    coherence invariant excluding a NEW active host with a grant.
    An explicit old-host-grant/coherence premise is needed
    before the accounting algebra may be used.

EXACT REMAINING OBLIGATIONS FOR A REPAIRED ASSEMBLY:
(A) POSITIVE BIRTH CREDIT for any selected FIRE with an
    active, surviving label:
      grantDrainSelect ring s e != .none ->
      (grantDrainWarmLabelStep ring fresh update s e label).warm
        = true ->
      (exists q, (grantDrainWarmLabelStep ring fresh update s e
        label).host = some q /\
        (grantDrainStep ring fresh update s e).grant q = true) ->
      1 <= label.birthsLeft.
    This is FALSE for arbitrary labels satisfying
    GrantDrainWarmMergeSpent (see the closed regression).

(B) COMPLETE NO-FIRE INSIDE-SCAN FIXED-HOST ROW:
      C_native ring s.native ->
      grantDrainWarmAt s g = true ->
      grantDrainSelect ring s e = .none ->
      grantDrainExceptionalDeath ring s e g = false ->
      grantDrainWarmAt (grantDrainStep ring fresh update s e) g
        = true ->
      grantDrainWarmRank ring (nativeE ring s.native e) g <=
        grantDrainWarmRank ring s.native g.
    Existing merged lemmas cover subfamilies, not this
    all-physical-row statement.

(C) COMPLETE MOVING-HOST REDUCTION:
      C_native ring s.native ->
      label.host = some (ring.rightNeighbor e) ->
      grantDrainWarmAt s (ring.rightNeighbor e) = true ->
      s.grant (ring.rightNeighbor e) = true ->
      (grantDrainWarmLabelStep ring fresh update s e label).host
        = some e ->
      (grantDrainWarmLabelStep ring fresh update s e label).warm
        = true ->
      grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native e <=
      grantDrainWarmRank ring s.native (ring.rightNeighbor e).
    The existing grantDrainD6MovingHostEmptyFollowerRank
    proves a stronger bound for its restricted row only.

(D) FULL HOST-AT-BIRTH CLASSIFICATION:
      label.host = some g ->
      (exists z, z = g /\
        (grantDrainSelect ring s e = .leftLocal /\ z = e \/
         grantDrainSelect ring s e = .rightLocal /\
           z = ring.rightNeighbor e \/
         grantDrainSelect ring s e = .cross /\ z = e)) ->
      (grantDrainWarmLabelStep ring fresh update s e label).host
        = none \/
      (grantDrainWarmLabelStep ring fresh update s e label).warm
        = false.
    Follows physically from the two composite birth-ends-warm
    lemmas and the two contact-host lemmas; not merged as a
    single logical case.

(E) READY RESPONDER E-RANK: the ONLY permitted provisional
    proof hypothesis, grantDrainD6ReadyResponderERankLe.
    Closing (E) alone does not repair the false (A).

The proof below gives the unconditional cold/hostless/retired
cases, the exact prepaid-increment arithmetic, and a CLOSED
counterexample to the claimed all-step theorem.  It does NOT
postulate any of (A)-(E).
-/

/-- A cold label stays cold, hence the new charged rank is zero. -/
theorem grantDrainD6ChargedColdStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hCold : label.warm = false) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) <=
      grantDrainChargedWarmRank ring s label := by
  have hColdNext :=
    grantDrainD6MergeColdLabelRemainsCold
      ring fresh update s e label hCold
  simp [grantDrainChargedWarmRank, hCold, hColdNext]

/-- A label whose host is none cannot acquire a host on one step. -/
theorem grantDrainD6ChargedHostlessStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hHostless : label.host = none) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) <=
      grantDrainChargedWarmRank ring s label := by
  have hNextHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = none := by
    simp [grantDrainWarmLabelStep, hHostless]
  simp [grantDrainChargedWarmRank, hHostless, hNextHost]

/-- If the new label is cold or has retired, the new quota is zero. -/
theorem grantDrainD6ChargedRetiredStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hRetired :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = false \/
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = none) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) <=
      grantDrainChargedWarmRank ring s label := by
  rcases hRetired with hCold | hHostless
  · have hZero :
        grantDrainChargedWarmRank ring
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label) =
          0 := by
      simp [grantDrainChargedWarmRank, hCold]
    rw [hZero]
    exact Nat.zero_le _
  · have hZero :
        grantDrainChargedWarmRank ring
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label) =
          0 := by
      simp [grantDrainChargedWarmRank, hHostless]
    rw [hZero]
    exact Nat.zero_le _

/-- Arithmetic row for one paid ordinary FIRE.
The nontrivial premise is the positive prepaid birth allowance. -/
theorem grantDrainD6ChargedOrdinaryFireArithmetic
    (w w' b d : Nat)
    (hPositive : 1 <= b)
    (hRank : w' <= w + 1) :
    w' + (b - 1) + d <= w + b + d := by
  apply grantDrainWarmQuota_nonincrease_of_paid_increment
    w w' b (b - 1) d d
  · omega
  · omega
  · omega

/-- Arithmetic row for exceptional death plus one paid FIRE.
Here d is the entire exceptional reserve spent at the step. -/
theorem grantDrainD6ChargedExceptionalFireArithmetic
    (w w' b d : Nat)
    (hPositive : 1 <= b)
    (hRank : w' <= w + d + 1) :
    w' + (b - 1) <= w + b + d := by
  have hPaid :=
    grantDrainWarmQuota_nonincrease_of_paid_increment
      w w' b (b - 1) d 0
      (by omega) (by omega) (by omega)
  omega

/-! A closed eight-site adversarial regression.  Its native word and
remote leftLocal FIRE are the existing public-logic witness in
GrantDrain.lean, restated because those declarations are private.
Only the ghost birth allowance is changed from two to zero. -/

def grantDrainD6ZeroBirthRing : DirectedRing 8 :=
  ⟨by decide⟩

def grantDrainD6ZeroBirthNative (i : Fin 8) : CertNative :=
  if i.val == 0 then firedNative
  else if i.val == 1 then
    { l := false, b := (1 : Fin 3), sh := false, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := true }

def grantDrainD6ZeroBirthState : GrantDrainState 8 Unit :=
  { native := grantDrainD6ZeroBirthNative
    request := fun i => i.val == 2
    grant := fun i => i.val == 2 || i.val == 4
    scratch := ()
    history := [] }

def grantDrainD6ZeroBirthLabel : GrantDrainWarmLabel 8 :=
  { identity := (4 : Fin 8)
    host := some (4 : Fin 8)
    warm := true
    birthsLeft := 0
    exceptionalLeft := true }

def grantDrainD6ZeroBirthAfter : GrantDrainState 8 Unit :=
  grantDrainStep grantDrainD6ZeroBirthRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainD6ZeroBirthState (2 : Fin 8)

def grantDrainD6ZeroBirthLabelAfter : GrantDrainWarmLabel 8 :=
  grantDrainWarmLabelStep grantDrainD6ZeroBirthRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainD6ZeroBirthState (2 : Fin 8)
    grantDrainD6ZeroBirthLabel

/-- Closed OLD C_native; this is NOT inferred from a sample trace. -/
theorem grantDrainD6ZeroBirthClean :
    C_native grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthState.native := by
  decide

/-- The only spent-reserve implication is vacuous because the
ghost still carries its exceptional allowance. -/
theorem grantDrainD6ZeroBirthMergeSpent :
    GrantDrainWarmMergeSpent grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthState
      grantDrainD6ZeroBirthLabel := by
  intro g _ _ hSpent
  change true = false at hSpent
  cases hSpent

/-- All actual one-step guards, including selected remote FIRE and
the still-warm physical and ghost host, hold on this CLOSED state. -/
theorem grantDrainD6ZeroBirthGuardTrace :
    grantDrainWarmAt grantDrainD6ZeroBirthState
      (4 : Fin 8) = true /\
    grantDrainD6ZeroBirthState.grant (4 : Fin 8) = true /\
    grantDrainSelect grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthState (2 : Fin 8) =
        .leftLocal /\
    grantDrainExceptionalDeath grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthState (2 : Fin 8)
      (4 : Fin 8) = false /\
    grantDrainD6ZeroBirthLabelAfter.host = some (4 : Fin 8) /\
    grantDrainD6ZeroBirthLabelAfter.warm = true /\
    grantDrainWarmAt grantDrainD6ZeroBirthAfter
      (4 : Fin 8) = true /\
    grantDrainD6ZeroBirthAfter.grant (4 : Fin 8) = true /\
    grantDrainWarmRank grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthState.native (4 : Fin 8) = 3 /\
    grantDrainWarmRank grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthAfter.native (4 : Fin 8) = 4 := by
  decide

/-- With zero birth credit, the old charged quota is 3+12=15. -/
theorem grantDrainD6ZeroBirthChargedBefore :
    grantDrainChargedWarmRank grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthState grantDrainD6ZeroBirthLabel =
        15 := by
  decide

/-- The remote birth raises W from 3 to 4 but spends ZERO credit;
the same exceptional reserve remains available. -/
theorem grantDrainD6ZeroBirthChargedAfter :
    grantDrainChargedWarmRank grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthAfter grantDrainD6ZeroBirthLabelAfter =
        16 := by
  decide

/-- Closed violation of the requested charged monotonicity.
Both OLD premises hold, the tracked old/new host remains active
with a grant, and the selected FIRE is away from that host. -/
theorem grantDrainD6ChargedWarmRankStepCounterexample :
    C_native grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthState.native /\
    GrantDrainWarmMergeSpent grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthState grantDrainD6ZeroBirthLabel /\
    grantDrainWarmAt grantDrainD6ZeroBirthState
      (4 : Fin 8) = true /\
    grantDrainD6ZeroBirthState.grant (4 : Fin 8) = true /\
    grantDrainSelect grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthState (2 : Fin 8) = .leftLocal /\
    grantDrainExceptionalDeath grantDrainD6ZeroBirthRing
      grantDrainD6ZeroBirthState (2 : Fin 8)
      (4 : Fin 8) = false /\
    grantDrainD6ZeroBirthLabelAfter.host = some (4 : Fin 8) /\
    grantDrainD6ZeroBirthLabelAfter.warm = true /\
    grantDrainWarmAt grantDrainD6ZeroBirthAfter
      (4 : Fin 8) = true /\
    grantDrainD6ZeroBirthAfter.grant (4 : Fin 8) = true /\
    ¬ (grantDrainChargedWarmRank grantDrainD6ZeroBirthRing
        grantDrainD6ZeroBirthAfter
        grantDrainD6ZeroBirthLabelAfter <=
      grantDrainChargedWarmRank grantDrainD6ZeroBirthRing
        grantDrainD6ZeroBirthState
        grantDrainD6ZeroBirthLabel) := by
  have hTrace := grantDrainD6ZeroBirthGuardTrace
  refine ⟨grantDrainD6ZeroBirthClean,
    grantDrainD6ZeroBirthMergeSpent,
    hTrace.1, hTrace.2.1, hTrace.2.2.1,
    hTrace.2.2.2.1, hTrace.2.2.2.2.1,
    hTrace.2.2.2.2.2.1, hTrace.2.2.2.2.2.2.1,
    hTrace.2.2.2.2.2.2.2.1, ?_⟩
  rw [grantDrainD6ZeroBirthChargedBefore,
    grantDrainD6ZeroBirthChargedAfter]
  decide

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedColdStep
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedHostlessStep
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedRetiredStep
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedOrdinaryFireArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedExceptionalFireArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainD6ZeroBirthClean
#print axioms L3.GrantDrainEntrance.grantDrainD6ZeroBirthMergeSpent
#print axioms L3.GrantDrainEntrance.grantDrainD6ZeroBirthGuardTrace
#print axioms L3.GrantDrainEntrance.grantDrainD6ZeroBirthChargedBefore
#print axioms L3.GrantDrainEntrance.grantDrainD6ZeroBirthChargedAfter
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedWarmRankStepCounterexample

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Ready-responder off-front and family closure. -/

/-- B2: the ready OLD responder is not the OLD front.  The OLD
sector witness for the warm host gives a genuine nearest leader
and excludes every leader at a smaller positive left offset.
If the source lay in the inclusive scan, its immediate right
neighbor would lie at a smaller offset, contradicting the same
OLD nearest-leader property.  Both E endpoints are therefore
outside the entire OLD inclusive scan. -/
theorem grantDrainD6ReadyResponderOffFrontERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (_hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (_hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (_hxFollower : (s.native e).l = false)
    (_hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hOffFront :
      ring.rightNeighbor e ≠
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hOldFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  obtain ⟨p, D, a, hSector, haInside, hAt⟩ :=
    grantDrainEntranceSectorCoverOfRoot
      ring s.native hC.1.1.1 g
  have hDistance :=
    grantDrainD6OutgoingBulletSectorDistance
      ring s.native g p D a hSector haInside hAt hOldFollower
  have hFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g a.val hDistance.1 a.isLt).mp hDistance.2
  have hSourceAway :=
    (grantDrainD6ReadyResponderSelectedAway
      ring hn s e g z hyLeader hyReady hSelected hz).2
  have hNoY :
      ∀ j : Nat,
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
    intro j hj hEq
    by_cases hjZero : j = 0
    · subst j
      rw [grantDrainWarmShiftLeftZero] at hEq
      have hBad : (s.native g).l = true := by
        rw [hEq]
        exact hyLeader
      rw [hOldFollower] at hBad
      cases hBad
    · by_cases hjAt :
          j = grantDrainLeftLeaderDistance ring s.native g
      · rw [hjAt] at hEq
        exact hOffFront hEq.symm
      · have hBefore : j < a.val := by omega
        have hBad := hFirst.2 j (by omega) hBefore
        rw [hEq, hyLeader] at hBad
        cases hBad
  have hNoE :
      ∀ j : Nat,
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g j ≠ e := by
    intro j hj hEq
    by_cases hjZero : j = 0
    · subst j
      rw [grantDrainWarmShiftLeftZero] at hEq
      exact hSourceAway hEq
    · have hjShort : j < n := by
        have haShort := a.isLt
        omega
      have hNext :=
        grantDrainD6OutgoingBulletSuccessorAtOffset
          ring g e j (by omega) hjShort hEq.symm
      exact (hNoY (j - 1) (by omega)) hNext.symm
  have hOutside :
      ∀ j : Nat,
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g j ≠ e ∧
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
    intro j hj
    exact ⟨hNoE j hj, hNoY j hj⟩
  exact Nat.le_of_eq
    (grantDrainD6EScanOutsidePair ring s.native e g hOutside)

/-- The entire selected-FIRE ready-responder E family.  In the
front case the OLD sector witness identifies the front with
its sector leader and the earlier selected-front lemma applies.
The off-front case is B2 above. -/
theorem grantDrainD6ReadyResponderERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  by_cases hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)
  · have hOldFollower :=
      (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
    obtain ⟨p, D, a, hSector, haInside, hAt⟩ :=
      grantDrainEntranceSectorCoverOfRoot
        ring s.native hC.1.1.1 g
    have hDistance :=
      grantDrainD6OutgoingBulletSectorDistance
        ring s.native g p D a hSector haInside hAt hOldFollower
    have hFrontSite :
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g) = p := by
      rw [hDistance.2, hAt,
        grantDrainMarksArcShiftLeftRight
          ring p a.val a.val (Nat.le_refl _) a.isLt,
        Nat.sub_self, grantDrainWeakDeathShiftRightZero ring p]
    have hTo : ring.rightNeighbor e = p :=
      hFront.trans hFrontSite
    have hReadyP : (s.native p).sg = true := by
      rw [← hTo]
      exact hyReady
    exact grantDrainD6ReadyResponderSelectedFrontERankLe
      ring hn fresh update s e p g z D a.val hC hWarm
      hNonExceptional hSelected hz hStillWarm
      hSector hAt hDistance.1 haInside hDistance.2
      hTo hxFollower hxEmpty hReadyP
  · exact grantDrainD6ReadyResponderOffFrontERankLe
      ring hn fresh update s e g z hC hWarm
      hNonExceptional hSelected hz hStillWarm
      hxFollower hxEmpty hyLeader hyReady hFront

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderOffFrontERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderERankLe

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
D6-PAIR-SCAN.

The intended budget is only tested at a warm label's actual
granted host.  A standalone one-step preservation theorem with
no additional ghost coherence premise is false: an arbitrary
warm label can sit on an UNGRANTED old host.  The Y-to-X token
transport can grant this host on a no-FIRE step without spending
birthsLeft, activating a previously vacuous budget.  The closed
n=8 example at the bottom checks precisely this row.

Positive birth credit for an ACTUAL continuing warm granted label
is nevertheless derivable from the OLD budget:
  - a selected FIRE strictly lowers the global physical grant count;
  - the new granted host ensures the count after FIRE is at least one;
  - on a FIRE a continuing host has not moved, and its NEW grant
    was already present at that site in the OLD state.
Thus the OLD count is at least two and the budget forces
birthsLeft >= 1.

The unconditional one-step preservation claim requires additionally
a coherent OLD ghost: whenever a label is warm and hosted, its
host actually has a physical grant.  A theorem with this explicit
condition is supplied; the condition is not silently assumed.

All finite arithmetic counts use List.ofFn and Nat.  No Mathlib,
Batteries, Finset, axioms, or assumed proof leaf is involved.
-/

/-- The number of physically occupied GRANT sites at the cut. -/
def grantDrainD6GrantCount {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch) : Nat :=
  (List.ofFn (fun i : Fin n =>
    if s.grant i then 1 else 0)).sum

/-- Birth allowance is a bound on OTHER old grants, but only while
this particular label is both warm and hosted at a granted site. -/
def GrantDrainD6BirthBudget
    {n : Nat} {Scratch : Type}
    (_ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n) : Prop :=
  ∀ g : Fin n, label.warm = true →
    label.host = some g → s.grant g = true →
      grantDrainD6GrantCount s ≤ label.birthsLeft + 1

/-- A full n birth allowance satisfies the new cut invariant. -/
theorem grantDrainD6BirthBudgetInitialFull
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n)
    (hBirths : label.birthsLeft = n) :
    GrantDrainD6BirthBudget ring s label := by
  intro g _ _ _
  have hSlots := grantDrain_slots_le s
  change grantDrainD6GrantCount s ≤ label.birthsLeft + 1
  rw [hBirths]
  unfold grantDrainD6GrantCount
  omega

/-- If n is positive, n-1 is also a sufficient initial allowance. -/
theorem grantDrainD6BirthBudgetInitialMinusOne
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 1 ≤ n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n)
    (hBirths : label.birthsLeft = n - 1) :
    GrantDrainD6BirthBudget ring s label := by
  intro g _ _ _
  have hSlots := grantDrain_slots_le s
  change grantDrainD6GrantCount s ≤ label.birthsLeft + 1
  rw [hBirths]
  unfold grantDrainD6GrantCount
  omega

/-! The next two generic sum lemmas are restated publicly
because a similarly named two-entry helper in another module
is private and cannot be relied on here. -/

/-- Removing a single distinguished summand changes the two
complete finite sums by exactly the two distinguished values. -/
theorem grantDrainD6GrantSumBalanceOne :
    ∀ (n : Nat) (f g : Fin n → Nat) (j : Fin n),
      (∀ i : Fin n, i ≠ j → f i = g i) →
      (List.ofFn f).sum + g j =
        (List.ofFn g).sum + f j := by
  intro n
  induction n with
  | zero =>
      intro f g j _
      exact Fin.elim0 j
  | succ n ih =>
      intro f g j hOther
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hjZero : j = 0
      · subst j
        have hTail :
            (List.ofFn (fun i : Fin n => f i.succ)).sum =
              (List.ofFn (fun i : Fin n => g i.succ)).sum := by
          apply FiniteUniformStoppingTree.ofFn_sum_eq
          intro i
          apply hOther i.succ
          intro hBad
          have hv := congrArg Fin.val hBad
          simp at hv
        rw [hTail]
        omega
      · have hjPos : 0 < j.val := by
          have hjNe : j.val ≠ 0 := by
            intro hZero
            apply hjZero
            apply Fin.ext
            simpa using hZero
          omega
        have hjBound : j.val < n + 1 := j.isLt
        obtain ⟨jPred, hjPred⟩ : ∃ k : Fin n, k.val = j.val - 1 :=
          ⟨⟨j.val - 1, show j.val - 1 < n by omega⟩, rfl⟩
        have hSucc : jPred.succ = j := by
          apply Fin.ext
          rw [Fin.val_succ, hjPred]
          omega
        have hHead : f 0 = g 0 :=
          hOther 0 (Ne.symm hjZero)
        have hTail := ih
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ)
          jPred
          (by
            intro i hi
            apply hOther i.succ
            intro hBad
            apply hi
            apply Fin.ext
            have hv := congrArg Fin.val hBad
            change i.val + 1 = j.val at hv
            rw [hjPred]
            omega)
        rw [hSucc] at hTail
        omega

/-- Subtraction-free balance for two changed sites. -/
theorem grantDrainD6GrantSumBalanceTwo
    {n : Nat} (f g : Fin n → Nat)
    (a b : Fin n) (hab : a ≠ b)
    (hOther : ∀ i : Fin n, i ≠ a → i ≠ b → f i = g i) :
    (List.ofFn f).sum + g a + g b =
      (List.ofFn g).sum + f a + f b := by
  have hGa :
      (List.ofFn (fun i : Fin n =>
        if i = a then f i else g i)).sum + g a =
      (List.ofFn g).sum + f a := by
    have hh := grantDrainD6GrantSumBalanceOne n
      (fun i : Fin n => if i = a then f i else g i)
      g a (by intro i hi; simp [hi])
    simpa using hh
  have hFb :
      (List.ofFn f).sum + g b =
      (List.ofFn (fun i : Fin n =>
        if i = a then f i else g i)).sum + f b := by
    have hh := grantDrainD6GrantSumBalanceOne n
      f (fun i : Fin n => if i = a then f i else g i)
      b (by
        intro i hib
        by_cases hia : i = a
        · subst i
          simp
        · simp [hia, hOther i hia hib])
    simpa [Ne.symm hab] using hh
  omega

/-- The two-token physical grant balance, using only the actual
changed endpoints of grantDrainStep. -/
theorem grantDrainD6GrantCountPairBalance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    grantDrainD6GrantCount
        (grantDrainStep ring fresh update s e) +
        (if s.grant e then 1 else 0) +
        (if s.grant (ring.rightNeighbor e) then 1 else 0) =
      grantDrainD6GrantCount s +
        (if (grantDrainStep ring fresh update s e).grant e
          then 1 else 0) +
        (if (grantDrainStep ring fresh update s e).grant
            (ring.rightNeighbor e) then 1 else 0) := by
  have hDistinct :
      e ≠ ring.rightNeighbor e :=
    (grantDrainEntranceRightNeighborDistinct ring hn e).symm
  unfold grantDrainD6GrantCount
  apply grantDrainD6GrantSumBalanceTwo
    (fun i : Fin n =>
      if (grantDrainStep ring fresh update s e).grant i
        then 1 else 0)
    (fun i : Fin n => if s.grant i then 1 else 0)
    e (ring.rightNeighbor e) hDistinct
  intro i hiX hiY
  have hFrame :
      (grantDrainStep ring fresh update s e).grant i =
        s.grant i := by
    simp [grantDrainStep, hiX, hiY]
  rw [hFrame]

/-- A physical step cannot increase its two-site grant count. -/
theorem grantDrainD6GrantPairNoCloning
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    (if (grantDrainStep ring fresh update s e).grant e
      then 1 else 0) +
    (if (grantDrainStep ring fresh update s e).grant
      (ring.rightNeighbor e) then 1 else 0) ≤
    (if s.grant e then 1 else 0) +
    (if s.grant (ring.rightNeighbor e) then 1 else 0) := by
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  simpa [grantDrainStep, hDistinct] using
    (grantDrainTokenRow_noncloning
      (s.request e) (s.grant e)
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l
      (fresh s e) (grantDrainSelect ring s e))

/-- Total occupied GRANT count is nonincreasing on every edge. -/
theorem grantDrainD6GrantCountStepLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    grantDrainD6GrantCount
      (grantDrainStep ring fresh update s e) ≤
    grantDrainD6GrantCount s := by
  have hBalance :=
    grantDrainD6GrantCountPairBalance
      ring hn fresh update s e
  have hPair :=
    grantDrainD6GrantPairNoCloning
      ring hn fresh update s e
  omega

/-- The actual selector reads a physical OLD grant at the payer:
X for leftLocal, Y for rightLocal or cross. -/
theorem grantDrainD6FireFundingPorts
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    (grantDrainSelect ring s e = .leftLocal →
      s.grant e = true) ∧
    (grantDrainSelect ring s e = .rightLocal →
      s.grant (ring.rightNeighbor e) = true) ∧
    (grantDrainSelect ring s e = .cross →
      s.grant (ring.rightNeighbor e) = true) := by
  cases hrx : s.request e <;>
    cases hgx : s.grant e <;>
    cases hry : s.request (ring.rightNeighbor e) <;>
    cases hgy : s.grant (ring.rightNeighbor e) <;>
    cases hel : grantDrainEligible
      (nativeE ring s.native e) e <;>
    cases her : grantDrainEligible
      (nativeE ring s.native e) (ring.rightNeighbor e) <;>
    simp [grantDrainSelect, hrx, hgx, hry, hgy, hel, her]

/-- Every physically funded non-none FIRE removes at least one
grant from the local pair. This is a finite Boolean fact about
the exact T0/T1/HOLD/transport row, with no probabilistic premise. -/
theorem grantDrainD6TokenFireStrict
    (rx gx ry gy lx ly fresh : Bool)
    (fire : GrantDrainFire)
    (hFire : fire ≠ .none)
    (hPay :
      (fire = .leftLocal → gx = true) ∧
      (fire = .rightLocal → gy = true) ∧
      (fire = .cross → gy = true)) :
    (if (grantDrainTokenRow
      rx gx ry gy lx ly fresh fire).1.grant then 1 else 0) +
    (if (grantDrainTokenRow
      rx gx ry gy lx ly fresh fire).2.grant then 1 else 0) +
      1 ≤
    (if gx then 1 else 0) + (if gy then 1 else 0) := by
  cases fire with
  | none =>
      exact False.elim (hFire rfl)
  | leftLocal =>
      have hx : gx = true := hPay.1 rfl
      rw [hx]
      cases rx <;> cases ry <;> cases gy <;>
        cases lx <;> cases ly <;> cases fresh <;> decide
  | rightLocal =>
      have hy : gy = true := hPay.2.1 rfl
      rw [hy]
      cases rx <;> cases gx <;> cases ry <;>
        cases lx <;> cases ly <;> cases fresh <;> decide
  | cross =>
      have hy : gy = true := hPay.2.2 rfl
      rw [hy]
      cases rx <;> cases gx <;> cases ry <;>
        cases lx <;> cases ly <;> cases fresh <;> decide

/-- A selected canonical FIRE strictly decreases the physical
total grant count, without assuming a ghost budget. -/
theorem grantDrainD6GrantCountFireStrict
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    grantDrainD6GrantCount
      (grantDrainStep ring fresh update s e) + 1 ≤
    grantDrainD6GrantCount s := by
  have hFunding := grantDrainD6FireFundingPorts ring s e
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  have hPair :
      (if (grantDrainStep ring fresh update s e).grant e
        then 1 else 0) +
      (if (grantDrainStep ring fresh update s e).grant
          (ring.rightNeighbor e) then 1 else 0) + 1 ≤
      (if s.grant e then 1 else 0) +
      (if s.grant (ring.rightNeighbor e) then 1 else 0) := by
    simpa [grantDrainStep, hDistinct] using
      (grantDrainD6TokenFireStrict
        (s.request e) (s.grant e)
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring s e e).l
        (grantDrainNativeNext ring s e
          (ring.rightNeighbor e)).l
        (fresh s e) (grantDrainSelect ring s e)
        hFire hFunding)
  have hBalance :=
    grantDrainD6GrantCountPairBalance
      ring hn fresh update s e
  omega

/-- A nonzero summand belongs to the total nonnegative sum. -/
theorem grantDrainD6GrantTermLeSum :
    ∀ (n : Nat) (f : Fin n → Nat) (j : Fin n),
      f j ≤ (List.ofFn f).sum := by
  intro n
  induction n with
  | zero =>
      intro f j
      exact Fin.elim0 j
  | succ n ih =>
      intro f j
      rw [List.ofFn_succ, List.sum_cons]
      by_cases hjZero : j = 0
      · subst j
        omega
      · have hjPos : 0 < j.val := by
          have hjNe : j.val ≠ 0 := by
            intro hZero
            apply hjZero
            apply Fin.ext
            simpa using hZero
          omega
        have hjBound : j.val < n + 1 := j.isLt
        obtain ⟨jPred, hjPred⟩ : ∃ k : Fin n, k.val = j.val - 1 :=
          ⟨⟨j.val - 1, show j.val - 1 < n by omega⟩, rfl⟩
        have hSucc : jPred.succ = j := by
          apply Fin.ext
          rw [Fin.val_succ, hjPred]
          omega
        have hTail :=
          ih (fun i : Fin n => f i.succ) jPred
        rw [hSucc] at hTail
        omega

/-- One actual granted host gives at least one occupied site. -/
theorem grantDrainD6GrantCountPositive
    {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch)
    (g : Fin n) (hGrant : s.grant g = true) :
    1 ≤ grantDrainD6GrantCount s := by
  have hTerm :=
    grantDrainD6GrantTermLeSum n
      (fun i : Fin n => if s.grant i then 1 else 0) g
  simp only [hGrant, ite_true] at hTerm
  exact hTerm

/-- On a selected FIRE, any surviving physical grant at the
source or responder was already there on the OLD cut.
The key physical fact is that leftLocal/cross makes the
source a leader, suppressing Y-to-X grant transport. -/
theorem grantDrainD6TokenFireNoNewGrant
    (rx gx ry gy lx ly fresh : Bool)
    (fire : GrantDrainFire)
    (hFire : fire ≠ .none)
    (hBorn : (fire = .leftLocal ∨ fire = .cross) →
      lx = true) :
    ((grantDrainTokenRow rx gx ry gy lx ly fresh fire).1.grant =
      true → gx = true) ∧
    ((grantDrainTokenRow rx gx ry gy lx ly fresh fire).2.grant =
      true → gy = true) := by
  cases fire with
  | none =>
      exact False.elim (hFire rfl)
  | leftLocal =>
      have hl : lx = true := hBorn (Or.inl rfl)
      rw [hl]
      cases rx <;> cases gx <;> cases ry <;>
        cases gy <;> cases ly <;> cases fresh <;> decide
  | rightLocal =>
      cases rx <;> cases gx <;> cases ry <;>
        cases gy <;> cases lx <;> cases ly <;>
        cases fresh <;> decide
  | cross =>
      have hl : lx = true := hBorn (Or.inr rfl)
      rw [hl]
      cases rx <;> cases gx <;> cases ry <;>
        cases gy <;> cases ly <;> cases fresh <;> decide

/-- Selected FIRE has pointwise GRANT noncreation, a stronger
property than its aggregate strict decrease. No such pointwise
claim is made for no-FIRE Y-to-X movement. -/
theorem grantDrainD6FireGrantPointwise
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    ∀ i : Fin n,
      (grantDrainStep ring fresh update s e).grant i = true →
      s.grant i = true := by
  have hBorn :
      (grantDrainSelect ring s e = .leftLocal ∨
        grantDrainSelect ring s e = .cross) →
      (grantDrainNativeNext ring s e e).l = true := by
    intro h
    rcases h with hLeft | hCross
    · simp [grantDrainNativeNext, hLeft,
        canonicalBirth, firedNative]
    · simp [grantDrainNativeNext, hCross,
        canonicalBirth, firedNative]
  have hPair :=
    grantDrainD6TokenFireNoNewGrant
      (s.request e) (s.grant e)
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l
      (fresh s e) (grantDrainSelect ring s e)
      hFire hBorn
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  intro i hNew
  by_cases hiX : i = e
  · subst i
    apply hPair.1
    simpa [grantDrainStep] using hNew
  · by_cases hiY : i = ring.rightNeighbor e
    · subst i
      apply hPair.2
      simpa [grantDrainStep, hDistinct] using hNew
    · have hFrame :
          (grantDrainStep ring fresh update s e).grant i =
            s.grant i := by
        simp [grantDrainStep, hiX, hiY]
      rw [hFrame] at hNew
      exact hNew

/-- If a selected FIRE leaves a ghost with any named host, its
host has NOT moved.  The only possible Y-to-X move is a
no-FIRE row: selected rightLocal/cross retires an old Y host;
selected leftLocal makes the source a leader and also retires it. -/
theorem grantDrainD6FireSurvivingHostUnmoved
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e q : Fin n)
    (label : GrantDrainWarmLabel n)
    (hFire : grantDrainSelect ring s e ≠ .none)
    (hNextHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some q) :
    label.host = some q := by
  cases hOldHost : label.host with
  | none =>
      have hNone :
          (grantDrainWarmLabelStep ring fresh update s e
            label).host = none := by
        simp [grantDrainWarmLabelStep, hOldHost]
      rw [hNone] at hNextHost
      cases hNextHost
  | some p =>
      by_cases hpX : p = e
      · subst p
        have hContact :=
          grantDrainD6ContactHostAtSource
            ring fresh update s e label hOldHost
        cases hx :
            grantDrainD6ContactRowSourceGrant ring fresh s e with
        | false =>
            rw [hContact, hx] at hNextHost
            cases hNextHost
        | true =>
            rw [hContact, hx] at hNextHost
            have hEq : e = q := Option.some.inj hNextHost
            exact congrArg some hEq
      · by_cases hpY : p = ring.rightNeighbor e
        · subst p
          have hContact :=
            grantDrainD6ContactHostAtResponder
              ring hn fresh update s e label hOldHost
          cases hf : grantDrainSelect ring s e with
          | none =>
              exact False.elim (hFire hf)
          | rightLocal =>
              rw [hContact] at hNextHost
              simp [hf] at hNextHost
          | cross =>
              rw [hContact] at hNextHost
              simp [hf] at hNextHost
          | leftLocal =>
              have hLeader :
                  (grantDrainNativeNext ring s e e).l =
                    true := by
                simp [grantDrainNativeNext, hf,
                  canonicalBirth, firedNative]
              rw [hContact] at hNextHost
              simp [hf, hLeader] at hNextHost
        · have hFixed :
            (grantDrainWarmLabelStep ring fresh update s e
              label).host = some p := by
            simp [grantDrainWarmLabelStep, hOldHost, hpX, hpY]
          have hEq : p = q :=
            Option.some.inj (hFixed.symm.trans hNextHost)
          exact congrArg some hEq

/-- Obligation A, without an assumed payer/label-disjointness
leaf.  A continuing warm granted label on a FIRE had an OLD
grant at the same host; selected FIRE removed at least one
additional site, since a granted site is still present afterward.
The budget therefore forces one positive birth credit. -/
theorem grantDrainD6BirthBudgetFireCredit
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hBudget : GrantDrainD6BirthBudget ring s label)
    (hFire : grantDrainSelect ring s e ≠ .none)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true)
    (q : Fin n)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some q)
    (hNewGrant :
      (grantDrainStep ring fresh update s e).grant q = true) :
    1 ≤ label.birthsLeft := by
  have hOldWarm : label.warm = true := by
    cases hw : label.warm with
    | true => rfl
    | false =>
        have hCold :=
          grantDrainD6MergeColdLabelRemainsCold
            ring fresh update s e label hw
        rw [hCold] at hNewWarm
        cases hNewWarm
  have hOldHost :=
    grantDrainD6FireSurvivingHostUnmoved
      ring hn fresh update s e q label hFire hNewHost
  have hOldGrant :=
    grantDrainD6FireGrantPointwise
      ring (by omega : 2 ≤ n) fresh update s e
      hFire q hNewGrant
  have hOldBound := hBudget q hOldWarm hOldHost hOldGrant
  have hFireStrict :=
    grantDrainD6GrantCountFireStrict
      ring (by omega : 2 ≤ n) fresh update s e hFire
  have hNewPositive :=
    grantDrainD6GrantCountPositive
      (grantDrainStep ring fresh update s e)
      q hNewGrant
  omega

/-- Exact ghost cost of every selected FIRE; this holds even
for an exhausted allowance, so the positive-credit lemma above
is needed to make the subtraction actually pay one. -/
theorem grantDrainD6BirthBudgetFireDebit
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    (grantDrainWarmLabelStep ring fresh update s e
      label).birthsLeft = label.birthsLeft - 1 :=
  grantDrainD6ContactPhysicalBirthBudget
    ring fresh update s e label hFire

/-- A coherent OLD ghost has a grant whenever it is warm and
hosted.  This explicit condition rules out an UNGRANTED old
ghost becoming newly active through a no-FIRE transfer.
It is deliberately NOT built into GrantDrainD6BirthBudget. -/
def GrantDrainD6HostCoherent
    {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n) : Prop :=
  ∀ g : Fin n, label.warm = true →
    label.host = some g → s.grant g = true

/-- The birth budget is preserved by every physical step for
an OLD coherent label. In a FIRE the strict grant-count drop,
credit decrement and positive-credit lemma are all derived;
without FIRE the count cannot increase and b is unchanged. -/
theorem grantDrainD6BirthBudgetStepOfCoherent
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hBudget : GrantDrainD6BirthBudget ring s label)
    (hCoherent : GrantDrainD6HostCoherent s label) :
    GrantDrainD6BirthBudget ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  intro q hNewWarm hNewHost hNewGrant
  have hOldWarm : label.warm = true := by
    cases hw : label.warm with
    | true => rfl
    | false =>
        have hCold :=
          grantDrainD6MergeColdLabelRemainsCold
            ring fresh update s e label hw
        rw [hCold] at hNewWarm
        cases hNewWarm
  cases hOldHost : label.host with
  | none =>
      have hNone :
          (grantDrainWarmLabelStep ring fresh update s e
            label).host = none := by
        simp [grantDrainWarmLabelStep, hOldHost]
      rw [hNone] at hNewHost
      cases hNewHost
  | some p =>
      have hOldGrant := hCoherent p hOldWarm hOldHost
      have hOldBound :=
        hBudget p hOldWarm hOldHost hOldGrant
      change
        grantDrainD6GrantCount
          (grantDrainStep ring fresh update s e) ≤
        (grantDrainWarmLabelStep ring fresh update s e
          label).birthsLeft + 1
      by_cases hNone : grantDrainSelect ring s e = .none
      · have hUnchanged :
            (grantDrainWarmLabelStep ring fresh update s e
              label).birthsLeft = label.birthsLeft := by
          simp [grantDrainWarmLabelStep, hNone]
        have hCount :=
          grantDrainD6GrantCountStepLe
            ring (by omega : 2 ≤ n) fresh update s e
        rw [hUnchanged]
        omega
      · have hDebit :=
          grantDrainD6BirthBudgetFireDebit
            ring fresh update s e label hNone
        have hPositive :=
          grantDrainD6BirthBudgetFireCredit
            ring hn fresh update s e label hBudget
            hNone hNewWarm q hNewHost hNewGrant
        have hCount :=
          grantDrainD6GrantCountFireStrict
            ring (by omega : 2 ≤ n) fresh update s e hNone
        rw [hDebit]
        omega

/-! The following actual OLD native state is the merged
n=8 C_native witness.  Only its OLD request/grant word and
the ghost host differ: the ghost is warm at e=2 but does
NOT own a GRANT there.  Its budget therefore holds vacuously.
The edge e=2, y=3 is a no-FIRE Y-to-X transfer; the total count
stays 2, and the after-step ghost has a warm granted host. -/

def grantDrainD6BudgetUnheldState : GrantDrainState 8 Unit :=
  { native := grantDrainD6ZeroBirthNative
    request := fun _ => false
    grant := fun i => i.val == 3 || i.val == 4
    scratch := ()
    history := [] }

def grantDrainD6BudgetUnheldLabel : GrantDrainWarmLabel 8 :=
  { identity := (2 : Fin 8)
    host := some (2 : Fin 8)
    warm := true
    birthsLeft := 0
    exceptionalLeft := true }

def grantDrainD6BudgetUnheldAfter : GrantDrainState 8 Unit :=
  grantDrainStep grantDrainD6ZeroBirthRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainD6BudgetUnheldState (2 : Fin 8)

def grantDrainD6BudgetUnheldLabelAfter :
    GrantDrainWarmLabel 8 :=
  grantDrainWarmLabelStep grantDrainD6ZeroBirthRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainD6BudgetUnheldState (2 : Fin 8)
    grantDrainD6BudgetUnheldLabel

/-- The OLD native word is unchanged from the public
C_native control. -/
theorem grantDrainD6BudgetUnheldClean :
    C_native grantDrainD6ZeroBirthRing
      grantDrainD6BudgetUnheldState.native := by
  exact grantDrainD6ZeroBirthClean

/-- OLD label is warm but is not at a granted host; its
budget implication is consequently vacuous. -/
theorem grantDrainD6BudgetUnheldBefore :
    GrantDrainD6BirthBudget grantDrainD6ZeroBirthRing
      grantDrainD6BudgetUnheldState
      grantDrainD6BudgetUnheldLabel := by
  intro g _ hHost hGrant
  have hg : g = (2 : Fin 8) := by
    change some (2 : Fin 8) = some g at hHost
    exact (Option.some.inj hHost).symm
  subst g
  have hNoGrant :
      grantDrainD6BudgetUnheldState.grant (2 : Fin 8) =
        false := by
    unfold grantDrainD6BudgetUnheldState
    decide
  rw [hNoGrant] at hGrant
  cases hGrant

/-- The physical edge and its ghost update are closed n=8 terms:
no FIRE, a newly granted warm host e, two total GRANT sites. -/
theorem grantDrainD6BudgetUnheldTrace :
    grantDrainWarmAt grantDrainD6BudgetUnheldState
        (2 : Fin 8) = true ∧
    grantDrainD6BudgetUnheldState.grant (2 : Fin 8) = false ∧
    grantDrainSelect grantDrainD6ZeroBirthRing
      grantDrainD6BudgetUnheldState (2 : Fin 8) = .none ∧
    grantDrainD6BudgetUnheldAfter.grant (2 : Fin 8) = true ∧
    grantDrainD6BudgetUnheldAfter.grant (4 : Fin 8) = true ∧
    grantDrainWarmAt grantDrainD6BudgetUnheldAfter
      (2 : Fin 8) = true ∧
    grantDrainD6BudgetUnheldLabelAfter.host = some (2 : Fin 8) ∧
    grantDrainD6BudgetUnheldLabelAfter.warm = true ∧
    grantDrainD6GrantCount grantDrainD6BudgetUnheldState = 2 ∧
    grantDrainD6GrantCount grantDrainD6BudgetUnheldAfter = 2 ∧
    grantDrainD6BudgetUnheldLabelAfter.birthsLeft = 0 := by
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_, ?_, by decide⟩
  · unfold grantDrainD6GrantCount
    decide
  · unfold grantDrainD6GrantCount
    decide

/-- After the no-FIRE transfer the budget is active and FALSE:
two grants remain but the unchanged birth allowance is zero. -/
theorem grantDrainD6BudgetUnheldAfterFails :
    ¬ GrantDrainD6BirthBudget grantDrainD6ZeroBirthRing
      grantDrainD6BudgetUnheldAfter
      grantDrainD6BudgetUnheldLabelAfter := by
  intro hBudget
  have hWarm :
      grantDrainD6BudgetUnheldLabelAfter.warm = true :=
    grantDrainD6BudgetUnheldTrace.2.2.2.2.2.2.2.1
  have hHost :
      grantDrainD6BudgetUnheldLabelAfter.host =
        some (2 : Fin 8) :=
    grantDrainD6BudgetUnheldTrace.2.2.2.2.2.2.1
  have hGrant :
      grantDrainD6BudgetUnheldAfter.grant (2 : Fin 8) =
        true :=
    grantDrainD6BudgetUnheldTrace.2.2.2.1
  have hCount :
      grantDrainD6GrantCount grantDrainD6BudgetUnheldAfter =
        2 :=
    grantDrainD6BudgetUnheldTrace.2.2.2.2.2.2.2.2.2.1
  have hBirth :
      grantDrainD6BudgetUnheldLabelAfter.birthsLeft = 0 :=
    grantDrainD6BudgetUnheldTrace.2.2.2.2.2.2.2.2.2.2
  have hBound :=
    hBudget (2 : Fin 8) hWarm hHost hGrant
  rw [hCount, hBirth] at hBound
  omega

/-- CLOSED counterexample to an unconditional preservation
assertion under just C_native and the proposed birth budget.
No FIRE and no new GRANT is produced; failure is solely the
missing OLD host/grant coherence condition. -/
theorem grantDrainD6BirthBudgetPreservationCounterexample :
    C_native grantDrainD6ZeroBirthRing
      grantDrainD6BudgetUnheldState.native ∧
    GrantDrainD6BirthBudget grantDrainD6ZeroBirthRing
      grantDrainD6BudgetUnheldState
      grantDrainD6BudgetUnheldLabel ∧
    grantDrainSelect grantDrainD6ZeroBirthRing
      grantDrainD6BudgetUnheldState (2 : Fin 8) = .none ∧
    grantDrainD6BudgetUnheldLabelAfter.warm = true ∧
    grantDrainD6BudgetUnheldLabelAfter.host = some (2 : Fin 8) ∧
    grantDrainD6BudgetUnheldAfter.grant (2 : Fin 8) = true ∧
    ¬ GrantDrainD6BirthBudget grantDrainD6ZeroBirthRing
      grantDrainD6BudgetUnheldAfter
      grantDrainD6BudgetUnheldLabelAfter := by
  exact ⟨grantDrainD6BudgetUnheldClean,
    grantDrainD6BudgetUnheldBefore,
    grantDrainD6BudgetUnheldTrace.2.2.1,
    grantDrainD6BudgetUnheldTrace.2.2.2.2.2.2.2.1,
    grantDrainD6BudgetUnheldTrace.2.2.2.2.2.2.1,
    grantDrainD6BudgetUnheldTrace.2.2.2.1,
    grantDrainD6BudgetUnheldAfterFails⟩

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6BirthBudgetInitialFull
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthBudgetInitialMinusOne
#print axioms L3.GrantDrainEntrance.grantDrainD6GrantSumBalanceOne
#print axioms L3.GrantDrainEntrance.grantDrainD6GrantSumBalanceTwo
#print axioms L3.GrantDrainEntrance.grantDrainD6GrantCountPairBalance
#print axioms L3.GrantDrainEntrance.grantDrainD6GrantPairNoCloning
#print axioms L3.GrantDrainEntrance.grantDrainD6GrantCountStepLe
#print axioms L3.GrantDrainEntrance.grantDrainD6FireFundingPorts
#print axioms L3.GrantDrainEntrance.grantDrainD6TokenFireStrict
#print axioms L3.GrantDrainEntrance.grantDrainD6GrantCountFireStrict
#print axioms L3.GrantDrainEntrance.grantDrainD6GrantTermLeSum
#print axioms L3.GrantDrainEntrance.grantDrainD6GrantCountPositive
#print axioms L3.GrantDrainEntrance.grantDrainD6TokenFireNoNewGrant
#print axioms L3.GrantDrainEntrance.grantDrainD6FireGrantPointwise
#print axioms L3.GrantDrainEntrance.grantDrainD6FireSurvivingHostUnmoved
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthBudgetFireCredit
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthBudgetFireDebit
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthBudgetStepOfCoherent
#print axioms L3.GrantDrainEntrance.grantDrainD6BudgetUnheldClean
#print axioms L3.GrantDrainEntrance.grantDrainD6BudgetUnheldBefore
#print axioms L3.GrantDrainEntrance.grantDrainD6BudgetUnheldTrace
#print axioms L3.GrantDrainEntrance.grantDrainD6BudgetUnheldAfterFails
#print axioms L3.GrantDrainEntrance.grantDrainD6BirthBudgetPreservationCounterexample

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Corrected selected-FIRE rank assembly,
host-at-birth retirement, and independently proved no-FIRE rows. -/

/-- The selected-FIRE E-only rank comparison, with all four
OLD physical rows discharged by the already merged D6 facts. -/
theorem grantDrainD6NonExceptionalERankLeOfStillWarm
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  cases hxLeader : (s.native e).l with
  | true =>
      exact grantDrainD6SourceLeaderERankLe
        ring hn fresh update s e g z hC hWarm
        hNonExceptional hSelected hz hStillWarm hxLeader
  | false =>
      by_cases hxEmpty : (s.native e).b = (0 : Fin 3)
      · cases hyLeader : (s.native (ring.rightNeighbor e)).l with
        | false =>
            exact grantDrainD6EmptyFollowerNotReadyResponderERankLe
              ring hn s e g hC hWarm hxLeader hxEmpty
              (Or.inl hyLeader)
        | true =>
            cases hyReady : (s.native (ring.rightNeighbor e)).sg with
            | false =>
                exact grantDrainD6EmptyFollowerNotReadyResponderERankLe
                  ring hn s e g hC hWarm hxLeader hxEmpty
                  (Or.inr hyReady)
            | true =>
                exact grantDrainD6ReadyResponderERankLe
                  ring hn fresh update s e g z hC hWarm
                  hNonExceptional hSelected hz hStillWarm
                  hxLeader hxEmpty hyLeader hyReady
      · exact grantDrainD6OutgoingBulletERankLe
          ring hn fresh update s e g z hC hWarm
          hNonExceptional hSelected hz hStillWarm
          hxLeader hxEmpty

/-- The unconditional corrected s1n birth lift: the E-only
comparison is obtained by the complete four-row dispatch above,
then consumed by the existing E-then-birth bridge. -/
theorem grantDrainD6NonExceptionalBirthRankLift
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hz : z ≠ g)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true) :
    grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
      grantDrainWarmRank ring s.native g + 1 := by
  have hERank :=
    grantDrainD6NonExceptionalERankLeOfStillWarm
      ring hn fresh update s e g z hC hWarm
      hNonExceptional hSelected hz hStillWarm
  exact grantDrainD6NonExceptionalBirthRankLiftOfERank
    ring hn fresh update s e g z hC hNonExceptional
    hSelected hz hStillWarm hERank

/-- Read the ghost's warm bit through its actual next host.
This is definitional, not an invariant assumption. -/
theorem grantDrainD6LabelWarmHostReadout
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n) :
    (grantDrainWarmLabelStep ring fresh update s e label).warm =
      match (grantDrainWarmLabelStep ring fresh update s e
          label).host with
      | none => false
      | some g => label.warm &&
          grantDrainWarmAt (grantDrainStep ring fresh update s e) g := by
  rfl

/-- A canonical birth at the OLD source host either retires
that identity through the literal token row or makes its
continuing host physically cold. -/
theorem grantDrainD6HostAtSourceBirthRetires
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hHost : label.host = some e)
    (hFire :
      grantDrainSelect ring s e = .leftLocal ∨
      grantDrainSelect ring s e = .cross) :
    (grantDrainWarmLabelStep ring fresh update s e label).host =
        none ∨
      (grantDrainWarmLabelStep ring fresh update s e label).warm =
        false := by
  have hPhysical :=
    grantDrainD6CompositeSourceBirthEndsWarm
      ring fresh update s e hFire
  have hRoute :=
    grantDrainD6ContactHostAtSource
      ring fresh update s e label hHost
  have hRead :=
    grantDrainD6LabelWarmHostReadout
      ring fresh update s e label
  cases hGrant : grantDrainD6ContactRowSourceGrant ring fresh s e with
  | false =>
      left
      rw [hRoute]
      simp [hGrant]
  | true =>
      right
      rw [hRead, hRoute]
      simp [hGrant, hPhysical]

/-- A selected canonical birth at the tracked OLD host
cannot leave the label both hosted and warm. -/
theorem grantDrainD6HostAtBirthRetires
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hHost : label.host = some g)
    (hBirth : ∃ z : Fin n,
      z = g ∧
      ((grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
       (grantDrainSelect ring s e = .rightLocal ∧
          z = ring.rightNeighbor e) ∨
       (grantDrainSelect ring s e = .cross ∧ z = e))) :
    (grantDrainWarmLabelStep ring fresh update s e label).host =
        none ∨
      (grantDrainWarmLabelStep ring fresh update s e label).warm =
        false := by
  obtain ⟨z, hz, hChoice⟩ := hBirth
  rcases hChoice with hLeft | hRight | hCross
  · have hGE : g = e := hz.symm.trans hLeft.2
    have hHostE : label.host = some e := by
      rw [← hGE]
      exact hHost
    exact grantDrainD6HostAtSourceBirthRetires
      ring fresh update s e label hHostE (Or.inl hLeft.1)
  · have hGY : g = ring.rightNeighbor e :=
      hz.symm.trans hRight.2
    have hHostY :
        label.host = some (ring.rightNeighbor e) := by
      rw [← hGY]
      exact hHost
    left
    rw [grantDrainD6ContactHostAtResponder
      ring hn fresh update s e label hHostY]
    simp [hRight.1]
  · have hGE : g = e := hz.symm.trans hCross.2
    have hHostE : label.host = some e := by
      rw [← hGE]
      exact hHost
    exact grantDrainD6HostAtSourceBirthRetires
      ring fresh update s e label hHostE (Or.inr hCross.1)

/-! Unconditional no-FIRE subrows.  These results do
not assume a selected FIRE or a future birth-site relation. -/

/-- In a no-FIRE follower-to-follower outgoing-bullet contact,
post-step warmth excludes the responder as host.  The old
C_native first-bullet/outside-scan dichotomy then applies. -/
theorem grantDrainD6NoFireOutgoingFollowerERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNone : grantDrainSelect ring s e = .none)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hNewEmpty :
      (nativeE ring s.native e g).b = (0 : Fin 3) := by
    have hPhysical :=
      (grantDrainD6ExceptionalDeathHostFields
        (grantDrainStep ring fresh update s e)
        g hStillWarm).2.1
    rw [grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone] at hPhysical
    exact hPhysical
  have hFields :=
    grantDrainD6OutgoingBulletFollowerEFields
      ring hn s.native e hC hxFollower hxBullet hyFollower
  have hAtY :
      (nativeE ring s.native e (ring.rightNeighbor e)).b ≠
        (0 : Fin 3) := by
    rw [hFields.2.2.2.2.1]
    exact hxBullet
  have hNotResponder : ring.rightNeighbor e ≠ g := by
    intro hYG
    apply hAtY
    rw [hYG]
    exact hNewEmpty
  rcases grantDrainD6OutgoingBulletFollowerScanDichotomy
      ring hn s e g hC hWarm hxFollower hxBullet
      hyFollower hNotResponder with
    hOutside | ⟨k, hk, hInside, hDShort, hFirst,
      hSource, hTarget⟩
  · exact grantDrainD6OutgoingBulletOutsideScanERankLe
      ring hn s e g hC hWarm hxFollower hxBullet hOutside
  · exact grantDrainD6OutgoingBulletFirstInScanERankLe
      ring hn s e g hC hWarm
      hxFollower hxBullet hyFollower
      (grantDrainLeftLeaderDistance ring s.native g) k
      rfl hDShort hk hInside hFirst hSource hTarget

/-- Outgoing follower bullets meeting an OLD leader require no
FIRE hypothesis: either the pair is outside the old scan, the
front is ready, the quiet front survives, or its nonexceptional
death preserves an OLD scanned bullet. -/
theorem grantDrainD6NoFireOutgoingLeaderERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  rcases grantDrainD6OutgoingBulletLeaderOutsideOrBoundaryRank
      ring hn s e g hC hWarm hxFollower hxBullet hyLeader with
    hRank | hFront
  · exact hRank
  · cases hyReady : (s.native (ring.rightNeighbor e)).sg with
    | true =>
        exact grantDrainD6OutgoingBulletReadyFrontERankLe
          ring hn s e g hC hWarm hxFollower hxBullet
          hyLeader hyReady hFront
    | false =>
        cases hAlive :
            (nativeE ring s.native e (ring.rightNeighbor e)).l with
        | true =>
            exact grantDrainD6OutgoingBulletQuietFrontSurvivesERankLe
              ring hn s e g hC hWarm
              hxFollower hxBullet hyLeader hyReady hFront hAlive
        | false =>
            obtain ⟨k, hOldBullet⟩ :=
              grantDrainD6OutgoingBulletQuietFrontDeathHasOldBullet
                ring hn s e g hC hWarm hxFollower hxBullet
                hyLeader hyReady hFront hAlive hNonExceptional
            exact grantDrainD6OutgoingBulletQuietFrontDeathOldBulletERankLe
              ring hn s e g hC hWarm
              hxFollower hxBullet hyLeader hyReady
              hFront k hOldBullet

/-- Hence the whole no-FIRE outgoing-bullet family is closed. -/
theorem grantDrainD6NoFireOutgoingBulletERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNone : grantDrainSelect ring s e = .none)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3)) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  cases hyLeader : (s.native (ring.rightNeighbor e)).l with
  | false =>
      exact grantDrainD6NoFireOutgoingFollowerERankLe
        ring hn fresh update s e g hC hWarm hNone hStillWarm
        hxFollower hxBullet hyLeader
  | true =>
      exact grantDrainD6NoFireOutgoingLeaderERankLe
        ring hn s e g hC hWarm hNonExceptional
        hxFollower hxBullet hyLeader

/-- Independent OLD geometry for a leader responder: if it is
not the OLD front and the source is not the warm host, neither
endpoint belongs to the OLD inclusive scan. -/
theorem grantDrainD6ReadyResponderOutsideIfSourceAway
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hSourceAway : g ≠ e)
    (hOffFront :
      ring.rightNeighbor e ≠
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)) :
    ∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g j ≠ e ∧
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
  have hOldFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  obtain ⟨p, D, a, hSector, haInside, hAt⟩ :=
    grantDrainEntranceSectorCoverOfRoot
      ring s.native hC.1.1.1 g
  have hDistance :=
    grantDrainD6OutgoingBulletSectorDistance
      ring s.native g p D a hSector haInside hAt hOldFollower
  have hFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g a.val hDistance.1 a.isLt).mp hDistance.2
  have hNoY :
      ∀ j : Nat,
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
          PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
    intro j hj hEq
    by_cases hjZero : j = 0
    · subst j
      rw [grantDrainWarmShiftLeftZero] at hEq
      have hBad : (s.native g).l = true := by
        rw [hEq]
        exact hyLeader
      rw [hOldFollower] at hBad
      cases hBad
    · by_cases hjAt :
          j = grantDrainLeftLeaderDistance ring s.native g
      · rw [hjAt] at hEq
        exact hOffFront hEq.symm
      · have hBefore : j < a.val := by omega
        have hBad := hFirst.2 j (by omega) hBefore
        rw [hEq, hyLeader] at hBad
        cases hBad
  have hNoE :
      ∀ j : Nat,
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
          PPL.shiftLeft ring g j ≠ e := by
    intro j hj hEq
    by_cases hjZero : j = 0
    · subst j
      rw [grantDrainWarmShiftLeftZero] at hEq
      exact hSourceAway hEq
    · have hjShort : j < n := by
        have haShort := a.isLt
        omega
      have hNext :=
        grantDrainD6OutgoingBulletSuccessorAtOffset
          ring g e j (by omega) hjShort hEq.symm
      exact (hNoY (j - 1) (by omega)) hNext.symm
  intro j hj
  exact ⟨hNoE j hj, hNoY j hj⟩

/-- The ready-responder E-row also needs no selected FIRE if the
warm host is distinct from the source.  The remaining g=e case
has intentionally not been assumed or asserted. -/
theorem grantDrainD6ReadyResponderAwayERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxFollower : (s.native e).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hSourceAway : g ≠ e) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  by_cases hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)
  · have hOldFollower :=
      (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
    obtain ⟨p, D, a, hSector, haInside, hAt⟩ :=
      grantDrainEntranceSectorCoverOfRoot
        ring s.native hC.1.1.1 g
    have hDistance :=
      grantDrainD6OutgoingBulletSectorDistance
        ring s.native g p D a hSector haInside hAt hOldFollower
    have hFrontSite :
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g) = p := by
      rw [hDistance.2, hAt,
        grantDrainMarksArcShiftLeftRight
          ring p a.val a.val (Nat.le_refl _) a.isLt,
        Nat.sub_self, grantDrainWeakDeathShiftRightZero ring p]
    have hTo : ring.rightNeighbor e = p :=
      hFront.trans hFrontSite
    have hReadyP : (s.native p).sg = true := by
      rw [← hTo]
      exact hyReady
    exact grantDrainD6ReadyResponderFrontERankLe
      ring hn s e p g D a.val hC hWarm
      hSector hAt hDistance.1 haInside hDistance.2
      hTo hxFollower hxEmpty hReadyP hSourceAway
  · have hOutside :=
      grantDrainD6ReadyResponderOutsideIfSourceAway
        ring hn s e g hC hWarm
        hyLeader hSourceAway hFront
    exact Nat.le_of_eq
      (grantDrainD6EScanOutsidePair
        ring s.native e g hOutside)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalERankLeOfStillWarm
#print axioms L3.GrantDrainEntrance.grantDrainD6NonExceptionalBirthRankLift
#print axioms L3.GrantDrainEntrance.grantDrainD6LabelWarmHostReadout
#print axioms L3.GrantDrainEntrance.grantDrainD6HostAtSourceBirthRetires
#print axioms L3.GrantDrainEntrance.grantDrainD6HostAtBirthRetires
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireOutgoingFollowerERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireOutgoingLeaderERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireOutgoingBulletERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderOutsideIfSourceAway
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderAwayERankLe

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
SCAN.

(H) The ghost's host-routing decision uses exactly the same
two-site grant row as grantDrainStep.  A kept source host is
therefore granted; a kept responder host is an actual HOLD;
an incoming Y-to-X transfer is recorded only if the row
grants X; and the grant of every off-edge host is framed.

(C) A continuing warm ghost moving from Y to X cannot be a
FIRE row: rightLocal/cross retire the Y host, while leftLocal
makes X a leader and thus cold.  In the no-FIRE row, OLD
warmness at Y makes it an empty follower.  NEW warmness at X
makes the source an OLD follower, and C_native excludes an
OLD bullet there: an outgoing bullet would leave X cold by
grantDrainD6MergeOutgoingBulletNoFireColdEndpoints.  The
OLD nearest leader is at distance d >= 2, so the merged
grantDrainD6MovingHostEmptyFollowerRank applies, yielding
the stronger W(new,X)+1 <= W(old,Y).

No assumed rank or ghost invariant leaf is used.
-/

/-- Warmness in the new ghost is always inherited from the old
ghost, even when the physical host moves. -/
theorem grantDrainD6HostNextWarmOld
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hNext :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true) :
    label.warm = true := by
  cases hw : label.warm with
  | true => rfl
  | false =>
      have hCold :=
        grantDrainD6MergeColdLabelRemainsCold
          ring fresh update s e label hw
      rw [hCold] at hNext
      cases hNext

/-- A warm ghost at the new named host certifies that the
actual physical new host satisfies the literal warm predicate. -/
theorem grantDrainD6HostNextWarmPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e q : Fin n)
    (label : GrantDrainWarmLabel n)
    (hHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some q)
    (hWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true) :
    grantDrainWarmAt
      (grantDrainStep ring fresh update s e) q = true := by
  have hWarmEquation :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm =
      match (grantDrainWarmLabelStep ring fresh update s e
        label).host with
      | none => false
      | some g =>
          label.warm &&
            grantDrainWarmAt
              (grantDrainStep ring fresh update s e) g := by
    rfl
  rw [hWarmEquation, hHost] at hWarm
  cases hw :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) q with
  | true => rfl
  | false =>
      simp [hw] at hWarm

/-- A true source-port output in the token row is exactly the
real source's GRANT field in the corresponding physical step. -/
theorem grantDrainD6HostSourceRowIsPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hRow :
      grantDrainD6ContactRowSourceGrant ring fresh s e = true) :
    (grantDrainStep ring fresh update s e).grant e = true := by
  simpa [grantDrainStep, grantDrainD6ContactRowSourceGrant]
    using hRow

/-- A responder HOLD keeps its grant in the exact token row.
The exclusions reflect precisely the branch of the ghost
router in which the responder can remain its own host. -/
theorem grantDrainD6HostResponderHoldToken
    (rx gx ry gy lx ly fresh : Bool)
    (fire : GrantDrainFire)
    (hHold : (ry && gy) = true)
    (hNotRight : fire ≠ .rightLocal)
    (hNotCross : fire ≠ .cross)
    (hLX : lx = false)
    (hLY : ly = false) :
    (grantDrainTokenRow
      rx gx ry gy lx ly fresh fire).2.grant = true := by
  cases hry : ry with
  | false =>
      simp [hry] at hHold
  | true =>
      cases hgy : gy with
      | false =>
          simp [hry, hgy] at hHold
      | true =>
          rw [hLX, hLY]
          cases fire with
          | none =>
              cases rx <;> cases gx <;> cases fresh <;>
                (unfold grantDrainTokenRow; decide)
          | leftLocal =>
              cases rx <;> cases gx <;> cases fresh <;>
                (unfold grantDrainTokenRow; decide)
          | rightLocal =>
              exact False.elim (hNotRight rfl)
          | cross =>
              exact False.elim (hNotCross rfl)

/-- H: a ghost's warm granted-host coherence is preserved
under every actual native-plus-token physical step.  The proof
uses the two existing host-contact equations and the literal
grant frame off the serviced edge. -/
theorem grantDrainD6HostCoherentStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hCoherent : GrantDrainD6HostCoherent s label) :
    GrantDrainD6HostCoherent
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  intro q hWarmNext hHostNext
  cases hOldHost : label.host with
  | none =>
      have hNone :
          (grantDrainWarmLabelStep ring fresh update s e
            label).host = none := by
        simp [grantDrainWarmLabelStep, hOldHost]
      rw [hNone] at hHostNext
      cases hHostNext
  | some p =>
      by_cases hpX : p = e
      · subst p
        have hContact :=
          grantDrainD6ContactHostAtSource
            ring fresh update s e label hOldHost
        cases hRow :
            grantDrainD6ContactRowSourceGrant ring fresh s e with
        | false =>
            rw [hContact, hRow] at hHostNext
            cases hHostNext
        | true =>
            rw [hContact, hRow] at hHostNext
            have hEq : e = q := Option.some.inj hHostNext
            subst q
            exact grantDrainD6HostSourceRowIsPhysical
              ring fresh update s e hRow
      · by_cases hpY : p = ring.rightNeighbor e
        · subst p
          have hContact :=
            grantDrainD6ContactHostAtResponder
              ring hn fresh update s e label hOldHost
          by_cases hRetire :
              grantDrainSelect ring s e = .rightLocal ∨
              grantDrainSelect ring s e = .cross ∨
              (grantDrainNativeNext ring s e e).l = true ∨
              (grantDrainNativeNext ring s e
                (ring.rightNeighbor e)).l = true
          · rw [hContact, if_pos hRetire] at hHostNext
            cases hHostNext
          · rw [hContact, if_neg hRetire] at hHostNext
            by_cases hHold :
                (s.request (ring.rightNeighbor e) &&
                  s.grant (ring.rightNeighbor e)) = true
            · rw [if_pos hHold] at hHostNext
              have hEq : ring.rightNeighbor e = q :=
                Option.some.inj hHostNext
              subst q
              have hNotRight :
                  grantDrainSelect ring s e ≠ .rightLocal := by
                intro hf
                exact hRetire (Or.inl hf)
              have hNotCross :
                  grantDrainSelect ring s e ≠ .cross := by
                intro hf
                exact hRetire (Or.inr (Or.inl hf))
              have hLX :
                  (grantDrainNativeNext ring s e e).l =
                    false := by
                cases h : (grantDrainNativeNext ring s e e).l with
                | false => rfl
                | true =>
                    exact False.elim
                      (hRetire (Or.inr (Or.inr (Or.inl h))))
              have hLY :
                  (grantDrainNativeNext ring s e
                    (ring.rightNeighbor e)).l = false := by
                cases h :
                    (grantDrainNativeNext ring s e
                      (ring.rightNeighbor e)).l with
                | false => rfl
                | true =>
                    exact False.elim
                      (hRetire (Or.inr (Or.inr (Or.inr h))))
              have hToken :=
                grantDrainD6HostResponderHoldToken
                  (s.request e) (s.grant e)
                  (s.request (ring.rightNeighbor e))
                  (s.grant (ring.rightNeighbor e))
                  (grantDrainNativeNext ring s e e).l
                  (grantDrainNativeNext ring s e
                    (ring.rightNeighbor e)).l
                  (fresh s e) (grantDrainSelect ring s e)
                  hHold hNotRight hNotCross hLX hLY
              have hDistinct :
                  ring.rightNeighbor e ≠ e :=
                grantDrainEntranceRightNeighborDistinct
                  ring (by omega : 2 ≤ n) e
              simpa [grantDrainStep, hDistinct] using hToken
            · rw [if_neg hHold] at hHostNext
              by_cases hRow :
                  grantDrainD6ContactRowSourceGrant
                    ring fresh s e = true
              · rw [if_pos hRow] at hHostNext
                have hEq : e = q :=
                  Option.some.inj hHostNext
                subst q
                exact grantDrainD6HostSourceRowIsPhysical
                  ring fresh update s e hRow
              · rw [if_neg hRow] at hHostNext
                cases hHostNext
        · have hFixed :
              (grantDrainWarmLabelStep ring fresh update s e
                label).host = some p := by
            simp [grantDrainWarmLabelStep, hOldHost, hpX, hpY]
          have hEq : p = q :=
            Option.some.inj (hFixed.symm.trans hHostNext)
          subst q
          have hOldWarm :=
            grantDrainD6HostNextWarmOld
              ring fresh update s e label hWarmNext
          have hOldGrant :
              s.grant p = true :=
            hCoherent p hOldWarm hOldHost
          have hFrame :
              (grantDrainStep ring fresh update s e).grant p =
                s.grant p := by
            simp [grantDrainStep, hpX, hpY]
          rw [hFrame]
          exact hOldGrant

/-- A newly tracked warm label created at an actually granted
site satisfies host coherence immediately, for any budget. -/
theorem grantDrainD6HostCoherentInitial
    {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch)
    (g : Fin n) (birthBudget : Nat)
    (hGrant : s.grant g = true) :
    GrantDrainD6HostCoherent s
      (grantDrainD6MergeInitialLabel g true birthBudget) := by
  intro q _ hHost
  change some g = some q at hHost
  have hEq : g = q := Option.some.inj hHost
  rw [← hEq]
  exact hGrant

/-- In a physical move Y-to-X with the NEW host warm, the
old selector cannot have selected any FIRE.  A rightLocal
or cross fire retires Y's label; a leftLocal fire makes X
physically a leader. -/
theorem grantDrainD6MovingHostNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hHost :
      label.host = some (ring.rightNeighbor e))
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some e)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true) :
    grantDrainSelect ring s e = .none := by
  have hAtE :=
    grantDrainD6HostNextWarmPhysical
      ring fresh update s e e label hNewHost hNewWarm
  cases hf : grantDrainSelect ring s e with
  | none => rfl
  | leftLocal =>
      have hCold :=
        grantDrainD6CompositeSourceBirthEndsWarm
          ring fresh update s e (Or.inl hf)
      rw [hCold] at hAtE
      cases hAtE
  | rightLocal =>
      have hRoute :=
        grantDrainD6ContactHostAtResponder
          ring hn fresh update s e label hHost
      rw [hRoute] at hNewHost
      simp [hf] at hNewHost
  | cross =>
      have hRoute :=
        grantDrainD6ContactHostAtResponder
          ring hn fresh update s e label hHost
      rw [hRoute] at hNewHost
      simp [hf] at hNewHost

/-- If a no-FIRE edge ends with a warm source, that source was
already an OLD follower.  Literal E never deletes its initiator
leader bit. -/
theorem grantDrainD6MovingHostOldSourceFollower
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hNone : grantDrainSelect ring s e = .none)
    (hNewWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) e = true) :
    (s.native e).l = false := by
  have hNewFollower :=
    (grantDrainD6ExceptionalDeathHostFields
      (grantDrainStep ring fresh update s e) e hNewWarm).1
  have hNative :=
    grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone
  have hAfterFollower :
      (nativeE ring s.native e e).l = false := by
    rw [← hNative]
    exact hNewFollower
  have hSourceFixed :
      (nativeE ring s.native e e).l = (s.native e).l := by
    simpa [nativeE] using
      (grantDrainEntranceLiteralESourceLeaderFixed
        (s.native e) (s.native (ring.rightNeighbor e)))
  exact hSourceFixed.symm.trans hAfterFollower

/-- A continuing warm source after a no-FIRE incoming grant
cannot have carried an OLD outgoing LIVE/DUMMY.  Under C_native
such an outgoing bullet makes both endpoints cold. -/
theorem grantDrainD6MovingHostOldSourceEmpty
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hNone : grantDrainSelect ring s e = .none)
    (hYFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hYEmpty :
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hNewWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) e = true) :
    (s.native e).b = (0 : Fin 3) := by
  have hxFollower :=
    grantDrainD6MovingHostOldSourceFollower
      ring fresh update s e hNone hNewWarm
  by_cases hxEmpty : (s.native e).b = (0 : Fin 3)
  · exact hxEmpty
  · have hxQuiet :=
      grantDrainD6OutgoingBulletSourceQuiet
        ring s.native hC e hxEmpty
    have hCold :=
      grantDrainD6MergeOutgoingBulletNoFireColdEndpoints
        ring hn fresh update s e hxFollower hxEmpty
        hxQuiet hYFollower hYEmpty hNone
    rw [hCold.1] at hNewWarm
    cases hNewWarm

/-- C: the actual Y-to-X grant move is necessarily the
empty-follower, no-FIRE, old-distance-at-least-two row.
The rank drops by at least one; no E-transport hypothesis
has been assumed. -/
theorem grantDrainD6MovingHostRankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hHost :
      label.host = some (ring.rightNeighbor e))
    (hWarm :
      grantDrainWarmAt s (ring.rightNeighbor e) = true)
    (hGrant :
      s.grant (ring.rightNeighbor e) = true)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some e)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true) :
    grantDrainWarmRank ring
      (grantDrainStep ring fresh update s e).native e ≤
    grantDrainWarmRank ring s.native
      (ring.rightNeighbor e) := by
  have hNone :=
    grantDrainD6MovingHostNoFire
      ring hn fresh update s e label
      hHost hNewHost hNewWarm
  have hAtE :=
    grantDrainD6HostNextWarmPhysical
      ring fresh update s e e label hNewHost hNewWarm
  have hOldY :=
    grantDrainD6ExceptionalDeathHostFields
      s (ring.rightNeighbor e) hWarm
  have hUnheld :
      s.request (ring.rightNeighbor e) = false := by
    cases hr : s.request (ring.rightNeighbor e) with
    | false => rfl
    | true =>
        simp [grantDrainWarmAt, hr] at hWarm
  have hxFollower :=
    grantDrainD6MovingHostOldSourceFollower
      ring fresh update s e hNone hAtE
  have hxEmpty :=
    grantDrainD6MovingHostOldSourceEmpty
      ring hn fresh update s e hC hNone
      hOldY.1 hOldY.2.1 hAtE
  have hDist :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s (ring.rightNeighbor e) hC hWarm
  have hNotOne :
      grantDrainLeftLeaderDistance ring s.native
        (ring.rightNeighbor e) ≠ 1 := by
    intro hOne
    have hFront :=
      grantDrainD6OldWarmFrontLeader
        ring hn s (ring.rightNeighbor e) hC hWarm
    rw [hOne, grantDrainWarmRightNeighborLeftOne
      ring hn e, hxFollower] at hFront
    cases hFront
  have hDistanceTwo :
      2 ≤ grantDrainLeftLeaderDistance ring s.native
        (ring.rightNeighbor e) := by
    omega
  have hRank :=
    grantDrainD6MovingHostEmptyFollowerRank
      ring hn fresh update s e label
      (grantDrainLeftLeaderDistance ring s.native
        (ring.rightNeighbor e))
      hHost hUnheld hGrant hWarm rfl
      hDistanceTwo hDist.2
      hxFollower hxEmpty hOldY.1 hOldY.2.1 hNone
  exact Nat.le_trans (Nat.le_succ _) hRank.2

/-- The stronger inequality explicitly exposes the progress
that was used internally in the moving-host rebase. -/
theorem grantDrainD6MovingHostRankStrict
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hHost :
      label.host = some (ring.rightNeighbor e))
    (hWarm :
      grantDrainWarmAt s (ring.rightNeighbor e) = true)
    (hGrant :
      s.grant (ring.rightNeighbor e) = true)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some e)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true) :
    grantDrainWarmRank ring
      (grantDrainStep ring fresh update s e).native e + 1 ≤
    grantDrainWarmRank ring s.native
      (ring.rightNeighbor e) := by
  have hNone :=
    grantDrainD6MovingHostNoFire
      ring hn fresh update s e label
      hHost hNewHost hNewWarm
  have hAtE :=
    grantDrainD6HostNextWarmPhysical
      ring fresh update s e e label hNewHost hNewWarm
  have hOldY :=
    grantDrainD6ExceptionalDeathHostFields
      s (ring.rightNeighbor e) hWarm
  have hUnheld :
      s.request (ring.rightNeighbor e) = false := by
    cases hr : s.request (ring.rightNeighbor e) with
    | false => rfl
    | true =>
        simp [grantDrainWarmAt, hr] at hWarm
  have hxFollower :=
    grantDrainD6MovingHostOldSourceFollower
      ring fresh update s e hNone hAtE
  have hxEmpty :=
    grantDrainD6MovingHostOldSourceEmpty
      ring hn fresh update s e hC hNone
      hOldY.1 hOldY.2.1 hAtE
  have hDist :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s (ring.rightNeighbor e) hC hWarm
  have hNotOne :
      grantDrainLeftLeaderDistance ring s.native
        (ring.rightNeighbor e) ≠ 1 := by
    intro hOne
    have hFront :=
      grantDrainD6OldWarmFrontLeader
        ring hn s (ring.rightNeighbor e) hC hWarm
    rw [hOne, grantDrainWarmRightNeighborLeftOne
      ring hn e, hxFollower] at hFront
    cases hFront
  have hDistanceTwo :
      2 ≤ grantDrainLeftLeaderDistance ring s.native
        (ring.rightNeighbor e) := by
    omega
  exact (grantDrainD6MovingHostEmptyFollowerRank
    ring hn fresh update s e label
    (grantDrainLeftLeaderDistance ring s.native
      (ring.rightNeighbor e))
    hHost hUnheld hGrant hWarm rfl
    hDistanceTwo hDist.2
    hxFollower hxEmpty hOldY.1 hOldY.2.1 hNone).2

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6HostNextWarmOld
#print axioms L3.GrantDrainEntrance.grantDrainD6HostNextWarmPhysical
#print axioms L3.GrantDrainEntrance.grantDrainD6HostSourceRowIsPhysical
#print axioms L3.GrantDrainEntrance.grantDrainD6HostResponderHoldToken
#print axioms L3.GrantDrainEntrance.grantDrainD6HostCoherentStep
#print axioms L3.GrantDrainEntrance.grantDrainD6HostCoherentInitial
#print axioms L3.GrantDrainEntrance.grantDrainD6MovingHostNoFire
#print axioms L3.GrantDrainEntrance.grantDrainD6MovingHostOldSourceFollower
#print axioms L3.GrantDrainEntrance.grantDrainD6MovingHostOldSourceEmpty
#print axioms L3.GrantDrainEntrance.grantDrainD6MovingHostRankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6MovingHostRankStrict

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- The counterclockwise coordinate of an interior sector point. -/
theorem grantDrainD6FireFrontCoordinatePub
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


/-- The old warm source is an empty signal-one follower.  Against
a leader it is unchanged by literal E, including the signal:
the leader's presence copies signal one back to the source. -/
theorem grantDrainD6ReadyHostSourcePairFixed
    (x y : CertNative)
    (hxFollower : x.l = false)
    (hxEmpty : x.b = (0 : Fin 3))
    (hxSignal : x.sg = true)
    (hyLeader : y.l = true) :
    (certLiteralEPair x y).1 = x := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  simp only [CertNative.l, CertNative.b, CertNative.sg] at hxFollower hxEmpty hxSignal hyLeader
  subst xl
  subst xb
  subst xsg
  subst yl
  cases ysg <;> simp [certLiteralEPair, certFinThree]

/-- No-FIRE ready-responder at the warm source/host.
The source e is *not* assumed away from the scan.  If the ready
responder is not the old front, the entire inclusive old scan
is unchanged (including offset zero).  If it is the old front,
its emitted DUMMY becomes the first bullet at distance a, and
the warm rank falls from a+1 to a. -/
theorem grantDrainD6NoFireReadyResponderAtHostERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s e = true)
    (hxFollower : (s.native e).l = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) e ≤
      grantDrainWarmRank ring s.native e := by
  have hOldFields :=
    grantDrainD6ExceptionalDeathHostFields s e hWarm
  have hSourceFixed :
      nativeE ring s.native e e = s.native e := by
    simpa [nativeE] using
      (grantDrainD6ReadyHostSourcePairFixed
        (s.native e) (s.native (ring.rightNeighbor e))
        hxFollower hxEmpty hOldFields.2.2 hyLeader)
  have hDistinct :
      ring.rightNeighbor e ≠ e :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hResponderFixed :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        (s.native (ring.rightNeighbor e)).l := by
    have hPair :
        (certLiteralEPair
          (s.native e) (s.native (ring.rightNeighbor e))).2.l =
          (s.native (ring.rightNeighbor e)).l := by
      simp [certLiteralEPair, hxFollower, hxEmpty, hyLeader]
    simpa [nativeE, hDistinct] using hPair
  have hLeaders :=
    grantDrainEntranceNativeELeadersFixed
      ring (by omega : 2 ≤ n) s.native e hResponderFixed
  have hDistanceShort :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s e hC hWarm
  have hOldFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native e
      (grantDrainLeftLeaderDistance ring s.native e)
      hDistanceShort.1 hDistanceShort.2).mp rfl
  have hNewDistance :
      grantDrainLeftLeaderDistance
        ring (nativeE ring s.native e) e =
      grantDrainLeftLeaderDistance ring s.native e := by
    simp [grantDrainLeftLeaderDistance, hLeaders]
  by_cases hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring e
          (grantDrainLeftLeaderDistance ring s.native e)
  · obtain ⟨p, D, a, hSector, haInside, hAt⟩ :=
      grantDrainEntranceSectorCoverOfRoot
        ring s.native hC.1.1.1 e
    have hDistance :=
      grantDrainD6OutgoingBulletSectorDistance
        ring s.native e p D a hSector haInside hAt hxFollower
    have hFrontSite :
        PPL.shiftLeft ring e a.val = p :=
      grantDrainD6FireFrontCoordinatePub ring p e a.val
        a.isLt hAt
    have hTo : ring.rightNeighbor e = p := by
      rw [hDistance.2] at hFront
      exact hFront.trans hFrontSite
    have hReadyP : (s.native p).sg = true := by
      rw [← hTo]
      exact hyReady
    have hReadyPrefix :=
      grantDrainD6ReadyResponderWarmPrefix
        ring s.native p e D a.val hC hSector
        hDistance.1 haInside hAt hReadyP
    have hOldNoBullet :
        grantDrainLeftBulletDistance ring s.native e
          a.val = none := by
      apply (grantDrainWarmBulletNoneCharacterization
        ring s.native e a.val).mpr
      intro j _ hj
      rw [hReadyPrefix.2 j hj]
      rfl
    have hNewDistanceAt :
        grantDrainLeftLeaderDistance
          ring (nativeE ring s.native e) e = a.val := by
      rw [hNewDistance]
      exact hDistance.2
    have hNewPBullet :
        (nativeE ring s.native e p).b = (1 : Fin 3) := by
      rw [← hTo]
      exact grantDrainEntranceNativeEReadyVictimBulletDummy
        ring (by omega : 2 ≤ n) s.native e hyLeader hyReady
    have hPositiveFrame :
        ∀ j : Nat, 1 ≤ j → j < a.val →
          nativeE ring s.native e
            (PPL.shiftLeft ring e j) =
          s.native (PPL.shiftLeft ring e j) := by
      intro j hj hja
      have hNotE :=
        grantDrainD6DeathSourceOutsidePositive
          ring hn e p e a.val a.isLt hAt hTo
          j hj (by omega)
      have hNotP : PPL.shiftLeft ring e j ≠ p := by
        intro hEq
        have hjBefore :
            j < grantDrainLeftLeaderDistance ring s.native e := by
          rw [hDistance.2]
          exact hja
        have hOldFollower :=
          hOldFirst.2 j hj hjBefore
        rw [hEq, hSector.2.1] at hOldFollower
        cases hOldFollower
      exact grantDrainEntranceNativeEFrame
        ring s.native e (PPL.shiftLeft ring e j) hNotE
        (by rw [hTo]; exact hNotP)
    have hNewFirstBullet :
        grantDrainLeftBulletDistance
          ring (nativeE ring s.native e) e a.val =
            some a.val := by
      apply (grantDrainWarmBulletSomeCharacterization
        ring (nativeE ring s.native e) e
        a.val a.val).mpr
      refine ⟨hDistance.1, Nat.le_refl _, ?_, ?_⟩
      · rw [hFrontSite, hNewPBullet]
        decide
      · intro j hj hja
        rw [hPositiveFrame j hj hja,
          hReadyPrefix.2 j (by omega)]
        rfl
    have hNewSignalPrefix :
        ∀ j : Nat, j < a.val →
          (nativeE ring s.native e
            (PPL.shiftLeft ring e j)).sg = true := by
      intro j hj
      by_cases hjZero : j = 0
      · subst j
        rw [grantDrainWarmShiftLeftZero, hSourceFixed]
        exact hOldFields.2.2
      · rw [hPositiveFrame j (by omega) hj]
        exact hReadyPrefix.1 j hj
    have hNewHead :
        (nativeE ring s.native e e).sg = true := by
      rw [hSourceFixed]
      exact hOldFields.2.2
    have hNewTerminal :
        grantDrainTerminalRun
          ring (nativeE ring s.native e) e a.val =
            a.val - 1 := by
      apply (grantDrainWarmTerminalCharacterization
        ring (nativeE ring s.native e) e
        a.val (a.val - 1) hDistance.1 hNewHead).mpr
      refine ⟨by omega, ?_, Or.inl (by omega)⟩
      intro j hj
      exact hNewSignalPrefix j (by omega)
    have hOldRank :
        grantDrainWarmRank ring s.native e = 1 + a.val := by
      simp [grantDrainWarmRank, hDistance.2,
        hOldNoBullet, hFrontSite, hReadyP]
    have hNewRank :
        grantDrainWarmRank ring (nativeE ring s.native e) e =
          a.val := by
      simp [grantDrainWarmRank, hNewDistanceAt,
        hNewFirstBullet, hNewTerminal] <;> omega
    rw [hOldRank, hNewRank]
    omega
  · have hNoResponder :
        ∀ j : Nat,
          j ≤ grantDrainLeftLeaderDistance ring s.native e →
          PPL.shiftLeft ring e j ≠ ring.rightNeighbor e := by
      intro j hj hEq
      by_cases hjZero : j = 0
      · subst j
        rw [grantDrainWarmShiftLeftZero] at hEq
        exact hDistinct hEq.symm
      · by_cases hjAt :
            j = grantDrainLeftLeaderDistance ring s.native e
        · rw [hjAt] at hEq
          exact hFront hEq.symm
        · have hBefore :
              j < grantDrainLeftLeaderDistance ring s.native e := by
            omega
          have hFollowerAt := hOldFirst.2 j (by omega) hBefore
          rw [hEq, hyLeader] at hFollowerAt
          cases hFollowerAt
    have hScanFrame :
        ∀ j : Nat,
          j ≤ grantDrainLeftLeaderDistance ring s.native e →
          nativeE ring s.native e
            (PPL.shiftLeft ring e j) =
            s.native (PPL.shiftLeft ring e j) := by
      intro j hj
      by_cases hjZero : j = 0
      · subst j
        simpa only [grantDrainWarmShiftLeftZero] using hSourceFixed
      · have hNotSource :
            PPL.shiftLeft ring e j ≠ e := by
          intro hEq
          have hDifferent :=
            grantDrainD6BirthLeftOffsetsDistinct
              ring e j 0 (by omega : j < n)
              (by omega : 0 < n) (by omega)
          apply hDifferent
          simpa only [grantDrainWarmShiftLeftZero] using hEq
        exact grantDrainEntranceNativeEFrame
          ring s.native e (PPL.shiftLeft ring e j)
          hNotSource (hNoResponder j hj)
    exact Nat.le_of_eq
      (grantDrainWarmFullScanFrame
        ring s.native (nativeE ring s.native e) e
        hScanFrame).2.2.2

/-- A source leader that is quiet and bullet-free serving a follower
only expands signals; leaders and bullets remain pointwise fixed.
This is a source-leader subrow, not the unrestricted source-leader
theorem. -/
theorem grantDrainD6NoFireSourceLeaderQuietEmptyFollowerERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hxLeader : (s.native e).l = true)
    (hxQuiet : (s.native e).sg = false)
    (hxEmpty : (s.native e).b = (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hRows :=
    grantDrainEntranceQuietEmptySourceNativeERows
      ring (by omega : 2 ≤ n) s.native e
      (Or.inr hxQuiet) hxEmpty hyFollower
  have hSignals :
      ∀ i : Fin n,
        (s.native i).sg = true →
          (nativeE ring s.native e i).sg = true := by
    intro i hi
    by_cases he : i = e
    · subst i
      rw [hxQuiet] at hi
      cases hi
    · by_cases hy : i = ring.rightNeighbor e
      · subst i
        rw [hRows.2.2]
        exact hi
      · rw [grantDrainEntranceNativeEFrame
          ring s.native e i he hy]
        exact hi
  exact grantDrainD6WarmSignalExpansionRank
    ring hn s.native (nativeE ring s.native e) g
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).2.2
    (fun i => (hRows.1 i).1)
    (fun i => (hRows.1 i).2)
    hSignals

/-- All no-FIRE cases with an old FOLLOWER source are closed:
outgoing bullet, empty/nonready pair, ready responder away from
the host, and ready responder at the host (above). -/
theorem grantDrainD6NoFireFollowerERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNone : grantDrainSelect ring s e = .none)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxFollower : (s.native e).l = false) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  by_cases hxEmpty : (s.native e).b = (0 : Fin 3)
  · cases hyLeader : (s.native (ring.rightNeighbor e)).l with
    | false =>
        exact grantDrainD6EmptyFollowerNotReadyResponderERankLe
          ring hn s e g hC hWarm hxFollower hxEmpty
          (Or.inl hyLeader)
    | true =>
        cases hyReady :
            (s.native (ring.rightNeighbor e)).sg with
        | false =>
            exact grantDrainD6EmptyFollowerNotReadyResponderERankLe
              ring hn s e g hC hWarm hxFollower hxEmpty
              (Or.inr hyReady)
        | true =>
            by_cases hAt : g = e
            · subst g
              exact grantDrainD6NoFireReadyResponderAtHostERankLe
                ring hn s e hC hWarm hxFollower hxEmpty
                hyLeader hyReady
            · exact grantDrainD6ReadyResponderAwayERankLe
                ring hn s e g hC hWarm
                hxFollower hxEmpty hyLeader hyReady hAt
  · exact grantDrainD6NoFireOutgoingBulletERankLe
      ring hn fresh update s e g hC hWarm hNone
      hNonExceptional hStillWarm hxFollower hxEmpty

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyHostSourcePairFixed
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireReadyResponderAtHostERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderQuietEmptyFollowerERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireFollowerERankLe

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- Reused independently of the selected-FIRE hypothesis. -/
theorem grantDrainD6NoFireSourceLeaderReadyFrontERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxLeader : (s.native e).l = true)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hOldFields :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hDistanceShort :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hDistanceShort.1 hDistanceShort.2).mp rfl
  have hNoSource :=
    grantDrainD6SourceLeaderLeaderNoSourceInScan
      ring hn s e g hC hWarm hxLeader hyLeader
  obtain ⟨p, D, a, hSector, haInside, hAt⟩ :=
    grantDrainEntranceSectorCoverOfRoot
      ring s.native hC.1.1.1 g
  have hDistance :=
    grantDrainD6OutgoingBulletSectorDistance
      ring s.native g p D a hSector haInside hAt
      hOldFields.1
  have hFrontSite :
      PPL.shiftLeft ring g a.val = p := by
    rw [hAt, grantDrainMarksArcShiftLeftRight
      ring p a.val a.val (Nat.le_refl _) a.isLt,
      Nat.sub_self, grantDrainWeakDeathShiftRightZero ring p]
  have hTo : ring.rightNeighbor e = p := by
    calc
      ring.rightNeighbor e =
          PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g) := hFront
      _ = PPL.shiftLeft ring g a.val := by rw [hDistance.2]
      _ = p := hFrontSite
  have hReadyP : (s.native p).sg = true := by
    rw [← hTo]
    exact hyReady
  have hReadyPrefix :=
    grantDrainD6ReadyResponderWarmPrefix
      ring s.native p g D a.val hC hSector
      hDistance.1 haInside hAt hReadyP
  have hOldNoBullet :
      grantDrainLeftBulletDistance
        ring s.native g a.val = none := by
    apply (grantDrainWarmBulletNoneCharacterization
      ring s.native g a.val).mpr
    intro j _ hj
    rw [hReadyPrefix.2 j hj]
    rfl
  have hFrame :
      ∀ j : Nat,
        j < grantDrainLeftLeaderDistance ring s.native g →
        nativeE ring s.native e
          (PPL.shiftLeft ring g j) =
          s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    have hNotE := hNoSource j (by omega)
    have hNotY :
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
      intro heq
      by_cases hjZero : j = 0
      · subst j
        rw [grantDrainWarmShiftLeftZero] at heq
        have hBad : (s.native g).l = true := by
          rw [heq]
          exact hyLeader
        rw [hOldFields.1] at hBad
        cases hBad
      · have hBad := hFirst.2 j (by omega) hj
        rw [heq, hyLeader] at hBad
        cases hBad
    exact grantDrainEntranceNativeEFrame
      ring s.native e (PPL.shiftLeft ring g j)
      hNotE hNotY
  have hNewDistanceLower :
      grantDrainLeftLeaderDistance ring s.native g ≤
        grantDrainLeftLeaderDistance
          ring (nativeE ring s.native e) g := by
    apply grantDrainD6DeathLeaderPrefixLowerBound
      ring (nativeE ring s.native e) g
      (grantDrainLeftLeaderDistance ring s.native g)
      (by omega)
    intro j hj hjBefore
    rw [hFrame j hjBefore]
    exact hFirst.2 j hj hjBefore
  have hNewPBullet :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (1 : Fin 3) :=
    grantDrainEntranceNativeEReadyVictimBulletDummy
      ring (by omega : 2 ≤ n) s.native e hyLeader hyReady
  have hNewPQuiet :
      (nativeE ring s.native e (ring.rightNeighbor e)).sg =
        false :=
    (grantDrainEntranceNativeELeaderBulletAfter
      ring (by omega : 2 ≤ n) s.native e hyLeader).2
  have hNewBullet :
      grantDrainLeftBulletDistance
        ring (nativeE ring s.native e) g
        (grantDrainLeftLeaderDistance
          ring (nativeE ring s.native e) g) =
        some (grantDrainLeftLeaderDistance ring s.native g) := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring (nativeE ring s.native e) g
      (grantDrainLeftLeaderDistance
        ring (nativeE ring s.native e) g)
      (grantDrainLeftLeaderDistance ring s.native g)).mpr
    refine ⟨hDistanceShort.1, hNewDistanceLower, ?_, ?_⟩
    · rw [← hFront, hNewPBullet]
      decide
    · intro j hj hjBefore
      rw [hFrame j hjBefore]
      have hjA : j < a.val := by
        rw [← hDistance.2]
        exact hjBefore
      rw [hReadyPrefix.2 j (by omega)]
      rfl
  have hNewSignalPrefix :
      ∀ j : Nat,
        j < grantDrainLeftLeaderDistance ring s.native g →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).sg = true := by
    intro j hj
    rw [hFrame j hj]
    have hjA : j < a.val := by
      rw [← hDistance.2]
      exact hj
    exact hReadyPrefix.1 j hjA
  have hNewGSignal :
      (nativeE ring s.native e g).sg = true := by
    have hHead := hNewSignalPrefix 0 (by omega)
    rw [grantDrainWarmShiftLeftZero] at hHead
    exact hHead
  have hNewTerminal :
      grantDrainTerminalRun ring
        (nativeE ring s.native e) g
        (grantDrainLeftLeaderDistance
          ring (nativeE ring s.native e) g) =
        grantDrainLeftLeaderDistance ring s.native g - 1 := by
    apply (grantDrainWarmTerminalCharacterization
      ring (nativeE ring s.native e) g
      (grantDrainLeftLeaderDistance
        ring (nativeE ring s.native e) g)
      (grantDrainLeftLeaderDistance ring s.native g - 1)
      (by omega) hNewGSignal).mpr
    refine ⟨by omega, ?_, Or.inr ?_⟩
    · intro j hj
      exact hNewSignalPrefix j (by omega)
    · have hIndex :
          grantDrainLeftLeaderDistance ring s.native g - 1 + 1 =
          grantDrainLeftLeaderDistance ring s.native g := by
        omega
      rw [hIndex, ← hFront]
      exact hNewPQuiet
  have hOldRank :
      grantDrainWarmRank ring s.native g =
        1 + grantDrainLeftLeaderDistance ring s.native g := by
    simp [grantDrainWarmRank, hDistance.2, hOldNoBullet,
      hFrontSite, hReadyP]
  have hNewRank :
      grantDrainWarmRank ring (nativeE ring s.native e) g =
        grantDrainLeftLeaderDistance ring s.native g := by
    simp [grantDrainWarmRank, hNewBullet, hNewTerminal] <;>
      omega
  rw [hOldRank, hNewRank]
  omega

/-- Reused independently of the selected-FIRE hypothesis. -/
theorem grantDrainD6NoFireQuietLeaderResponderSurvivorPair
    (x y : CertNative)
    (hyLeader : y.l = true)
    (hyQuiet : y.sg = false)
    (hAlive : (certLiteralEPair x y).2.l = true) :
    (certLiteralEPair x y).2 = y := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  change yl = true at hyLeader
  change ysg = false at hyQuiet
  subst yl
  subst ysg
  rcases grantDrainEntranceLocalFinThreeCases xb with hb | hb | hb <;>
    subst xb <;>
    cases xl <;> cases xsg <;> cases ysh <;>
    simp [certLiteralEPair, certFinThree] at hAlive ⊢

/-- Reused independently of the selected-FIRE hypothesis. -/
theorem grantDrainD6NoFireSourceLeaderQuietSurvivorERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxLeader : (s.native e).l = true)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyQuiet :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))
    (hAlive :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hNoSource :=
    grantDrainD6SourceLeaderLeaderNoSourceInScan
      ring hn s e g hC hWarm hxLeader hyLeader
  have hOldHost :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hShort :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hOldFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hShort.1 hShort.2).mp rfl
  have hPrefix :
      ∀ j : Nat,
        j < grantDrainLeftLeaderDistance ring s.native g →
        nativeE ring s.native e
          (PPL.shiftLeft ring g j) =
          s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    have hNotE := hNoSource j (by omega)
    have hNotY :
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
      intro hEq
      by_cases hjZero : j = 0
      · subst j
        rw [grantDrainWarmShiftLeftZero] at hEq
        have hBad : (s.native g).l = true := by
          rw [hEq]
          exact hyLeader
        rw [hOldHost.1] at hBad
        cases hBad
      · have hBad := hOldFirst.2 j (by omega) hj
        rw [hEq, hyLeader] at hBad
        cases hBad
    exact grantDrainEntranceNativeEFrame
      ring s.native e (PPL.shiftLeft ring g j)
      hNotE hNotY
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hAlivePair :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.l = true := by
    simpa [nativeE, hDistinct] using hAlive
  have hPair :=
    grantDrainD6NoFireQuietLeaderResponderSurvivorPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hyLeader hyQuiet hAlivePair
  have hYFixed :
      nativeE ring s.native e (ring.rightNeighbor e) =
        s.native (ring.rightNeighbor e) := by
    simpa [nativeE, hDistinct] using hPair
  have hFull :
      ∀ j : Nat,
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
        nativeE ring s.native e
          (PPL.shiftLeft ring g j) =
          s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    by_cases hjBefore :
        j < grantDrainLeftLeaderDistance ring s.native g
    · exact hPrefix j hjBefore
    · have hjAt :
          j = grantDrainLeftLeaderDistance ring s.native g := by
        omega
      rw [hjAt, ← hFront]
      exact hYFixed
  exact Nat.le_of_eq
    (grantDrainWarmFullScanFrame
      ring s.native (nativeE ring s.native e) g
      hFull).2.2.2

/-- Reused independently of the selected-FIRE hypothesis. -/
theorem grantDrainD6NoFireSourceLeaderQuietDeathFrontERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hxLeader : (s.native e).l = true)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hyQuiet :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hFront :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))
    (hDead :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = false) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPairDead :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.l = false := by
    simpa [nativeE, hDistinct] using hDead
  have hReason :=
    (grantDrainEntranceLiteralELeaderDeathCases
      (s.native e) (s.native (ring.rightNeighbor e))
      hyLeader).mp hPairDead
  have hyOpen :
      (s.native (ring.rightNeighbor e)).sh = false := by
    rcases hReason.2 with hReady | hOpen
    · rw [hyQuiet] at hReady
      cases hReady
    · exact hOpen
  have hHost :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hDistance :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hDistance.1 hDistance.2).mp rfl
  have hNoSource :=
    grantDrainD6SourceLeaderLeaderNoSourceInScan
      ring hn s e g hC hWarm hxLeader hyLeader
  have hFrame :
      ∀ j : Nat,
        j < grantDrainLeftLeaderDistance ring s.native g →
        nativeE ring s.native e
          (PPL.shiftLeft ring g j) =
        s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    have hNoResponder :
        PPL.shiftLeft ring g j ≠
          ring.rightNeighbor e := by
      by_cases hjZero : j = 0
      · subst j
        rw [grantDrainWarmShiftLeftZero]
        intro hEq
        have hBad : (s.native g).l = true := by
          rw [hEq]
          exact hyLeader
        rw [hHost.1] at hBad
        cases hBad
      · intro hEq
        have hOldFollower := hFirst.2 j (by omega) hj
        rw [hEq, hyLeader] at hOldFollower
        cases hOldFollower
    exact grantDrainEntranceNativeEFrame
      ring s.native e _
      (hNoSource j (by omega)) hNoResponder
  have hAfter :=
    grantDrainEntranceNativeELeaderBulletAfter
      ring (by omega : 2 ≤ n) s.native e hyLeader
  have hResponderBullet :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).b =
        (s.native (ring.rightNeighbor e)).b := by
    simpa [hyQuiet] using hAfter.1
  have hNewDistance :
      grantDrainLeftLeaderDistance ring s.native g ≤
        grantDrainLeftLeaderDistance
          ring (nativeE ring s.native e) g := by
    apply grantDrainD6DeathLeaderPrefixLowerBound
      ring (nativeE ring s.native e) g
      (grantDrainLeftLeaderDistance ring s.native g)
      (by omega)
    intro j hj hjBefore
    rw [hFrame j hjBefore]
    exact hFirst.2 j hj hjBefore
  have hBulletPrefix :
      ∀ j : Nat, 1 ≤ j →
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).b.val =
        (s.native (PPL.shiftLeft ring g j)).b.val := by
    intro j _ hjLe
    by_cases hjBefore :
        j < grantDrainLeftLeaderDistance ring s.native g
    · rw [hFrame j hjBefore]
    · have hjAt :
          j = grantDrainLeftLeaderDistance ring s.native g := by
        omega
      rw [hjAt, ← hFront, hResponderBullet]
  have hSignalPrefix :
      ∀ j : Nat,
        j < grantDrainLeftLeaderDistance ring s.native g →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).sg =
        (s.native (PPL.shiftLeft ring g j)).sg := by
    intro j hj
    exact congrArg CertNative.sg (hFrame j hj)
  have hNewFrontQuiet :
      (nativeE ring s.native e
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))).sg =
        false := by
    rw [← hFront]
    exact hAfter.2
  cases hBullet :
      grantDrainLeftBulletDistance ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) with
  | none =>
      have hFrontLeader :
          (s.native (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g))).l =
            true := by
        rw [← hFront]
        exact hyLeader
      have hFrontShield :
          (s.native (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g))).sh =
            false := by
        rw [← hFront]
        exact hyOpen
      have hFrontSignal :
          (s.native (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g))).sg =
            false := by
        rw [← hFront]
        exact hyQuiet
      have hSurvive :=
        grantDrainD6NonExceptionalQuietFrontSurvivesE
          ring s e g hNonExceptional hFrontLeader
          hFrontShield hFrontSignal hBullet
      rw [← hFront, hDead] at hSurvive
      cases hSurvive
  | some k =>
      exact Nat.le_of_eq
        (grantDrainD6DeathBulletRankPrefix
          ring s.native (nativeE ring s.native e) g
          (grantDrainLeftLeaderDistance ring s.native g)
          k hDistance.1 rfl hNewDistance hBullet
          hHost.2.2 hSignalPrefix hBulletPrefix
          hNewFrontQuiet).2.2

/-- Reused independently of the selected-FIRE hypothesis. -/
theorem grantDrainD6NoFireSourceLeaderLeaderERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hxLeader : (s.native e).l = true)
    (hyLeader :
      (s.native (ring.rightNeighbor e)).l = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  rcases grantDrainD6SourceLeaderLeaderOutsideOrFront
      ring hn s e g hC hWarm hxLeader hyLeader with
    hOutside | hFront
  · exact Nat.le_of_eq
      (grantDrainD6EScanOutsidePair
        ring s.native e g hOutside)
  · cases hyReady :
        (s.native (ring.rightNeighbor e)).sg with
    | true =>
        exact grantDrainD6NoFireSourceLeaderReadyFrontERankLe
          ring hn s e g hC hWarm
          hxLeader hyLeader hyReady hFront
    | false =>
        cases hAlive :
            (nativeE ring s.native e
              (ring.rightNeighbor e)).l with
        | true =>
            exact grantDrainD6NoFireSourceLeaderQuietSurvivorERankLe
              ring hn s e g hC hWarm
              hxLeader hyLeader hyReady hFront hAlive
        | false =>
            exact grantDrainD6NoFireSourceLeaderQuietDeathFrontERankLe
              ring hn s e g hC hWarm hNonExceptional
              hxLeader hyLeader hyReady hFront hAlive

/-- Reused independently of the selected-FIRE hypothesis. -/
theorem grantDrainD6NoFireReadySourcePair
    (x y : CertNative)
    (hXL : x.l = true) (hXS : x.sg = true)
    (hYL : y.l = false) (hYB : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.l = x.l ∧
    (certLiteralEPair x y).2.l = y.l ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, hXL, hXS, hYL, hYB, certFinThree]

/-- Reused independently of the selected-FIRE hypothesis. -/
theorem grantDrainD6NoFireSourceLeaderReadySectorStrict
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hSector : sectorLength ring s.native e D)
    (hAt : g = PPL.shiftRight ring e a)
    (ha : 2 ≤ a) (haInside : a < D.val)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = a)
    (hReady : (s.native e).sg = true)
    (hTo : ring.rightNeighbor e =
      PPL.shiftLeft ring g (a - 1))
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have haN : a < n := by
    have hD := D.isLt
    omega
  have hFront :
      PPL.shiftLeft ring g a = e := by
    rw [hAt, grantDrainMarksArcShiftLeftRight
      ring e a a (Nat.le_refl _) haN,
      Nat.sub_self, grantDrainWeakDeathShiftRightZero ring e]
  have hReadyArc :=
    grantDrainD6ReadyResponderWarmPrefix ring s.native e g D a
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
    have hOldFirst :=
      (grantDrainWarmLeaderFirstCharacterization
        ring s.native g a (by omega) haN).mp hDistance
    exact hOldFirst.2 (a - 1) (by omega) (by omega)
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
    grantDrainD6NoFireReadySourcePair
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
        have hNe := grantDrainEntranceRightNeighborDistinct
          ring (by omega : 2 ≤ n) e
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
      exact (grantDrainD6BirthLeftOffsetsDistinct
        ring g j a hjN haN (by omega)) heq
    have hNY :
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
      rw [hTo]
      intro heq
      exact (grantDrainD6BirthLeftOffsetsDistinct
        ring g j (a - 1) hjN (by omega) (by omega)) heq
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
    have hNe := grantDrainEntranceRightNeighborDistinct
          ring (by omega : 2 ≤ n) e
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
  rw [hNewRank, hOldRank]
  omega

/-- Reused independently of the selected-FIRE hypothesis. -/
theorem grantDrainD6NoFireSourceLeaderReadySectorERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hSector : sectorLength ring s.native e D)
    (hAt : g = PPL.shiftRight ring e a)
    (ha : 2 ≤ a) (haInside : a < D.val)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = a)
    (hReady : (s.native e).sg = true)
    (hTo : ring.rightNeighbor e =
      PPL.shiftLeft ring g (a - 1))
    (hNone : grantDrainSelect ring s e = .none) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  have hStrict :=
    grantDrainD6NoFireSourceLeaderReadySectorStrict
      ring hn fresh update s e g D a hC hWarm hSector
      hAt ha haInside hDistance hReady hTo hNone
  rw [grantDrainWarmPhysicalNoBirthNative
    ring fresh update s e hNone] at hStrict
  omega


/-- Successor is injective: shifting it left by one recovers its source. -/
theorem grantDrainD6NoFireRightNeighborInjective
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (x y : Fin n)
    (h : ring.rightNeighbor x = ring.rightNeighbor y) :
    x = y := by
  have hx := grantDrainWarmRightNeighborLeftOne ring hn x
  have hy := grantDrainWarmRightNeighborLeftOne ring hn y
  rw [h] at hx
  exact hx.symm.trans hy

/-- The responder of an OLD leader source can enter the
inclusive backward warm scan only immediately after the OLD
front. This includes offset-zero and wraparound cases. -/
theorem grantDrainD6NoFireSourceLeaderFollowerResponderScanFront
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxLeader : (s.native e).l = true)
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (j : Nat)
    (hj : j ≤ grantDrainLeftLeaderDistance ring s.native g)
    (hHit : PPL.shiftLeft ring g j = ring.rightNeighbor e) :
    e = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g) := by
  have hShort :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hShort.1 hShort.2).mp rfl
  have hjBefore :
      j < grantDrainLeftLeaderDistance ring s.native g := by
    by_cases hjEnd :
        j = grantDrainLeftLeaderDistance ring s.native g
    · have hL : (s.native (ring.rightNeighbor e)).l = true := by
        rw [← hHit, hjEnd]
        exact hFirst.1
      rw [hL] at hyFollower
      cases hyFollower
    · omega
  have hjNextPos : 1 ≤ j + 1 := by omega
  have hjNextShort : j + 1 < n := by omega
  have hNeighbor :=
    grantDrainD6OutgoingBulletSuccessorAtOffset
      ring g (PPL.shiftLeft ring g (j + 1)) (j + 1)
      hjNextPos hjNextShort rfl
  have hSubtract : j + 1 - 1 = j := by omega
  rw [hSubtract] at hNeighbor
  have hEqualNeighbor :
      ring.rightNeighbor (PPL.shiftLeft ring g (j + 1)) =
        ring.rightNeighbor e :=
    hNeighbor.trans hHit
  have hSource :
      PPL.shiftLeft ring g (j + 1) = e :=
    grantDrainD6NoFireRightNeighborInjective
      ring hn _ _ hEqualNeighbor
  by_cases hEarlier :
      j + 1 < grantDrainLeftLeaderDistance ring s.native g
  · have hMiss := hFirst.2 (j + 1) hjNextPos hEarlier
    rw [hSource, hxLeader] at hMiss
    cases hMiss
  · have hAtFront :
        j + 1 = grantDrainLeftLeaderDistance ring s.native g := by
      omega
    rw [hAtFront] at hSource
    exact hSource.symm

/-- OLD leader/follower source rows meet the warm scan only at
the source's own old-front boundary; otherwise both E endpoints
are strictly outside the full inclusive scan. -/
theorem grantDrainD6NoFireSourceLeaderFollowerOutsideOrFront
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hxLeader : (s.native e).l = true)
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false) :
    (∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g j ≠ e ∧
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e) ∨
    e = PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g) := by
  have hHost :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hShort :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hShort.1 hShort.2).mp rfl
  by_cases hFront :
      e = PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g)
  · exact Or.inr hFront
  · left
    intro j hj
    constructor
    · intro hEq
      by_cases hjZero : j = 0
      · subst j
        rw [grantDrainWarmShiftLeftZero] at hEq
        have hOldL : (s.native g).l = true := by
          rw [hEq]
          exact hxLeader
        rw [hHost.1] at hOldL
        cases hOldL
      · by_cases hjAt :
            j = grantDrainLeftLeaderDistance ring s.native g
        · rw [hjAt] at hEq
          exact hFront hEq.symm
        · have hMiss := hFirst.2 j (by omega) (by omega)
          rw [hEq, hxLeader] at hMiss
          cases hMiss
    · intro hEq
      exact hFront
        (grantDrainD6NoFireSourceLeaderFollowerResponderScanFront
          ring hn s e g hC hWarm hxLeader hyFollower
          j hj hEq)


/-- A quiet OLD leader forwards its resident DUMMY/LIVE to an
empty OLD follower; E clears the source and the responder's
signal. This lemma is a literal two-record verification. -/
theorem grantDrainD6NoFireLeaderBulletPair
    (x y : CertNative)
    (hxLeader : x.l = true)
    (hxQuiet : x.sg = false)
    (hxBullet : x.b ≠ (0 : Fin 3))
    (hyFollower : y.l = false)
    (hyEmpty : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).2.b = x.b ∧
      (certLiteralEPair x y).2.sg = false := by
  rcases grantDrainEntranceNonzeroBulletKind x.b hxBullet with
    hDummy | hLive
  · simp [certLiteralEPair, certFinThree,
      hxLeader, hxQuiet, hyFollower, hyEmpty, hDummy]
  · simp [certLiteralEPair, certFinThree,
      hxLeader, hxQuiet, hyFollower, hyEmpty, hLive]

/-- OLD source e is its warm follower g's preceding leader,
has a resident bullet, and forwards that bullet to the empty
responder at distance a-1. The source's old bullet is the
unique first bullet of its entire clean sector. The generic
first-bullet-move bound yields an E rank decrease, even when
its kind is DUMMY rather than LIVE. -/
theorem grantDrainD6NoFireSourceLeaderBulletSectorERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (D : Fin (n + 1)) (a : Nat)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hSector : sectorLength ring s.native e D)
    (hAt : g = PPL.shiftRight ring e a)
    (ha : 2 ≤ a) (haInside : a < D.val)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = a)
    (hxLeader : (s.native e).l = true)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hTo : ring.rightNeighbor e =
      PPL.shiftLeft ring g (a - 1)) :
    grantDrainWarmRank ring (nativeE ring s.native e) g + 1 ≤
      grantDrainWarmRank ring s.native g := by
  have haN : a < n := by
    have hBound := D.isLt
    omega
  have hFront :
      PPL.shiftLeft ring g a = e :=
    grantDrainD6FireFrontCoordinatePub ring e g a haN hAt
  have hOldHost :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hLocal : GrantDrainEntranceILocal ring s.native :=
    (grantDrainEntranceIffILocal ring s.native).mp hC.1
  have hyEmpty :=
    grantDrainEntranceILocalFollowerBulletNextEmpty
      ring s.native e hLocal hxBullet hyFollower
  have hxQuiet :=
    grantDrainD6OutgoingBulletSourceQuiet
      ring s.native hC e hxBullet
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPair :=
    grantDrainD6NoFireLeaderBulletPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hxLeader hxQuiet hxBullet hyFollower hyEmpty
  have hYBullet :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (s.native e).b := by
    simpa [nativeE, hDistinct] using hPair.1
  have hResponderLeader :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        (s.native (ring.rightNeighbor e)).l := by
    have hLocalFollower :=
      grantDrainEntranceLiteralEFollowerResponderRemains
        (s.native e) (s.native (ring.rightNeighbor e))
        hyFollower
    simpa [nativeE, hDistinct, hyFollower] using hLocalFollower
  have hLeaders :=
    grantDrainEntranceNativeELeadersFixed
      ring (by omega : 2 ≤ n) s.native e hResponderLeader
  have hSourceZero :=
    grantDrainEntranceNativeESourceBulletZero
      ring s.native e
  have hFrame :
      ∀ j : Nat, j < a - 1 →
      nativeE ring s.native e (PPL.shiftLeft ring g j) =
        s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    have hNotE :
        PPL.shiftLeft ring g j ≠ e := by
      rw [← hFront]
      exact grantDrainD6BirthLeftOffsetsDistinct
        ring g j a (by omega) haN (by omega)
    have hNotY :
        PPL.shiftLeft ring g j ≠ ring.rightNeighbor e := by
      rw [hTo]
      exact grantDrainD6BirthLeftOffsetsDistinct
        ring g j (a - 1) (by omega) (by omega) (by omega)
    exact grantDrainEntranceNativeEFrame
      ring s.native e (PPL.shiftLeft ring g j) hNotE hNotY
  have hOldLeaderBullet :
      HasBullet s.native (PPL.shiftRight ring e 0) := by
    rw [grantDrainWeakDeathShiftRightZero ring e]
    exact hxBullet
  have hUnique := (hC.1.2 e D hSector).1
  have hOldFirst :
      grantDrainLeftBulletDistance ring s.native g a =
        some a := by
    apply (grantDrainWarmBulletSomeCharacterization
      ring s.native g a a).mpr
    refine ⟨by omega, Nat.le_refl _, ?_, ?_⟩
    · rw [hFront]
      intro hZero
      apply hxBullet
      apply Fin.ext
      exact hZero
    · intro j hj hja
      have hArc :
          PPL.shiftLeft ring g j =
            PPL.shiftRight ring e (a - j) := by
        rw [hAt]
        exact grantDrainMarksArcShiftLeftRight
          ring e a j (by omega) haN
      by_cases hEmpty :
          (s.native (PPL.shiftLeft ring g j)).b =
            (0 : Fin 3)
      · rw [hEmpty]
        rfl
      · have hBulletAt :
            HasBullet s.native (PPL.shiftRight ring e (a - j)) := by
          rw [← hArc]
          exact hEmpty
        have hEq :
            (⟨0, ring.hn⟩ : Fin n) =
              (⟨a - j, show a - j < n by omega⟩ : Fin n) :=
          hUnique
            (⟨0, ring.hn⟩ : Fin n)
            (⟨a - j, show a - j < n by omega⟩ : Fin n)
            hSector.1
            (by omega : a - j < D.val)
            hOldLeaderBullet hBulletAt
        have hVal := congrArg Fin.val hEq
        dsimp only at hVal
        omega
  have hBulletValue : (s.native e).b.val ≠ 0 := by
    intro hZero
    apply hxBullet
    apply Fin.ext
    exact hZero
  have hNear :
      (nativeE ring s.native e
        (PPL.shiftLeft ring g (a - 1))).b.val ≠ 0 := by
    rw [← hTo, hYBullet]
    exact hBulletValue
  have hFar :
      (nativeE ring s.native e
        (PPL.shiftLeft ring g a)).b.val = 0 := by
    rw [hFront, hSourceZero]
    rfl
  have hSignalPrefix :
      ∀ j : Nat, j < a - 1 →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).sg =
        (s.native (PPL.shiftLeft ring g j)).sg := by
    intro j hj
    rw [hFrame j hj]
  have hBulletPrefix :
      ∀ j : Nat, 1 ≤ j → j < a - 1 →
        (nativeE ring s.native e
          (PPL.shiftLeft ring g j)).b.val =
        (s.native (PPL.shiftLeft ring g j)).b.val := by
    intro j _ hj
    rw [hFrame j hj]
  have hBeforeIndex : a - 1 + 1 = a := by omega
  have hOldFirstBefore :
      grantDrainLeftBulletDistance ring s.native g a =
        some (a - 1 + 1) := by
    rw [hBeforeIndex]
    exact hOldFirst
  have hFarBefore :
      (nativeE ring s.native e
        (PPL.shiftLeft ring g (a - 1 + 1))).b.val = 0 := by
    rw [hBeforeIndex]
    exact hFar
  exact (grantDrainD6PairFirstBulletMoveRankSignal
    ring s.native (nativeE ring s.native e) g a (a - 1)
    (by omega) (by omega) hC hOldHost.2.2
    hLeaders hSignalPrefix hBulletPrefix hDistance
    hOldFirstBefore hNear hFarBefore).2.2.2


/-- Remaining OLD leader-source/follower-responder family.
The source is either outside the full warm scan, is a quiet
bullet-free old front, fires a ready LIVE from that front, or
forwards the unique resident bullet from the old front. In
both active front rows, post-step warmth excludes g=the new
bullet host, giving at least one strict interior follower. -/
theorem grantDrainD6NoFireSourceLeaderFollowerERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNone : grantDrainSelect ring s e = .none)
    (_hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxLeader : (s.native e).l = true)
    (hyFollower :
      (s.native (ring.rightNeighbor e)).l = false) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  rcases grantDrainD6NoFireSourceLeaderFollowerOutsideOrFront
      ring hn s e g hC hWarm hxLeader hyFollower with
    hOutside | hFront
  · exact Nat.le_of_eq
      (grantDrainD6EScanOutsidePair
        ring s.native e g hOutside)
  · have hOldHost :=
      grantDrainD6ExceptionalDeathHostFields s g hWarm
    obtain ⟨p, D, a, hSector, haInside, hAt⟩ :=
      grantDrainEntranceSectorCoverOfRoot
        ring s.native hC.1.1.1 g
    have hDistance :=
      grantDrainD6OutgoingBulletSectorDistance
        ring s.native g p D a hSector haInside hAt hOldHost.1
    have hFrontCoordinate :
        PPL.shiftLeft ring g a.val = p :=
      grantDrainD6FireFrontCoordinatePub
        ring p g a.val a.isLt hAt
    have hSourceSector : e = p := by
      calc
        e = PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g) := hFront
        _ = PPL.shiftLeft ring g a.val := by rw [hDistance.2]
        _ = p := hFrontCoordinate
    have hSectorE : sectorLength ring s.native e D := by
      rw [hSourceSector]
      exact hSector
    have hAtE : g = PPL.shiftRight ring e a.val := by
      rw [hSourceSector]
      exact hAt
    have hFrontE : e = PPL.shiftLeft ring g a.val := by
      rw [hDistance.2] at hFront
      exact hFront
    have hTo :
        ring.rightNeighbor e =
          PPL.shiftLeft ring g (a.val - 1) :=
      grantDrainD6OutgoingBulletSuccessorAtOffset
        ring g e a.val hDistance.1 a.isLt hFrontE
    have hAfterEmpty :
        (nativeE ring s.native e g).b = (0 : Fin 3) := by
      have hPhysical :=
        (grantDrainD6ExceptionalDeathHostFields
          (grantDrainStep ring fresh update s e) g hStillWarm).2.1
      rw [grantDrainWarmPhysicalNoBirthNative
        ring fresh update s e hNone] at hPhysical
      exact hPhysical
    cases hxReady : (s.native e).sg with
    | true =>
        have hLocal : GrantDrainEntranceILocal ring s.native :=
          (grantDrainEntranceIffILocal ring s.native).mp hC.1
        have hRow :=
          grantDrainEntranceILocalReadySourceNativeE
            ring (by omega : 3 ≤ n) s.native e hLocal
            hxLeader hxReady hyFollower
        have hYBullet :
            (nativeE ring s.native e
              (ring.rightNeighbor e)).b = (2 : Fin 3) :=
          hRow.2.2.2.1
        have hNotY : ring.rightNeighbor e ≠ g := by
          intro hEq
          rw [hEq, hAfterEmpty] at hYBullet
          cases hYBullet
        have haTwo : 2 ≤ a.val := by
          by_cases hOne : a.val = 1
          · have hYIsG : ring.rightNeighbor e = g := by
              calc
                ring.rightNeighbor e =
                    PPL.shiftLeft ring g (a.val - 1) := hTo
                _ = PPL.shiftLeft ring g 0 := by
                      rw [hOne]
                _ = g := grantDrainWarmShiftLeftZero ring g
            exact False.elim (hNotY hYIsG)
          · omega
        exact grantDrainD6NoFireSourceLeaderReadySectorERankLe
          ring hn fresh update s e g D a.val hC hWarm
          hSectorE hAtE haTwo haInside hDistance.2
          hxReady hTo hNone
    | false =>
        by_cases hxEmpty : (s.native e).b = (0 : Fin 3)
        · exact grantDrainD6NoFireSourceLeaderQuietEmptyFollowerERankLe
            ring hn s e g hWarm hxLeader hxReady hxEmpty hyFollower
        · have hLocal : GrantDrainEntranceILocal ring s.native :=
            (grantDrainEntranceIffILocal ring s.native).mp hC.1
          have hyEmpty :=
            grantDrainEntranceILocalFollowerBulletNextEmpty
              ring s.native e hLocal hxEmpty hyFollower
          have hPair :=
            grantDrainD6NoFireLeaderBulletPair
              (s.native e) (s.native (ring.rightNeighbor e))
              hxLeader hxReady hxEmpty hyFollower hyEmpty
          have hDistinct :=
            grantDrainEntranceRightNeighborDistinct
              ring (by omega : 2 ≤ n) e
          have hYBullet :
              (nativeE ring s.native e
                (ring.rightNeighbor e)).b = (s.native e).b := by
            simpa [nativeE, hDistinct] using hPair.1
          have hNotY : ring.rightNeighbor e ≠ g := by
            intro hEq
            rw [hEq, hAfterEmpty] at hYBullet
            exact hxEmpty hYBullet.symm
          have haTwo : 2 ≤ a.val := by
            by_cases hOne : a.val = 1
            · have hYIsG : ring.rightNeighbor e = g := by
                calc
                  ring.rightNeighbor e =
                      PPL.shiftLeft ring g (a.val - 1) := hTo
                  _ = PPL.shiftLeft ring g 0 := by
                        rw [hOne]
                  _ = g := grantDrainWarmShiftLeftZero ring g
              exact False.elim (hNotY hYIsG)
            · omega
          have hDrop :=
            grantDrainD6NoFireSourceLeaderBulletSectorERankLe
              ring hn s e g D a.val hC hWarm hSectorE
              hAtE haTwo haInside hDistance.2
              hxLeader hxEmpty hyFollower hTo
          omega

/-- Source-leader half.  OLD leader-to-leader
contacts are handled without a selector premise, and
leader-to-follower contacts are handled by their old-front
geometry and exact no-FIRE E rows above. -/
theorem grantDrainD6NoFireSourceLeaderERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNone : grantDrainSelect ring s e = .none)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true)
    (hxLeader : (s.native e).l = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  cases hyLeader : (s.native (ring.rightNeighbor e)).l with
  | true =>
      exact grantDrainD6NoFireSourceLeaderLeaderERankLe
        ring hn s e g hC hWarm hNonExceptional
        hxLeader hyLeader
  | false =>
      exact grantDrainD6NoFireSourceLeaderFollowerERankLe
        ring hn fresh update s e g hC hWarm hNone
        hNonExceptional hStillWarm hxLeader hyLeader

/-- Final no-FIRE E-only rank nonincrease.
Old source leader/follower is a complete Boolean dispatch,
not an assumed proof obligation. -/
theorem grantDrainD6NoFireERankLe
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hNone : grantDrainSelect ring s e = .none)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hStillWarm :
      grantDrainWarmAt
        (grantDrainStep ring fresh update s e) g = true) :
    grantDrainWarmRank ring (nativeE ring s.native e) g ≤
      grantDrainWarmRank ring s.native g := by
  cases hxLeader : (s.native e).l with
  | true =>
      exact grantDrainD6NoFireSourceLeaderERankLe
        ring hn fresh update s e g hC hWarm hNone
        hNonExceptional hStillWarm hxLeader
  | false =>
      exact grantDrainD6NoFireFollowerERankLe
        ring hn fresh update s e g hC hWarm hNone
        hNonExceptional hStillWarm hxLeader


end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderReadyFrontERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireQuietLeaderResponderSurvivorPair
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderQuietSurvivorERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderQuietDeathFrontERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderLeaderERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireReadySourcePair
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderReadySectorStrict
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderReadySectorERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireRightNeighborInjective
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderFollowerResponderScanFront
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderFollowerOutsideOrFront
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireLeaderBulletPair
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderBulletSectorERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderFollowerERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireSourceLeaderERankLe
#print axioms L3.GrantDrainEntrance.grantDrainD6NoFireERankLe

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Independently derived charged subrows and unconditional
ghost-invariant word closure. The unrestricted charged step and
full native-clean word closure are not claimed below. -/

/-- Explicit physical meaning of an OLD warm ghost. Unlike
GrantDrainD6HostCoherent, this controls native/request warmness. -/
def GrantDrainD6PhysicalWarmHost
    {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n) : Prop :=
  ∀ g : Fin n, label.warm = true →
    label.host = some g → grantDrainWarmAt s g = true

/-- An actual continuing label is physically warm at its NEW host.
This additional coherence property is automatically propagated
by the exact ghost step, without a safety premise. -/
theorem grantDrainD6PhysicalWarmHostStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n) :
    GrantDrainD6PhysicalWarmHost
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  intro g hWarm hHost
  exact grantDrainD6HostNextWarmPhysical
    ring fresh update s e g label hHost hWarm

/-- At the D.6 entrance, an initially warm ghost has its native
warm guard by the stated physical entrance predicate. -/
theorem grantDrainD6PhysicalWarmHostInitial
    {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch)
    (g : Fin n) (b : Nat)
    (hWarm : grantDrainWarmAt s g = true) :
    GrantDrainD6PhysicalWarmHost s
      (grantDrainD6MergeInitialLabel g true b) := by
  intro q _ hHost
  change some g = some q at hHost
  have hSame : g = q := Option.some.inj hHost
  rw [← hSame]
  exact hWarm

/-- A fixed, physically warm OLD host on an ordinary
no-FIRE edge has nonincreasing charged rank. Both birth credit
and exceptional credit remain unchanged on this row. -/
theorem grantDrainD6ChargedNoFireFixedOrdinary
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hOldPhysical : grantDrainWarmAt s g = true)
    (hOldWarm : label.warm = true)
    (hOldHost : label.host = some g)
    (hOldGrant : s.grant g = true)
    (hNone : grantDrainSelect ring s e = .none)
    (hNonExceptional :
      grantDrainExceptionalDeath ring s e g = false)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g)
    (hNewGrant :
      (grantDrainStep ring fresh update s e).grant g = true) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) ≤
    grantDrainChargedWarmRank ring s label := by
  have hNewPhysical :=
    grantDrainD6HostNextWarmPhysical
      ring fresh update s e g label hNewHost hNewWarm
  have hRank :
      grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g ≤
      grantDrainWarmRank ring s.native g := by
    rw [grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone]
    exact grantDrainD6NoFireERankLe
      ring hn fresh update s e g hC hOldPhysical
      hNone hNonExceptional hNewPhysical
  have hBirth :
      (grantDrainWarmLabelStep ring fresh update s e
        label).birthsLeft = label.birthsLeft := by
    simp [grantDrainWarmLabelStep, hNone]
  have hReserve :
      (grantDrainWarmLabelStep ring fresh update s e
        label).exceptionalLeft = label.exceptionalLeft := by
    simp [grantDrainWarmLabelStep, hOldHost,
      hOldWarm, hNonExceptional]
  have hOldCost :
      grantDrainChargedWarmRank ring s label =
        grantDrainWarmRank ring s.native g +
          label.birthsLeft +
          (if label.exceptionalLeft then 2 * (n - 2) else 0) := by
    simp [grantDrainChargedWarmRank,
      hOldWarm, hOldHost, hOldGrant]
  have hNewCost :
      grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label) =
        grantDrainWarmRank ring
          (grantDrainStep ring fresh update s e).native g +
        (grantDrainWarmLabelStep ring fresh update s e
          label).birthsLeft +
        (if (grantDrainWarmLabelStep ring fresh update s e
            label).exceptionalLeft then 2 * (n - 2) else 0) := by
    simp [grantDrainChargedWarmRank,
      hNewWarm, hNewHost, hNewGrant]
  rw [hOldCost, hNewCost, hBirth, hReserve]
  omega

/-- Exceptional no-FIRE fixed-host subrow. The actual old
exceptional guard consumes the available one-time reserve,
paying the (at most) 2(n-2) increase from native leader death. -/
theorem grantDrainD6ChargedNoFireFixedExceptional
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hOldPhysical : grantDrainWarmAt s g = true)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hOldWarm : label.warm = true)
    (hOldHost : label.host = some g)
    (hOldGrant : s.grant g = true)
    (hNone : grantDrainSelect ring s e = .none)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g)
    (hNewGrant :
      (grantDrainStep ring fresh update s e).grant g = true) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) ≤
    grantDrainChargedWarmRank ring s label := by
  have hRank :
      grantDrainWarmRank ring
        (grantDrainStep ring fresh update s e).native g ≤
      grantDrainWarmRank ring s.native g + 2 * (n - 2) := by
    rw [grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone]
    exact grantDrainD6ExceptionalDeathERank
      ring hn s e g hC hOldPhysical hExceptional
  have hBirth :
      (grantDrainWarmLabelStep ring fresh update s e
        label).birthsLeft = label.birthsLeft := by
    simp [grantDrainWarmLabelStep, hNone]
  have hOldReserve :=
    grantDrainD6MergeExceptionalRequiresReserve
      ring s label e g hInv hOldWarm hOldHost hExceptional
  have hNewReserve :=
    grantDrainD6MergeExceptionalConsumesReserve
      ring fresh update s e g label
      hOldHost hOldWarm hExceptional
  have hOldCost :
      grantDrainChargedWarmRank ring s label =
        grantDrainWarmRank ring s.native g +
          label.birthsLeft + 2 * (n - 2) := by
    simp [grantDrainChargedWarmRank,
      hOldWarm, hOldHost, hOldGrant, hOldReserve]
  have hNewCost :
      grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label) =
        grantDrainWarmRank ring
          (grantDrainStep ring fresh update s e).native g +
        (grantDrainWarmLabelStep ring fresh update s e
          label).birthsLeft := by
    simp [grantDrainChargedWarmRank,
      hNewWarm, hNewHost, hNewGrant, hNewReserve]
  rw [hOldCost, hNewCost, hBirth]
  omega

/-- Complete no-FIRE fixed-host charge, dispatching on the OLD
exceptional death test; this is not a postulated rank leaf. -/
theorem grantDrainD6ChargedNoFireFixedHost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hOldPhysical : grantDrainWarmAt s g = true)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hOldWarm : label.warm = true)
    (hOldHost : label.host = some g)
    (hOldGrant : s.grant g = true)
    (hNone : grantDrainSelect ring s e = .none)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g)
    (hNewGrant :
      (grantDrainStep ring fresh update s e).grant g = true) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) ≤
    grantDrainChargedWarmRank ring s label := by
  cases hExceptional : grantDrainExceptionalDeath ring s e g with
  | false =>
      exact grantDrainD6ChargedNoFireFixedOrdinary
        ring hn fresh update s e g label
        hC hOldPhysical hOldWarm hOldHost hOldGrant
        hNone hExceptional hNewWarm hNewHost hNewGrant
  | true =>
      exact grantDrainD6ChargedNoFireFixedExceptional
        ring hn fresh update s e g label
        hC hOldPhysical hInv hOldWarm hOldHost hOldGrant
        hNone hExceptional hNewWarm hNewHost hNewGrant

/-- An actual warm Y-to-X transport is no-FIRE and decreases W.
Its charged rank also cannot increase, because no birth is
charged and the exceptional reserve is never replenished. -/
theorem grantDrainD6ChargedMovingHost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hOldPhysical :
      grantDrainWarmAt s (ring.rightNeighbor e) = true)
    (hOldWarm : label.warm = true)
    (hOldHost : label.host = some (ring.rightNeighbor e))
    (hOldGrant : s.grant (ring.rightNeighbor e) = true)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some e)
    (hNewGrant :
      (grantDrainStep ring fresh update s e).grant e = true) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) ≤
    grantDrainChargedWarmRank ring s label := by
  have hNone :=
    grantDrainD6MovingHostNoFire
      ring hn fresh update s e label
      hOldHost hNewHost hNewWarm
  have hRank :=
    grantDrainD6MovingHostRankLe
      ring hn fresh update s e label
      hC hOldHost hOldPhysical hOldGrant hNewHost hNewWarm
  have hBirth :
      (grantDrainWarmLabelStep ring fresh update s e
        label).birthsLeft = label.birthsLeft := by
    simp [grantDrainWarmLabelStep, hNone]
  have hReserveLe :
      (if (grantDrainWarmLabelStep ring fresh update s e
        label).exceptionalLeft then 2 * (n - 2) else 0) ≤
      (if label.exceptionalLeft then 2 * (n - 2) else 0) := by
    cases hReserve : label.exceptionalLeft with
    | false =>
        have hNew :=
          grantDrainD6MergeReserveNeverRefills
            ring fresh update s e label hReserve
        simp [hReserve, hNew]
    | true =>
        cases hNew :
            (grantDrainWarmLabelStep ring fresh update s e
              label).exceptionalLeft <;>
          simp [hReserve, hNew]
  have hOldCost :
      grantDrainChargedWarmRank ring s label =
        grantDrainWarmRank ring s.native (ring.rightNeighbor e) +
          label.birthsLeft +
          (if label.exceptionalLeft then 2 * (n - 2) else 0) := by
    simp [grantDrainChargedWarmRank,
      hOldWarm, hOldHost, hOldGrant]
  have hNewCost :
      grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label) =
        grantDrainWarmRank ring
          (grantDrainStep ring fresh update s e).native e +
        (grantDrainWarmLabelStep ring fresh update s e
          label).birthsLeft +
        (if (grantDrainWarmLabelStep ring fresh update s e
            label).exceptionalLeft then 2 * (n - 2) else 0) := by
    simp [grantDrainChargedWarmRank,
      hNewWarm, hNewHost, hNewGrant]
  rw [hOldCost, hNewCost, hBirth]
  omega

/-- Exact entrance charge for an actually warm and granted host.
This is an equality, not a speculative running-time bound. -/
theorem grantDrainD6ChargedEntranceExact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (g : Fin n) (b : Nat)
    (hGrant : s.grant g = true) :
    grantDrainChargedWarmRank ring s
      (grantDrainD6MergeInitialLabel g true b) =
        grantDrainWarmRank ring s.native g + b +
          2 * (n - 2) := by
  simp [grantDrainChargedWarmRank,
    grantDrainD6MergeInitialLabel, hGrant]

/-- A finite word applies the exact physical and label steps,
rather than replacing physical evolution with an abstract counter. -/
def grantDrainD6GhostWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n)
    (word : List (Fin n)) :
    GrantDrainState n Scratch × GrantDrainWarmLabel n :=
  word.foldl
    (fun pair e =>
      (grantDrainStep ring fresh update pair.1 e,
        grantDrainWarmLabelStep ring fresh update pair.1 e pair.2))
    (s, label)

/-- Both the actual grant-count birth budget and host GRANT
coherence are word-closed, without native-clean assumptions.
This does NOT claim that C_native or MergeSpent is word-closed. -/
theorem grantDrainD6GhostWordBudgetCoherent
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainWarmLabel n),
      GrantDrainD6BirthBudget ring s label →
      GrantDrainD6HostCoherent s label →
      GrantDrainD6BirthBudget ring
        (grantDrainD6GhostWord ring fresh update s label word).1
        (grantDrainD6GhostWord ring fresh update s label word).2 ∧
      GrantDrainD6HostCoherent
        (grantDrainD6GhostWord ring fresh update s label word).1
        (grantDrainD6GhostWord ring fresh update s label word).2 := by
  intro word
  induction word with
  | nil =>
      intro s label hBudget hCoherent
      exact ⟨hBudget, hCoherent⟩
  | cons e tail ih =>
      intro s label hBudget hCoherent
      have hNextBudget :=
        grantDrainD6BirthBudgetStepOfCoherent
          ring hn fresh update s e label hBudget hCoherent
      have hNextCoherent :=
        grantDrainD6HostCoherentStep
          ring hn fresh update s e label hCoherent
      simpa only [grantDrainD6GhostWord, List.foldl_cons]
        using ih
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)
          hNextBudget hNextCoherent

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! R8e / D6 charged-step assembly.
Only the OLD C_native and MergeSpent hypotheses are required
at the current state. Their full evolution is treated separately. -/

/-- Every genuine FIRE has an actual chosen canonical birth site,
with the exact first-match selector, not an assumed eligible site. -/
theorem grantDrainD6FireSelectedBirthSite
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    ∃ z : Fin n,
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e) := by
  cases hf : grantDrainSelect ring s e with
  | none =>
      exact False.elim (hFire hf)
  | leftLocal =>
      exact ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  | rightLocal =>
      exact ⟨ring.rightNeighbor e, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | cross =>
      exact ⟨e, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-- The born site is never the host of a ghost which stays
named and warm after this very FIRE. This applies the literal
host-at-birth retirement row, not a positional convention. -/
theorem grantDrainD6FireSurvivingHostAvoidsBirth
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g z : Fin n)
    (label : GrantDrainWarmLabel n)
    (hHost : label.host = some g)
    (hSelected :
      (grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
      (grantDrainSelect ring s e = .rightLocal ∧
        z = ring.rightNeighbor e) ∨
      (grantDrainSelect ring s e = .cross ∧ z = e))
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true) :
    z ≠ g := by
  intro hAt
  have hBirth : ∃ w : Fin n,
      w = g ∧
      ((grantDrainSelect ring s e = .leftLocal ∧ w = e) ∨
       (grantDrainSelect ring s e = .rightLocal ∧
          w = ring.rightNeighbor e) ∨
       (grantDrainSelect ring s e = .cross ∧ w = e)) :=
    ⟨z, hAt, hSelected⟩
  rcases grantDrainD6HostAtBirthRetires
      ring hn fresh update s e g label hHost hBirth with
    hRetired | hCold
  · rw [hNewHost] at hRetired
    cases hRetired
  · rw [hNewWarm] at hCold
    cases hCold

/-- Selected-FIRE charged inequality for a continuing, granted
fixed host. The birth-budget invariant proves positive credit.
An ordinary birth costs at most 1 W; an exceptional front death
costs at most 2(n-2)+1 W and consumes the old reserve as well. -/
theorem grantDrainD6ChargedFireFixedHost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hBudget : GrantDrainD6BirthBudget ring s label)
    (hPhysical : grantDrainWarmAt s g = true)
    (hOldWarm : label.warm = true)
    (hOldHost : label.host = some g)
    (hOldGrant : s.grant g = true)
    (hFire : grantDrainSelect ring s e ≠ .none)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g)
    (hNewGrant :
      (grantDrainStep ring fresh update s e).grant g = true) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) ≤
    grantDrainChargedWarmRank ring s label := by
  obtain ⟨z, hSelected⟩ :=
    grantDrainD6FireSelectedBirthSite ring s e hFire
  have hAway :=
    grantDrainD6FireSurvivingHostAvoidsBirth
      ring hn fresh update s e g z label
      hOldHost hSelected hNewHost hNewWarm
  have hNewPhysical :=
    grantDrainD6HostNextWarmPhysical
      ring fresh update s e g label hNewHost hNewWarm
  have hCredit :=
    grantDrainD6BirthBudgetFireCredit
      ring hn fresh update s e label hBudget
      hFire hNewWarm g hNewHost hNewGrant
  have hDebit :=
    grantDrainD6BirthBudgetFireDebit
      ring fresh update s e label hFire
  have hOldCost :
      grantDrainChargedWarmRank ring s label =
        grantDrainWarmRank ring s.native g +
          label.birthsLeft +
          (if label.exceptionalLeft then 2 * (n - 2) else 0) := by
    simp [grantDrainChargedWarmRank,
      hOldWarm, hOldHost, hOldGrant]
  have hNewCost :
      grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label) =
        grantDrainWarmRank ring
          (grantDrainStep ring fresh update s e).native g +
        (grantDrainWarmLabelStep ring fresh update s e
          label).birthsLeft +
        (if (grantDrainWarmLabelStep ring fresh update s e
            label).exceptionalLeft then 2 * (n - 2) else 0) := by
    simp [grantDrainChargedWarmRank,
      hNewWarm, hNewHost, hNewGrant]
  cases hExceptional : grantDrainExceptionalDeath ring s e g with
  | false =>
      have hRank :
          grantDrainWarmRank ring
            (grantDrainStep ring fresh update s e).native g ≤
          grantDrainWarmRank ring s.native g + 1 := by
        change
          grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
          grantDrainWarmRank ring s.native g + 1
        exact grantDrainD6NonExceptionalBirthRankLift
          ring hn fresh update s e g z hC hPhysical
          hExceptional hSelected hAway hNewPhysical
      have hReserve :
          (grantDrainWarmLabelStep ring fresh update s e
            label).exceptionalLeft = label.exceptionalLeft := by
        simp [grantDrainWarmLabelStep,
          hOldHost, hOldWarm, hExceptional]
      have hPaid :=
        grantDrainD6ChargedOrdinaryFireArithmetic
          (grantDrainWarmRank ring s.native g)
          (grantDrainWarmRank ring
            (grantDrainStep ring fresh update s e).native g)
          label.birthsLeft
          (if label.exceptionalLeft then 2 * (n - 2) else 0)
          hCredit hRank
      rw [hNewCost, hOldCost, hDebit, hReserve]
      exact hPaid
  | true =>
      have hCharge :=
        grantDrainD6ExceptionalBirthRankChargeAndCredits
          ring hn fresh update s e g label
          hC hPhysical hExceptional hFire hInv
          hOldWarm hOldHost
      have hRank :
          grantDrainWarmRank ring
            (grantDrainStep ring fresh update s e).native g ≤
          grantDrainWarmRank ring s.native g +
            2 * (n - 2) + 1 := by
        change
          grantDrainWarmRank ring (grantDrainNativeNext ring s e) g ≤
          grantDrainWarmRank ring s.native g +
            2 * (n - 2) + 1
        exact hCharge.1
      have hPaid :=
        grantDrainD6ChargedExceptionalFireArithmetic
          (grantDrainWarmRank ring s.native g)
          (grantDrainWarmRank ring
            (grantDrainStep ring fresh update s e).native g)
          label.birthsLeft (2 * (n - 2))
          hCredit hRank
      rw [hNewCost, hOldCost, hCharge.2.2.2,
        hCharge.2.1, hCharge.2.2.1]
      simp only [ite_true, ite_false, Nat.add_zero]
      exact hPaid


/-- A named host change is necessarily the literal Y-to-X
token movement. The source-host case cannot move; an off-pair
host is framed; a responder host can only survive at Y or move
to X. No premise about time or the native rank is involved. -/
theorem grantDrainD6HostChangedOnlyResponderToSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g q : Fin n)
    (label : GrantDrainWarmLabel n)
    (hOldHost : label.host = some g)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some q)
    (hDifferent : q ≠ g) :
    g = ring.rightNeighbor e ∧ q = e := by
  by_cases hSource : g = e
  · have hHostSource : label.host = some e := by
      rw [← hSource]
      exact hOldHost
    have hContact :=
      grantDrainD6ContactHostAtSource
        ring fresh update s e label hHostSource
    cases hRow : grantDrainD6ContactRowSourceGrant ring fresh s e with
    | false =>
        rw [hContact, hRow] at hNewHost
        cases hNewHost
    | true =>
        rw [hContact, hRow] at hNewHost
        have hEq : e = q := Option.some.inj hNewHost
        exact False.elim (hDifferent (hEq.symm.trans hSource.symm))
  · by_cases hResponder : g = ring.rightNeighbor e
    · have hHostResponder :
          label.host = some (ring.rightNeighbor e) := by
        rw [← hResponder]
        exact hOldHost
      have hContact :=
        grantDrainD6ContactHostAtResponder
          ring hn fresh update s e label hHostResponder
      rw [hContact] at hNewHost
      split at hNewHost
      · cases hNewHost
      · split at hNewHost
        · have hEq : ring.rightNeighbor e = q :=
            Option.some.inj hNewHost
          exact False.elim
            (hDifferent (hEq.symm.trans hResponder.symm))
        · split at hNewHost
          · have hEq : e = q := Option.some.inj hNewHost
            exact ⟨hResponder, hEq.symm⟩
          · cases hNewHost
    · have hFixed :
          (grantDrainWarmLabelStep ring fresh update s e
            label).host = some g := by
        simp [grantDrainWarmLabelStep,
          hOldHost, hSource, hResponder]
      have hEq : g = q :=
        Option.some.inj (hFixed.symm.trans hNewHost)
      exact False.elim (hDifferent hEq.symm)

/-- The actual D.6 charged rank is monotone for one physical
service when the five OLD assumptions hold: native cleanliness,
spent exceptional protection, sufficient prepaid grants,
GRANT-host coherence and literal physical warm-host coherence.
No preservation assumption is hidden in this one-step theorem. -/
theorem grantDrainD6ChargedWarmRankStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hBudget : GrantDrainD6BirthBudget ring s label)
    (hCoherent : GrantDrainD6HostCoherent s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) ≤
    grantDrainChargedWarmRank ring s label := by
  cases hOldWarm : label.warm with
  | false =>
      exact grantDrainD6ChargedColdStep
        ring fresh update s e label hOldWarm
  | true =>
      cases hOldHost : label.host with
      | none =>
          exact grantDrainD6ChargedHostlessStep
            ring fresh update s e label hOldHost
      | some g =>
          have hOldGrant :=
            hCoherent g hOldWarm hOldHost
          have hOldPhysical :=
            hPhysical g hOldWarm hOldHost
          cases hNewWarm :
              (grantDrainWarmLabelStep ring fresh update s e
                label).warm with
          | false =>
              exact grantDrainD6ChargedRetiredStep
                ring fresh update s e label (Or.inl hNewWarm)
          | true =>
              cases hNewHost :
                  (grantDrainWarmLabelStep ring fresh update s e
                    label).host with
              | none =>
                  exact grantDrainD6ChargedRetiredStep
                    ring fresh update s e label (Or.inr hNewHost)
              | some q =>
                  have hNewCoherent :=
                    grantDrainD6HostCoherentStep
                      ring hn fresh update s e label hCoherent
                  have hNewGrant :=
                    hNewCoherent q hNewWarm hNewHost
                  by_cases hSame : q = g
                  · subst q
                    by_cases hNone :
                        grantDrainSelect ring s e = .none
                    · exact grantDrainD6ChargedNoFireFixedHost
                        ring hn fresh update s e g label
                        hC hOldPhysical hInv hOldWarm hOldHost
                        hOldGrant hNone hNewWarm hNewHost hNewGrant
                    · exact grantDrainD6ChargedFireFixedHost
                        ring hn fresh update s e g label
                        hC hInv hBudget hOldPhysical
                        hOldWarm hOldHost hOldGrant hNone
                        hNewWarm hNewHost hNewGrant
                  · obtain ⟨hResponder, hSource⟩ :=
                      grantDrainD6HostChangedOnlyResponderToSource
                        ring hn fresh update s e g q label
                        hOldHost hNewHost hSame
                    have hOldHostResponder :
                        label.host = some (ring.rightNeighbor e) :=
                      hOldHost.trans (congrArg some hResponder)
                    have hOldPhysicalResponder :
                        grantDrainWarmAt s
                          (ring.rightNeighbor e) = true := by
                      rw [← hResponder]
                      exact hOldPhysical
                    have hOldGrantResponder :
                        s.grant (ring.rightNeighbor e) = true := by
                      rw [← hResponder]
                      exact hOldGrant
                    have hNewHostSource :
                        (grantDrainWarmLabelStep ring fresh update s e
                          label).host = some e :=
                      hNewHost.trans (congrArg some hSource)
                    have hNewGrantSource :
                        (grantDrainStep ring fresh update s e).grant e =
                          true := by
                      rw [hSource] at hNewGrant
                      exact hNewGrant
                    exact grantDrainD6ChargedMovingHost
                      ring hn fresh update s e label hC
                      hOldPhysicalResponder hOldWarm
                      hOldHostResponder hOldGrantResponder
                      hNewWarm hNewHostSource hNewGrantSource


/-- Charged-rank monotonicity along an exact finite word.
C_native and MergeSpent are supplied at every prefix cut, as
explicit hypotheses. BirthBudget, GRANT coherence and physical
warm-host coherence are carried by their proved step lemmas. -/
theorem grantDrainD6ChargedWarmRankWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainWarmLabel n),
      (∀ k : Nat, k ≤ word.length →
        C_native ring
          (grantDrainD6GhostWord ring fresh update s label
            (word.take k)).1.native) →
      (∀ k : Nat, k ≤ word.length →
        GrantDrainWarmMergeSpent ring
          (grantDrainD6GhostWord ring fresh update s label
            (word.take k)).1
          (grantDrainD6GhostWord ring fresh update s label
            (word.take k)).2) →
      GrantDrainD6BirthBudget ring s label →
      GrantDrainD6HostCoherent s label →
      GrantDrainD6PhysicalWarmHost s label →
      grantDrainChargedWarmRank ring
        (grantDrainD6GhostWord ring fresh update s label word).1
        (grantDrainD6GhostWord ring fresh update s label word).2 ≤
      grantDrainChargedWarmRank ring s label := by
  intro word
  induction word with
  | nil =>
      intro s label _ _ _ _ _
      exact Nat.le_refl _
  | cons e tail ih =>
      intro s label hClean hMerge hBudget hCoherent hPhysical
      have hCleanStart : C_native ring s.native := by
        have hAtZero := hClean 0 (by simp)
        simpa [grantDrainD6GhostWord] using hAtZero
      have hMergeStart : GrantDrainWarmMergeSpent ring s label := by
        have hAtZero := hMerge 0 (by simp)
        simpa [grantDrainD6GhostWord] using hAtZero
      have hOneStep :=
        grantDrainD6ChargedWarmRankStep
          ring hn fresh update s e label
          hCleanStart hMergeStart hBudget hCoherent hPhysical
      have hNextBudget :=
        grantDrainD6BirthBudgetStepOfCoherent
          ring hn fresh update s e label hBudget hCoherent
      have hNextCoherent :=
        grantDrainD6HostCoherentStep
          ring hn fresh update s e label hCoherent
      have hNextPhysical :=
        grantDrainD6PhysicalWarmHostStep
          ring fresh update s e label
      have hCleanTail :
          ∀ k : Nat, k ≤ tail.length →
            C_native ring
              (grantDrainD6GhostWord ring fresh update
                (grantDrainStep ring fresh update s e)
                (grantDrainWarmLabelStep ring fresh update s e
                  label) (tail.take k)).1.native := by
        intro k hk
        have hBound : k + 1 ≤ (e :: tail).length := by
          simp only [List.length_cons]
          omega
        have hAtPrefix := hClean (k + 1) hBound
        have hTake :
            (e :: tail).take (k + 1) =
              e :: tail.take k := by
          simp
        rw [hTake] at hAtPrefix
        change C_native ring
          (grantDrainD6GhostWord ring fresh update
            (grantDrainStep ring fresh update s e)
            (grantDrainWarmLabelStep ring fresh update s e
              label) (tail.take k)).1.native at hAtPrefix
        exact hAtPrefix
      have hMergeTail :
          ∀ k : Nat, k ≤ tail.length →
            GrantDrainWarmMergeSpent ring
              (grantDrainD6GhostWord ring fresh update
                (grantDrainStep ring fresh update s e)
                (grantDrainWarmLabelStep ring fresh update s e
                  label) (tail.take k)).1
              (grantDrainD6GhostWord ring fresh update
                (grantDrainStep ring fresh update s e)
                (grantDrainWarmLabelStep ring fresh update s e
                  label) (tail.take k)).2 := by
        intro k hk
        have hBound : k + 1 ≤ (e :: tail).length := by
          simp only [List.length_cons]
          omega
        have hAtPrefix := hMerge (k + 1) hBound
        have hTake :
            (e :: tail).take (k + 1) =
              e :: tail.take k := by
          simp
        rw [hTake] at hAtPrefix
        change GrantDrainWarmMergeSpent ring
          (grantDrainD6GhostWord ring fresh update
            (grantDrainStep ring fresh update s e)
            (grantDrainWarmLabelStep ring fresh update s e
              label) (tail.take k)).1
          (grantDrainD6GhostWord ring fresh update
            (grantDrainStep ring fresh update s e)
            (grantDrainWarmLabelStep ring fresh update s e
              label) (tail.take k)).2 at hAtPrefix
        exact hAtPrefix
      have hTailBound :=
        ih (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)
          hCleanTail hMergeTail
          hNextBudget hNextCoherent hNextPhysical
      change
        grantDrainChargedWarmRank ring
          (grantDrainD6GhostWord ring fresh update
            (grantDrainStep ring fresh update s e)
            (grantDrainWarmLabelStep ring fresh update s e label)
            tail).1
          (grantDrainD6GhostWord ring fresh update
            (grantDrainStep ring fresh update s e)
            (grantDrainWarmLabelStep ring fresh update s e label)
            tail).2 ≤
        grantDrainChargedWarmRank ring s label
      exact Nat.le_trans hTailBound hOneStep

/-- D.6 entrance with an explicit valid prepaid birth budget.
This is the exact W plus credits of the initial true-reserve
ghost, followed by finite-word charged monotonicity. -/
theorem grantDrainD6ChargedWarmRankEntranceWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (g : Fin n) (birthBudget : Nat)
    (word : List (Fin n))
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hBudget : GrantDrainD6BirthBudget ring s
      (grantDrainD6MergeInitialLabel g true birthBudget))
    (hClean : ∀ k : Nat, k ≤ word.length →
      C_native ring
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true birthBudget)
          (word.take k)).1.native)
    (hMerge : ∀ k : Nat, k ≤ word.length →
      GrantDrainWarmMergeSpent ring
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true birthBudget)
          (word.take k)).1
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true birthBudget)
          (word.take k)).2) :
    grantDrainChargedWarmRank ring
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true birthBudget)
        word).1
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true birthBudget)
        word).2 ≤
      grantDrainWarmRank ring s.native g +
        birthBudget + 2 * (n - 2) := by
  have hCoherent :=
    grantDrainD6HostCoherentInitial
      s g birthBudget hGrant
  have hPhysical :=
    grantDrainD6PhysicalWarmHostInitial
      s g birthBudget hWarm
  have hWord :=
    grantDrainD6ChargedWarmRankWord
      ring hn fresh update word s
      (grantDrainD6MergeInitialLabel g true birthBudget)
      hClean hMerge hBudget hCoherent hPhysical
  rw [grantDrainD6ChargedEntranceExact
    ring s g birthBudget hGrant] at hWord
  exact hWord

/-- The full n prepaid allowance discharges the entrance
birth-budget premise from the physical n-slot bound. -/
theorem grantDrainD6ChargedWarmRankEntranceFull
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (g : Fin n) (word : List (Fin n))
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hClean : ∀ k : Nat, k ≤ word.length →
      C_native ring
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true n)
          (word.take k)).1.native)
    (hMerge : ∀ k : Nat, k ≤ word.length →
      GrantDrainWarmMergeSpent ring
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true n)
          (word.take k)).1
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true n)
          (word.take k)).2) :
    grantDrainChargedWarmRank ring
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n)
        word).1
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n)
        word).2 ≤
      grantDrainWarmRank ring s.native g + n +
        2 * (n - 2) := by
  have hBudget :=
    grantDrainD6BirthBudgetInitialFull
      ring s (grantDrainD6MergeInitialLabel g true n) rfl
  exact grantDrainD6ChargedWarmRankEntranceWord
    ring hn fresh update s g n word
    hWarm hGrant hBudget hClean hMerge

/-- The alternative n-1 entrance allowance is also valid:
the tracked site itself occupies one of the n GRANT slots. -/
theorem grantDrainD6ChargedWarmRankEntranceMinusOne
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (g : Fin n) (word : List (Fin n))
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hClean : ∀ k : Nat, k ≤ word.length →
      C_native ring
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true (n - 1))
          (word.take k)).1.native)
    (hMerge : ∀ k : Nat, k ≤ word.length →
      GrantDrainWarmMergeSpent ring
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true (n - 1))
          (word.take k)).1
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true (n - 1))
          (word.take k)).2) :
    grantDrainChargedWarmRank ring
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true (n - 1))
        word).1
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true (n - 1))
        word).2 ≤
      grantDrainWarmRank ring s.native g + (n - 1) +
        2 * (n - 2) := by
  have hBudget :=
    grantDrainD6BirthBudgetInitialMinusOne
      ring (by omega : 1 ≤ n) s
      (grantDrainD6MergeInitialLabel g true (n - 1)) rfl
  exact grantDrainD6ChargedWarmRankEntranceWord
    ring hn fresh update s g (n - 1) word
    hWarm hGrant hBudget hClean hMerge

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6PhysicalWarmHostStep
#print axioms L3.GrantDrainEntrance.grantDrainD6PhysicalWarmHostInitial
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedNoFireFixedOrdinary
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedNoFireFixedExceptional
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedNoFireFixedHost
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedMovingHost
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedEntranceExact
#print axioms L3.GrantDrainEntrance.grantDrainD6GhostWordBudgetCoherent
#print axioms L3.GrantDrainEntrance.grantDrainD6FireSelectedBirthSite
#print axioms L3.GrantDrainEntrance.grantDrainD6FireSurvivingHostAvoidsBirth
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedFireFixedHost
#print axioms L3.GrantDrainEntrance.grantDrainD6HostChangedOnlyResponderToSource
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedWarmRankStep
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedWarmRankWord
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedWarmRankEntranceWord
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedWarmRankEntranceFull
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedWarmRankEntranceMinusOne

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
These statements certify a genuine restricted
class of native/ghost transitions; they do not assert unproved
multi-leader native-E-and-birth closure or interacting spent-reserve
closure. The two general obligations are left explicit below.
-/

/-- An already proved physical native-clean row, covering a
singleton leader, a quiet/empty source and follower responder,
or a responder leader killed by the literal E before any birth. -/
def GrantDrainD6CertifiedNoFireRow
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e : Fin n) : Prop :=
  grantDrainSelect ring s e = .none ∧
  (OneNativeLeader s.native ∨
    (((s.native (ring.rightNeighbor e)).l = false ∧
      (s.native e).b = (0 : Fin 3) ∧
      ((s.native e).l = false ∨ (s.native e).sg = false)) ∨
     ((s.native (ring.rightNeighbor e)).l = true ∧
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false)))

/-- Actual physical C_native closure for all three certified rows.
The proof uses the old multi-leader G1/G2 theorems, and the existing
singleton theorem; no global preservation fact is assumed. -/
theorem grantDrainD6CertifiedNoFireRowPreservesC
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hRow : GrantDrainD6CertifiedNoFireRow ring s e) :
    C_native ring
      (grantDrainStep ring fresh update s e).native := by
  rcases hRow with ⟨hNone, hShape⟩
  rcases hShape with hOne | hOther
  · exact grantDrainStepSingletonNoBirthPreserves_C_native
      ring hn fresh update s e hOne hC hNone
  · have hE : C_native ring (nativeE ring s.native e) :=
      grantDrainD6NativeECNativeOfRows
        ring hn s e hC hOther
    change C_native ring (grantDrainNativeNext ring s e)
    simpa [grantDrainNativeNext, hNone] using hE

/-- Any failure of universal C_native preservation is forced
outside the three already established no-FIRE native rows.
In particular, multi-leader inner-bullet and selected-birth cases
are the only unproved source classes remaining after this cut. -/
theorem grantDrainD6CNativeFailureOnlyUncertified
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hBad :
      ¬ C_native ring
        (grantDrainStep ring fresh update s e).native) :
    grantDrainSelect ring s e ≠ .none ∨
    (¬ OneNativeLeader s.native ∧
      ¬ (((s.native (ring.rightNeighbor e)).l = false ∧
          (s.native e).b = (0 : Fin 3) ∧
          ((s.native e).l = false ∨ (s.native e).sg = false)) ∨
         ((s.native (ring.rightNeighbor e)).l = true ∧
          (nativeE ring s.native e
            (ring.rightNeighbor e)).l = false))) := by
  by_cases hNone : grantDrainSelect ring s e = .none
  · right
    constructor
    · intro hOne
      have hGood :=
        grantDrainStepSingletonNoBirthPreserves_C_native
          ring hn fresh update s e hOne hC hNone
      exact hBad hGood
    · intro hKnown
      have hE :=
        grantDrainD6NativeECNativeOfRows
          ring hn s e hC hKnown
      have hGood :
          C_native ring
            (grantDrainStep ring fresh update s e).native := by
        change C_native ring (grantDrainNativeNext ring s e)
        simpa [grantDrainNativeNext, hNone] using hE
      exact hBad hGood
  · exact Or.inl hNone

/-- A certified no-FIRE row also avoids spending the exceptional
reserve, and, if that reserve was already spent, avoids the OLD
inclusive warm leader/bullet scan of the named host.
These latter conditions concern the actual label, not a dummy g. -/
def GrantDrainD6CertifiedNoFireEdge
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n) : Prop :=
  GrantDrainD6CertifiedNoFireRow ring s e ∧
  (∀ g : Fin n, label.host = some g →
    label.exceptionalLeft = true →
    grantDrainExceptionalDeath ring s e g = false) ∧
  (∀ g : Fin n, label.host = some g →
    label.exceptionalLeft = false →
    ∀ k : Nat,
      k ≤ grantDrainLeftLeaderDistance ring s.native g →
      PPL.shiftLeft ring g k ≠ e ∧
      PPL.shiftLeft ring g k ≠ ring.rightNeighbor e)

/-- Actual two-state MergeSpent preservation under the certified
local guards, including the previously spent-reserve alternative.
A violation would have to be an exceptional old hit or a contact
inside the old inclusive scan, contradicting the certified guards. -/
theorem grantDrainD6CertifiedNoFireEdgePreservesSpent
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hSafe : GrantDrainD6CertifiedNoFireEdge ring s e label) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  by_cases hGood :
      GrantDrainWarmMergeSpent ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label)
  · exact hGood
  · rcases grantDrainD6MergeFailureDichotomy
        ring fresh update s e label hInv hGood with
      hExceptional | hContact
    · obtain ⟨g, hHost, hReserve, hHit⟩ := hExceptional
      have hNo := hSafe.2.1 g hHost hReserve
      rw [hNo] at hHit
      cases hHit
    · obtain ⟨g, hHost, hSpent, k, hk, hAt⟩ := hContact
      have hOutside := hSafe.2.2 g hHost hSpent k hk
      rcases hAt with hSource | hResponder
      · exact False.elim (hOutside.1 hSource)
      · exact False.elim (hOutside.2 hResponder)

/-- Certified nontrivial simultaneous physical C_native and ghost
MergeSpent closure. The two conclusions are about actual successors. -/
theorem grantDrainD6CertifiedNoFireEdgePreservesBoth
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hSafe : GrantDrainD6CertifiedNoFireEdge ring s e label) :
    C_native ring
      (grantDrainStep ring fresh update s e).native ∧
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  exact ⟨grantDrainD6CertifiedNoFireRowPreservesC
      ring hn fresh update s e hC hSafe.1,
    grantDrainD6CertifiedNoFireEdgePreservesSpent
      ring fresh update s e label hInv hSafe⟩


/-- A recursive certificate for an actual finite service word:
every edge is checked against the native state and label at the
corresponding cut, not against a frozen entrance configuration. -/
def GrantDrainD6CertifiedNoFireWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    GrantDrainState n Scratch →
    GrantDrainWarmLabel n → List (Fin n) → Prop
  | _, _, [] => True
  | s, label, e :: rest =>
      GrantDrainD6CertifiedNoFireEdge ring s e label ∧
      GrantDrainD6CertifiedNoFireWord ring fresh update
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label)
        rest

/-- On this certified service-word class, the two missing
invariants do propagate, unconditionally from their initial
values, without postulating their preservation at intermediate cuts.
The certified-word premise is stronger than mere reachability. -/
theorem grantDrainD6CertifiedNoFireWordPreservesBoth
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainWarmLabel n),
      C_native ring s.native →
      GrantDrainWarmMergeSpent ring s label →
      GrantDrainD6CertifiedNoFireWord ring fresh update
        s label word →
      C_native ring
        (grantDrainD6GhostWord ring fresh update s label word).1.native ∧
      GrantDrainWarmMergeSpent ring
        (grantDrainD6GhostWord ring fresh update s label word).1
        (grantDrainD6GhostWord ring fresh update s label word).2 := by
  intro word
  induction word with
  | nil =>
      intro s label hC hInv _
      exact ⟨hC, hInv⟩
  | cons e rest ih =>
      intro s label hC hInv hSafe
      change
        GrantDrainD6CertifiedNoFireEdge ring s e label ∧
        GrantDrainD6CertifiedNoFireWord ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)
          rest at hSafe
      have hNext :=
        grantDrainD6CertifiedNoFireEdgePreservesBoth
          ring hn fresh update s e label hC hInv hSafe.1
      have hTail :=
        ih (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)
          hNext.1 hNext.2 hSafe.2
      simpa only [grantDrainD6GhostWord, List.foldl_cons]
        using hTail

/-- For certified full words, the other three invariants are
propagated by the earlier lemmas and the charged step is assembled
by the charged-step assembly. This is a genuine word result without separately
supplied C_native or MergeSpent at each prefix state. -/
theorem grantDrainD6CertifiedNoFireWordCharged
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainWarmLabel n),
      C_native ring s.native →
      GrantDrainWarmMergeSpent ring s label →
      GrantDrainD6BirthBudget ring s label →
      GrantDrainD6HostCoherent s label →
      GrantDrainD6PhysicalWarmHost s label →
      GrantDrainD6CertifiedNoFireWord ring fresh update
        s label word →
      grantDrainChargedWarmRank ring
        (grantDrainD6GhostWord ring fresh update s label word).1
        (grantDrainD6GhostWord ring fresh update s label word).2 ≤
      grantDrainChargedWarmRank ring s label := by
  intro word
  induction word with
  | nil =>
      intro s label _ _ _ _ _ _
      exact Nat.le_refl _
  | cons e rest ih =>
      intro s label hC hInv hBudget hCoherent hPhysical hSafe
      change
        GrantDrainD6CertifiedNoFireEdge ring s e label ∧
        GrantDrainD6CertifiedNoFireWord ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)
          rest at hSafe
      have hNativeAndSpent :=
        grantDrainD6CertifiedNoFireEdgePreservesBoth
          ring hn fresh update s e label hC hInv hSafe.1
      have hBudgetNext :=
        grantDrainD6BirthBudgetStepOfCoherent
          ring hn fresh update s e label hBudget hCoherent
      have hCoherentNext :=
        grantDrainD6HostCoherentStep
          ring hn fresh update s e label hCoherent
      have hPhysicalNext :=
        grantDrainD6PhysicalWarmHostStep
          ring fresh update s e label
      have hSingle :=
        grantDrainD6ChargedWarmRankStep
          ring hn fresh update s e label
          hC hInv hBudget hCoherent hPhysical
      have hRest :=
        ih (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)
          hNativeAndSpent.1 hNativeAndSpent.2
          hBudgetNext hCoherentNext hPhysicalNext hSafe.2
      have hBound := Nat.le_trans hRest hSingle
      simpa only [grantDrainD6GhostWord, List.foldl_cons]
        using hBound

/-- An entrance theorem without externally supplied prefix
C_native/MergeSpent premises, for the explicitly certified trace
class. The conclusion includes the two final-state invariants
and the full-n prepaid charged-rank bound. -/
theorem grantDrainD6CertifiedNoFireEntranceBound
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (g : Fin n) (word : List (Fin n))
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hSafe :
      GrantDrainD6CertifiedNoFireWord ring fresh update
        s (grantDrainD6MergeInitialLabel g true n) word) :
    C_native ring
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n)
        word).1.native ∧
    GrantDrainWarmMergeSpent ring
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n) word).1
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n) word).2 ∧
    grantDrainChargedWarmRank ring
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n) word).1
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n) word).2 ≤
      grantDrainWarmRank ring s.native g + n +
        2 * (n - 2) := by
  have hInv :=
    grantDrainD6MergeInitially ring s g true n
  have hBudget :=
    grantDrainD6BirthBudgetInitialFull
      ring s (grantDrainD6MergeInitialLabel g true n) rfl
  have hCoherent :=
    grantDrainD6HostCoherentInitial
      s g n hGrant
  have hPhysical :=
    grantDrainD6PhysicalWarmHostInitial
      s g n hWarm
  have hBoth :=
    grantDrainD6CertifiedNoFireWordPreservesBoth
      ring hn fresh update word s
      (grantDrainD6MergeInitialLabel g true n)
      hC hInv hSafe
  have hCharged :=
    grantDrainD6CertifiedNoFireWordCharged
      ring hn fresh update word s
      (grantDrainD6MergeInitialLabel g true n)
      hC hInv hBudget hCoherent hPhysical hSafe
  rw [grantDrainD6ChargedEntranceExact
    ring s g n hGrant] at hCharged
  exact ⟨hBoth.1, hBoth.2, hCharged⟩

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6CertifiedNoFireRowPreservesC
#print axioms L3.GrantDrainEntrance.grantDrainD6CNativeFailureOnlyUncertified
#print axioms L3.GrantDrainEntrance.grantDrainD6CertifiedNoFireEdgePreservesSpent
#print axioms L3.GrantDrainEntrance.grantDrainD6CertifiedNoFireEdgePreservesBoth
#print axioms L3.GrantDrainEntrance.grantDrainD6CertifiedNoFireWordPreservesBoth
#print axioms L3.GrantDrainEntrance.grantDrainD6CertifiedNoFireWordCharged
#print axioms L3.GrantDrainEntrance.grantDrainD6CertifiedNoFireEntranceBound

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! A complete eligible-birth closure
from the three existing settled-sector split lemmas. -/

/-- Every eligible interior follower split yields two individually
settled NEW sectors, regardless of which side of the birth
contains the unique OLD bullet. -/
theorem grantDrainD6EligibleBirthSplitSettled
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p z : Fin n)
    (d : Fin (n + 1)) (k : Nat)
    (hC : C_native ring N)
    (hOld : sectorLength ring N p d)
    (hk : 0 < k) (hInside : k < d.val)
    (hz : z = PPL.shiftRight ring p k)
    (hzEmpty : (N z).b = (0 : Fin 3)) :
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
  have hSettled :=
    ((grantDrainC_native_iff_sectors ring N).mp hC).2
      p d hOld
  rcases hSettled.2.2 with
    ⟨h, hh, hb, _, _⟩ | ⟨hNo, _, _⟩
  · by_cases hBefore : h.val < k
    · exact grantDrainSettledBirthBeforeBulletSplit
        ring N p z d k h hz hk hInside hBefore hb hOld hSettled
    · by_cases hAfter : k < h.val
      · exact grantDrainSettledBirthAfterBulletSplit
          ring N p z d k h hz hk hInside hAfter hh hb
          hOld hSettled
      · have hEq : h.val = k := by omega
        have hAt : PPL.shiftRight ring p h.val = z := by
          rw [hEq]
          exact hz.symm
        rw [hAt] at hb
        unfold HasBullet at hb
        exact False.elim (hb hzEmpty)
  · exact grantDrainSettledCanonicalBirthBulletFreeSplit
      ring N p z d k hz hk hInside hOld hSettled hNo

/-- A canonical birth at an OLD empty follower preserves every
settled sector in a multi-leader ring. For the newborn-root
sector we use the right half of the old enclosing sector; for
an old root we use either the left split or a full old-sector
frame. This is unconditional in the number of OLD leaders. -/
theorem grantDrainD6EligibleCanonicalBirthPreservesC
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z : Fin n)
    (hC : C_native ring N)
    (hzFollower : (N z).l = false)
    (hzEmpty : (N z).b = (0 : Fin 3)) :
    C_native ring (canonicalBirth N z) := by
  have hOldLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hC.1
  have hNewLocal :=
    grantDrainEntranceILocalCanonicalBirth
      ring N z hOldLocal
  have hNewI : I ring (canonicalBirth N z) :=
    (grantDrainEntranceIffILocal
      ring (canonicalBirth N z)).mpr hNewLocal
  apply (grantDrainC_native_iff_sectors
    ring (canonicalBirth N z)).mpr
  refine ⟨hNewI.1, ?_⟩
  intro p d hNewSector
  by_cases hpz : p = z
  · subst p
    obtain ⟨q, D, a, hOldSector, haInside, hAt⟩ :=
      grantDrainEntranceSectorCoverOfRoot
        ring N hC.1.1.1 z
    have haPos : 0 < a.val := by
      by_cases hZero : a.val = 0
      · have hEq : z = q := by
          rw [hAt, hZero]
          exact grantDrainEntranceR8eShiftZero ring q
        have hLeader : (N z).l = true := by
          rw [hEq]
          exact hOldSector.2.1
        rw [hzFollower] at hLeader
        cases hLeader
      · omega
    have hSplit :=
      grantDrainD6EligibleBirthSplitSettled
        ring N q z D a.val hC hOldSector haPos
        haInside hAt hzEmpty
    have hUnique :=
      grantDrainEntranceR8eSectorLengthUnique
        ring (canonicalBirth N z) z d
        (⟨D.val - a.val, show D.val - a.val < n + 1 by omega⟩ :
          Fin (n + 1)) hNewSector hSplit.2.1
    rw [hUnique]
    exact hSplit.2.2
  · have hpOld : (N p).l = true := by
      have hRoot : (canonicalBirth N z p).l = true :=
        hNewSector.2.1
      rw [grantDrainEntranceCanonicalBirthFrame N z p hpz]
        at hRoot
      exact hRoot
    obtain ⟨D, hOldSector⟩ :=
      grantDrainEntranceR8eSectorAtLeader
        ring N hC.1.1.1 p hpOld
    have hkLt : PPL.cyclicOffset ring p z < n :=
      grantDrainEntranceArcOffsetLt ring p z
    have hzAt :
        z = PPL.shiftRight ring p
          (PPL.cyclicOffset ring p z) :=
      (grantDrainMarksArcShiftRightOffset ring p z).symm
    have hkPos : 0 < PPL.cyclicOffset ring p z := by
      by_cases hZero : PPL.cyclicOffset ring p z = 0
      · have hpEq : z = p := by
          rw [hzAt, hZero]
          exact grantDrainEntranceR8eShiftZero ring p
        exact False.elim (hpz hpEq.symm)
      · omega
    by_cases hInside :
        PPL.cyclicOffset ring p z < D.val
    · have hSplit :=
        grantDrainD6EligibleBirthSplitSettled
          ring N p z D (PPL.cyclicOffset ring p z)
          hC hOldSector hkPos hInside hzAt hzEmpty
      have hUnique :=
        grantDrainEntranceR8eSectorLengthUnique
          ring (canonicalBirth N z) p d
          (⟨PPL.cyclicOffset ring p z,
            show PPL.cyclicOffset ring p z < n + 1 by omega⟩ :
            Fin (n + 1)) hNewSector hSplit.1.1
      rw [hUnique]
      exact hSplit.1.2
    · have hNotEnd :
          D.val ≠ PPL.cyclicOffset ring p z := by
        intro hEq
        have hEnd : (N z).l = true := by
          rw [hzAt, ← hEq]
          exact hOldSector.2.2.1
        rw [hzFollower] at hEnd
        cases hEnd
      have hAway :
          ∀ j : Nat, j ≤ D.val →
            PPL.shiftRight ring p j ≠ z := by
        intro j hj
        rw [hzAt]
        exact grantDrainWeakDeathShiftRightNe
          ring p j (PPL.cyclicOffset ring p z)
          (by omega : j < n) hkLt (by omega)
      have hFramed :=
        grantDrainCanonicalBirthFramesSettledSector
          ring N z p D hOldSector
          (((grantDrainC_native_iff_sectors
            ring N).mp hC).2 p D hOldSector) hAway
      have hUnique :=
        grantDrainEntranceR8eSectorLengthUnique
          ring (canonicalBirth N z) p d D
          hNewSector hFramed.1
      rw [hUnique]
      exact hFramed.2

/-- The canonical FIRE part of a genuine D.6 physical step is
settled for every number of OLD leaders, provided E itself has
produced a clean native configuration. It uses the actual
post-E birth eligibility guaranteed by grantDrainSelect. -/
theorem grantDrainD6SelectedFirePreservesCOfE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hE : C_native ring (nativeE ring s.native e))
    (hFire : grantDrainSelect ring s e ≠ .none) :
    C_native ring
      (grantDrainStep ring fresh update s e).native := by
  obtain ⟨z, _, hNext, hEligible⟩ :=
    grantDrainD6SelectedBirthEligible ring s e hFire
  have hzFollower :
      (nativeE ring s.native e z).l = false := by
    cases hL : (nativeE ring s.native e z).l with
    | false => rfl
    | true =>
        simp [grantDrainEligible, hL] at hEligible
  have hzVal :
      (nativeE ring s.native e z).b.val = 0 := by
    simpa [grantDrainEligible, hzFollower] using hEligible
  have hzEmpty :
      (nativeE ring s.native e z).b = (0 : Fin 3) := by
    apply Fin.ext
    exact hzVal
  change C_native ring (grantDrainNativeNext ring s e)
  rw [hNext]
  exact grantDrainD6EligibleCanonicalBirthPreservesC
    ring (nativeE ring s.native e) z hE hzFollower hzEmpty


/-- Restated publicly from the private
R8e monotone-suffix proofs, so the E closure has no private
cross-file dependencies. -/
theorem grantDrainD6PatternOfMonotoneSignals
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n) :
    ∀ (fuel start : Nat),
      start + fuel ≤ n →
      (∀ r k : Nat, start ≤ r → r < k →
        k < start + fuel →
        (N (PPL.shiftRight ring p r)).sg = true →
        (N (PPL.shiftRight ring p k)).sg = true) →
      signalZeroStarOneStar ring N p start (start + fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start hBound hMonotone
      refine ⟨⟨start, show start < n + 1 by omega⟩, ?_, ?_, ?_, ?_⟩
      · change start ≤ start
        exact Nat.le_refl start
      · change start ≤ start + 0
        omega
      · intro k hk hlt
        change k.val < start at hlt
        omega
      · intro k hk hlt
        change start ≤ k.val at hk
        change k.val < start + 0 at hlt
        omega
  | succ fuel ih =>
      intro start hBound hMonotone
      by_cases hFirst :
          (N (PPL.shiftRight ring p start)).sg = true
      · refine ⟨⟨start, show start < n + 1 by omega⟩, ?_, ?_, ?_, ?_⟩
        · change start ≤ start
          exact Nat.le_refl start
        · change start ≤ start + Nat.succ fuel
          omega
        · intro k hk hlt
          change k.val < start at hlt
          omega
        · intro k hk hlt
          change start ≤ k.val at hk
          by_cases hEq : k.val = start
          · rw [hEq]
            exact hFirst
          · exact hMonotone start k.val
              (Nat.le_refl _) (by omega) hlt hFirst
      · have hFalse :
            (N (PPL.shiftRight ring p start)).sg = false := by
          cases hs : (N (PPL.shiftRight ring p start)).sg with
          | false => rfl
          | true => exact False.elim (hFirst hs)
        have hTailMonotone :
            ∀ r k : Nat, start + 1 ≤ r → r < k →
              k < start + 1 + fuel →
              (N (PPL.shiftRight ring p r)).sg = true →
              (N (PPL.shiftRight ring p k)).sg = true := by
          intro r k hr hrk hk hOne
          exact hMonotone r k (by omega) hrk (by omega) hOne
        have hTail := ih (start + 1)
          (by omega) hTailMonotone
        rcases hTail with ⟨cut, hLo, hHi, hZeros, hOnes⟩
        refine ⟨cut, (by omega), (by omega), ?_, ?_⟩
        · intro k hk hlt
          by_cases hEq : k.val = start
          · rw [hEq]
            exact hFalse
          · exact hZeros k (by omega) hlt
        · intro k hk hlt
          exact hOnes k hk (by omega)

theorem grantDrainD6SuffixFromNoDefects
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hNoDefect : ∀ v : Fin n,
      ¬ GrantDrainEntranceSignalDefect ring N v)
    (p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring N p d)
    (lo : Nat) (hLo : 1 ≤ lo) (hHi : lo ≤ d.val)
    (hAfterBullet :
      ∀ j : Fin n, j.val < d.val →
        HasBullet N (PPL.shiftRight ring p j.val) →
        j.val < lo) :
    signalZeroStarOneStar ring N p lo d.val := by
  have hBound : d.val ≤ n := by omega
  have hMonotone :
      ∀ r k : Nat, lo ≤ r → r < k → k < d.val →
        (N (PPL.shiftRight ring p r)).sg = true →
        (N (PPL.shiftRight ring p k)).sg = true := by
    intro r k hr hrk hk hOne
    cases hKSignal : (N (PPL.shiftRight ring p k)).sg with
    | true => rfl
    | false =>
        have hrn : r < n := by omega
        have hkn : k < n := by omega
        have hSuffix :
            GrantDrainEntranceSignalSuffixSite ring N p d
              (⟨r, hrn⟩ : Fin n) := by
          refine ⟨hSector, ?_, ?_, ?_⟩
          · change 1 ≤ r
            omega
          · change r < d.val
            omega
          · intro j hj hBullet
            have hjBefore := hAfterBullet j hj hBullet
            change j.val < r
            omega
        have hDefect :
            GrantDrainEntranceCountedZero ring N
              (PPL.shiftRight ring p k) := by
          exact ⟨p, d, (⟨r, hrn⟩ : Fin n),
            (⟨k, hkn⟩ : Fin n), hSuffix,
            rfl, hrk, hk, hKSignal, hOne⟩
        exact False.elim
          (hNoDefect (PPL.shiftRight ring p k)
            (Or.inl hDefect))
  have hFuelBound : lo + (d.val - lo) ≤ n := by omega
  have hPatternMonotone :
      ∀ r k : Nat, lo ≤ r → r < k →
        k < lo + (d.val - lo) →
        (N (PPL.shiftRight ring p r)).sg = true →
        (N (PPL.shiftRight ring p k)).sg = true := by
    intro r k hr hrk hk hOne
    exact hMonotone r k hr hrk (by omega) hOne
  have hPattern :=
    grantDrainD6PatternOfMonotoneSignals
      ring N p (d.val - lo) lo hFuelBound
      hPatternMonotone
  have hSame : lo + (d.val - lo) = d.val := by omega
  rw [hSame] at hPattern
  exact hPattern

theorem grantDrainD6CNativeOfIAndNoSignalDefect
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hOldI : I ring N)
    (hNoDefect : ∀ v : Fin n,
      ¬ GrantDrainEntranceSignalDefect ring N v) :
    C_native ring N := by
  refine ⟨hOldI, ?_⟩
  intro p d hSector
  have hOldSector := hOldI.2 p d hSector
  by_cases hBullet :
      ∃ a : Fin n, a.val < d.val ∧
        HasBullet N (PPL.shiftRight ring p a.val)
  · rcases hBullet with ⟨a, ha, hOccupied⟩
    have hAfter :
        ∀ j : Fin n, j.val < d.val →
          HasBullet N (PPL.shiftRight ring p j.val) →
          j.val < a.val + 1 := by
      intro j hj hJ
      have hSame := hOldSector.1 a j ha hj hOccupied hJ
      have hVal := congrArg Fin.val hSame
      omega
    have hPattern :=
      grantDrainD6SuffixFromNoDefects
        ring N hNoDefect p d hSector
        (a.val + 1) (by omega) (by omega) hAfter
    exact Or.inl
      ⟨a, ha, hOccupied,
        hOldSector.2 a ha hOccupied, hPattern⟩
  · have hEmpty :
        ∀ a : Fin n, a.val < d.val →
          ¬ HasBullet N
            (PPL.shiftRight ring p a.val) := by
      intro a ha hb
      exact hBullet ⟨a, ha, hb⟩
    have hAfter :
        ∀ j : Fin n, j.val < d.val →
          HasBullet N (PPL.shiftRight ring p j.val) →
          j.val < 1 := by
      intro j hj hJ
      exact False.elim (hEmpty j hj hJ)
    have hdPositive : 0 < d.val := hSector.1
    have hOneBound : 1 ≤ d.val := by omega
    have hPattern :=
      grantDrainD6SuffixFromNoDefects
        ring N hNoDefect p d hSector
        1 (Nat.le_refl 1) hOneBound hAfter
    have hReadyCondition :
        (N p).sg = true →
        ∀ k : Fin n, 1 ≤ k.val → k.val < d.val →
          (N (PPL.shiftRight ring p k.val)).sg =
            true := by
      intro hReady k hkFirst hkInside
      have hNoMismatch :
          ¬ GrantDrainEntranceReadyMismatch ring N
            (ring.rightNeighbor p) := by
        intro hm
        exact hNoDefect (ring.rightNeighbor p) (Or.inr hm)
      have hFirstTrue :
          (N (ring.rightNeighbor p)).sg = true := by
        cases hs : (N (ring.rightNeighbor p)).sg with
        | true => rfl
        | false =>
            have hMismatch :
                GrantDrainEntranceReadyMismatch ring N
                  (ring.rightNeighbor p) := by
              exact ⟨p, d, hSector, (by omega), rfl,
                hEmpty, hReady, hs⟩
            exact False.elim (hNoMismatch hMismatch)
      rcases hPattern with ⟨cut, hCutLo, hCutHi, hZeros, hOnes⟩
      have hCut : cut.val ≤ 1 := by
        by_cases hc : cut.val ≤ 1
        · exact hc
        · have hOneInRing : 1 < n := by omega
          have hOneBefore :
              (⟨1, hOneInRing⟩ : Fin n).val < cut.val := by
            change 1 < cut.val
            omega
          have hZeroFirst :
              (N (PPL.shiftRight ring p 1)).sg =
                false :=
            hZeros (⟨1, hOneInRing⟩ : Fin n)
              (Nat.le_refl 1) hOneBefore
          have hRightSite :
              PPL.shiftRight ring p 1 = ring.rightNeighbor p := rfl
          rw [hRightSite, hFirstTrue] at hZeroFirst
          cases hZeroFirst
      exact hOnes k (by omega) hkInside
    exact Or.inr ⟨hEmpty, hPattern, hReadyCondition⟩

/-- Native E preserves every clean sector for all n ≥ 5,
including arbitrary many native leaders, a ready source emitting
LIVE, a resident moving bullet, an unready leader responder,
and the leader-death sector merge. No case is omitted: the
existing backward-defect theorem controls all E rows pointwise. -/
theorem grantDrainD6NativeEPreservesC
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hC : C_native ring N) :
    C_native ring (nativeE ring N e) := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hC.1
  have hNewLocal :=
    grantDrainEntranceILocalNativeEAll
      ring (by omega : 3 ≤ n) N e hLocal
  have hNewI : I ring (nativeE ring N e) :=
    (grantDrainEntranceIffILocal
      ring (nativeE ring N e)).mpr hNewLocal
  have hNoDefect :
      ∀ v : Fin n,
        ¬ GrantDrainEntranceSignalDefect ring
          (nativeE ring N e) v := by
    intro v hDef
    have hBack :=
      (grantDrainEntranceR8eDefectBackward
        ring (by omega : 3 ≤ n) N e hC.1 v).1
    exact (grantDrainEntranceCleanNoSignalDefect
      ring N hC v) (hBack hDef)
  exact grantDrainD6CNativeOfIAndNoSignalDefect
    ring (nativeE ring N e) hNewI hNoDefect

/-- Obligation C: the genuine physical step preserves
C_native for any number of OLD leaders and any selected grant.
The no-FIRE branch is native E; on a FIRE the post-E eligible
newborn is handled by the clean-sector split theorem. -/
theorem grantDrainStepPreservesC_native
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native) :
    C_native ring
      (grantDrainStep ring fresh update s e).native := by
  have hE :=
    grantDrainD6NativeEPreservesC ring hn s.native e hC
  by_cases hNone : grantDrainSelect ring s e = .none
  · change C_native ring (grantDrainNativeNext ring s e)
    simpa [grantDrainNativeNext, hNone] using hE
  · exact grantDrainD6SelectedFirePreservesCOfE
      ring fresh update s e hE hNone

/-- Obligation C along every actual physical/ghost service word,
without prefix certificates. This is the native component of
the exact foldl word, independent of label protection. -/
theorem grantDrainD6GhostWordPreservesC
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainWarmLabel n),
      C_native ring s.native →
      C_native ring
        (grantDrainD6GhostWord ring fresh update s label word).1.native := by
  intro word
  induction word with
  | nil =>
      intro s label hC
      exact hC
  | cons e rest ih =>
      intro s label hC
      have hNext :=
        grantDrainStepPreservesC_native
          ring hn fresh update s e hC
      simpa only [grantDrainD6GhostWord, List.foldl_cons]
        using ih
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)
          hNext

/-- Because the full physical native array is now proved
clean along all words, the charged word theorem needs
only the remaining MergeSpent certificates at each prefix.
No C_native certificate is supplied at intermediate cuts. -/
theorem grantDrainD6ChargedWordOfMergeSpentPrefixes
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (word : List (Fin n))
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hMerge : ∀ k : Nat, k ≤ word.length →
      GrantDrainWarmMergeSpent ring
        (grantDrainD6GhostWord ring fresh update s label
          (word.take k)).1
        (grantDrainD6GhostWord ring fresh update s label
          (word.take k)).2)
    (hBudget : GrantDrainD6BirthBudget ring s label)
    (hCoherent : GrantDrainD6HostCoherent s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label) :
    grantDrainChargedWarmRank ring
      (grantDrainD6GhostWord ring fresh update s label word).1
      (grantDrainD6GhostWord ring fresh update s label word).2 ≤
    grantDrainChargedWarmRank ring s label := by
  have hCleanPrefixes :
      ∀ k : Nat, k ≤ word.length →
      C_native ring
        (grantDrainD6GhostWord ring fresh update s label
          (word.take k)).1.native := by
    intro k _
    exact grantDrainD6GhostWordPreservesC
      ring hn fresh update (word.take k) s label hC
  exact grantDrainD6ChargedWarmRankWord
    ring hn fresh update word s label
    hCleanPrefixes hMerge hBudget hCoherent hPhysical

/-- The only externally supplied prefix safety hypothesis at
the natural D.6 entrance is now MergeSpent. All physical
C_native obligations are discharged by this round. -/
theorem grantDrainD6ChargedEntranceOfMergeSpentPrefixes
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (word : List (Fin n))
    (s : GrantDrainState n Scratch)
    (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (hMerge : ∀ k : Nat, k ≤ word.length →
      GrantDrainWarmMergeSpent ring
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true n)
          (word.take k)).1
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true n)
          (word.take k)).2) :
    grantDrainChargedWarmRank ring
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n) word).1
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n) word).2 ≤
    grantDrainWarmRank ring s.native g + n +
      2 * (n - 2) := by
  have hCleanPrefixes :
      ∀ k : Nat, k ≤ word.length →
      C_native ring
        (grantDrainD6GhostWord ring fresh update s
          (grantDrainD6MergeInitialLabel g true n)
          (word.take k)).1.native := by
    intro k _
    exact grantDrainD6GhostWordPreservesC
      ring hn fresh update (word.take k) s
      (grantDrainD6MergeInitialLabel g true n) hC
  exact grantDrainD6ChargedWarmRankEntranceFull
    ring hn fresh update s g word hWarm hGrant
    hCleanPrefixes hMerge

/-- With unconditional native cleanliness now proved, any X1
MergeSpent failure has only the two exact contact/death
mechanisms. The native successor itself is still C_native.
No general MergeSpent preservation theorem is asserted. -/
theorem grantDrainD6MergeSpentFailureCleanDichotomy
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hFailure :
      ¬ GrantDrainWarmMergeSpent ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label)) :
    C_native ring (grantDrainStep ring fresh update s e).native ∧
      ((∃ g : Fin n,
          label.host = some g ∧
          label.exceptionalLeft = true ∧
          grantDrainExceptionalDeath ring s e g = true) ∨
       (∃ g : Fin n,
          label.host = some g ∧
          label.exceptionalLeft = false ∧
          ∃ k : Nat,
            k ≤ grantDrainLeftLeaderDistance ring s.native g ∧
            (PPL.shiftLeft ring g k = e ∨
             PPL.shiftLeft ring g k =
               ring.rightNeighbor e))) := by
  exact ⟨grantDrainStepPreservesC_native
      ring hn fresh update s e hC,
    grantDrainD6MergeFailureDichotomy
      ring fresh update s e label hInv hFailure⟩


end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6EligibleBirthSplitSettled
#print axioms L3.GrantDrainEntrance.grantDrainD6EligibleCanonicalBirthPreservesC
#print axioms L3.GrantDrainEntrance.grantDrainD6SelectedFirePreservesCOfE
#print axioms L3.GrantDrainEntrance.grantDrainD6PatternOfMonotoneSignals
#print axioms L3.GrantDrainEntrance.grantDrainD6SuffixFromNoDefects
#print axioms L3.GrantDrainEntrance.grantDrainD6CNativeOfIAndNoSignalDefect
#print axioms L3.GrantDrainEntrance.grantDrainD6NativeEPreservesC
#print axioms L3.GrantDrainEntrance.grantDrainStepPreservesC_native
#print axioms L3.GrantDrainEntrance.grantDrainD6GhostWordPreservesC
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedWordOfMergeSpentPrefixes
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedEntranceOfMergeSpentPrefixes
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeSpentFailureCleanDichotomy

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
These declarations close the three genuinely vacuous successor
branches and assemble the already proved off-scan and unspent
branches without assuming an unproved physical row.

They do NOT prove X1.  In particular, nothing below claims that
a spent warm host retains a protected NEW nearest leader after
a selected interacting-pair service, or that exceptional-front
death always transports the shield/bullet witness.  No unconditional
D.6 entrance bound follows from this block.
-/

/-- If the NEW ghost is cold, the spent-front obligation is vacuous.
This is a theorem about the ACTUAL label successor, not about
an assumed physical-sector update. -/
theorem grantDrainD6XOneNextCold
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hCold :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = false) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  intro g hWarm _ _
  rw [hCold] at hWarm
  cases hWarm

/-- A NEW hostless label carries no spent-front obligation. -/
theorem grantDrainD6XOneNextHostless
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hNone :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  intro g _ hHost _
  rw [hNone] at hHost
  cases hHost

/-- When the NEW reserve is still available, MergeSpent
imposes no physical shield, signal, or bullet test. -/
theorem grantDrainD6XOneNextAvailable
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hAvailable :
      (grantDrainWarmLabelStep ring fresh update s e
        label).exceptionalLeft = true) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  intro g _ _ hSpent
  rw [hAvailable] at hSpent
  cases hSpent

/-- Every X1 failure has an ACTIVE, HOSTED, SPENT successor.
Thus the actual Y3 crossing/cold exit is a logically complete
way to discharge a whole interacting-pair branch. -/
theorem grantDrainD6XOneFailureActiveSpent
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hFailure :
      ¬ GrantDrainWarmMergeSpent ring
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)) :
    (grantDrainWarmLabelStep ring fresh update s e
      label).warm = true ∧
    (∃ g : Fin n,
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g) ∧
    (grantDrainWarmLabelStep ring fresh update s e
      label).exceptionalLeft = false := by
  have hWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true := by
    cases hw :
        (grantDrainWarmLabelStep ring fresh update s e
          label).warm with
    | true => rfl
    | false =>
        exact False.elim (hFailure
          (grantDrainD6XOneNextCold
            ring fresh update s e label hw))
  have hHost :
      ∃ g : Fin n,
        (grantDrainWarmLabelStep ring fresh update s e
          label).host = some g := by
    cases hh :
        (grantDrainWarmLabelStep ring fresh update s e
          label).host with
    | none =>
        exact False.elim (hFailure
          (grantDrainD6XOneNextHostless
            ring fresh update s e label hh))
    | some g =>
        exact ⟨g, rfl⟩
  have hSpent :
      (grantDrainWarmLabelStep ring fresh update s e
        label).exceptionalLeft = false := by
    cases hf :
        (grantDrainWarmLabelStep ring fresh update s e
          label).exceptionalLeft with
    | false => rfl
    | true =>
        exact False.elim (hFailure
          (grantDrainD6XOneNextAvailable
            ring fresh update s e label hf))
  exact ⟨hWarm, hHost, hSpent⟩

/-- The four easy OLD cases assemble into one actual physical
step theorem: retired/cold; unspent with no exceptional death;
or spent whose inclusive OLD scan misses both endpoints.
No hidden C_native or merge hypothesis has been added. -/
theorem grantDrainD6XOneEasyCases
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hEasy :
      label.warm = false ∨
      label.host = none ∨
      (label.exceptionalLeft = true ∧
        ∀ g : Fin n, label.host = some g →
          grantDrainExceptionalDeath ring s e g = false) ∨
      (∃ g : Fin n,
        label.warm = true ∧
        label.host = some g ∧
        label.exceptionalLeft = false ∧
        ∀ k : Nat,
          k ≤ grantDrainLeftLeaderDistance ring s.native g →
          PPL.shiftLeft ring g k ≠ e ∧
          PPL.shiftLeft ring g k ≠ ring.rightNeighbor e)) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  rcases hEasy with hCold | hHostless | hAvailable | hOutside
  · have hNewCold :=
      grantDrainD6MergeColdLabelRemainsCold
        ring fresh update s e label hCold
    exact grantDrainD6XOneNextCold
      ring fresh update s e label hNewCold
  · have hNewNone :
        (grantDrainWarmLabelStep ring fresh update s e
          label).host = none := by
      simp [grantDrainWarmLabelStep, hHostless]
    exact grantDrainD6XOneNextHostless
      ring fresh update s e label hNewNone
  · exact grantDrainD6MergeUnspentWithoutExceptional
      ring fresh update s e label hAvailable.1 hAvailable.2
  · rcases hOutside with
      ⟨g, hWarm, hHost, hSpent, hOutside⟩
    exact grantDrainD6MergeSpentOutsidePair
      ring fresh update s label e g
      hInv hWarm hHost hSpent hOutside

/-- Contrapositive interface specialized from the earlier exact
failure dichotomy. Its premises rule out BOTH genuine hard
cases. It does not replace their future geometric proofs. -/
theorem grantDrainD6XOneOfNoHardContact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hNoExceptional :
      ∀ g : Fin n, label.host = some g →
        label.exceptionalLeft = true →
        grantDrainExceptionalDeath ring s e g = false)
    (hNoScan :
      ∀ g : Fin n, label.host = some g →
        label.exceptionalLeft = false →
        ∀ k : Nat,
          k ≤ grantDrainLeftLeaderDistance ring s.native g →
          PPL.shiftLeft ring g k ≠ e ∧
          PPL.shiftLeft ring g k ≠ ring.rightNeighbor e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  classical
  by_cases hNext :
      GrantDrainWarmMergeSpent ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label)
  · exact hNext
  · have hCases :=
      (grantDrainD6MergeSpentFailureCleanDichotomy
        ring hn fresh update s e label hC hInv hNext).2
    rcases hCases with
      ⟨g, hHost, hAvailable, hExceptional⟩ |
      ⟨g, hHost, hSpent, k, hk, hMeet⟩
    · have hImpossible :=
        hNoExceptional g hHost hAvailable
      rw [hImpossible] at hExceptional
      cases hExceptional
    · have hAway :=
        hNoScan g hHost hSpent k hk
      rcases hMeet with hAt | hAt
      · exact False.elim (hAway.1 hAt)
      · exact False.elim (hAway.2 hAt)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainD6XOneNextCold
#print axioms L3.GrantDrainEntrance.grantDrainD6XOneNextHostless
#print axioms L3.GrantDrainEntrance.grantDrainD6XOneNextAvailable
#print axioms L3.GrantDrainEntrance.grantDrainD6XOneFailureActiveSpent
#print axioms L3.GrantDrainEntrance.grantDrainD6XOneEasyCases
#print axioms L3.GrantDrainEntrance.grantDrainD6XOneOfNoHardContact

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
H1.

The proof uses the actual selected native E + canonical FIRE, not
a hypothetical post-state. The protected source of an exceptional
death is supplied by grantDrainWeakDeathFrontRootHolds; the remaining
work is first-leader scan geometry, without assuming that signals
between the old front and the warm host are all zero.
-/

/-- An actual positive nearest-leader arc identifies the shield
of the recomputed first-hit counterclockwise leader. -/
theorem grantDrainD6ShieldedFrontOfNearestArc
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (q g : Fin n)
    (hArc : GrantDrainMarksNearestArc ring N q g)
    (hShield : (N q).sh = true) :
    (N (grantDrainD6MergeFront ring N g)).sh = true := by
  have hShift :
      PPL.shiftLeft ring g (PPL.cyclicOffset ring q g) =
        q := by
    have hR := grantDrainMarksArcShiftRightOffset ring q g
    have h2 := grantDrainMarksArcShiftLeftRight ring q
      (PPL.cyclicOffset ring q g)
      (PPL.cyclicOffset ring q g)
      (Nat.le_refl _)
      (grantDrainEntranceArcOffsetLt ring q g)
    rw [hR] at h2
    rw [h2, Nat.sub_self]
    exact grantDrainWeakDeathShiftRightZero ring q
  change
    (N (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring N g))).sh = true
  rw [grantDrainMarksScanOfNearestArc ring N q g hArc, hShift]
  exact hShield

/-- Only the nearest-LEADER part of the birth-arc theorem is
needed here: the old corridor need not have zero signals. -/
theorem grantDrainD6NearestArcAfterBirth
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (q g z : Fin n) (j : Nat)
    (hArc : GrantDrainMarksNearestArc ring N q g)
    (hSite : z = PPL.shiftRight ring q j)
    (hInside : j < PPL.cyclicOffset ring q g) :
    GrantDrainMarksNearestArc ring (canonicalBirth N z) z g := by
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
    have hBound : j + k < n :=
      Nat.lt_trans hCombined
        (grantDrainEntranceArcOffsetLt ring q g)
    have hJBound : j < n :=
      Nat.lt_trans hInside
        (grantDrainEntranceArcOffsetLt ring q g)
    have hDifferent :=
      grantDrainWeakDeathShiftRightNe ring q (j + k) j
        hBound hJBound (by omega)
    rw [grantDrainWeakDeathShiftRightAdd ring q j k]
    exact grantDrainMarksBirthOtherSite N
      (PPL.shiftRight ring q j)
      (PPL.shiftRight ring q (j + k)) hDifferent
  refine ⟨?_, hBorn.1, ?_⟩
  · rw [hOffset]
    omega
  · intro k hk hlt
    rw [hLater k hk hlt]
    have hCombined :
        j + k < PPL.cyclicOffset ring q g := by
      rw [hOffset] at hlt
      omega
    exact hArc.2.2 (j + k) (by omega) hCombined

/-- A genuine bounded first-hit left scan is the corresponding
clockwise nearest arc, even when the signal word is not zero. -/
theorem grantDrainD6OldNearestArcOfScan
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) (d : Nat)
    (hd : 1 ≤ d) (hShort : d < n)
    (hDistance : grantDrainLeftLeaderDistance ring N g = d) :
    GrantDrainMarksNearestArc ring N
      (PPL.shiftLeft ring g d) g := by
  have hOld :=
    (grantDrainWarmLeaderFirstCharacterization
      ring N g d hd hShort).mp hDistance
  have hOffset :=
    grantDrainD6BirthLeftOffset ring g d hShort
  have hInverse :
      g = PPL.shiftRight ring (PPL.shiftLeft ring g d) d :=
    (grantDrainD6BirthShiftCancel ring g d hShort).symm
  refine ⟨?_, hOld.1, ?_⟩
  · rw [hOffset]
    omega
  · intro k hk hkd
    rw [hOffset] at hkd
    have hShift :
        PPL.shiftRight ring (PPL.shiftLeft ring g d) k =
          PPL.shiftLeft ring g (d - k) := by
      have h :=
        grantDrainMarksArcShiftLeftRight ring
          (PPL.shiftLeft ring g d) d (d - k)
          (by omega) hShort
      rw [← hInverse] at h
      have hSub : d - (d - k) = k := by omega
      rw [hSub] at h
      exact h.symm
    rw [hShift]
    exact hOld.2 (d - k) (by omega) (by omega)

/-- Concatenate two nearest-leader arcs after deleting their
common middle leader p. This lemma deliberately DOES NOT
demand a zero-signal suffix and so applies to warm hosts. -/
theorem grantDrainD6NearestArcConcat
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (q p g : Fin n)
    (hFront : GrantDrainMarksNearestArc ring N q p)
    (hDead : (N p).l = false)
    (hRight : ∀ k : Nat, 0 < k →
      k < PPL.cyclicOffset ring p g →
      (N (PPL.shiftRight ring p k)).l = false)
    (hNoWrap : PPL.cyclicOffset ring q p +
      PPL.cyclicOffset ring p g < n) :
    GrantDrainMarksNearestArc ring N q g := by
  have hJoin :=
    grantDrainWeakDeathOffsetConcat ring q p g hNoWrap
  refine ⟨?_, hFront.2.1, ?_⟩
  · rw [hJoin]
    have h1 := hFront.1
    omega
  · intro k hk hkg
    rw [hJoin] at hkg
    by_cases hLeft : k < PPL.cyclicOffset ring q p
    · exact hFront.2.2 k hk hLeft
    · have hPast :
          PPL.cyclicOffset ring q p ≤ k := by omega
      have hShift :
          PPL.shiftRight ring q k =
            PPL.shiftRight ring p
              (k - PPL.cyclicOffset ring q p) := by
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
      rw [hShift]
      by_cases hAt : k - PPL.cyclicOffset ring q p = 0
      · rw [hAt, grantDrainWeakDeathShiftRightZero]
        exact hDead
      · exact hRight (k - PPL.cyclicOffset ring q p)
          (by omega) (by omega)

/-- H1 physical kernel. The shielded new leader is computed from
the actual post-E + optional canonical-birth native array.
Neither a next-label assumption nor an old zero-signal arc
is needed. -/
theorem grantDrainD6ExceptionalPhysicalNewFrontShield
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    ((grantDrainStep ring fresh update s e).native
      (grantDrainD6MergeFront ring
        (grantDrainStep ring fresh update s e).native g)).sh =
      true := by
  have hOldRange :=
    grantDrainD6ExceptionalDeathOldDistanceShort
      ring hn s e g hWarm hExceptional
  have hResponder :=
    grantDrainD6MergeExceptionalAtResponder
      ring s e g hExceptional
  change PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g) =
      ring.rightNeighbor e at hResponder
  have hOldArc :
      GrantDrainMarksNearestArc ring s.native
        (ring.rightNeighbor e) g := by
    have hArc :=
      grantDrainD6OldNearestArcOfScan
        ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        hOldRange.1 hOldRange.2 rfl
    rw [hResponder] at hArc
    exact hArc
  obtain ⟨hOldLeader, hUnshielded, hQuiet, _, hDead⟩ :=
    grantDrainD6MergeExceptionalFields ring s e g hExceptional
  change
    (s.native (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).l = true
      at hOldLeader
  change
    (s.native (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).sh = false
      at hUnshielded
  change
    (s.native (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).sg = false
      at hQuiet
  change
    (nativeE ring s.native e
      (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))).l =
      false at hDead
  rw [hResponder] at hOldLeader hUnshielded hQuiet hDead
  obtain ⟨q, hOldQLeader, hBehind, hFront, _hFrontZero,
      hQShield⟩ :=
    grantDrainWeakDeathFrontRootHolds
      ring hn s e (ring.rightNeighbor e) hC.1.1
      rfl hOldLeader hUnshielded hQuiet hDead
  have hNoWrap :=
    grantDrainWeakDeathArcNonoverlap
      ring s.native q (ring.rightNeighbor e) g
      hOldQLeader hBehind hOldArc
      (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  have hRight :=
    grantDrainWeakDeathRightFollowersAfterE
      ring hn s e (ring.rightNeighbor e) g rfl hOldArc
  have hEArc :
      GrantDrainMarksNearestArc ring
        (nativeE ring s.native e) q g :=
    grantDrainD6NearestArcConcat ring
      (nativeE ring s.native e)
      q (ring.rightNeighbor e) g
      hFront hDead hRight hNoWrap
  have hSites :=
    grantDrainWeakDeathSpliceBirthSites
      ring hn e q (ring.rightNeighbor e) g
      rfl hBehind hOldArc.1 hNoWrap
  change
    (grantDrainNativeNext ring s e
      (grantDrainD6MergeFront ring
        (grantDrainNativeNext ring s e) g)).sh = true
  cases hf : grantDrainSelect ring s e with
  | none =>
      have hTarget :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (nativeE ring s.native e) q g hEArc hQShield
      simpa [grantDrainNativeNext, hf] using hTarget
  | leftLocal =>
      obtain ⟨j, hSite, hInside⟩ := hSites.1
      have hArc :=
        grantDrainD6NearestArcAfterBirth
          ring (nativeE ring s.native e) q g e j
          hEArc hSite hInside
      have hBorn :=
        (grantDrainD6MergeCanonicalBirthProtected
          (nativeE ring s.native e) e).2.1
      have hTarget :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (canonicalBirth (nativeE ring s.native e) e)
          e g hArc hBorn
      simpa [grantDrainNativeNext, hf] using hTarget
  | rightLocal =>
      obtain ⟨j, hSite, hInside⟩ := hSites.2
      have hArc :=
        grantDrainD6NearestArcAfterBirth
          ring (nativeE ring s.native e) q g
          (ring.rightNeighbor e) j hEArc hSite hInside
      have hBorn :=
        (grantDrainD6MergeCanonicalBirthProtected
          (nativeE ring s.native e) (ring.rightNeighbor e)).2.1
      have hTarget :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (canonicalBirth (nativeE ring s.native e)
            (ring.rightNeighbor e))
          (ring.rightNeighbor e) g hArc hBorn
      simpa [grantDrainNativeNext, hf] using hTarget
  | cross =>
      obtain ⟨j, hSite, hInside⟩ := hSites.1
      have hArc :=
        grantDrainD6NearestArcAfterBirth
          ring (nativeE ring s.native e) q g e j
          hEArc hSite hInside
      have hBorn :=
        (grantDrainD6MergeCanonicalBirthProtected
          (nativeE ring s.native e) e).2.1
      have hTarget :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (canonicalBirth (nativeE ring s.native e) e)
          e g hArc hBorn
      simpa [grantDrainNativeNext, hf] using hTarget

/-- The exact requested H1 label interface: a continuing NEW
warm hosted label has a shielded NEW nearest leader. -/
theorem grantDrainD6ExceptionalNewFrontShield
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g g' : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hOldWarm : label.warm = true)
    (hOldHost : label.host = some g)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e label).warm =
        true)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e label).host =
        some g') :
    ((grantDrainStep ring fresh update s e).native
      (grantDrainD6MergeFront ring
        (grantDrainStep ring fresh update s e).native g')).sh =
      true := by
  have hOldPhysical := hPhysical g hOldWarm hOldHost
  have hShield :=
    grantDrainD6ExceptionalPhysicalNewFrontShield
      ring hn fresh update s e g hC hOldPhysical hExceptional
  have hNotX : g ≠ e :=
    Ne.symm (grantDrainD6ExceptionalDeathSourceNotHost
      ring hn s e g hOldPhysical hExceptional)
  have hNotY : g ≠ ring.rightNeighbor e :=
    Ne.symm (grantDrainD6ExceptionalBirthResponderAway
      ring s e g hOldPhysical hExceptional)
  have hKept :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hOldHost, hNotX, hNotY]
  rw [hKept] at hNewHost
  have hSame : g = g' := Option.some.inj hNewHost
  subst g'
  exact hShield

/-- H1 conclusion: after one exceptional OLD front death,
the first (shield) disjunct of the spent invariant holds for
every continuing warm hosted ghost, including all FIRE rows. -/
theorem grantDrainD6ExceptionalHOneMergeSpent
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hOldWarm : label.warm = true)
    (hOldHost : label.host = some g)
    (hExceptional :
      grantDrainExceptionalDeath ring s e g = true) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  intro g' hNewWarm hNewHost _hSpent
  exact Or.inl
    (grantDrainD6ExceptionalNewFrontShield
      ring hn fresh update s e g g' label hC hPhysical
      hOldWarm hOldHost hExceptional hNewWarm hNewHost)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
The first two results close the strict-interior, empty-follower
contact row, with and without selected canonical FIRE. The third
isolates every hypothetical remaining X1 failure in the spent
inclusive OLD scan-contact branch, using the earlier result to eliminate H1.

The general H2 theorem and unconditional X1 are NOT proved here.
No assertion about an unproved leaf is introduced.
-/

/-- When two empty followers service a no-FIRE edge away from the
tracked host, E preserves every leader and bullet field. The OLD
nearest leader is therefore the NEW nearest leader, its complete
record is framed, and all three spent witnesses transport. -/
theorem grantDrainD6EmptyFollowerNoFireSpent
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (hGX : g ≠ e)
    (hGY : g ≠ ring.rightNeighbor e)
    (hXL : (s.native e).l = false)
    (hXB : (s.native e).b = (0 : Fin 3))
    (hYL : (s.native (ring.rightNeighbor e)).l = false)
    (hYB : (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hPair :=
    grantDrainWarmEmptyFollowerSignalCopyNativeE
      ring s.native e hXL hXB hYL hYB
  have hLeaderField :
      ∀ i : Fin n,
        ((grantDrainStep ring fresh update s e).native i).l =
          (s.native i).l := by
    intro i
    rw [grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone]
    exact (hPair i).1
  have hBulletField :
      ∀ i : Fin n,
        ((grantDrainStep ring fresh update s e).native i).b =
          (s.native i).b := by
    intro i
    rw [grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone]
    exact (hPair i).2.1
  have hDistance :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g =
      grantDrainLeftLeaderDistance ring s.native g := by
    simp [grantDrainLeftLeaderDistance, hLeaderField]
  have hBullets :
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g) =
      grantDrainLeftBulletDistance ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) := by
    rw [hDistance]
    simp [grantDrainLeftBulletDistance, hBulletField]
  have hFront :
      grantDrainD6MergeFront ring
        (grantDrainStep ring fresh update s e).native g =
      grantDrainD6MergeFront ring s.native g := by
    unfold grantDrainD6MergeFront
    rw [hDistance]
  have hOldFrontLeader :=
    grantDrainD6OldWarmFrontLeader
      ring hn s g hC (hPhysical g hWarm hHost)
  change (s.native
    (grantDrainD6MergeFront ring s.native g)).l = true
    at hOldFrontLeader
  have hFrontNotX :
      grantDrainD6MergeFront ring s.native g ≠ e := by
    intro he
    rw [he, hXL] at hOldFrontLeader
    cases hOldFrontLeader
  have hFrontNotY :
      grantDrainD6MergeFront ring s.native g ≠
        ring.rightNeighbor e := by
    intro he
    rw [he, hYL] at hOldFrontLeader
    cases hOldFrontLeader
  have hFrontFrame :=
    grantDrainSettledNativeStepOutsidePair
      ring fresh update s e
      (grantDrainD6MergeFront ring s.native g)
      hFrontNotX hFrontNotY
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
      rw [hFront, hFrontFrame]
      exact hSh
    · right
      left
      rw [hFront, hFrontFrame]
      exact hSg
    · right
      right
      rw [hBullets]
      exact hB
  have hHostFixed :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost, hGX, hGY]
  intro q _ hNewHost _
  have hSame : g = q :=
    Option.some.inj (hHostFixed.symm.trans hNewHost)
  subst q
  exact hPost

/-- In the strict interior, E does not alter leader flags when
the two OLD endpoints are empty followers. Every selected
canonical FIRE therefore creates the protected NEW nearest
leader: the newborn lies strictly between the old front and g.
The native successor is the actual E+FIRE array. -/
theorem grantDrainD6EmptyFollowerInteriorFireFrontShield
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (d k : Nat)
    (hdPos : 1 ≤ d) (hdShort : d < n)
    (hDistance : grantDrainLeftLeaderDistance ring s.native g = d)
    (hFront : p = PPL.shiftLeft ring g d)
    (hk : 1 ≤ k) (hInterior : k + 1 < d)
    (hSource : e = PPL.shiftLeft ring g (k + 1))
    (hResponder : ring.rightNeighbor e = PPL.shiftLeft ring g k)
    (hXL : (s.native e).l = false)
    (hXB : (s.native e).b = (0 : Fin 3))
    (hYL : (s.native (ring.rightNeighbor e)).l = false)
    (hYB : (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hFire : grantDrainSelect ring s e ≠ .none) :
    ((grantDrainStep ring fresh update s e).native
      (grantDrainD6MergeFront ring
        (grantDrainStep ring fresh update s e).native g)).sh =
      true := by
  have hOldArc :
      GrantDrainMarksNearestArc ring s.native p g := by
    rw [hFront]
    exact grantDrainD6OldNearestArcOfScan
      ring s.native g d hdPos hdShort hDistance
  have hPair :=
    grantDrainWarmEmptyFollowerSignalCopyNativeE
      ring s.native e hXL hXB hYL hYB
  have hEArc :
      GrantDrainMarksNearestArc ring
        (nativeE ring s.native e) p g := by
    refine ⟨hOldArc.1, ?_, ?_⟩
    · rw [(hPair p).1]
      exact hOldArc.2.1
    · intro j hj hBound
      rw [(hPair (PPL.shiftRight ring p j)).1]
      exact hOldArc.2.2 j hj hBound
  have hAt : g = PPL.shiftRight ring p d := by
    rw [hFront]
    exact (grantDrainD6BirthShiftCancel
      ring g d hdShort).symm
  have hOffset : PPL.cyclicOffset ring p g = d := by
    rw [hFront]
    exact grantDrainD6BirthLeftOffset ring g d hdShort
  have hSourceSite :
      e = PPL.shiftRight ring p (d - (k + 1)) := by
    rw [hSource, hAt]
    exact grantDrainMarksArcShiftLeftRight
      ring p d (k + 1) (by omega) hdShort
  have hResponderSite :
      ring.rightNeighbor e = PPL.shiftRight ring p (d - k) := by
    rw [hResponder, hAt]
    exact grantDrainMarksArcShiftLeftRight
      ring p d k (by omega) hdShort
  have hSourceInside :
      d - (k + 1) < PPL.cyclicOffset ring p g := by
    rw [hOffset]
    omega
  have hResponderInside :
      d - k < PPL.cyclicOffset ring p g := by
    rw [hOffset]
    omega
  change
    (grantDrainNativeNext ring s e
      (grantDrainD6MergeFront ring
        (grantDrainNativeNext ring s e) g)).sh = true
  cases hf : grantDrainSelect ring s e with
  | none =>
      exact False.elim (hFire hf)
  | leftLocal =>
      have hArc :=
        grantDrainD6NearestArcAfterBirth
          ring (nativeE ring s.native e) p g e
          (d - (k + 1)) hEArc hSourceSite hSourceInside
      have hBorn :=
        (grantDrainD6MergeCanonicalBirthProtected
          (nativeE ring s.native e) e).2.1
      have hShield :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (canonicalBirth (nativeE ring s.native e) e)
          e g hArc hBorn
      simpa [grantDrainNativeNext, hf] using hShield
  | rightLocal =>
      have hArc :=
        grantDrainD6NearestArcAfterBirth
          ring (nativeE ring s.native e) p g
          (ring.rightNeighbor e)
          (d - k) hEArc hResponderSite hResponderInside
      have hBorn :=
        (grantDrainD6MergeCanonicalBirthProtected
          (nativeE ring s.native e)
          (ring.rightNeighbor e)).2.1
      have hShield :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (canonicalBirth (nativeE ring s.native e)
            (ring.rightNeighbor e))
          (ring.rightNeighbor e) g hArc hBorn
      simpa [grantDrainNativeNext, hf] using hShield
  | cross =>
      have hArc :=
        grantDrainD6NearestArcAfterBirth
          ring (nativeE ring s.native e) p g e
          (d - (k + 1)) hEArc hSourceSite hSourceInside
      have hBorn :=
        (grantDrainD6MergeCanonicalBirthProtected
          (nativeE ring s.native e) e).2.1
      have hShield :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (canonicalBirth (nativeE ring s.native e) e)
          e g hArc hBorn
      simpa [grantDrainNativeNext, hf] using hShield

/-- A real H2 subcase: both OLD serviced endpoints are strictly
inside the old nearest-leader arc and are empty followers. This
covers all selected FIRE rows, not merely no-FIRE. -/
theorem grantDrainD6SpentInteriorEmptyFollowerContact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (k : Nat) (hk : 1 ≤ k)
    (hInterior : k + 1 <
      grantDrainLeftLeaderDistance ring s.native g)
    (hSource : e = PPL.shiftLeft ring g (k + 1))
    (hResponder : ring.rightNeighbor e = PPL.shiftLeft ring g k)
    (hXL : (s.native e).l = false)
    (hXB : (s.native e).b = (0 : Fin 3))
    (hYL : (s.native (ring.rightNeighbor e)).l = false)
    (hYB : (s.native (ring.rightNeighbor e)).b = (0 : Fin 3)) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC (hPhysical g hWarm hHost)
  have hNotX : g ≠ e := by
    rw [hSource]
    have hDistinct :=
      grantDrainD6BirthLeftOffsetsDistinct ring g 0 (k + 1)
        (by omega : 0 < n)
        (by omega : k + 1 < n)
        (by omega : 0 ≠ k + 1)
    simpa only [grantDrainWarmShiftLeftZero] using hDistinct
  have hNotY : g ≠ ring.rightNeighbor e := by
    rw [hResponder]
    have hDistinct :=
      grantDrainD6BirthLeftOffsetsDistinct ring g 0 k
        (by omega : 0 < n)
        (by omega : k < n)
        (by omega : 0 ≠ k)
    simpa only [grantDrainWarmShiftLeftZero] using hDistinct
  by_cases hNone : grantDrainSelect ring s e = .none
  · exact grantDrainD6EmptyFollowerNoFireSpent
      ring hn fresh update s e g label
      hC hInv hPhysical hWarm hHost hSpent
      hNotX hNotY hXL hXB hYL hYB hNone
  · have hShield :=
      grantDrainD6EmptyFollowerInteriorFireFrontShield
        ring fresh update s e
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))
        g
        (grantDrainLeftLeaderDistance ring s.native g)
        k hRange.1 hRange.2 rfl rfl
        hk hInterior hSource hResponder
        hXL hXB hYL hYB hNone
    have hHostFixed :
        (grantDrainWarmLabelStep ring fresh update s e
          label).host = some g := by
      simp [grantDrainWarmLabelStep, hHost, hNotX, hNotY]
    intro q _ hNewHost _
    have hSame : g = q :=
      Option.some.inj (hHostFixed.symm.trans hNewHost)
    subst q
    exact Or.inl hShield

/-- Exact remaining-obstruction interface, conditional only on
the genuine D.6 physical warm-host coherence, native cleanliness,
and the OLD MergeSpent invariant. The earlier result removes H1: every
hypothetical X1 failure must be an H2 spent OLD scan contact. -/
theorem grantDrainD6XOneFailureOnlySpentScanContact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hFailure :
      ¬ GrantDrainWarmMergeSpent ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label)) :
    ∃ g : Fin n,
      label.warm = true ∧
      label.host = some g ∧
      label.exceptionalLeft = false ∧
      ∃ k : Nat,
        k ≤ grantDrainLeftLeaderDistance ring s.native g ∧
        (PPL.shiftLeft ring g k = e ∨
          PPL.shiftLeft ring g k = ring.rightNeighbor e) := by
  have hOldWarm : label.warm = true := by
    cases hw : label.warm with
    | true => rfl
    | false =>
        have hNextCold :=
          grantDrainD6MergeColdLabelRemainsCold
            ring fresh update s e label hw
        exact False.elim (hFailure
          (grantDrainD6XOneNextCold
            ring fresh update s e label hNextCold))
  have hCases :=
    (grantDrainD6MergeSpentFailureCleanDichotomy
      ring hn fresh update s e label hC hInv hFailure).2
  rcases hCases with
      ⟨g, hHost, _hAvailable, hExceptional⟩ |
      ⟨g, hHost, hSpent, k, hk, hContact⟩
  · have hHOne :=
      grantDrainD6ExceptionalHOneMergeSpent
        ring hn fresh update s e g label
        hC hPhysical hOldWarm hHost hExceptional
    exact False.elim (hFailure hHOne)
  · exact ⟨g, hOldWarm, hHost, hSpent,
      k, hk, hContact⟩

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
This block proves actual physical subcases. It does not assume
general spent scan-contact preservation or assert unconditional X1.
-/

theorem grantDrainD6SpentOldFrontGeometry
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch)
    (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true) :
    (s.native (grantDrainD6MergeFront ring s.native g)).l =
      true ∧
    grantDrainD6MergeFront ring s.native g ≠ g ∧
    (s.native g).l = false := by
  have hLeader :=
    grantDrainD6OldWarmFrontLeader ring hn s g hC hWarm
  have hFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  refine ⟨hLeader, ?_, hFollower⟩
  intro hEq
  change (s.native (grantDrainD6MergeFront ring s.native g)).l = true at hLeader
  rw [hEq, hFollower] at hLeader
  cases hLeader


/-- A physically warm follower used as the E source is unchanged
by that literal native row (even if its responder is a leader). -/
theorem grantDrainD6WarmFollowerSourceLiteralFixed
    (x y : CertNative)
    (hFollower : x.l = false)
    (hEmpty : x.b = (0 : Fin 3))
    (hSignal : x.sg = true) :
    (certLiteralEPair x y).1 = x := by
  cases x with
  | mk xl xb xsh xsg =>
      simp only [CertNative.l, CertNative.b, CertNative.sg]
        at hFollower hEmpty hSignal
      subst xl
      subst xb
      subst xsg
      simp [certLiteralEPair, certFinThree]

/-- If the OLD responder is a follower, literal E cannot change
any leader flag anywhere. This makes the nearest-leader arc
transportable even when a bullet moves between the two sites. -/
theorem grantDrainD6ResponderFollowerELeaderFrame
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hYFollower : (N (ring.rightNeighbor e)).l = false) :
    ∀ i : Fin n,
      (nativeE ring N e i).l = (N i).l := by
  intro i
  by_cases hAtX : i = e
  · subst i
    simpa [nativeE] using
      (grantDrainEntranceLiteralESourceLeaderFixed
        (N e) (N (ring.rightNeighbor e)))
  · by_cases hAtY : i = ring.rightNeighbor e
    · subst i
      simp [nativeE, hAtX, certLiteralEPair, hYFollower]
    · simp [nativeE, hAtX, hAtY]

theorem grantDrainD6SpentProtectedFrontSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (hFront : grantDrainD6MergeFront ring s.native g = e)
    (hProtected :
      (s.native e).sh = true ∨ (s.native e).sg = true)
    (hHostAwayY : g ≠ ring.rightNeighbor e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hPhysicalWarm := hPhysical g hWarm hHost
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hPhysicalWarm
  have hOldArc :
      GrantDrainMarksNearestArc ring s.native e g := by
    have hArc := grantDrainD6OldNearestArcOfScan
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hRange.1 hRange.2 rfl
    change GrantDrainMarksNearestArc ring s.native
      (grantDrainD6MergeFront ring s.native g) g at hArc
    rw [hFront] at hArc
    exact hArc
  have hOldFrontLeader : (s.native e).l = true :=
    hOldArc.2.1
  have hHostFollower :=
    (grantDrainD6ExceptionalDeathHostFields
      s g hPhysicalWarm).1
  have hHostNotX : g ≠ e := by
    intro hEq
    rw [← hEq, hHostFollower] at hOldFrontLeader
    cases hOldFrontLeader
  have hRight :
      PPL.shiftRight ring e 1 = ring.rightNeighbor e := by
    apply Fin.ext
    rfl
  have hYInside :
      1 < PPL.cyclicOffset ring e g := by
    by_cases hOne : PPL.cyclicOffset ring e g = 1
    · have hYIsG : ring.rightNeighbor e = g := by
        calc
          ring.rightNeighbor e =
              PPL.shiftRight ring e 1 := hRight.symm
          _ = PPL.shiftRight ring e
                (PPL.cyclicOffset ring e g) := by rw [hOne]
          _ = g :=
            grantDrainMarksArcShiftRightOffset ring e g
      exact False.elim (hHostAwayY hYIsG.symm)
    · have hPositive := hOldArc.1
      omega
  have hYFollower :
      (s.native (ring.rightNeighbor e)).l = false := by
    rw [← hRight]
    exact hOldArc.2.2 1 (by omega) hYInside
  have hLeaderFrame :=
    grantDrainD6ResponderFollowerELeaderFrame
      ring hn s.native e hYFollower
  have hEArc :
      GrantDrainMarksNearestArc ring
        (nativeE ring s.native e) e g := by
    refine ⟨hOldArc.1, ?_, ?_⟩
    · rw [hLeaderFrame e]
      exact hOldArc.2.1
    · intro j hj hjShort
      rw [hLeaderFrame (PPL.shiftRight ring e j)]
      exact hOldArc.2.2 j hj hjShort
  have hEShield :
      (nativeE ring s.native e e).sh = true := by
    have hPair := grantDrainD6MergeLeaderSourceProtection
      (s.native e) (s.native (ring.rightNeighbor e))
      hOldFrontLeader hProtected
    simpa [nativeE] using hPair
  have hENotEligible :
      grantDrainEligible (nativeE ring s.native e) e = false := by
    have hELeader : (nativeE ring s.native e e).l = true := by
      rw [hLeaderFrame e]
      exact hOldFrontLeader
    simp [grantDrainEligible, hELeader]
  have hNoSourceFire :
      grantDrainSelect ring s e ≠ .leftLocal ∧
      grantDrainSelect ring s e ≠ .cross := by
    constructor
    · intro hFire
      have hEligible :=
        grantDrainD6SelectedEligible ring s e e
          (Or.inl ⟨hFire, rfl⟩)
      rw [hENotEligible] at hEligible
      cases hEligible
    · intro hFire
      have hEligible :=
        grantDrainD6SelectedEligible ring s e e
          (Or.inr (Or.inr ⟨hFire, rfl⟩))
      rw [hENotEligible] at hEligible
      cases hEligible
  have hNewShield :
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native g)).sh =
        true := by
    change
      (grantDrainNativeNext ring s e
        (grantDrainD6MergeFront ring
          (grantDrainNativeNext ring s e) g)).sh = true
    cases hf : grantDrainSelect ring s e with
    | none =>
        have hTarget :=
          grantDrainD6ShieldedFrontOfNearestArc
            ring (nativeE ring s.native e) e g hEArc hEShield
        simpa [grantDrainNativeNext, hf] using hTarget
    | leftLocal =>
        exact False.elim (hNoSourceFire.1 hf)
    | rightLocal =>
        have hArc :=
          grantDrainD6NearestArcAfterBirth
            ring (nativeE ring s.native e) e g
            (ring.rightNeighbor e) 1
            hEArc hRight.symm hYInside
        have hBorn :=
          (grantDrainD6MergeCanonicalBirthProtected
            (nativeE ring s.native e)
            (ring.rightNeighbor e)).2.1
        have hTarget :=
          grantDrainD6ShieldedFrontOfNearestArc
            ring (canonicalBirth (nativeE ring s.native e)
              (ring.rightNeighbor e))
            (ring.rightNeighbor e) g hArc hBorn
        simpa [grantDrainNativeNext, hf] using hTarget
    | cross =>
        exact False.elim (hNoSourceFire.2 hf)
  have hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost,
      hHostNotX, hHostAwayY]
  intro q _ hHostQ _
  have hSame : g = q :=
    Option.some.inj (hNewHost.symm.trans hHostQ)
  subst q
  exact Or.inl hNewShield


/-- HOST-SOURCE, no FIRE: when the responder is outside the
inclusive old backward scan, the OLD warm source is itself
unchanged by E, hence the entire old scan including distance
zero is framed. All three spent witnesses survive literally. -/
theorem grantDrainD6SpentHostSourceNoFireAwayScan
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some e)
    (hSpent : label.exceptionalLeft = false)
    (hNoY : ∀ j : Nat, 1 ≤ j →
      j ≤ grantDrainLeftLeaderDistance ring s.native e →
      PPL.shiftLeft ring e j ≠ ring.rightNeighbor e)
    (hNone : grantDrainSelect ring s e = .none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldWarm := hPhysical e hWarm hHost
  have hFields :=
    grantDrainD6ExceptionalDeathHostFields s e hOldWarm
  have hLiteral :=
    grantDrainD6WarmFollowerSourceLiteralFixed
      (s.native e) (s.native (ring.rightNeighbor e))
      hFields.1 hFields.2.1 hFields.2.2
  have hSourceFrame :
      ((grantDrainStep ring fresh update s e).native e) =
        s.native e := by
    rw [grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone]
    simpa [nativeE] using hLiteral
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s e hC hOldWarm
  have hFrame : ∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native e →
      (grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring e j) =
      s.native (PPL.shiftLeft ring e j) := by
    intro j hj
    by_cases hZero : j = 0
    · subst j
      rw [grantDrainWarmShiftLeftZero]
      exact hSourceFrame
    · have hNotSource :
          PPL.shiftLeft ring e j ≠ e := by
        have hNe :=
          grantDrainD6BirthLeftOffsetsDistinct
            ring e j 0 (by omega : j < n)
            (by omega : 0 < n) (by omega : j ≠ 0)
        simpa only [grantDrainWarmShiftLeftZero] using hNe
      exact grantDrainSettledNativeStepOutsidePair
        ring fresh update s e (PPL.shiftLeft ring e j)
        hNotSource (hNoY j (by omega) hj)
  have hScan :=
    grantDrainWarmFullScanFrame
      ring s.native (grantDrainStep ring fresh update s e).native
      e hFrame
  have hOld := hInv e hWarm hHost hSpent
  have hPost :
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native e)).sh =
          true ∨
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native e)).sg =
          true ∨
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native e
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native e) ≠
          none := by
    rcases hOld with hShield | hSignal | hBullet
    · left
      unfold grantDrainD6MergeFront
      rw [hScan.1, hFrame _ (Nat.le_refl _)]
      exact hShield
    · right
      left
      unfold grantDrainD6MergeFront
      rw [hScan.1, hFrame _ (Nat.le_refl _)]
      exact hSignal
    · right
      right
      rw [hScan.1, hScan.2.2.1]
      exact hBullet
  have hRoute :=
    grantDrainD6ContactHostAtSource
      ring fresh update s e label hHost
  intro q _ hNextHost _
  cases hr : grantDrainD6ContactRowSourceGrant ring fresh s e with
  | false =>
      rw [hRoute, hr] at hNextHost
      cases hNextHost
  | true =>
      rw [hRoute, hr] at hNextHost
      have hEq : e = q := Option.some.inj hNextHost
      subst q
      exact hPost

/-- HOST-RESPONDER, incoming bullet into an empty warm follower:
the literal no-FIRE row makes BOTH possible next host sites cold.
This handles a moving grant as well as a stationary one. -/
theorem grantDrainD6SpentHostResponderIncomingBulletNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hXL : (s.native e).l = false)
    (hXB : (s.native e).b ≠ (0 : Fin 3))
    (hXS : (s.native e).sg = false)
    (hYL : (s.native (ring.rightNeighbor e)).l = false)
    (hYB : (s.native (ring.rightNeighbor e)).b =
      (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hColdPair :=
    grantDrainD6MergeOutgoingBulletNoFireColdEndpoints
      ring hn fresh update s e hXL hXB hXS hYL hYB hNone
  intro q hNewWarm hNewHost _
  have hNewPhysical :=
    grantDrainD6HostNextWarmPhysical
      ring fresh update s e q label hNewHost hNewWarm
  by_cases hSame : q = ring.rightNeighbor e
  · rw [hSame, hColdPair.2] at hNewPhysical
    cases hNewPhysical
  · have hChanged :=
      grantDrainD6HostChangedOnlyResponderToSource
        ring hn fresh update s e (ring.rightNeighbor e)
        q label hHost hNewHost hSame
    rw [hChanged.2, hColdPair.1] at hNewPhysical
    cases hNewPhysical

/-- HOST BIRTH at either selected physical endpoint makes the
actual next warm-host requirement vacuous. -/
theorem grantDrainD6SpentHostBirthRetires
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hHost : label.host = some g)
    (hBirth : ∃ z : Fin n,
      z = g ∧
      ((grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
       (grantDrainSelect ring s e = .rightLocal ∧
         z = ring.rightNeighbor e) ∨
       (grantDrainSelect ring s e = .cross ∧ z = e))) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  rcases grantDrainD6HostAtBirthRetires
      ring hn fresh update s e g label hHost hBirth with
      hNoHost | hCold
  · exact grantDrainD6XOneNextHostless
      ring fresh update s e label hNoHost
  · exact grantDrainD6XOneNextCold
      ring fresh update s e label hCold

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Continued: literal moving-bullet and interior-follower rows. -/

/-- Literal bounded Fin-3 reconstruction; isolated from the E row. -/
theorem grantDrainD6CertFinThreeRoundTrip
    (b : Fin 3) : certFinThree b.val = b := by
  unfold certFinThree
  split
  · apply Fin.ext
    rfl
  · have hb := b.isLt
    omega

/-- In a follower/follower E row, a bullet at either old endpoint
leaves a nonzero bullet at the responder. This covers both the
source-transfer row and an already occupied responder. -/
theorem grantDrainD6FollowerPairResponderKeepsBullet
    (x y : CertNative)
    (hXL : x.l = false)
    (hYL : y.l = false)
    (hBullet :
      x.b ≠ (0 : Fin 3) ∨ y.b ≠ (0 : Fin 3)) :
    (certLiteralEPair x y).2.b ≠ (0 : Fin 3) := by
  by_cases hXZero : x.b = (0 : Fin 3)
  · have hYNonzero : y.b ≠ (0 : Fin 3) := by
      rcases hBullet with hX | hY
      · exact False.elim (hX hXZero)
      · exact hY
    have hYFixed :
        (certLiteralEPair x y).2.b = y.b := by
      simp [certLiteralEPair, hXL, hYL, hXZero,
        grantDrainD6CertFinThreeRoundTrip]
    rw [hYFixed]
    exact hYNonzero
  · by_cases hYZero : y.b = (0 : Fin 3)
    · have hMoved :=
        grantDrainWarmLeftBulletMovePair x y
          hXL hXZero hYL hYZero
      rw [hMoved.2.1]
      exact hXZero
    · have hXPos : 0 < x.b.val := by
        have hNonzero : x.b.val ≠ 0 := by
          intro hz
          apply hXZero
          apply Fin.ext
          exact hz
        omega
      have hYNonzero : y.b.val ≠ 0 := by
        intro hz
        apply hYZero
        apply Fin.ext
        exact hz
      have hYBool : (y.b.val == 0) = false := by
        simp [hYNonzero]
      have hYFixed :
          (certLiteralEPair x y).2.b = y.b := by
        simp [certLiteralEPair, hXL, hYL, hXPos,
          hYBool, grantDrainD6CertFinThreeRoundTrip]
      rw [hYFixed]
      exact hYZero

/-- Strictly interior follower/follower contact with NO FIRE:
a shield/signal at the old front is framed. An old left bullet
is either framed or transfers one site clockwise, still strictly
to the left of g and still within the recomputed leader scan. -/
theorem grantDrainD6SpentInteriorFollowerNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (k : Nat) (hk : 1 ≤ k)
    (hInterior : k + 1 <
      grantDrainLeftLeaderDistance ring s.native g)
    (hSource : e = PPL.shiftLeft ring g (k + 1))
    (hResponder : ring.rightNeighbor e = PPL.shiftLeft ring g k)
    (hXL : (s.native e).l = false)
    (hYL : (s.native (ring.rightNeighbor e)).l = false)
    (hNone : grantDrainSelect ring s e = .none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldPhysical := hPhysical g hWarm hHost
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hOldPhysical
  have hLeaderFrame :=
    grantDrainD6ResponderFollowerELeaderFrame
      ring hn s.native e hYL
  have hNative :=
    grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone
  have hDistance :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g =
      grantDrainLeftLeaderDistance ring s.native g := by
    rw [hNative]
    simp [grantDrainLeftLeaderDistance, hLeaderFrame]
  have hNotHostSource : g ≠ e := by
    rw [hSource]
    have hDifferent :=
      grantDrainD6BirthLeftOffsetsDistinct ring g 0 (k + 1)
        (by omega : 0 < n)
        (by omega : k + 1 < n)
        (by omega : 0 ≠ k + 1)
    simpa only [grantDrainWarmShiftLeftZero] using hDifferent
  have hNotHostResponder : g ≠ ring.rightNeighbor e := by
    rw [hResponder]
    have hDifferent :=
      grantDrainD6BirthLeftOffsetsDistinct ring g 0 k
        (by omega : 0 < n)
        (by omega : k < n)
        (by omega : 0 ≠ k)
    simpa only [grantDrainWarmShiftLeftZero] using hDifferent
  have hNotFrontSource :
      PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g) ≠ e := by
    rw [hSource]
    exact grantDrainD6BirthLeftOffsetsDistinct ring g
      (grantDrainLeftLeaderDistance ring s.native g)
      (k + 1) hRange.2 (by omega) (by omega)
  have hNotFrontResponder :
      PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g) ≠
        ring.rightNeighbor e := by
    rw [hResponder]
    exact grantDrainD6BirthLeftOffsetsDistinct ring g
      (grantDrainLeftLeaderDistance ring s.native g)
      k hRange.2 (by omega) (by omega)
  have hFrontFrame :=
    grantDrainSettledNativeStepOutsidePair
      ring fresh update s e
      (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))
      hNotFrontSource hNotFrontResponder
  have hYDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPhysicalResponderBullet :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b =
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.b := by
    rw [hNative]
    simp [nativeE, hYDistinct]
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
    rcases hOld with hShield | hSignal | hBullet
    · left
      unfold grantDrainD6MergeFront
      rw [hDistance, hFrontFrame]
      simpa [grantDrainD6MergeFront] using hShield
    · right
      left
      unfold grantDrainD6MergeFront
      rw [hDistance, hFrontFrame]
      simpa [grantDrainD6MergeFront] using hSignal
    · right
      right
      rw [hDistance]
      intro hNewNone
      have hAllZero :=
        (grantDrainWarmBulletNoneCharacterization
          ring (grantDrainStep ring fresh update s e).native g
          (grantDrainLeftLeaderDistance ring s.native g)).mp
            hNewNone
      cases hFirst :
          grantDrainLeftBulletDistance ring s.native g
            (grantDrainLeftLeaderDistance ring s.native g) with
      | none =>
          exact hBullet hFirst
      | some j =>
          obtain ⟨hjPos, hjLe, hjHit, _⟩ :=
            (grantDrainWarmBulletSomeCharacterization
              ring s.native g
              (grantDrainLeftLeaderDistance ring s.native g)
              j).mp hFirst
          by_cases hAtSource : PPL.shiftLeft ring g j = e
          · have hOldBulletAtSource :
                (s.native e).b ≠ (0 : Fin 3) := by
              have hValue : (s.native e).b.val ≠ 0 := by
                rw [← hAtSource]
                exact hjHit
              intro hZero
              apply hValue
              rw [hZero]
              rfl
            have hNextAtResponder :=
              grantDrainD6FollowerPairResponderKeepsBullet
                (s.native e) (s.native (ring.rightNeighbor e))
                hXL hYL (Or.inl hOldBulletAtSource)
            have hNewValue :
                ((grantDrainStep ring fresh update s e).native
                  (ring.rightNeighbor e)).b.val ≠ 0 := by
              rw [hPhysicalResponderBullet]
              intro hz
              apply hNextAtResponder
              apply Fin.ext
              exact hz
            have hZeroAtK := hAllZero k hk (by omega)
            rw [← hResponder] at hZeroAtK
            exact hNewValue hZeroAtK
          · by_cases hAtResponder :
                PPL.shiftLeft ring g j = ring.rightNeighbor e
            · have hOldBulletAtResponder :
                  (s.native (ring.rightNeighbor e)).b ≠
                    (0 : Fin 3) := by
                have hValue :
                    (s.native (ring.rightNeighbor e)).b.val ≠ 0 := by
                  rw [← hAtResponder]
                  exact hjHit
                intro hZero
                apply hValue
                rw [hZero]
                rfl
              have hNextAtResponder :=
                grantDrainD6FollowerPairResponderKeepsBullet
                  (s.native e) (s.native (ring.rightNeighbor e))
                  hXL hYL (Or.inr hOldBulletAtResponder)
              have hNewValue :
                  ((grantDrainStep ring fresh update s e).native
                    (ring.rightNeighbor e)).b.val ≠ 0 := by
                rw [hPhysicalResponderBullet]
                intro hz
                apply hNextAtResponder
                apply Fin.ext
                exact hz
              have hZeroAtJ := hAllZero j hjPos hjLe
              rw [hAtResponder] at hZeroAtJ
              exact hNewValue hZeroAtJ
            · have hOutside :=
                grantDrainSettledNativeStepOutsidePair
                  ring fresh update s e
                  (PPL.shiftLeft ring g j)
                  hAtSource hAtResponder
              have hZeroAtJ := hAllZero j hjPos hjLe
              rw [hOutside] at hZeroAtJ
              exact hjHit hZeroAtJ
  have hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost,
      hNotHostSource, hNotHostResponder]
  intro q _ hNextHost _
  have hSame : g = q :=
    Option.some.inj (hNewHost.symm.trans hNextHost)
  subst q
  exact hPost

theorem grantDrainD6SpentInteriorFollowerFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (k : Nat) (hk : 1 ≤ k)
    (hInterior : k + 1 <
      grantDrainLeftLeaderDistance ring s.native g)
    (hSource : e = PPL.shiftLeft ring g (k + 1))
    (hResponder : ring.rightNeighbor e = PPL.shiftLeft ring g k)
    (hYL : (s.native (ring.rightNeighbor e)).l = false)
    (hFire : grantDrainSelect ring s e ≠ .none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC (hPhysical g hWarm hHost)
  have hOldArc :=
    grantDrainD6OldNearestArcOfScan ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hRange.1 hRange.2 rfl
  have hLeaderFrame :=
    grantDrainD6ResponderFollowerELeaderFrame
      ring hn s.native e hYL
  have hEArc :
      GrantDrainMarksNearestArc ring (nativeE ring s.native e)
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)) g := by
    refine ⟨hOldArc.1, ?_, ?_⟩
    · rw [hLeaderFrame]
      exact hOldArc.2.1
    · intro j hj hjShort
      rw [hLeaderFrame]
      exact hOldArc.2.2 j hj hjShort
  have hAt :
      g = PPL.shiftRight ring
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))
        (grantDrainLeftLeaderDistance ring s.native g) :=
    (grantDrainD6BirthShiftCancel ring g
      (grantDrainLeftLeaderDistance ring s.native g)
      hRange.2).symm
  have hOffset :=
    grantDrainD6BirthLeftOffset ring g
      (grantDrainLeftLeaderDistance ring s.native g)
      hRange.2
  have hSourceSite :
      e = PPL.shiftRight ring
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))
        (grantDrainLeftLeaderDistance ring s.native g - (k + 1)) := by
    calc
      e = PPL.shiftLeft ring g (k + 1) := hSource
      _ = PPL.shiftLeft ring
            (PPL.shiftRight ring
              (PPL.shiftLeft ring g
                (grantDrainLeftLeaderDistance ring s.native g))
              (grantDrainLeftLeaderDistance ring s.native g)) (k + 1) :=
            congrArg (fun z : Fin n => PPL.shiftLeft ring z (k + 1)) hAt
      _ = PPL.shiftRight ring
            (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))
            (grantDrainLeftLeaderDistance ring s.native g - (k + 1)) :=
            grantDrainMarksArcShiftLeftRight ring
              (PPL.shiftLeft ring g
                (grantDrainLeftLeaderDistance ring s.native g))
              (grantDrainLeftLeaderDistance ring s.native g)
              (k + 1) (by omega) hRange.2
  have hResponderSite :
      ring.rightNeighbor e = PPL.shiftRight ring
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g))
        (grantDrainLeftLeaderDistance ring s.native g - k) := by
    calc
      ring.rightNeighbor e = PPL.shiftLeft ring g k := hResponder
      _ = PPL.shiftLeft ring
            (PPL.shiftRight ring
              (PPL.shiftLeft ring g
                (grantDrainLeftLeaderDistance ring s.native g))
              (grantDrainLeftLeaderDistance ring s.native g)) k :=
            congrArg (fun z : Fin n => PPL.shiftLeft ring z k) hAt
      _ = PPL.shiftRight ring
            (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))
            (grantDrainLeftLeaderDistance ring s.native g - k) :=
            grantDrainMarksArcShiftLeftRight ring
              (PPL.shiftLeft ring g
                (grantDrainLeftLeaderDistance ring s.native g))
              (grantDrainLeftLeaderDistance ring s.native g)
              k (by omega) hRange.2
  have hSourceInside :
      grantDrainLeftLeaderDistance ring s.native g - (k + 1) <
      PPL.cyclicOffset ring
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)) g := by
    rw [hOffset]
    omega
  have hResponderInside :
      grantDrainLeftLeaderDistance ring s.native g - k <
      PPL.cyclicOffset ring
        (PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g)) g := by
    rw [hOffset]
    omega
  have hNewShield :
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native g)).sh =
        true := by
    change
      (grantDrainNativeNext ring s e
        (grantDrainD6MergeFront ring
          (grantDrainNativeNext ring s e) g)).sh = true
    cases hf : grantDrainSelect ring s e with
    | none =>
        exact False.elim (hFire hf)
    | leftLocal =>
        have hArc :=
          grantDrainD6NearestArcAfterBirth
            ring (nativeE ring s.native e)
            (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))
            g e
            (grantDrainLeftLeaderDistance ring s.native g - (k + 1))
            hEArc hSourceSite hSourceInside
        have hBorn :=
          (grantDrainD6MergeCanonicalBirthProtected
            (nativeE ring s.native e) e).2.1
        have hTarget :=
          grantDrainD6ShieldedFrontOfNearestArc
            ring (canonicalBirth (nativeE ring s.native e) e)
            e g hArc hBorn
        simpa [grantDrainNativeNext, hf] using hTarget
    | rightLocal =>
        have hArc :=
          grantDrainD6NearestArcAfterBirth
            ring (nativeE ring s.native e)
            (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))
            g (ring.rightNeighbor e)
            (grantDrainLeftLeaderDistance ring s.native g - k)
            hEArc hResponderSite hResponderInside
        have hBorn :=
          (grantDrainD6MergeCanonicalBirthProtected
            (nativeE ring s.native e) (ring.rightNeighbor e)).2.1
        have hTarget :=
          grantDrainD6ShieldedFrontOfNearestArc
            ring (canonicalBirth (nativeE ring s.native e)
              (ring.rightNeighbor e))
            (ring.rightNeighbor e) g hArc hBorn
        simpa [grantDrainNativeNext, hf] using hTarget
    | cross =>
        have hArc :=
          grantDrainD6NearestArcAfterBirth
            ring (nativeE ring s.native e)
            (PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g))
            g e
            (grantDrainLeftLeaderDistance ring s.native g - (k + 1))
            hEArc hSourceSite hSourceInside
        have hBorn :=
          (grantDrainD6MergeCanonicalBirthProtected
            (nativeE ring s.native e) e).2.1
        have hTarget :=
          grantDrainD6ShieldedFrontOfNearestArc
            ring (canonicalBirth (nativeE ring s.native e) e)
            e g hArc hBorn
        simpa [grantDrainNativeNext, hf] using hTarget
  have hNotHostSource : g ≠ e := by
    rw [hSource]
    have hDifferent :=
      grantDrainD6BirthLeftOffsetsDistinct ring g 0 (k + 1)
        (by omega : 0 < n)
        (by omega : k + 1 < n)
        (by omega : 0 ≠ k + 1)
    simpa only [grantDrainWarmShiftLeftZero] using hDifferent
  have hNotHostResponder : g ≠ ring.rightNeighbor e := by
    rw [hResponder]
    have hDifferent :=
      grantDrainD6BirthLeftOffsetsDistinct ring g 0 k
        (by omega : 0 < n)
        (by omega : k < n)
        (by omega : 0 ≠ k)
    simpa only [grantDrainWarmShiftLeftZero] using hDifferent
  have hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost,
      hNotHostSource, hNotHostResponder]
  intro q _ hNextHost _
  have hSame : g = q :=
    Option.some.inj (hNewHost.symm.trans hNextHost)
  subst q
  exact Or.inl hNewShield


/-- All strictly interior follower/follower contacts: the no-FIRE
case preserves the old witness (including moving bullets), while
every selected FIRE creates a shielded closer front. -/
theorem grantDrainD6SpentInteriorFollowerContact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (k : Nat) (hk : 1 ≤ k)
    (hInterior : k + 1 <
      grantDrainLeftLeaderDistance ring s.native g)
    (hSource : e = PPL.shiftLeft ring g (k + 1))
    (hResponder : ring.rightNeighbor e = PPL.shiftLeft ring g k)
    (hXL : (s.native e).l = false)
    (hYL : (s.native (ring.rightNeighbor e)).l = false) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  by_cases hNone : grantDrainSelect ring s e = .none
  · exact grantDrainD6SpentInteriorFollowerNoFire
      ring hn fresh update s e g label
      hC hInv hPhysical hWarm hHost hSpent
      k hk hInterior hSource hResponder hXL hYL hNone
  · exact grantDrainD6SpentInteriorFollowerFire
      ring hn fresh update s e g label
      hC hPhysical hWarm hHost
      k hk hInterior hSource hResponder hYL hNone

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
READY rows. Source-side signal consumption becomes a shield.
For a surviving ready responder, the literal DUMMY at the OLD
front remains in the inclusive left-bullet scan.
-/

/-- A ready OLD front acting as SOURCE becomes shielded; the
front-source proof also handles a selected responder-side birth. -/
theorem grantDrainD6SpentReadyFrontSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (hFront : grantDrainD6MergeFront ring s.native g = e)
    (hReady : (s.native e).sg = true)
    (hHostAwayY : g ≠ ring.rightNeighbor e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  exact grantDrainD6SpentProtectedFrontSource
    ring hn fresh update s e g label
    hC hPhysical hWarm hHost hSpent
    hFront (Or.inr hReady) hHostAwayY

/-- A ready OLD front acting as RESPONDER dummy-fires before
collision. If its leader survives and no FIRE is selected, the
DUMMY on that front is an inclusive left-bullet witness.
No OLD shield/signal/bullet disjunct needs to be chosen. -/
theorem grantDrainD6SpentReadyFrontResponderSurvivesNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (hFront :
      grantDrainD6MergeFront ring s.native g =
        ring.rightNeighbor e)
    (hReadyLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hReadySignal : (s.native (ring.rightNeighbor e)).sg = true)
    (hSurvives :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = true)
    (hHostAwayX : g ≠ e)
    (hHostAwayY : g ≠ ring.rightNeighbor e)
    (hNone : grantDrainSelect ring s e = .none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC (hPhysical g hWarm hHost)
  have hYDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hLeaderFrame :
      ∀ i : Fin n,
        (nativeE ring s.native e i).l = (s.native i).l := by
    intro i
    by_cases hAtX : i = e
    · subst i
      simpa [nativeE] using
        (grantDrainEntranceLiteralESourceLeaderFixed
          (s.native e) (s.native (ring.rightNeighbor e)))
    · by_cases hAtY : i = ring.rightNeighbor e
      · subst i
        exact hSurvives.trans hReadyLeader.symm
      · simp [nativeE, hAtX, hAtY]
  have hDistance :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g =
      grantDrainLeftLeaderDistance ring s.native g := by
    rw [grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone]
    simp [grantDrainLeftLeaderDistance, hLeaderFrame]
  have hPair :=
    grantDrainD6MergeReadyResponderDummyPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hReadyLeader hReadySignal
  have hNewBullet :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b = (1 : Fin 3) := by
    rw [grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone]
    simpa [nativeE, hYDistinct] using hPair.2.1
  have hOldFront :
      PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g) =
        ring.rightNeighbor e := by
    change
      PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g) =
        ring.rightNeighbor e at hFront
    exact hFront
  have hBulletWitness :
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g) ≠
          none := by
    rw [hDistance]
    intro hNoneBullet
    have hZero :=
      (grantDrainWarmBulletNoneCharacterization
        ring (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring s.native g)).mp
          hNoneBullet
          (grantDrainLeftLeaderDistance ring s.native g)
          hOldRange.1 (Nat.le_refl _)
    rw [hOldFront, hNewBullet] at hZero
    have hNonzero : (1 : Fin 3).val ≠ 0 := by decide
    exact hNonzero hZero
  have hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost,
      hHostAwayX, hHostAwayY]
  intro q _ hNextHost _
  have hSame : g = q :=
    Option.some.inj (hNewHost.symm.trans hNextHost)
  subst q
  exact Or.inr (Or.inr hBulletWitness)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Actual E+FIRE front-death kernel without using the
OLD exceptionalLeft flag or the exceptional-death Boolean guard.
In particular the old inclusive scan may contain a bullet.
-/

/-- A warm follower cannot itself be the effective source of a
quiet unshielded nearest-leader responder death. This uses the
literal E pair, not an exceptional-reserve test. -/
theorem grantDrainD6QuietFrontDeathSourceAwayWarm
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hUnshield :
      (s.native (ring.rightNeighbor e)).sh = false)
    (hQuiet : (s.native (ring.rightNeighbor e)).sg = false)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false) :
    g ≠ e := by
  intro hSame
  have hOld := grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hFollower : (s.native e).l = false := by
    rw [← hSame]
    exact hOld.1
  have hEmpty : (s.native e).b = (0 : Fin 3) := by
    rw [← hSame]
    exact hOld.2.1
  have hPair :=
    grantDrainD6DeathEmptyFollowerCannotKill
      (s.native e) (s.native (ring.rightNeighbor e))
      hFollower hEmpty hLeader hUnshield hQuiet
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hAlive :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        true := by
    simpa [nativeE, hDistinct] using hPair
  rw [hAlive] at hDeath
  cases hDeath

/-- General front-death shield transport, valid EVEN WITH an old
left bullet and with arbitrary OLD exceptional-reserve flag.
the earlier nearest-arc concatenation and protected killer apply
because this is the old quiet, unshielded leader responder. -/
theorem grantDrainD6QuietFrontDeathPhysicalNewShield
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hFront :
      grantDrainD6MergeFront ring s.native g =
        ring.rightNeighbor e)
    (hUnshield :
      (s.native (ring.rightNeighbor e)).sh = false)
    (hQuiet :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hDeath :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = false) :
    ((grantDrainStep ring fresh update s e).native
      (grantDrainD6MergeFront ring
        (grantDrainStep ring fresh update s e).native g)).sh =
      true := by
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hOldArc :
      GrantDrainMarksNearestArc ring s.native
        (ring.rightNeighbor e) g := by
    have hArc :=
      grantDrainD6OldNearestArcOfScan ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.1 hRange.2 rfl
    change GrantDrainMarksNearestArc ring s.native
      (grantDrainD6MergeFront ring s.native g) g at hArc
    rw [hFront] at hArc
    exact hArc
  have hLeader : (s.native (ring.rightNeighbor e)).l =
      true := hOldArc.2.1
  obtain ⟨q, hQLeader, hBehind, hLeftArc, _hZero,
      hQShield⟩ :=
    grantDrainWeakDeathFrontRootHolds
      ring hn s e (ring.rightNeighbor e) hC.1.1
      rfl hLeader hUnshield hQuiet hDeath
  have hFollower :=
    (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  have hNoWrap :=
    grantDrainWeakDeathArcNonoverlap
      ring s.native q (ring.rightNeighbor e) g
      hQLeader hBehind hOldArc hFollower
  have hRight :=
    grantDrainWeakDeathRightFollowersAfterE
      ring hn s e (ring.rightNeighbor e) g rfl hOldArc
  have hEArc :
      GrantDrainMarksNearestArc ring
        (nativeE ring s.native e) q g :=
    grantDrainD6NearestArcConcat ring
      (nativeE ring s.native e) q
      (ring.rightNeighbor e) g
      hLeftArc hDeath hRight hNoWrap
  have hSites :=
    grantDrainWeakDeathSpliceBirthSites
      ring hn e q (ring.rightNeighbor e) g
      rfl hBehind hOldArc.1 hNoWrap
  change
    (grantDrainNativeNext ring s e
      (grantDrainD6MergeFront ring
        (grantDrainNativeNext ring s e) g)).sh = true
  cases hf : grantDrainSelect ring s e with
  | none =>
      have hTarget :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (nativeE ring s.native e) q g
          hEArc hQShield
      simpa [grantDrainNativeNext, hf] using hTarget
  | leftLocal =>
      obtain ⟨j, hSite, hInside⟩ := hSites.1
      have hArc :=
        grantDrainD6NearestArcAfterBirth
          ring (nativeE ring s.native e) q g e j
          hEArc hSite hInside
      have hBorn :=
        (grantDrainD6MergeCanonicalBirthProtected
          (nativeE ring s.native e) e).2.1
      have hTarget :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (canonicalBirth (nativeE ring s.native e) e)
          e g hArc hBorn
      simpa [grantDrainNativeNext, hf] using hTarget
  | rightLocal =>
      obtain ⟨j, hSite, hInside⟩ := hSites.2
      have hArc :=
        grantDrainD6NearestArcAfterBirth
          ring (nativeE ring s.native e) q g
          (ring.rightNeighbor e) j hEArc hSite hInside
      have hBorn :=
        (grantDrainD6MergeCanonicalBirthProtected
          (nativeE ring s.native e)
          (ring.rightNeighbor e)).2.1
      have hTarget :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (canonicalBirth (nativeE ring s.native e)
            (ring.rightNeighbor e))
          (ring.rightNeighbor e) g hArc hBorn
      simpa [grantDrainNativeNext, hf] using hTarget
  | cross =>
      obtain ⟨j, hSite, hInside⟩ := hSites.1
      have hArc :=
        grantDrainD6NearestArcAfterBirth
          ring (nativeE ring s.native e) q g e j
          hEArc hSite hInside
      have hBorn :=
        (grantDrainD6MergeCanonicalBirthProtected
          (nativeE ring s.native e) e).2.1
      have hTarget :=
        grantDrainD6ShieldedFrontOfNearestArc
          ring (canonicalBirth (nativeE ring s.native e) e)
          e g hArc hBorn
      simpa [grantDrainNativeNext, hf] using hTarget

/-- Actual label-level H2 closure of a quiet, unshielded OLD
front killed at the responder. The OLD spent witness may be a
bullet: the earlier shielded recomputed leader still follows from
the physical death row, without the exceptional-death guard. -/
theorem grantDrainD6SpentQuietFrontResponderDeath
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hFront :
      grantDrainD6MergeFront ring s.native g =
        ring.rightNeighbor e)
    (hUnshield :
      (s.native (ring.rightNeighbor e)).sh = false)
    (hQuiet :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hDeath :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = false) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldPhysical := hPhysical g hWarm hHost
  have hShield :=
    grantDrainD6QuietFrontDeathPhysicalNewShield
      ring hn fresh update s e g
      hC hOldPhysical hFront hUnshield hQuiet hDeath
  have hOldLeader :
      (s.native (ring.rightNeighbor e)).l = true := by
    have hL :=
      grantDrainD6OldWarmFrontLeader
        ring hn s g hC hOldPhysical
    change
      (s.native (grantDrainD6MergeFront ring s.native g)).l =
        true at hL
    rw [hFront] at hL
    exact hL
  have hNotX :=
    grantDrainD6QuietFrontDeathSourceAwayWarm
      ring hn s e g hOldPhysical hOldLeader
      hUnshield hQuiet hDeath
  have hNotY : g ≠ ring.rightNeighbor e := by
    intro hSame
    have hFollower :=
      (grantDrainD6ExceptionalDeathHostFields
        s g hOldPhysical).1
    have hL :=
      grantDrainD6OldWarmFrontLeader
        ring hn s g hC hOldPhysical
    change
      (s.native (grantDrainD6MergeFront ring s.native g)).l =
        true at hL
    rw [hFront, ← hSame, hFollower] at hL
    cases hL
  have hKept :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost, hNotX, hNotY]
  intro q _ hNextHost _
  have hSame : g = q :=
    Option.some.inj (hKept.symm.trans hNextHost)
  subst q
  exact Or.inl hShield

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Ready responder death: a DUMMY is created before collision. -/

/-- An empty follower cannot delete any leader responder, ready
or quiet; source LIVE is essential for a follower-source death. -/
theorem grantDrainD6EmptyFollowerNoResponderDeath
    (x y : CertNative)
    (hFollower : x.l = false)
    (hEmpty : x.b = (0 : Fin 3))
    (hLeader : y.l = true) :
    (certLiteralEPair x y).2.l = true := by
  cases hReady : y.sg with
  | false =>
      simp [certLiteralEPair, hFollower, hEmpty,
        hLeader, hReady, certFinThree]
  | true =>
      simp [certLiteralEPair, hFollower, hEmpty,
        hLeader, hReady, certFinThree]

/-- General responder death cannot originate at the warm host,
without any premise about the old victim's shield or signal. -/
theorem grantDrainD6AnyFrontDeathSourceAwayWarm
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hWarm : grantDrainWarmAt s g = true)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        false) :
    g ≠ e := by
  intro hSame
  have hOld :=
    grantDrainD6ExceptionalDeathHostFields s g hWarm
  have hFollower : (s.native e).l = false := by
    rw [← hSame]
    exact hOld.1
  have hEmpty : (s.native e).b = (0 : Fin 3) := by
    rw [← hSame]
    exact hOld.2.1
  have hAlivePair :=
    grantDrainD6EmptyFollowerNoResponderDeath
      (s.native e) (s.native (ring.rightNeighbor e))
      hFollower hEmpty hLeader
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hAlive :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        true := by
    simpa [nativeE, hDistinct] using hAlivePair
  rw [hAlive] at hDeath
  cases hDeath

/-- A ready OLD responder always leaves its DUMMY on its own
site after E, even when the incoming LIVE kills its leader flag.
This is independent of source state and the FIRE selector. -/
theorem grantDrainD6ReadyResponderDummyNativeE
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLeader : (N (ring.rightNeighbor e)).l = true)
    (hReady : (N (ring.rightNeighbor e)).sg = true) :
    (nativeE ring N e (ring.rightNeighbor e)).b =
      (1 : Fin 3) := by
  have hPair :=
    grantDrainD6MergeReadyResponderDummyPair
      (N e) (N (ring.rightNeighbor e))
      hLeader hReady
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  simpa [nativeE, hDistinct] using hPair.2.1

theorem grantDrainD6SpentReadyFrontResponderNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hFront :
      grantDrainD6MergeFront ring s.native g =
        ring.rightNeighbor e)
    (hReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hNone : grantDrainSelect ring s e = .none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hWarmPhysical := hPhysical g hWarm hHost
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarmPhysical
  have hOldArc :
      GrantDrainMarksNearestArc ring s.native
        (ring.rightNeighbor e) g := by
    have hArc :=
      grantDrainD6OldNearestArcOfScan ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.1 hRange.2 rfl
    change GrantDrainMarksNearestArc ring s.native
      (grantDrainD6MergeFront ring s.native g) g at hArc
    rw [hFront] at hArc
    exact hArc
  have hOldLeader := hOldArc.2.1
  have hNative :=
    grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone
  have hRightFollowers :=
    grantDrainWeakDeathRightFollowersAfterE
      ring hn s e (ring.rightNeighbor e) g rfl hOldArc
  have hAt :
      g = PPL.shiftRight ring (ring.rightNeighbor e)
        (grantDrainLeftLeaderDistance ring s.native g) := by
    have hShift :=
      (grantDrainD6BirthShiftCancel ring g
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.2).symm
    change
      g = PPL.shiftRight ring
        (grantDrainD6MergeFront ring s.native g)
        (grantDrainLeftLeaderDistance ring s.native g) at hShift
    rw [hFront] at hShift
    exact hShift
  have hNewNoLeader :
      ∀ j : Nat, 1 ≤ j →
        j < grantDrainLeftLeaderDistance ring s.native g →
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring g j)).l = false := by
    intro j hj hjBefore
    have hShift :
        PPL.shiftLeft ring g j =
          PPL.shiftRight ring (ring.rightNeighbor e)
            (grantDrainLeftLeaderDistance ring s.native g - j) := by
      calc
        PPL.shiftLeft ring g j =
            PPL.shiftLeft ring
              (PPL.shiftRight ring (ring.rightNeighbor e)
                (grantDrainLeftLeaderDistance ring s.native g)) j :=
            congrArg (fun z : Fin n => PPL.shiftLeft ring z j) hAt
        _ = PPL.shiftRight ring (ring.rightNeighbor e)
              (grantDrainLeftLeaderDistance ring s.native g - j) :=
            grantDrainMarksArcShiftLeftRight
              ring (ring.rightNeighbor e)
              (grantDrainLeftLeaderDistance ring s.native g)
              j (by omega) hRange.2
    rw [hNative, hShift]
    have hOffset :=
      grantDrainMarksScanOfNearestArc
        ring s.native (ring.rightNeighbor e) g hOldArc
    have hInside :
        grantDrainLeftLeaderDistance ring s.native g - j <
          PPL.cyclicOffset ring (ring.rightNeighbor e) g := by
      rw [← hOffset]
      omega
    exact hRightFollowers
      (grantDrainLeftLeaderDistance ring s.native g - j)
      (by omega) hInside
  have hNewDistance :
      grantDrainLeftLeaderDistance ring s.native g ≤
        grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g :=
    grantDrainD6DeathLeaderPrefixLowerBound
      ring (grantDrainStep ring fresh update s e).native
      g (grantDrainLeftLeaderDistance ring s.native g)
      (Nat.le_of_lt hRange.2) hNewNoLeader
  have hNewBullet :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b = (1 : Fin 3) := by
    rw [hNative]
    exact grantDrainD6ReadyResponderDummyNativeE
      ring hn s.native e hOldLeader hReady
  have hBullet :
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g) ≠
          none := by
    intro hNoneBullet
    have hZero :=
      (grantDrainWarmBulletNoneCharacterization
        ring (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g)).mp
        hNoneBullet
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.1 hNewDistance
    have hOldFront :
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g) =
            ring.rightNeighbor e := hFront
    rw [hOldFront, hNewBullet] at hZero
    have hOneNonzero : (1 : Fin 3).val ≠ 0 := by decide
    exact hOneNonzero hZero
  intro q _ hNewHost _
  by_cases hSame : q = g
  · subst q
    exact Or.inr (Or.inr hBullet)
  · obtain ⟨hHostResponder, _⟩ :=
      grantDrainD6HostChangedOnlyResponderToSource
        ring hn fresh update s e g q label
        hHost hNewHost hSame
    have hFollower :=
      (grantDrainD6ExceptionalDeathHostFields
        s g hWarmPhysical).1
    rw [hHostResponder, hOldLeader] at hFollower
    cases hFollower


end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! The actual Y-to-X HOST MOVE has an exact spent-witness
rebase. No post-state scan premise is assumed. -/

theorem grantDrainD6SpentHostMoveToSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n) (d : Nat)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hOldWarm : label.warm = true)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hSpent : label.exceptionalLeft = false)
    (hDistance :
      grantDrainLeftLeaderDistance ring s.native
        (ring.rightNeighbor e) = d)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e label).warm =
        true)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e label).host =
        some e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldPhysical :=
    hPhysical (ring.rightNeighbor e) hOldWarm hHost
  have hNone :=
    grantDrainD6MovingHostNoFire
      ring hn fresh update s e label
      hHost hNewHost hNewWarm
  have hNewPhysical :=
    grantDrainD6HostNextWarmPhysical
      ring fresh update s e e label hNewHost hNewWarm
  have hOldY :=
    grantDrainD6ExceptionalDeathHostFields
      s (ring.rightNeighbor e) hOldPhysical
  have hXFollower :=
    grantDrainD6MovingHostOldSourceFollower
      ring fresh update s e hNone hNewPhysical
  have hXEmpty :=
    grantDrainD6MovingHostOldSourceEmpty
      ring hn fresh update s e hC hNone
      hOldY.1 hOldY.2.1 hNewPhysical
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s (ring.rightNeighbor e) hC hOldPhysical
  have hNotOne : d ≠ 1 := by
    intro hOne
    have hOldLeader :=
      grantDrainD6OldWarmFrontLeader
        ring hn s (ring.rightNeighbor e) hC hOldPhysical
    rw [hDistance, hOne,
      grantDrainWarmRightNeighborLeftOne ring hn e,
      hXFollower] at hOldLeader
    cases hOldLeader
  have hTwo : 2 ≤ d := by
    rw [hDistance] at hRange
    omega
  have hShort : d < n := by
    rw [hDistance] at hRange
    exact hRange.2
  have hLiteral :=
    grantDrainWarmEmptyFollowerSignalCopyNativeE
      ring s.native e hXFollower hXEmpty hOldY.1 hOldY.2.1
  have hNative :=
    grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone
  have hLeader :
      ∀ i : Fin n,
        ((grantDrainStep ring fresh update s e).native i).l =
          (s.native i).l := by
    intro i
    rw [hNative]
    exact (hLiteral i).1
  have hBullet :
      ∀ i : Fin n,
        ((grantDrainStep ring fresh update s e).native i).b =
          (s.native i).b := by
    intro i
    rw [hNative]
    exact (hLiteral i).2.1
  have hLeftOne :
      PPL.shiftLeft ring (ring.rightNeighbor e) 1 = e :=
    grantDrainWarmRightNeighborLeftOne ring hn e
  have hNewDistance :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native e =
          d - 1 := by
    have hRebase :=
      grantDrainWarmLeaderRebase ring hn s.native
        (ring.rightNeighbor e) d hTwo hShort hDistance
    rw [hLeftOne] at hRebase
    have hSame :
        grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native e =
        grantDrainLeftLeaderDistance ring s.native e := by
      simp [grantDrainLeftLeaderDistance, hLeader]
    exact hSame.trans hRebase
  have hFrontRebase :
      PPL.shiftLeft ring e (d - 1) =
        PPL.shiftLeft ring (ring.rightNeighbor e) d := by
    calc
      PPL.shiftLeft ring e (d - 1) =
          PPL.shiftLeft ring
            (PPL.shiftLeft ring (ring.rightNeighbor e) 1)
            (d - 1) := by rw [hLeftOne]
      _ = PPL.shiftLeft ring (ring.rightNeighbor e)
            (d - 1 + 1) :=
          grantDrainWarmShiftLeftOneAdd
            ring (by omega : 2 ≤ n)
            (ring.rightNeighbor e) (d - 1)
      _ = PPL.shiftLeft ring (ring.rightNeighbor e) d := by
          have hSum : d - 1 + 1 = d := by omega
          rw [hSum]
  have hFrontLeader :=
    grantDrainD6OldWarmFrontLeader
      ring hn s (ring.rightNeighbor e) hC hOldPhysical
  rw [hDistance] at hFrontLeader
  have hNotSource :
      PPL.shiftLeft ring (ring.rightNeighbor e) d ≠ e := by
    intro hAt
    rw [hAt, hXFollower] at hFrontLeader
    cases hFrontLeader
  have hNotResponder :
      PPL.shiftLeft ring (ring.rightNeighbor e) d ≠
        ring.rightNeighbor e := by
    intro hAt
    rw [hAt, hOldY.1] at hFrontLeader
    cases hFrontLeader
  have hFrontFrame :=
    grantDrainSettledNativeStepOutsidePair
      ring fresh update s e
      (PPL.shiftLeft ring (ring.rightNeighbor e) d)
      hNotSource hNotResponder
  have hOldWitness :=
    hInv (ring.rightNeighbor e) hOldWarm hHost hSpent
  have hPost :
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native e)).sh =
            true ∨
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native e)).sg =
            true ∨
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native e
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native e) ≠
            none := by
    rcases hOldWitness with hShield | hSignal | hOldBullet
    · left
      change (s.native
        (PPL.shiftLeft ring (ring.rightNeighbor e)
          (grantDrainLeftLeaderDistance ring s.native
            (ring.rightNeighbor e)))).sh = true at hShield
      rw [hDistance] at hShield
      change
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring e
            (grantDrainLeftLeaderDistance ring
              (grantDrainStep ring fresh update s e).native e))).sh =
          true
      rw [hNewDistance, hFrontRebase, hFrontFrame]
      exact hShield
    · right
      left
      change (s.native
        (PPL.shiftLeft ring (ring.rightNeighbor e)
          (grantDrainLeftLeaderDistance ring s.native
            (ring.rightNeighbor e)))).sg = true at hSignal
      rw [hDistance] at hSignal
      change
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring e
            (grantDrainLeftLeaderDistance ring
              (grantDrainStep ring fresh update s e).native e))).sg =
          true
      rw [hNewDistance, hFrontRebase, hFrontFrame]
      exact hSignal
    · right
      right
      rw [hDistance] at hOldBullet
      cases hFirst :
          grantDrainLeftBulletDistance ring s.native
            (ring.rightNeighbor e) d with
      | none =>
          exact False.elim (hOldBullet hFirst)
      | some j =>
          obtain ⟨hJPos, hJBound, hJHit, _⟩ :=
            (grantDrainWarmBulletSomeCharacterization
              ring s.native (ring.rightNeighbor e) d j).mp
                hFirst
          have hJNotOne : j ≠ 1 := by
            intro hOne
            rw [hOne, hLeftOne, hXEmpty] at hJHit
            exact hJHit (by decide)
          have hJTwo : 2 ≤ j := by omega
          have hRebase :=
            grantDrainWarmBulletRebaseSome
              ring hn s.native (ring.rightNeighbor e)
              d j hTwo hJTwo hJBound hFirst
          rw [hLeftOne] at hRebase
          have hSameBullets :
              grantDrainLeftBulletDistance ring
                (grantDrainStep ring fresh update s e).native
                e (d - 1) =
              grantDrainLeftBulletDistance ring s.native
                e (d - 1) := by
            simp [grantDrainLeftBulletDistance, hBullet]
          have hPostBullet :
              grantDrainLeftBulletDistance ring
                (grantDrainStep ring fresh update s e).native
                e (d - 1) = some (j - 1) :=
            hSameBullets.trans hRebase
          rw [hNewDistance, hPostBullet]
          intro hImpossible
          cases hImpossible
  intro q _ hNextHost hNextSpent
  have hSame : e = q :=
    Option.some.inj (hNewHost.symm.trans hNextHost)
  subst q
  exact hPost


end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Literal old-front SOURCE with an OLD resident bullet. -/

/-- A leader with a resident OLD DUMMY/LIVE cannot select a
canonical birth when its responder is a follower. Every selected
case would force that same source bullet to be empty, by the
proved source-leader eligibility row. -/
theorem grantDrainD6BulletLeaderFollowerNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader : (s.native e).l = true)
    (hBullet : (s.native e).b ≠ (0 : Fin 3))
    (hYFollower :
      (s.native (ring.rightNeighbor e)).l = false) :
    grantDrainSelect ring s e = .none := by
  cases hf : grantDrainSelect ring s e with
  | none => rfl
  | leftLocal =>
      have hFields :=
        grantDrainD6SourceLeaderSelectedFollowerFields
          ring hn s e e hLeader hYFollower
          (Or.inl ⟨hf, rfl⟩)
      exact False.elim (hBullet hFields.2.1)
  | rightLocal =>
      have hFields :=
        grantDrainD6SourceLeaderSelectedFollowerFields
          ring hn s e (ring.rightNeighbor e)
          hLeader hYFollower
          (Or.inr (Or.inl ⟨hf, rfl⟩))
      exact False.elim (hBullet hFields.2.1)
  | cross =>
      have hFields :=
        grantDrainD6SourceLeaderSelectedFollowerFields
          ring hn s e e hLeader hYFollower
          (Or.inr (Or.inr ⟨hf, rfl⟩))
      exact False.elim (hBullet hFields.2.1)

theorem grantDrainD6BulletLeaderFollowerPhysicalRow
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hC : C_native ring s.native)
    (hLeader : (s.native e).l = true)
    (hBullet : (s.native e).b ≠ (0 : Fin 3))
    (hYFollower :
      (s.native (ring.rightNeighbor e)).l = false) :
    grantDrainSelect ring s e = .none ∧
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b = (s.native e).b ∧
      (∀ i : Fin n,
        ((grantDrainStep ring fresh update s e).native i).l =
          (s.native i).l) := by
  have hNoFire :=
    grantDrainD6BulletLeaderFollowerNoFire
      ring hn s e hLeader hBullet hYFollower
  have hQuiet :=
    grantDrainD6OutgoingBulletSourceQuiet
      ring s.native hC e hBullet
  have hLocal : GrantDrainEntranceILocal ring s.native :=
    (grantDrainEntranceIffILocal ring s.native).mp hC.1
  have hYEmpty :=
    grantDrainEntranceILocalFollowerBulletNextEmpty
      ring s.native e hLocal hBullet hYFollower
  have hPair :=
    grantDrainD6NoFireLeaderBulletPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hLeader hQuiet hBullet hYFollower hYEmpty
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hYBullet :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (s.native e).b := by
    simpa [nativeE, hDistinct] using hPair.1
  have hYLeader :
      (nativeE ring s.native e (ring.rightNeighbor e)).l =
        (s.native (ring.rightNeighbor e)).l := by
    have hPairLeader :=
      grantDrainEntranceLiteralEFollowerResponderRemains
        (s.native e) (s.native (ring.rightNeighbor e))
        hYFollower
    have hEZero :
        (nativeE ring s.native e (ring.rightNeighbor e)).l = false := by
      simpa [nativeE, hDistinct] using hPairLeader
    exact hEZero.trans hYFollower.symm
  have hELeaders :=
    grantDrainEntranceNativeELeadersFixed
      ring (by omega : 2 ≤ n) s.native e hYLeader
  have hNative :=
    grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNoFire
  refine ⟨hNoFire, ?_, ?_⟩
  · rw [hNative]
    exact hYBullet
  · intro i
    rw [hNative]
    exact hELeaders i


/-- If e is the actual old nearest leader of a warm follower g,
its clockwise responder remains a follower, including the
distance-one endpoint case where that responder is g itself. -/
theorem grantDrainD6FrontSourceResponderIsFollower
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hFront : grantDrainD6MergeFront ring s.native g = e) :
    (s.native (ring.rightNeighbor e)).l = false := by
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarm
  have hOldArc :
      GrantDrainMarksNearestArc ring s.native e g := by
    have hArc :=
      grantDrainD6OldNearestArcOfScan ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.1 hRange.2 rfl
    change GrantDrainMarksNearestArc ring s.native
      (grantDrainD6MergeFront ring s.native g) g at hArc
    rw [hFront] at hArc
    exact hArc
  have hResponder :
      PPL.shiftRight ring e 1 = ring.rightNeighbor e := by
    apply Fin.ext
    rfl
  have hOffset :=
    grantDrainMarksScanOfNearestArc ring s.native e g hOldArc
  by_cases hOne :
      grantDrainLeftLeaderDistance ring s.native g = 1
  · have hG :
        g = ring.rightNeighbor e := by
      have hAt :=
        (grantDrainMarksArcShiftRightOffset ring e g).symm
      rw [← hOffset, hOne, hResponder] at hAt
      exact hAt
    rw [← hG]
    exact (grantDrainD6ExceptionalDeathHostFields s g hWarm).1
  · have hLarge :
        1 < PPL.cyclicOffset ring e g := by
      rw [← hOffset]
      omega
    rw [← hResponder]
    exact hOldArc.2.2 1 (by omega) hLarge

/-- OLD front SOURCE with an actual resident bullet, away from the
warm host's responder site: the OLD source is a leader, so it
cannot birth, and its bullet moves into the new inclusive scan.
The next nearest-leader distance stays fixed. -/
theorem grantDrainD6SpentFrontSourceBulletAway
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hFront : grantDrainD6MergeFront ring s.native g = e)
    (hBullet : (s.native e).b ≠ (0 : Fin 3))
    (hAway : g ≠ ring.rightNeighbor e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldPhysical := hPhysical g hWarm hHost
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hOldPhysical
  have hLeader : (s.native e).l = true := by
    have hL :=
      grantDrainD6OldWarmFrontLeader
        ring hn s g hC hOldPhysical
    change
      (s.native (grantDrainD6MergeFront ring s.native g)).l =
        true at hL
    rw [hFront] at hL
    exact hL
  have hYFollower :=
    grantDrainD6FrontSourceResponderIsFollower
      ring hn s e g hC hOldPhysical hFront
  obtain ⟨hNone, hNewYBullet, hNewLeaders⟩ :=
    grantDrainD6BulletLeaderFollowerPhysicalRow
      ring hn fresh update s e hC hLeader hBullet hYFollower
  have hNewDistance :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g =
      grantDrainLeftLeaderDistance ring s.native g := by
    simp [grantDrainLeftLeaderDistance, hNewLeaders]
  have hSource :
      e = PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g) :=
    hFront.symm
  have hTo :=
    grantDrainD6OutgoingBulletSuccessorAtOffset
      ring g e (grantDrainLeftLeaderDistance ring s.native g)
      hRange.1 hRange.2 hSource
  have hGreater :
      2 ≤ grantDrainLeftLeaderDistance ring s.native g := by
    by_cases hOne :
        grantDrainLeftLeaderDistance ring s.native g = 1
    · have hYG : ring.rightNeighbor e = g := by
        rw [hTo, hOne]
        simp only [Nat.sub_self, grantDrainWarmShiftLeftZero]
      exact False.elim (hAway hYG.symm)
    · omega
  have hNewBullet :
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g) ≠
          none := by
    rw [hNewDistance]
    intro hNoneBullet
    have hZero :=
      (grantDrainWarmBulletNoneCharacterization
        ring (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring s.native g)).mp
        hNoneBullet
        (grantDrainLeftLeaderDistance ring s.native g - 1)
        (by omega) (by omega)
    rw [← hTo, hNewYBullet] at hZero
    have hVal : (s.native e).b.val ≠ 0 := by
      intro hz
      apply hBullet
      apply Fin.ext
      exact hz
    exact hVal hZero
  have hNotSource : g ≠ e := by
    intro hG
    have hFollower :=
      (grantDrainD6ExceptionalDeathHostFields
        s g hOldPhysical).1
    rw [hG, hLeader] at hFollower
    cases hFollower
  have hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost, hNotSource, hAway]
  intro q _ hNextHost _
  have hSame : g = q :=
    Option.some.inj (hNewHost.symm.trans hNextHost)
  subst q
  exact Or.inr (Or.inr hNewBullet)

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- The distance-one OLD front-source bullet transfer is not a
continuing warm case. Its responder is the tracked warm host:
that host acquires a nonzero bullet, while a moved host at the
OLD source would be a leader. Both possibilities are cold. -/
theorem grantDrainD6SpentFrontSourceBulletAtHost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hFront :
      grantDrainD6MergeFront ring s.native
        (ring.rightNeighbor e) = e)
    (hBullet : (s.native e).b ≠ (0 : Fin 3)) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldPhysical :=
    hPhysical (ring.rightNeighbor e) hWarm hHost
  have hLeader : (s.native e).l = true := by
    have hL :=
      grantDrainD6OldWarmFrontLeader
        ring hn s (ring.rightNeighbor e) hC hOldPhysical
    change
      (s.native
        (grantDrainD6MergeFront ring s.native
          (ring.rightNeighbor e))).l = true at hL
    rw [hFront] at hL
    exact hL
  have hYFollower :=
    (grantDrainD6ExceptionalDeathHostFields
      s (ring.rightNeighbor e) hOldPhysical).1
  obtain ⟨_hNone, hNewYBullet, hLeaderFrame⟩ :=
    grantDrainD6BulletLeaderFollowerPhysicalRow
      ring hn fresh update s e hC hLeader hBullet hYFollower
  have hYBullet :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b ≠ (0 : Fin 3) := by
    rw [hNewYBullet]
    exact hBullet
  have hYCold :=
    grantDrainWarmPhysicalBulletEndsWarm
      (grantDrainStep ring fresh update s e)
      (ring.rightNeighbor e) hYBullet
  have hXLeader :
      ((grantDrainStep ring fresh update s e).native e).l =
        true := by
    rw [hLeaderFrame e]
    exact hLeader
  intro q hNewWarm hNewHost _
  have hPhysicalNew :=
    grantDrainD6HostNextWarmPhysical
      ring fresh update s e q label hNewHost hNewWarm
  by_cases hSame : q = ring.rightNeighbor e
  · rw [hSame, hYCold] at hPhysicalNew
    cases hPhysicalNew
  · obtain ⟨_, hSource⟩ :=
      grantDrainD6HostChangedOnlyResponderToSource
        ring hn fresh update s e
        (ring.rightNeighbor e) q label
        hHost hNewHost hSame
    rw [hSource] at hPhysicalNew
    simp [grantDrainWarmAt, hXLeader] at hPhysicalNew

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
All READY front-responder FIRE modes. The emitted DUMMY at
the old front survives; the only eligible birth can be at the
source, outside the strictly positive old backward scan.
-/

/-- A ready responder with its freshly emitted DUMMY is not a
candidate rightLocal FIRE site after literal E. -/
theorem grantDrainD6ReadyResponderCannotBirthAtResponder
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hReady : (s.native (ring.rightNeighbor e)).sg = true) :
    grantDrainSelect ring s e ≠ .rightLocal := by
  have hDummy :=
    grantDrainD6ReadyResponderDummyNativeE
      ring hn s.native e hLeader hReady
  have hNotEligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hDummy]
  intro hRight
  have hEligible :=
    grantDrainD6SelectedEligible ring s e
      (ring.rightNeighbor e)
      (Or.inr (Or.inl ⟨hRight, rfl⟩))
  rw [hNotEligible] at hEligible
  cases hEligible

theorem grantDrainD6SpentReadyFrontResponderAwaySource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hFront :
      grantDrainD6MergeFront ring s.native g =
        ring.rightNeighbor e)
    (hReady :
      (s.native (ring.rightNeighbor e)).sg = true)
    (hAway : g ≠ e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldPhysical := hPhysical g hWarm hHost
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hOldPhysical
  have hOldArc :
      GrantDrainMarksNearestArc ring s.native
        (ring.rightNeighbor e) g := by
    have hArc :=
      grantDrainD6OldNearestArcOfScan ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.1 hRange.2 rfl
    change GrantDrainMarksNearestArc ring s.native
      (grantDrainD6MergeFront ring s.native g) g at hArc
    rw [hFront] at hArc
    exact hArc
  have hOldLeader := hOldArc.2.1
  have hNoRight :=
    grantDrainD6ReadyResponderCannotBirthAtResponder
      ring hn s e hOldLeader hReady
  have hEDummy :=
    grantDrainD6ReadyResponderDummyNativeE
      ring hn s.native e hOldLeader hReady
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hAt :
      g = PPL.shiftRight ring (ring.rightNeighbor e)
        (grantDrainLeftLeaderDistance ring s.native g) := by
    have hShift :=
      (grantDrainD6BirthShiftCancel ring g
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.2).symm
    change
      g = PPL.shiftRight ring
        (grantDrainD6MergeFront ring s.native g)
        (grantDrainLeftLeaderDistance ring s.native g) at hShift
    rw [hFront] at hShift
    exact hShift
  have hEOutside :
      ∀ j : Nat, 1 ≤ j →
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g j ≠ e :=
    grantDrainD6DeathSourceOutsidePositive
      ring hn e (ring.rightNeighbor e) g
      (grantDrainLeftLeaderDistance ring s.native g)
      hRange.2 hAt rfl
  have hRightFollowers :=
    grantDrainWeakDeathRightFollowersAfterE
      ring hn s e (ring.rightNeighbor e) g rfl hOldArc
  have hNewNoLeader :
      ∀ j : Nat, 1 ≤ j →
        j < grantDrainLeftLeaderDistance ring s.native g →
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring g j)).l = false := by
    intro j hj hjBefore
    have hShift :
        PPL.shiftLeft ring g j =
          PPL.shiftRight ring (ring.rightNeighbor e)
            (grantDrainLeftLeaderDistance ring s.native g - j) := by
      calc
        PPL.shiftLeft ring g j =
            PPL.shiftLeft ring
              (PPL.shiftRight ring (ring.rightNeighbor e)
                (grantDrainLeftLeaderDistance ring s.native g)) j :=
            congrArg (fun z : Fin n => PPL.shiftLeft ring z j) hAt
        _ = PPL.shiftRight ring (ring.rightNeighbor e)
              (grantDrainLeftLeaderDistance ring s.native g - j) :=
            grantDrainMarksArcShiftLeftRight
              ring (ring.rightNeighbor e)
              (grantDrainLeftLeaderDistance ring s.native g)
              j (by omega) hRange.2
    have hNoE := hEOutside j hj (by omega)
    have hFrame :
        (grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring g j) =
        nativeE ring s.native e (PPL.shiftLeft ring g j) := by
      change grantDrainNativeNext ring s e
        (PPL.shiftLeft ring g j) =
        nativeE ring s.native e (PPL.shiftLeft ring g j)
      cases hf : grantDrainSelect ring s e with
      | none =>
          simp [grantDrainNativeNext, hf]
      | leftLocal =>
          simp [grantDrainNativeNext, hf,
            canonicalBirth, hNoE]
      | rightLocal =>
          exact False.elim (hNoRight hf)
      | cross =>
          simp [grantDrainNativeNext, hf,
            canonicalBirth, hNoE]
    rw [hFrame, hShift]
    have hOffset :=
      grantDrainMarksScanOfNearestArc
        ring s.native (ring.rightNeighbor e) g hOldArc
    have hInside :
        grantDrainLeftLeaderDistance ring s.native g - j <
          PPL.cyclicOffset ring (ring.rightNeighbor e) g := by
      rw [← hOffset]
      omega
    exact hRightFollowers
      (grantDrainLeftLeaderDistance ring s.native g - j)
      (by omega) hInside
  have hNewDistance :
      grantDrainLeftLeaderDistance ring s.native g ≤
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native g :=
    grantDrainD6DeathLeaderPrefixLowerBound
      ring (grantDrainStep ring fresh update s e).native
      g (grantDrainLeftLeaderDistance ring s.native g)
      (Nat.le_of_lt hRange.2) hNewNoLeader
  have hBulletAtFront :
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).b = (1 : Fin 3) := by
    change
      (grantDrainNativeNext ring s e
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
  have hBulletWitness :
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g) ≠
          none := by
    intro hNoneBullet
    have hZero :=
      (grantDrainWarmBulletNoneCharacterization
        ring (grantDrainStep ring fresh update s e).native g
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native g)).mp
        hNoneBullet
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.1 hNewDistance
    have hOldFront :
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g) =
        ring.rightNeighbor e := hFront
    rw [hOldFront, hBulletAtFront] at hZero
    have hNonzero : (1 : Fin 3).val ≠ 0 := by decide
    exact hNonzero hZero
  have hAwayResponder : g ≠ ring.rightNeighbor e := by
    intro hSame
    have hFollower :=
      (grantDrainD6ExceptionalDeathHostFields
        s g hOldPhysical).1
    rw [hSame, hOldLeader] at hFollower
    cases hFollower
  have hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost,
      hAway, hAwayResponder]
  intro q _ hHostQ _
  have hSame : g = q :=
    Option.some.inj (hNewHost.symm.trans hHostQ)
  subst q
  exact Or.inr (Or.inr hBulletWitness)


/-- All READY old-front responder cases, including the host
coinciding with e: a source birth at that host retires it;
otherwise its DUMMY remains in the inclusive left scan. -/
theorem grantDrainD6SpentReadyFrontResponder
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hFront :
      grantDrainD6MergeFront ring s.native g =
        ring.rightNeighbor e)
    (hReady :
      (s.native (ring.rightNeighbor e)).sg = true) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  by_cases hAway : g ≠ e
  · exact grantDrainD6SpentReadyFrontResponderAwaySource
      ring hn fresh update s e g label hC hPhysical
      hWarm hHost hFront hReady hAway
  · have hAtHost : g = e := by
      by_cases heq : g = e
      · exact heq
      · exact False.elim (hAway heq)
    cases hf : grantDrainSelect ring s e with
    | none =>
        exact grantDrainD6SpentReadyFrontResponderNoFire
          ring hn fresh update s e g label
          hC hPhysical hWarm hHost hFront hReady hf
    | leftLocal =>
        have hBirth :
            ∃ z : Fin n,
              z = g ∧
              ((grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
              (grantDrainSelect ring s e = .rightLocal ∧
                z = ring.rightNeighbor e) ∨
              (grantDrainSelect ring s e = .cross ∧ z = e)) :=
          ⟨e, hAtHost.symm, Or.inl ⟨hf, rfl⟩⟩
        exact grantDrainD6SpentHostBirthRetires
          ring hn fresh update s e g label hHost hBirth
    | rightLocal =>
        have hLeader : (s.native (ring.rightNeighbor e)).l =
            true := by
          have hOld :=
            grantDrainD6OldWarmFrontLeader
              ring hn s g hC
              (hPhysical g hWarm hHost)
          change (s.native
            (grantDrainD6MergeFront ring s.native g)).l = true
              at hOld
          rw [hFront] at hOld
          exact hOld
        exact False.elim
          ((grantDrainD6ReadyResponderCannotBirthAtResponder
            ring hn s e hLeader hReady) hf)
    | cross =>
        have hBirth :
            ∃ z : Fin n,
              z = g ∧
              ((grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
              (grantDrainSelect ring s e = .rightLocal ∧
                z = ring.rightNeighbor e) ∨
              (grantDrainSelect ring s e = .cross ∧ z = e)) :=
          ⟨e, hAtHost.symm, Or.inr (Or.inr ⟨hf, rfl⟩)⟩
        exact grantDrainD6SpentHostBirthRetires
          ring hn fresh update s e g label hHost hBirth

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
Quiet OLD front responder survives physical E. Its full
native record is unchanged, even if the initiator transfers a
DUMMY. A canonical birth at the initiator remains outside the
OLD warm-host scan when the host is not itself that initiator.
-/

/-- A quiet leader RESPONDER that survives E cannot be a
rightLocal FIRE site; its post-E leader bit remains true. -/
theorem grantDrainD6QuietSurvivorCannotBirthAtResponder
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hAlive :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = true) :
    grantDrainSelect ring s e ≠ .rightLocal := by
  have hNoEligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hAlive]
  intro hRight
  have hEligible :=
    grantDrainD6SelectedEligible ring s e
      (ring.rightNeighbor e)
      (Or.inr (Or.inl ⟨hRight, rfl⟩))
  rw [hNoEligible] at hEligible
  cases hEligible

/-- Arbitrary OLD spent witness, quiet front contacted as
RESPONDER but surviving: its entire inclusive backward scan is
framed through actual E+FIRE. The source lies strictly outside
the scan and any selected birth can only occur there. -/
theorem grantDrainD6SpentQuietFrontResponderSurvivesAwaySource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (hFront :
      grantDrainD6MergeFront ring s.native g =
        ring.rightNeighbor e)
    (hQuiet :
      (s.native (ring.rightNeighbor e)).sg = false)
    (hAlive :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = true)
    (hAway : g ≠ e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hWarmPhysical := hPhysical g hWarm hHost
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hWarmPhysical
  have hOldArc :
      GrantDrainMarksNearestArc ring s.native
        (ring.rightNeighbor e) g := by
    have hArc :=
      grantDrainD6OldNearestArcOfScan ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.1 hRange.2 rfl
    change GrantDrainMarksNearestArc ring s.native
      (grantDrainD6MergeFront ring s.native g) g at hArc
    rw [hFront] at hArc
    exact hArc
  have hOldLeader := hOldArc.2.1
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hPairAlive :
      (certLiteralEPair
        (s.native e) (s.native (ring.rightNeighbor e))).2.l =
        true := by
    simpa [nativeE, hDistinct] using hAlive
  have hPairFixed :=
    grantDrainD6NoFireQuietLeaderResponderSurvivorPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hOldLeader hQuiet hPairAlive
  have hEFixed :
      nativeE ring s.native e (ring.rightNeighbor e) =
        s.native (ring.rightNeighbor e) := by
    simpa [nativeE, hDistinct] using hPairFixed
  have hNoRight :=
    grantDrainD6QuietSurvivorCannotBirthAtResponder
      ring s e hAlive
  have hPhysicalYFixed :
      (grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e) =
      s.native (ring.rightNeighbor e) := by
    change
      grantDrainNativeNext ring s e (ring.rightNeighbor e) =
        s.native (ring.rightNeighbor e)
    cases hf : grantDrainSelect ring s e with
    | none =>
        simpa [grantDrainNativeNext, hf] using hEFixed
    | leftLocal =>
        simpa [grantDrainNativeNext, hf,
          canonicalBirth, hDistinct] using hEFixed
    | rightLocal =>
        exact False.elim (hNoRight hf)
    | cross =>
        simpa [grantDrainNativeNext, hf,
          canonicalBirth, hDistinct] using hEFixed
  have hAt :
      g = PPL.shiftRight ring (ring.rightNeighbor e)
        (grantDrainLeftLeaderDistance ring s.native g) := by
    have hShift :=
      (grantDrainD6BirthShiftCancel ring g
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.2).symm
    change
      g = PPL.shiftRight ring
        (grantDrainD6MergeFront ring s.native g)
        (grantDrainLeftLeaderDistance ring s.native g) at hShift
    rw [hFront] at hShift
    exact hShift
  have hEOutside :
      ∀ j : Nat, 1 ≤ j →
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
        PPL.shiftLeft ring g j ≠ e :=
    grantDrainD6DeathSourceOutsidePositive
      ring hn e (ring.rightNeighbor e) g
      (grantDrainLeftLeaderDistance ring s.native g)
      hRange.2 hAt rfl
  have hAwayY : g ≠ ring.rightNeighbor e := by
    intro hSame
    have hFollower :=
      (grantDrainD6ExceptionalDeathHostFields
        s g hWarmPhysical).1
    rw [hSame, hOldLeader] at hFollower
    cases hFollower
  have hScanFrame :
      ∀ j : Nat,
        j ≤ grantDrainLeftLeaderDistance ring s.native g →
        (grantDrainStep ring fresh update s e).native
          (PPL.shiftLeft ring g j) =
        s.native (PPL.shiftLeft ring g j) := by
    intro j hj
    by_cases hAtY :
        PPL.shiftLeft ring g j = ring.rightNeighbor e
    · rw [hAtY]
      exact hPhysicalYFixed
    · have hNotE : PPL.shiftLeft ring g j ≠ e := by
        by_cases hZero : j = 0
        · rw [hZero, grantDrainWarmShiftLeftZero]
          exact hAway
        · exact hEOutside j (by omega) hj
      exact grantDrainSettledNativeStepOutsidePair
        ring fresh update s e (PPL.shiftLeft ring g j)
        hNotE hAtY
  have hScan :=
    grantDrainWarmFullScanFrame ring s.native
      (grantDrainStep ring fresh update s e).native g
      hScanFrame
  have hOldWitness := hInv g hWarm hHost hSpent
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
    rcases hOldWitness with hSh | hSg | hBullet
    · left
      unfold grantDrainD6MergeFront
      rw [hScan.1, hScanFrame _ (Nat.le_refl _)]
      exact hSh
    · right
      left
      unfold grantDrainD6MergeFront
      rw [hScan.1, hScanFrame _ (Nat.le_refl _)]
      exact hSg
    · right
      right
      rw [hScan.1, hScan.2.2.1]
      exact hBullet
  have hNextHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost,
      hAway, hAwayY]
  intro q _ hHostQ _
  have hSame : g = q :=
    Option.some.inj (hNextHost.symm.trans hHostQ)
  subst q
  exact hPost

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- An OLD shielded quiet responder leader cannot die in the
literal E row. A LIVE source only kills an unshielded responder,
and a quiet responder does not dummy-fire away its shield. -/
theorem grantDrainD6ShieldedQuietResponderSurvivesPair
    (x y : CertNative)
    (hLeader : y.l = true)
    (hShield : y.sh = true)
    (hQuiet : y.sg = false) :
    (certLiteralEPair x y).2.l = true := by
  simp [certLiteralEPair, hLeader, hShield, hQuiet,
    certFinThree]

/-- Entire OLD-front RESPONDER contact away from the source
host. Splitting on ready, E survival, and OLD shield resolves
the literal rows: ready leaves a DUMMY; a killed quiet front
splices to the protected killer root; a surviving quiet front
frames the old spent witness. -/
theorem grantDrainD6SpentFrontResponderAwaySource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (hFront :
      grantDrainD6MergeFront ring s.native g =
        ring.rightNeighbor e)
    (hAway : g ≠ e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  cases hReady :
      (s.native (ring.rightNeighbor e)).sg with
  | true =>
      exact grantDrainD6SpentReadyFrontResponder
        ring hn fresh update s e g label
        hC hPhysical hWarm hHost hFront hReady
  | false =>
      cases hAlive :
          (nativeE ring s.native e
            (ring.rightNeighbor e)).l with
      | true =>
          exact grantDrainD6SpentQuietFrontResponderSurvivesAwaySource
            ring hn fresh update s e g label
            hC hInv hPhysical hWarm hHost hSpent
            hFront hReady hAlive hAway
      | false =>
          have hLeader :
              (s.native (ring.rightNeighbor e)).l = true := by
            have hOld :=
              grantDrainD6OldWarmFrontLeader
                ring hn s g hC
                (hPhysical g hWarm hHost)
            change
              (s.native (grantDrainD6MergeFront
                ring s.native g)).l = true at hOld
            rw [hFront] at hOld
            exact hOld
          have hDistinct :=
            grantDrainEntranceRightNeighborDistinct
              ring (by omega : 2 ≤ n) e
          have hUnshield :
              (s.native (ring.rightNeighbor e)).sh = false := by
            cases hSh :
                (s.native (ring.rightNeighbor e)).sh with
            | false => rfl
            | true =>
                have hAlivePair :=
                  grantDrainD6ShieldedQuietResponderSurvivesPair
                    (s.native e)
                    (s.native (ring.rightNeighbor e))
                    hLeader hSh hReady
                have hEAlive :
                    (nativeE ring s.native e
                      (ring.rightNeighbor e)).l = true := by
                  simpa [nativeE, hDistinct] using hAlivePair
                rw [hAlive] at hEAlive
                cases hEAlive
          exact grantDrainD6SpentQuietFrontResponderDeath
            ring hn fresh update s e g label
            hC hPhysical hWarm hHost
            hFront hUnshield hReady hAlive

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
When the warm host itself is the source of a service
into its OLD nearest leader, the source is an empty follower.
The old front therefore cannot die. A selected source birth
retires the label; without birth, the inclusive old scan is
framed, with the source at offset zero fixed by the E copy row.
-/

/-- OLD front contacted as RESPONDER, with its predecessor source
equal to the tracked warm host itself. This includes the cyclic
wraparound distance n-1. A ready front leaves a DUMMY; a quiet
front survives E and the old spent witness is framed. -/
theorem grantDrainD6SpentFrontResponderAtHostSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some e)
    (hSpent : label.exceptionalLeft = false)
    (hFront :
      grantDrainD6MergeFront ring s.native e =
        ring.rightNeighbor e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hWarmPhysical := hPhysical e hWarm hHost
  have hOldFields :=
    grantDrainD6ExceptionalDeathHostFields s e hWarmPhysical
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s e hC hWarmPhysical
  have hLeader : (s.native (ring.rightNeighbor e)).l =
      true := by
    have hOld :=
      grantDrainD6OldWarmFrontLeader
        ring hn s e hC hWarmPhysical
    change
      (s.native (grantDrainD6MergeFront ring s.native e)).l =
        true at hOld
    rw [hFront] at hOld
    exact hOld
  cases hReady : (s.native (ring.rightNeighbor e)).sg with
  | true =>
      exact grantDrainD6SpentReadyFrontResponder
        ring hn fresh update s e e label
        hC hPhysical hWarm hHost hFront hReady
  | false =>
      have hAlivePair :=
        grantDrainD6EmptyFollowerNoResponderDeath
          (s.native e) (s.native (ring.rightNeighbor e))
          hOldFields.1 hOldFields.2.1 hLeader
      have hDistinct :=
        grantDrainEntranceRightNeighborDistinct
          ring (by omega : 2 ≤ n) e
      have hAlive :
          (nativeE ring s.native e
            (ring.rightNeighbor e)).l = true := by
        simpa [nativeE, hDistinct] using hAlivePair
      have hNoRight :=
        grantDrainD6QuietSurvivorCannotBirthAtResponder
          ring s e hAlive
      cases hf : grantDrainSelect ring s e with
      | leftLocal =>
          have hBirth :
              ∃ z : Fin n,
                z = e ∧
                ((grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
                 (grantDrainSelect ring s e = .rightLocal ∧
                    z = ring.rightNeighbor e) ∨
                 (grantDrainSelect ring s e = .cross ∧ z = e)) :=
            ⟨e, rfl, Or.inl ⟨hf, rfl⟩⟩
          exact grantDrainD6SpentHostBirthRetires
            ring hn fresh update s e e label hHost hBirth
      | rightLocal =>
          exact False.elim (hNoRight hf)
      | cross =>
          have hBirth :
              ∃ z : Fin n,
                z = e ∧
                ((grantDrainSelect ring s e = .leftLocal ∧ z = e) ∨
                 (grantDrainSelect ring s e = .rightLocal ∧
                    z = ring.rightNeighbor e) ∨
                 (grantDrainSelect ring s e = .cross ∧ z = e)) :=
            ⟨e, rfl, Or.inr (Or.inr ⟨hf, rfl⟩)⟩
          exact grantDrainD6SpentHostBirthRetires
            ring hn fresh update s e e label hHost hBirth
      | none =>
          have hSourcePairFixed :=
            grantDrainD6WarmFollowerSourceLiteralFixed
              (s.native e) (s.native (ring.rightNeighbor e))
              hOldFields.1 hOldFields.2.1 hOldFields.2.2
          have hSourceFixed :
              nativeE ring s.native e e = s.native e := by
            simpa [nativeE] using hSourcePairFixed
          have hYPairFixed :=
            grantDrainD6NoFireQuietLeaderResponderSurvivorPair
              (s.native e) (s.native (ring.rightNeighbor e))
              hLeader hReady hAlivePair
          have hYFixed :
              nativeE ring s.native e
                (ring.rightNeighbor e) =
                s.native (ring.rightNeighbor e) := by
            simpa [nativeE, hDistinct] using hYPairFixed
          have hNative :=
            grantDrainWarmPhysicalNoBirthNative
              ring fresh update s e hf
          have hAt :
              e = PPL.shiftRight ring (ring.rightNeighbor e)
                (grantDrainLeftLeaderDistance ring s.native e) := by
            have hShift :=
              (grantDrainD6BirthShiftCancel ring e
                (grantDrainLeftLeaderDistance ring s.native e)
                hRange.2).symm
            change
              e = PPL.shiftRight ring
                (grantDrainD6MergeFront ring s.native e)
                (grantDrainLeftLeaderDistance ring s.native e)
                  at hShift
            rw [hFront] at hShift
            exact hShift
          have hSourceOutside :
              ∀ j : Nat, 1 ≤ j →
                j ≤ grantDrainLeftLeaderDistance ring s.native e →
                PPL.shiftLeft ring e j ≠ e :=
            grantDrainD6DeathSourceOutsidePositive
              ring hn e (ring.rightNeighbor e) e
              (grantDrainLeftLeaderDistance ring s.native e)
              hRange.2 hAt rfl
          have hFrame :
              ∀ j : Nat,
                j ≤ grantDrainLeftLeaderDistance ring s.native e →
                (grantDrainStep ring fresh update s e).native
                  (PPL.shiftLeft ring e j) =
                s.native (PPL.shiftLeft ring e j) := by
            intro j hj
            by_cases hZero : j = 0
            · subst j
              rw [grantDrainWarmShiftLeftZero, hNative]
              exact hSourceFixed
            · have hAwayX := hSourceOutside j (by omega) hj
              by_cases hAtY :
                  PPL.shiftLeft ring e j = ring.rightNeighbor e
              · rw [hAtY, hNative]
                exact hYFixed
              · exact grantDrainSettledNativeStepOutsidePair
                  ring fresh update s e
                  (PPL.shiftLeft ring e j)
                  hAwayX hAtY
          have hScan :=
            grantDrainWarmFullScanFrame ring s.native
              (grantDrainStep ring fresh update s e).native
              e hFrame
          have hOldWitness := hInv e hWarm hHost hSpent
          have hPost :
              ((grantDrainStep ring fresh update s e).native
                (grantDrainD6MergeFront ring
                  (grantDrainStep ring fresh update s e).native e)).sh =
                true ∨
              ((grantDrainStep ring fresh update s e).native
                (grantDrainD6MergeFront ring
                  (grantDrainStep ring fresh update s e).native e)).sg =
                true ∨
              grantDrainLeftBulletDistance ring
                (grantDrainStep ring fresh update s e).native e
                (grantDrainLeftLeaderDistance ring
                  (grantDrainStep ring fresh update s e).native e) ≠
                none := by
            rcases hOldWitness with hSh | hSg | hBullet
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
              exact hBullet
          intro q _ hNextHost _
          by_cases hSame : q = e
          · subst q
            exact hPost
          · obtain ⟨hImpossible, _⟩ :=
              grantDrainD6HostChangedOnlyResponderToSource
                ring hn fresh update s e e q label
                hHost hNextHost hSame
            exact False.elim (hDistinct hImpossible.symm)

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

theorem grantDrainD6SpentFrontResponderContact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (hFront :
      grantDrainD6MergeFront ring s.native g =
        ring.rightNeighbor e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  by_cases hAway : g ≠ e
  · exact grantDrainD6SpentFrontResponderAwaySource
      ring hn fresh update s e g label hC hInv hPhysical
      hWarm hHost hSpent hFront hAway
  · have hSame : g = e := by
      by_cases hEq : g = e
      · exact hEq
      · exact False.elim (hAway hEq)
    have hHostAtSource : label.host = some e := by
      rw [← hSame]
      exact hHost
    have hFrontAtSource :
        grantDrainD6MergeFront ring s.native e =
          ring.rightNeighbor e := by
      simpa only [hSame] using hFront
    exact grantDrainD6SpentFrontResponderAtHostSource
      ring hn fresh update s e label
      hC hInv hPhysical hWarm hHostAtSource
      hSpent hFrontAtSource


/-- H2 old-front SOURCE with a resident bullet, at arbitrary
distance including the warm-host boundary. Its transfer either
leaves a bullet in the inclusive new scan or retires the warm
identity when the responder is the host itself. -/
theorem grantDrainD6SpentFrontSourceResidentBulletContact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hFront : grantDrainD6MergeFront ring s.native g = e)
    (hBullet : (s.native e).b ≠ (0 : Fin 3)) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  by_cases hAway : g ≠ ring.rightNeighbor e
  · exact grantDrainD6SpentFrontSourceBulletAway
      ring hn fresh update s e g label
      hC hPhysical hWarm hHost hFront hBullet hAway
  · have hSame : g = ring.rightNeighbor e := by
      by_cases hEq : g = ring.rightNeighbor e
      · exact hEq
      · exact False.elim (hAway hEq)
    have hHostAtResponder :
        label.host = some (ring.rightNeighbor e) := by
      rw [← hSame]
      exact hHost
    have hFrontAtResponder :
        grantDrainD6MergeFront ring s.native
          (ring.rightNeighbor e) = e := by
      rw [← hSame]
      exact hFront
    exact grantDrainD6SpentFrontSourceBulletAtHost
      ring hn fresh update s e label
      hC hPhysical hWarm hHostAtResponder
      hFrontAtResponder hBullet

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

theorem grantDrainD6SpentHostResponderEmptyPairNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hSpent : label.exceptionalLeft = false)
    (hXL : (s.native e).l = false)
    (hXB : (s.native e).b = (0 : Fin 3))
    (hYL : (s.native (ring.rightNeighbor e)).l = false)
    (hYB : (s.native (ring.rightNeighbor e)).b =
      (0 : Fin 3))
    (hNone : grantDrainSelect ring s e = .none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hLiteral :=
    grantDrainWarmEmptyFollowerSignalCopyNativeE
      ring s.native e hXL hXB hYL hYB
  have hNative :=
    grantDrainWarmPhysicalNoBirthNative
      ring fresh update s e hNone
  have hLeaderField :
      ∀ i : Fin n,
        ((grantDrainStep ring fresh update s e).native i).l =
          (s.native i).l := by
    intro i
    rw [hNative]
    exact (hLiteral i).1
  have hBulletField :
      ∀ i : Fin n,
        ((grantDrainStep ring fresh update s e).native i).b =
          (s.native i).b := by
    intro i
    rw [hNative]
    exact (hLiteral i).2.1
  have hOldWarmPhysical :=
    hPhysical (ring.rightNeighbor e) hWarm hHost
  have hFrontLeader :=
    grantDrainD6OldWarmFrontLeader
      ring hn s (ring.rightNeighbor e) hC hOldWarmPhysical
  have hFrontNotX :
      grantDrainD6MergeFront ring s.native
        (ring.rightNeighbor e) ≠ e := by
    intro hSame
    change (s.native (grantDrainD6MergeFront ring s.native
      (ring.rightNeighbor e))).l = true at hFrontLeader
    rw [hSame, hXL] at hFrontLeader
    cases hFrontLeader
  have hFrontNotY :
      grantDrainD6MergeFront ring s.native
        (ring.rightNeighbor e) ≠ ring.rightNeighbor e := by
    intro hSame
    change (s.native (grantDrainD6MergeFront ring s.native
      (ring.rightNeighbor e))).l = true at hFrontLeader
    rw [hSame, hYL] at hFrontLeader
    cases hFrontLeader
  have hFrontFrame :=
    grantDrainSettledNativeStepOutsidePair
      ring fresh update s e
      (grantDrainD6MergeFront ring s.native
        (ring.rightNeighbor e))
      hFrontNotX hFrontNotY
  change
    (grantDrainStep ring fresh update s e).native
      (PPL.shiftLeft ring (ring.rightNeighbor e)
        (grantDrainLeftLeaderDistance ring s.native
          (ring.rightNeighbor e))) =
    s.native (PPL.shiftLeft ring (ring.rightNeighbor e)
      (grantDrainLeftLeaderDistance ring s.native
        (ring.rightNeighbor e))) at hFrontFrame
  have hDistance :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e) =
      grantDrainLeftLeaderDistance ring s.native
        (ring.rightNeighbor e) := by
    simp [grantDrainLeftLeaderDistance, hLeaderField]
  have hBulletScan :
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native
          (ring.rightNeighbor e)) =
      grantDrainLeftBulletDistance ring s.native
        (ring.rightNeighbor e)
        (grantDrainLeftLeaderDistance ring s.native
          (ring.rightNeighbor e)) := by
    rw [hDistance]
    simp [grantDrainLeftBulletDistance, hBulletField]
  have hOld := hInv (ring.rightNeighbor e)
    hWarm hHost hSpent
  have hPostAtResponder :
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native
          (ring.rightNeighbor e))).sh = true ∨
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native
          (ring.rightNeighbor e))).sg = true ∨
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native
          (ring.rightNeighbor e)) ≠ none := by
    rcases hOld with hSh | hSg | hB
    · left
      unfold grantDrainD6MergeFront
      rw [hDistance, hFrontFrame]
      exact hSh
    · right
      left
      unfold grantDrainD6MergeFront
      rw [hDistance, hFrontFrame]
      exact hSg
    · right
      right
      rw [hBulletScan]
      exact hB
  intro q hNewWarm hNewHost hNewSpent
  by_cases hSame : q = ring.rightNeighbor e
  · subst q
    exact hPostAtResponder
  · obtain ⟨_, hChanged⟩ :=
      grantDrainD6HostChangedOnlyResponderToSource
        ring hn fresh update s e
        (ring.rightNeighbor e) q label
        hHost hNewHost hSame
    have hNewHostE :
        (grantDrainWarmLabelStep ring fresh update s e
          label).host = some e :=
      hNewHost.trans (congrArg Option.some hChanged)
    have hMoved :=
      grantDrainD6SpentHostMoveToSource
        ring hn fresh update s e label
        (grantDrainLeftLeaderDistance ring s.native
          (ring.rightNeighbor e))
        hC hInv hPhysical hWarm hHost hSpent
        rfl hNewWarm hNewHostE
    exact hMoved q hNewWarm hNewHost hNewSpent


end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Old-front SOURCE with no own bullet and a genuine
OLD left-bullet witness inside its sector. No abstract successor
field is assumed. -/

/-- A quiet old source leader with an empty bullet field preserves
all physical leader and bullet bits of both serviced sites, when
its responder is a follower. The source's signal may grow. -/
theorem grantDrainD6QuietEmptyLeaderFollowerFields
    (x y : CertNative)
    (hXL : x.l = true)
    (hXB : x.b = (0 : Fin 3))
    (hXS : x.sg = false)
    (hYL : y.l = false) :
    (certLiteralEPair x y).1.l = x.l ∧
    (certLiteralEPair x y).1.b = x.b ∧
    (certLiteralEPair x y).2.l = y.l ∧
    (certLiteralEPair x y).2.b = y.b := by
  simp [certLiteralEPair, hXL, hXB, hXS, hYL,
    certFinThree, grantDrainD6CertFinThreeRoundTrip]

/-- The OLD first left bullet cannot be at distance one when
the only preceding leader is the OLD source e and that leader's
own bullet field is empty. -/
theorem grantDrainD6FrontSourceInteriorBulletDistance
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e g : Fin n)
    (d : Nat)
    (hDistance : grantDrainLeftLeaderDistance ring N g = d)
    (hFront : PPL.shiftLeft ring g d = e)
    (hEmpty : (N e).b = (0 : Fin 3))
    (hBullet : grantDrainLeftBulletDistance ring N g d ≠ none) :
    2 ≤ d := by
  have hNotOne : d ≠ 1 := by
    intro hOne
    have hAtOne : PPL.shiftLeft ring g 1 = e := by
      rw [← hOne]
      exact hFront
    have hNone :
        grantDrainLeftBulletDistance ring N g 1 = none := by
      apply (grantDrainWarmBulletNoneCharacterization
        ring N g 1).mpr
      intro j hj hjBound
      have hjOne : j = 1 := by omega
      rw [hjOne, hAtOne, hEmpty]
      rfl
    rw [hOne] at hBullet
    exact hBullet hNone
  have hPos : 1 ≤ d := by
    -- The bullet scan is nonempty because its value is not none.
    cases hb : grantDrainLeftBulletDistance ring N g d with
    | none =>
        exact False.elim (hBullet hb)
    | some j =>
        obtain ⟨hjPos, hjLe, _, _⟩ :=
          (grantDrainWarmBulletSomeCharacterization
            ring N g d j).mp hb
        omega
  omega

/-- A quiet old source leader cannot itself birth, while an
eligible responder birth creates a shielded new nearest leader.
Without a selected FIRE, its OLD interior-bullet witness survives,
including any bullet at the selected responder site. -/
theorem grantDrainD6SpentFrontSourceInteriorBullet
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hFront : grantDrainD6MergeFront ring s.native g = e)
    (hXEmpty : (s.native e).b = (0 : Fin 3))
    (hXQuiet : (s.native e).sg = false)
    (hBullet :
      grantDrainLeftBulletDistance ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g) ≠ none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldPhysical := hPhysical g hWarm hHost
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hOldPhysical
  have hOldArc :
      GrantDrainMarksNearestArc ring s.native e g := by
    have hArc :=
      grantDrainD6OldNearestArcOfScan ring s.native g
        (grantDrainLeftLeaderDistance ring s.native g)
        hRange.1 hRange.2 rfl
    change GrantDrainMarksNearestArc ring s.native
      (grantDrainD6MergeFront ring s.native g) g at hArc
    rw [hFront] at hArc
    exact hArc
  have hXLeader : (s.native e).l = true := hOldArc.2.1
  have hYFollower :=
    grantDrainD6FrontSourceResponderIsFollower
      ring hn s e g hC hOldPhysical hFront
  have hPair :=
    grantDrainD6QuietEmptyLeaderFollowerFields
      (s.native e) (s.native (ring.rightNeighbor e))
      hXLeader hXEmpty hXQuiet hYFollower
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hEFields :
      ∀ i : Fin n,
        (nativeE ring s.native e i).l = (s.native i).l ∧
        (nativeE ring s.native e i).b = (s.native i).b := by
    intro i
    by_cases hX : i = e
    · subst i
      simpa [nativeE] using
        (And.intro hPair.1 hPair.2.1)
    · by_cases hY : i = ring.rightNeighbor e
      · subst i
        simpa [nativeE, hDistinct] using
          (And.intro hPair.2.2.1 hPair.2.2.2)
      · simp [nativeE, hX, hY]
  have hEArc :
      GrantDrainMarksNearestArc ring
        (nativeE ring s.native e) e g := by
    refine ⟨hOldArc.1, ?_, ?_⟩
    · rw [(hEFields e).1]
      exact hXLeader
    · intro j hj hjLt
      rw [(hEFields (PPL.shiftRight ring e j)).1]
      exact hOldArc.2.2 j hj hjLt
  have hFrontShift :
      PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g) = e :=
    hFront
  have hDistanceTwo :
      2 ≤ grantDrainLeftLeaderDistance ring s.native g :=
    grantDrainD6FrontSourceInteriorBulletDistance
      ring s.native e g
      (grantDrainLeftLeaderDistance ring s.native g)
      rfl hFrontShift hXEmpty hBullet
  have hNotHostX : g ≠ e := by
    intro hSame
    have hFollower :=
      (grantDrainD6ExceptionalDeathHostFields
        s g hOldPhysical).1
    rw [hSame, hXLeader] at hFollower
    cases hFollower
  have hYIsLeft :
      ring.rightNeighbor e =
        PPL.shiftLeft ring g
          (grantDrainLeftLeaderDistance ring s.native g - 1) :=
    grantDrainD6OutgoingBulletSuccessorAtOffset
      ring g e
      (grantDrainLeftLeaderDistance ring s.native g)
      hRange.1 hRange.2 hFront.symm
  have hNotHostY : g ≠ ring.rightNeighbor e := by
    intro hSame
    have hDistinctShift :=
      grantDrainD6BirthLeftOffsetsDistinct ring g
        0 (grantDrainLeftLeaderDistance ring s.native g - 1)
        (by omega : 0 < n)
        (by omega :
          grantDrainLeftLeaderDistance ring s.native g - 1 < n)
        (by omega :
          0 ≠ grantDrainLeftLeaderDistance ring s.native g - 1)
    have hShift :
        PPL.shiftLeft ring g 0 =
          PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring s.native g - 1) := by
      rw [grantDrainWarmShiftLeftZero]
      exact hSame.trans hYIsLeft
    exact hDistinctShift hShift
  have hHostKept :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some g := by
    simp [grantDrainWarmLabelStep, hHost,
      hNotHostX, hNotHostY]
  have hESourceLeader : (nativeE ring s.native e e).l = true := by
    rw [(hEFields e).1]
    exact hXLeader
  have hSourceNotEligible :
      grantDrainEligible (nativeE ring s.native e) e = false := by
    simp [grantDrainEligible, hESourceLeader]
  have hNoSourceBirth :
      grantDrainSelect ring s e ≠ .leftLocal ∧
      grantDrainSelect ring s e ≠ .cross := by
    constructor
    · intro hf
      have hEligible :=
        grantDrainD6SelectedEligible ring s e e
          (Or.inl ⟨hf, rfl⟩)
      rw [hSourceNotEligible] at hEligible
      cases hEligible
    · intro hf
      have hEligible :=
        grantDrainD6SelectedEligible ring s e e
          (Or.inr (Or.inr ⟨hf, rfl⟩))
      rw [hSourceNotEligible] at hEligible
      cases hEligible
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
    change
      (grantDrainNativeNext ring s e
        (grantDrainD6MergeFront ring
          (grantDrainNativeNext ring s e) g)).sh = true ∨
      (grantDrainNativeNext ring s e
        (grantDrainD6MergeFront ring
          (grantDrainNativeNext ring s e) g)).sg = true ∨
      grantDrainLeftBulletDistance ring
        (grantDrainNativeNext ring s e) g
        (grantDrainLeftLeaderDistance ring
          (grantDrainNativeNext ring s e) g) ≠ none
    cases hf : grantDrainSelect ring s e with
    | none =>
        right
        right
        have hELeaderDistance :
            grantDrainLeftLeaderDistance ring
              (nativeE ring s.native e) g =
            grantDrainLeftLeaderDistance ring s.native g :=
          (grantDrainMarksScanOfNearestArc ring
            (nativeE ring s.native e) e g hEArc).trans
            (grantDrainMarksScanOfNearestArc ring
              s.native e g hOldArc).symm
        have hEBullet : ∀ i : Fin n,
            (nativeE ring s.native e i).b = (s.native i).b :=
          fun i => (hEFields i).2
        have hBulletSame :
            grantDrainLeftBulletDistance ring
              (nativeE ring s.native e) g
              (grantDrainLeftLeaderDistance ring
                (nativeE ring s.native e) g) =
            grantDrainLeftBulletDistance ring s.native g
              (grantDrainLeftLeaderDistance ring s.native g) := by
          rw [hELeaderDistance]
          simp [grantDrainLeftBulletDistance, hEBullet]
        simpa [grantDrainNativeNext, hf, hBulletSame] using hBullet
    | leftLocal =>
        exact False.elim (hNoSourceBirth.1 hf)
    | rightLocal =>
        left
        have hYSite :
            ring.rightNeighbor e = PPL.shiftRight ring e 1 := by
          apply Fin.ext
          rfl
        have hInside : 1 < PPL.cyclicOffset ring e g := by
          have hD := grantDrainMarksScanOfNearestArc
            ring s.native e g hOldArc
          rw [← hD]
          exact hDistanceTwo
        have hArc :=
          grantDrainD6NearestArcAfterBirth
            ring (nativeE ring s.native e) e g
            (ring.rightNeighbor e) 1 hEArc hYSite hInside
        have hBorn :=
          (grantDrainD6MergeCanonicalBirthProtected
            (nativeE ring s.native e)
            (ring.rightNeighbor e)).2.1
        have hShield :=
          grantDrainD6ShieldedFrontOfNearestArc
            ring
            (canonicalBirth (nativeE ring s.native e)
              (ring.rightNeighbor e))
            (ring.rightNeighbor e) g hArc hBorn
        simpa [grantDrainNativeNext, hf] using hShield
    | cross =>
        exact False.elim (hNoSourceBirth.2 hf)
  intro q _ hNewHost _
  have hSame : g = q :=
    Option.some.inj (hHostKept.symm.trans hNewHost)
  subst q
  exact hPost

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! OLD warm host at the physical RESPONDER. The selected
FIRE cases retire the host; without FIRE, empty-follower pairs
retain their witness, bullets enter the host and end warm, or a
protected OLD leader source remains the NEW shielded front.
-/

/-- Any selected canonical FIRE on the serviced pair retires
an OLD label hosted at the responder, regardless of its
OLD spent/birth allowance. -/
theorem grantDrainD6SpentHostResponderFireRetires
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hFire : grantDrainSelect ring s e ≠ .none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hRoute :=
    grantDrainD6ContactHostAtResponder
      ring hn fresh update s e label hHost
  have hRetired :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = none := by
    cases hf : grantDrainSelect ring s e with
    | none => exact False.elim (hFire hf)
    | leftLocal =>
        have hBorn : (grantDrainNativeNext ring s e e).l =
            true := by
          simp [grantDrainNativeNext, hf, canonicalBirth,
            firedNative]
        rw [hRoute]
        simp [hf, hBorn]
    | rightLocal =>
        rw [hRoute]
        simp [hf]
    | cross =>
        rw [hRoute]
        simp [hf]
  exact grantDrainD6XOneNextHostless
    ring fresh update s e label hRetired

/-- A spent warm RESPONDER immediately clockwise from an OLD
leader source, with no OLD resident source bullet, has a
protected OLD front. Even if its ghost host moves, the actual
NEW source is a leader and so cannot remain warm. -/
theorem grantDrainD6SpentHostResponderLeaderEmpty
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hSpent : label.exceptionalLeft = false)
    (hXLeader : (s.native e).l = true)
    (hXEmpty : (s.native e).b = (0 : Fin 3)) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldPhysical :=
    hPhysical (ring.rightNeighbor e) hWarm hHost
  have hOldDistance :
      grantDrainLeftLeaderDistance ring s.native
        (ring.rightNeighbor e) = 1 := by
    apply (grantDrainWarmLeaderFirstCharacterization
      ring s.native (ring.rightNeighbor e) 1
      (by omega) (by omega)).mpr
    constructor
    · rw [grantDrainWarmRightNeighborLeftOne ring hn e]
      exact hXLeader
    · intro k hk hkBefore
      omega
  have hOldFront :
      grantDrainD6MergeFront ring s.native
        (ring.rightNeighbor e) = e := by
    unfold grantDrainD6MergeFront
    rw [hOldDistance]
    exact grantDrainWarmRightNeighborLeftOne ring hn e
  have hNoBullet :
      grantDrainLeftBulletDistance ring s.native
        (ring.rightNeighbor e)
        (grantDrainLeftLeaderDistance ring s.native
          (ring.rightNeighbor e)) = none := by
    rw [hOldDistance]
    apply (grantDrainWarmBulletNoneCharacterization
      ring s.native (ring.rightNeighbor e) 1).mpr
    intro k hk hkBound
    have hkOne : k = 1 := by omega
    rw [hkOne, grantDrainWarmRightNeighborLeftOne
      ring hn e, hXEmpty]
    rfl
  have hOldWitness :=
    hInv (ring.rightNeighbor e) hWarm hHost hSpent
  have hProtected :
      (s.native e).sh = true ∨ (s.native e).sg = true := by
    rcases hOldWitness with hShield | hSignal | hBullet
    · left
      rw [hOldFront] at hShield
      exact hShield
    · right
      rw [hOldFront] at hSignal
      exact hSignal
    · exact False.elim (hBullet hNoBullet)
  have hSourceProtected :=
    grantDrainD6MergeProtectedSourcePhysical
      ring hn fresh update s e hXLeader hProtected
  have hNewDistance :
      grantDrainLeftLeaderDistance ring
        (grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e) = 1 := by
    apply (grantDrainWarmLeaderFirstCharacterization
      ring (grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e) 1 (by omega) (by omega)).mpr
    constructor
    · rw [grantDrainWarmRightNeighborLeftOne ring hn e]
      exact hSourceProtected.1
    · intro k hk hkBefore
      omega
  have hNewShield :
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native
          (ring.rightNeighbor e))).sh = true := by
    unfold grantDrainD6MergeFront
    rw [hNewDistance,
      grantDrainWarmRightNeighborLeftOne ring hn e]
    exact hSourceProtected.2
  intro q hNewWarm hNewHost _
  by_cases hStay : q = ring.rightNeighbor e
  · subst q
    exact Or.inl hNewShield
  · obtain ⟨_, hMoved⟩ :=
      grantDrainD6HostChangedOnlyResponderToSource
        ring hn fresh update s e
        (ring.rightNeighbor e) q label
        hHost hNewHost hStay
    have hAtSource :=
      grantDrainD6HostNextWarmPhysical
        ring fresh update s e q label hNewHost hNewWarm
    have hColdSource :
        grantDrainWarmAt
          (grantDrainStep ring fresh update s e) e = false := by
      simp [grantDrainWarmAt, hSourceProtected.1]
    rw [hMoved, hColdSource] at hAtSource
    cases hAtSource

/-- For every no-FIRE serviced pair ending at a spent OLD warm
host, all literal old SOURCE rows are covered. -/
theorem grantDrainD6SpentHostResponderNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hSpent : label.exceptionalLeft = false)
    (hNone : grantDrainSelect ring s e = .none) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldPhysical :=
    hPhysical (ring.rightNeighbor e) hWarm hHost
  have hY :=
    grantDrainD6ExceptionalDeathHostFields
      s (ring.rightNeighbor e) hOldPhysical
  cases hXL : (s.native e).l with
  | true =>
      by_cases hEmpty : (s.native e).b = (0 : Fin 3)
      · exact grantDrainD6SpentHostResponderLeaderEmpty
          ring hn fresh update s e label
          hC hInv hPhysical hWarm hHost hSpent
          hXL hEmpty
      · have hDistance :
            grantDrainLeftLeaderDistance ring s.native
              (ring.rightNeighbor e) = 1 := by
          apply (grantDrainWarmLeaderFirstCharacterization
            ring s.native (ring.rightNeighbor e) 1
            (by omega) (by omega)).mpr
          constructor
          · rw [grantDrainWarmRightNeighborLeftOne ring hn e]
            exact hXL
          · intro k hk hkBefore
            omega
        have hOldFront :
            grantDrainD6MergeFront ring s.native
              (ring.rightNeighbor e) = e := by
          unfold grantDrainD6MergeFront
          rw [hDistance]
          exact grantDrainWarmRightNeighborLeftOne ring hn e
        exact grantDrainD6SpentFrontSourceBulletAtHost
          ring hn fresh update s e label
          hC hPhysical hWarm hHost hOldFront hEmpty
  | false =>
      by_cases hEmpty : (s.native e).b = (0 : Fin 3)
      · exact grantDrainD6SpentHostResponderEmptyPairNoFire
          ring hn fresh update s e label
          hC hInv hPhysical hWarm hHost hSpent
          hXL hEmpty hY.1 hY.2.1 hNone
      · have hQuiet :=
          grantDrainD6OutgoingBulletSourceQuiet
            ring s.native hC e hEmpty
        exact grantDrainD6SpentHostResponderIncomingBulletNoFire
          ring hn fresh update s e label
          hHost hXL hEmpty hQuiet hY.1 hY.2.1 hNone

/-- Complete OLD warm-host RESPONDER contact: selected FIRE
retires the host, otherwise the leader/follower source split
preserves a shielded front or an inclusive left bullet, or
the ghost becomes cold. -/
theorem grantDrainD6SpentHostResponderContact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hSpent : label.exceptionalLeft = false) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  by_cases hFire : grantDrainSelect ring s e = .none
  · exact grantDrainD6SpentHostResponderNoFire
      ring hn fresh update s e label
      hC hInv hPhysical hWarm hHost hSpent hFire
  · exact grantDrainD6SpentHostResponderFireRetires
      ring hn fresh update s e label hHost hFire

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- On a ring of size at least five, the right neighbor of g
is at the last positive counterclockwise offset n-1. It cannot
lie on a shorter positive left scan unless it is the terminal
old nearest leader itself. -/
theorem grantDrainD6HostSourceResponderOutsideUnlessFront
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (g : Fin n) (d : Nat) (hdShort : d < n)
    (hNotFront :
      PPL.shiftLeft ring g d ≠ ring.rightNeighbor g) :
    ∀ j : Nat, 1 ≤ j → j ≤ d →
      PPL.shiftLeft ring g j ≠ ring.rightNeighbor g := by
  have hLast :
      ring.rightNeighbor g =
        PPL.shiftLeft ring g (n - 1) := by
    apply Fin.ext
    change (g.val + 1) % n =
      (g.val + n - (n - 1) % n) % n
    rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    have hArithmetic : g.val + n - (n - 1) = g.val + 1 := by
      omega
    rw [hArithmetic]
  intro j hj hjBound hAt
  have hjShort : j < n := by omega
  have hJLast : j = n - 1 := by
    by_cases hSame : j = n - 1
    · exact hSame
    · have hDistinct :=
        grantDrainD6BirthLeftOffsetsDistinct ring g
          j (n - 1) hjShort (by omega : n - 1 < n) hSame
      exact False.elim (hDistinct (hAt.trans hLast))
  have hDLast : d = n - 1 := by omega
  apply hNotFront
  rw [hDLast]
  exact hLast.symm

theorem grantDrainD6SpentHostSourceRightLocalOutsideScan
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some e)
    (hSpent : label.exceptionalLeft = false)
    (hNoY : ∀ j : Nat, 1 ≤ j →
      j ≤ grantDrainLeftLeaderDistance ring s.native e →
      PPL.shiftLeft ring e j ≠ ring.rightNeighbor e)
    (hRight : grantDrainSelect ring s e = .rightLocal) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldWarm := hPhysical e hWarm hHost
  have hFields :=
    grantDrainD6ExceptionalDeathHostFields s e hOldWarm
  have hLiteral :=
    grantDrainD6WarmFollowerSourceLiteralFixed
      (s.native e) (s.native (ring.rightNeighbor e))
      hFields.1 hFields.2.1 hFields.2.2
  have hDistinct : e ≠ ring.rightNeighbor e :=
    Ne.symm (grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e)
  have hSourceFrame :
      ((grantDrainStep ring fresh update s e).native e) =
        s.native e := by
    change grantDrainNativeNext ring s e e = s.native e
    simpa [grantDrainNativeNext, hRight, canonicalBirth,
      hDistinct, nativeE] using hLiteral
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s e hC hOldWarm
  have hFrame : ∀ j : Nat,
      j ≤ grantDrainLeftLeaderDistance ring s.native e →
      (grantDrainStep ring fresh update s e).native
        (PPL.shiftLeft ring e j) =
      s.native (PPL.shiftLeft ring e j) := by
    intro j hj
    by_cases hZero : j = 0
    · subst j
      rw [grantDrainWarmShiftLeftZero]
      exact hSourceFrame
    · have hNotSource :
          PPL.shiftLeft ring e j ≠ e := by
        have hNe :=
          grantDrainD6BirthLeftOffsetsDistinct
            ring e j 0 (by omega : j < n)
            (by omega : 0 < n) (by omega : j ≠ 0)
        simpa only [grantDrainWarmShiftLeftZero] using hNe
      exact grantDrainSettledNativeStepOutsidePair
        ring fresh update s e (PPL.shiftLeft ring e j)
        hNotSource (hNoY j (by omega) hj)
  have hScan :=
    grantDrainWarmFullScanFrame
      ring s.native (grantDrainStep ring fresh update s e).native
      e hFrame
  have hOld := hInv e hWarm hHost hSpent
  have hPost :
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native e)).sh =
          true ∨
      ((grantDrainStep ring fresh update s e).native
        (grantDrainD6MergeFront ring
          (grantDrainStep ring fresh update s e).native e)).sg =
          true ∨
      grantDrainLeftBulletDistance ring
        (grantDrainStep ring fresh update s e).native e
        (grantDrainLeftLeaderDistance ring
          (grantDrainStep ring fresh update s e).native e) ≠
          none := by
    rcases hOld with hShield | hSignal | hBullet
    · left
      unfold grantDrainD6MergeFront
      rw [hScan.1, hFrame _ (Nat.le_refl _)]
      exact hShield
    · right
      left
      unfold grantDrainD6MergeFront
      rw [hScan.1, hFrame _ (Nat.le_refl _)]
      exact hSignal
    · right
      right
      rw [hScan.1, hScan.2.2.1]
      exact hBullet
  have hRoute :=
    grantDrainD6ContactHostAtSource
      ring fresh update s e label hHost
  intro q _ hNextHost _
  cases hr : grantDrainD6ContactRowSourceGrant ring fresh s e with
  | false =>
      rw [hRoute, hr] at hNextHost
      cases hNextHost
  | true =>
      rw [hRoute, hr] at hNextHost
      have hEq : e = q := Option.some.inj hNextHost
      subst q
      exact hPost

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! OLD warm host is the actual E source. The right-hand
responder either is the old nearest leader (the earlier lemma handles the
wraparound) or lies completely outside the positive backward
leader-and-bullet scan. -/

/-- Complete spent OLD HOST-SOURCE contact. A selected birth at
the host retires it; rightLocal and no-FIRE frame the entire
inclusive backward scan; and a right-hand OLD nearest leader
is handled by the responder-front closure. -/
theorem grantDrainD6SpentHostSourceContact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some e)
    (hSpent : label.exceptionalLeft = false) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldWarm := hPhysical e hWarm hHost
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s e hC hOldWarm
  by_cases hFront :
      grantDrainD6MergeFront ring s.native e =
        ring.rightNeighbor e
  · exact grantDrainD6SpentFrontResponderContact
      ring hn fresh update s e e label
      hC hInv hPhysical hWarm hHost hSpent hFront
  · have hNoY :
        ∀ j : Nat, 1 ≤ j →
          j ≤ grantDrainLeftLeaderDistance ring s.native e →
          PPL.shiftLeft ring e j ≠ ring.rightNeighbor e := by
      apply grantDrainD6HostSourceResponderOutsideUnlessFront
        ring hn e
        (grantDrainLeftLeaderDistance ring s.native e)
        hRange.2
      exact hFront
    cases hf : grantDrainSelect ring s e with
    | none =>
        exact grantDrainD6SpentHostSourceNoFireAwayScan
          ring hn fresh update s e label
          hC hInv hPhysical hWarm hHost hSpent hNoY hf
    | rightLocal =>
        exact grantDrainD6SpentHostSourceRightLocalOutsideScan
          ring hn fresh update s e label
          hC hInv hPhysical hWarm hHost hSpent hNoY hf
    | leftLocal =>
        have hExit :=
          grantDrainD6HostAtSourceBirthRetires
            ring fresh update s e label hHost (Or.inl hf)
        rcases hExit with hNoHost | hCold
        · exact grantDrainD6XOneNextHostless
            ring fresh update s e label hNoHost
        · exact grantDrainD6XOneNextCold
            ring fresh update s e label hCold
    | cross =>
        have hExit :=
          grantDrainD6HostAtSourceBirthRetires
            ring fresh update s e label hHost (Or.inr hf)
        rcases hExit with hNoHost | hCold
        · exact grantDrainD6XOneNextHostless
            ring fresh update s e label hNoHost
        · exact grantDrainD6XOneNextCold
            ring fresh update s e label hCold

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! Front-source classification by the literal spent witness.
A protected source remains shielded; a resident bullet moves
clockwise; and a bullet strictly inside the OLD scan is framed
or a rightLocal birth becomes a new protected nearest leader. -/

/-- Complete OLD nearest-front source contact, including the
distance-one responder-host boundary and every OLD spent
shield, signal, or left-bullet witness. -/
theorem grantDrainD6SpentFrontSourceContact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (hFront : grantDrainD6MergeFront ring s.native g = e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  by_cases hAtHost : g = ring.rightNeighbor e
  · have hHostY : label.host = some (ring.rightNeighbor e) := by
      rw [← hAtHost]
      exact hHost
    exact grantDrainD6SpentHostResponderContact
      ring hn fresh update s e label
      hC hInv hPhysical hWarm hHostY hSpent
  · have hWitness := hInv g hWarm hHost hSpent
    rcases hWitness with hSh | hSg | hBullet
    · have hProtected :
          (s.native e).sh = true ∨ (s.native e).sg = true := by
        left
        rw [hFront] at hSh
        exact hSh
      exact grantDrainD6SpentProtectedFrontSource
        ring hn fresh update s e g label
        hC hPhysical hWarm hHost hSpent hFront
        hProtected hAtHost
    · have hProtected :
          (s.native e).sh = true ∨ (s.native e).sg = true := by
        right
        rw [hFront] at hSg
        exact hSg
      exact grantDrainD6SpentProtectedFrontSource
        ring hn fresh update s e g label
        hC hPhysical hWarm hHost hSpent hFront
        hProtected hAtHost
    · by_cases hEmpty : (s.native e).b = (0 : Fin 3)
      · cases hSignal : (s.native e).sg with
        | true =>
            exact grantDrainD6SpentProtectedFrontSource
              ring hn fresh update s e g label
              hC hPhysical hWarm hHost hSpent hFront
              (Or.inr hSignal) hAtHost
        | false =>
            exact grantDrainD6SpentFrontSourceInteriorBullet
              ring hn fresh update s e g label
              hC hPhysical hWarm hHost hFront
              hEmpty hSignal hBullet
      · exact grantDrainD6SpentFrontSourceResidentBulletContact
          ring hn fresh update s e g label
          hC hPhysical hWarm hHost hFront hEmpty

end L3.GrantDrainEntrance


namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
H2: classify the selected physical pair against the
inclusive OLD scan from g to its nearest counterclockwise
leader. A source or responder at offset zero contacts the warm
host; an endpoint at offset d contacts the OLD front; otherwise
the pair consists of strictly interior OLD followers. All the
case closures are actual E + optional canonical FIRE lemmas.
-/

/-- Full spent inclusive OLD scan-contact preservation, using
the actual OLD front and the literal next ghost label. -/
theorem grantDrainD6SpentScanContactMergeSpent
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hWarm : label.warm = true)
    (hHost : label.host = some g)
    (hSpent : label.exceptionalLeft = false)
    (k : Nat)
    (hk :
      k ≤ grantDrainLeftLeaderDistance ring s.native g)
    (hMeet :
      PPL.shiftLeft ring g k = e ∨
      PPL.shiftLeft ring g k = ring.rightNeighbor e) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  have hOldPhysical := hPhysical g hWarm hHost
  have hRange :=
    grantDrainD6OutgoingBulletOldDistanceShort
      ring hn s g hC hOldPhysical
  have hOldFirst :=
    (grantDrainWarmLeaderFirstCharacterization
      ring s.native g
      (grantDrainLeftLeaderDistance ring s.native g)
      hRange.1 hRange.2).mp rfl
  rcases hMeet with hAtSource | hAtResponder
  · by_cases hZero : k = 0
    · have hAtHost : g = e := by
        rw [hZero, grantDrainWarmShiftLeftZero] at hAtSource
        exact hAtSource
      have hHostAtSource : label.host = some e := by
        rw [← hAtHost]
        exact hHost
      exact grantDrainD6SpentHostSourceContact
        ring hn fresh update s e label
        hC hInv hPhysical hWarm hHostAtSource hSpent
    · by_cases hEnd :
          k = grantDrainLeftLeaderDistance ring s.native g
      · have hFront :
            grantDrainD6MergeFront ring s.native g = e := by
          change
            PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g) = e
          rw [← hEnd]
          exact hAtSource
        exact grantDrainD6SpentFrontSourceContact
          ring hn fresh update s e g label
          hC hInv hPhysical hWarm hHost hSpent hFront
      · have hkPositive : 1 ≤ k := by omega
        have hkInterior :
            k < grantDrainLeftLeaderDistance ring s.native g := by
          omega
        have hkShort : k < n := by omega
        have hResponderOffset :=
          grantDrainD6OutgoingBulletSuccessorAtOffset
            ring g e k hkPositive hkShort hAtSource.symm
        by_cases hOne : k = 1
        · have hYHost : ring.rightNeighbor e = g := by
            rw [hOne] at hResponderOffset
            simpa only [Nat.sub_self,
              grantDrainWarmShiftLeftZero] using hResponderOffset
          have hHostResponder :
              label.host = some (ring.rightNeighbor e) := by
            rw [hYHost]
            exact hHost
          exact grantDrainD6SpentHostResponderContact
            ring hn fresh update s e label
            hC hInv hPhysical hWarm hHostResponder hSpent
        · have hkTwo : 2 ≤ k := by omega
          have hSourceOffset :
              e = PPL.shiftLeft ring g (k - 1 + 1) := by
            have hSum : k - 1 + 1 = k := by omega
            rw [hSum]
            exact hAtSource.symm
          have hSourceFollower :
              (s.native e).l = false := by
            rw [hAtSource.symm]
            exact hOldFirst.2 k hkPositive hkInterior
          have hResponderFollower :
              (s.native (ring.rightNeighbor e)).l =
                false := by
            rw [hResponderOffset]
            exact hOldFirst.2 (k - 1) (by omega) (by omega)
          exact grantDrainD6SpentInteriorFollowerContact
            ring hn fresh update s e g label
            hC hInv hPhysical hWarm hHost hSpent
            (k - 1) (by omega) (by omega)
            hSourceOffset hResponderOffset
            hSourceFollower hResponderFollower
  · by_cases hZero : k = 0
    · have hYHost : ring.rightNeighbor e = g := by
        rw [hZero, grantDrainWarmShiftLeftZero] at hAtResponder
        exact hAtResponder.symm
      have hHostResponder :
          label.host = some (ring.rightNeighbor e) := by
        rw [hYHost]
        exact hHost
      exact grantDrainD6SpentHostResponderContact
        ring hn fresh update s e label
        hC hInv hPhysical hWarm hHostResponder hSpent
    · by_cases hEnd :
          k = grantDrainLeftLeaderDistance ring s.native g
      · have hFront :
            grantDrainD6MergeFront ring s.native g =
              ring.rightNeighbor e := by
          change
            PPL.shiftLeft ring g
              (grantDrainLeftLeaderDistance ring s.native g) =
            ring.rightNeighbor e
          rw [← hEnd]
          exact hAtResponder
        exact grantDrainD6SpentFrontResponderContact
          ring hn fresh update s e g label
          hC hInv hPhysical hWarm hHost hSpent hFront
      · have hkPositive : 1 ≤ k := by omega
        have hkInterior :
            k < grantDrainLeftLeaderDistance ring s.native g := by
          omega
        have hNextPos : 1 ≤ k + 1 := by omega
        have hNextShort : k + 1 < n := by omega
        have hCandidate :=
          grantDrainD6OutgoingBulletSuccessorAtOffset
            ring g (PPL.shiftLeft ring g (k + 1))
            (k + 1) hNextPos hNextShort rfl
        have hSameResponder :
            ring.rightNeighbor (PPL.shiftLeft ring g (k + 1)) =
              ring.rightNeighbor e := by
          calc
            ring.rightNeighbor (PPL.shiftLeft ring g (k + 1)) =
                PPL.shiftLeft ring g ((k + 1) - 1) := hCandidate
            _ = PPL.shiftLeft ring g k := by
                  have hSubtract : k + 1 - 1 = k := by omega
                  rw [hSubtract]
            _ = ring.rightNeighbor e := hAtResponder
        have hSourceOffset : e = PPL.shiftLeft ring g (k + 1) :=
          (grantDrainD6NoFireRightNeighborInjective ring hn
            (PPL.shiftLeft ring g (k + 1)) e
            hSameResponder).symm
        by_cases hFrontIndex :
            k + 1 = grantDrainLeftLeaderDistance ring s.native g
        · have hFront :
              grantDrainD6MergeFront ring s.native g = e := by
            change
              PPL.shiftLeft ring g
                (grantDrainLeftLeaderDistance ring s.native g) = e
            rw [← hFrontIndex]
            exact hSourceOffset.symm
          exact grantDrainD6SpentFrontSourceContact
            ring hn fresh update s e g label
            hC hInv hPhysical hWarm hHost hSpent hFront
        · have hSourceBefore :
              k + 1 <
                grantDrainLeftLeaderDistance ring s.native g := by
            omega
          have hSourceFollower :
              (s.native e).l = false := by
            rw [hSourceOffset]
            exact hOldFirst.2 (k + 1) (by omega) hSourceBefore
          have hResponderFollower :
              (s.native (ring.rightNeighbor e)).l =
                false := by
            rw [← hAtResponder]
            exact hOldFirst.2 k hkPositive hkInterior
          exact grantDrainD6SpentInteriorFollowerContact
            ring hn fresh update s e g label
            hC hInv hPhysical hWarm hHost hSpent
            k hkPositive hSourceBefore
            hSourceOffset hAtResponder.symm
            hSourceFollower hResponderFollower

/-- Unconditional one-step preservation of MergeSpent at a
C_native D.6 entrance. The exceptional-death case is
eliminated by the earlier failure-only-spent-contact theorem; the
remaining H2 contact is closed by the explicit geometric case
classification above. -/
theorem grantDrainD6XOneStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label) :
    GrantDrainWarmMergeSpent ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) := by
  classical
  by_cases hGood :
      GrantDrainWarmMergeSpent ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label)
  · exact hGood
  · obtain ⟨g, hOldWarm, hOldHost, hSpent,
        k, hk, hContact⟩ :=
      grantDrainD6XOneFailureOnlySpentScanContact
        ring hn fresh update s e label
        hC hInv hPhysical hGood
    have hClosure :=
      grantDrainD6SpentScanContactMergeSpent
        ring hn fresh update s e g label
        hC hInv hPhysical
        hOldWarm hOldHost hSpent k hk hContact
    exact False.elim (hGood hClosure)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- X1 along words: MergeSpent holds after every service word,
from C_native, MergeSpent and the physical warm host at the start.
Each step uses grantDrainD6XOneStep; C_native and the physical warm
host propagate by grantDrainStepPreservesC_native and
grantDrainD6PhysicalWarmHostStep. -/
theorem grantDrainD6MergeSpentGhostWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainWarmLabel n),
      C_native ring s.native →
      GrantDrainWarmMergeSpent ring s label →
      GrantDrainD6PhysicalWarmHost s label →
      GrantDrainWarmMergeSpent ring
        (grantDrainD6GhostWord ring fresh update s label word).1
        (grantDrainD6GhostWord ring fresh update s label word).2 := by
  intro word
  induction word with
  | nil =>
      intro s label _ hInv _
      exact hInv
  | cons e rest ih =>
      intro s label hC hInv hPhysical
      have hC' :=
        grantDrainStepPreservesC_native
          ring hn fresh update s e hC
      have hInv' :=
        grantDrainD6XOneStep
          ring hn fresh update s e label hC hInv hPhysical
      have hPhysical' :=
        grantDrainD6PhysicalWarmHostStep
          ring fresh update s e label
      simpa only [grantDrainD6GhostWord, List.foldl_cons]
        using ih
          (grantDrainStep ring fresh update s e)
          (grantDrainWarmLabelStep ring fresh update s e label)
          hC' hInv' hPhysical'

/-- The prefix form consumed by the charged word theorems. -/
theorem grantDrainD6MergeSpentPrefixes
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (word : List (Fin n))
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label) :
    ∀ k : Nat, k ≤ word.length →
      GrantDrainWarmMergeSpent ring
        (grantDrainD6GhostWord ring fresh update s label
          (word.take k)).1
        (grantDrainD6GhostWord ring fresh update s label
          (word.take k)).2 := by
  intro k _
  exact grantDrainD6MergeSpentGhostWord
    ring hn fresh update (word.take k) s label hC hInv hPhysical

/-- D.6 charged warm rank along every word, with no prefix
certificate: the MergeSpent prefixes of
grantDrainD6ChargedWordOfMergeSpentPrefixes are now proved. -/
theorem grantDrainD6ChargedWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (word : List (Fin n))
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hInv : GrantDrainWarmMergeSpent ring s label)
    (hBudget : GrantDrainD6BirthBudget ring s label)
    (hCoherent : GrantDrainD6HostCoherent s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label) :
    grantDrainChargedWarmRank ring
      (grantDrainD6GhostWord ring fresh update s label word).1
      (grantDrainD6GhostWord ring fresh update s label word).2 ≤
    grantDrainChargedWarmRank ring s label :=
  grantDrainD6ChargedWordOfMergeSpentPrefixes
    ring hn fresh update word s label hC
    (grantDrainD6MergeSpentPrefixes
      ring hn fresh update word s label hC hInv hPhysical)
    hBudget hCoherent hPhysical

/-- D.6 at the natural entrance: a warm granted host g with
C_native. The charged warm rank after any word is at most the
entrance warm rank plus n plus 2 (n - 2). No prefix hypothesis. -/
theorem grantDrainD6ChargedEntrance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (word : List (Fin n))
    (s : GrantDrainState n Scratch)
    (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true) :
    grantDrainChargedWarmRank ring
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n) word).1
      (grantDrainD6GhostWord ring fresh update s
        (grantDrainD6MergeInitialLabel g true n) word).2 ≤
    grantDrainWarmRank ring s.native g + n +
      2 * (n - 2) :=
  grantDrainD6ChargedEntranceOfMergeSpentPrefixes
    ring hn fresh update word s g hC hWarm hGrant
    (grantDrainD6MergeSpentPrefixes
      ring hn fresh update word s
      (grantDrainD6MergeInitialLabel g true n) hC
      (grantDrainD6MergeInitially ring s g true n)
      (grantDrainD6PhysicalWarmHostInitial s g n hWarm))

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared
open L3.RenewalReferenceClock
open L3.HeadlineRenewal

set_option autoImplicit false
set_option Elab.async false

/-- Package the exact BANK projection square into the canonical
grant-drain refinement at inherited-authority extinction. -/
theorem grantDrainBankCanonicalRefinementFromProjection
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankGrantDrainRefinement ring hbank
      (grantDrainCanonicalModel ring hn
        (bankStageDrainFresh ring hbank)
        (bankStageDrainScratchNext ring hbank))
      (bankStageDrainProjection ring hbank) := by
  constructor
  · intro z past _hExtinct
    refine ⟨rfl, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  · intro z past e hExtinct
    exact (bankSharedProjectionStep ring
      (by omega : 2 ≤ n) hbank z hExtinct past e).symm

/-- The local warm rank is bounded by 3n even without C_native. -/
theorem grantDrainWarmRankUniformCap
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (g : Fin n) :
    grantDrainWarmRank ring N g ≤ 3 * n := by
  have hDistance :=
    (grantDrainD6ExceptionalDistanceRange ring hn N g).2
  cases hBullet :
      grantDrainLeftBulletDistance ring N g
        (grantDrainLeftLeaderDistance ring N g) with
  | none =>
      cases hSignal :
          (N (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring N g))).sg with
      | false =>
          simp [grantDrainWarmRank, hBullet, hSignal] <;> omega
      | true =>
          simp [grantDrainWarmRank, hBullet, hSignal] <;> omega
  | some p =>
      have hBulletWithin :=
        ((grantDrainWarmBulletSomeCharacterization
          ring N g (grantDrainLeftLeaderDistance ring N g)
          p).mp hBullet).2.1
      simp [grantDrainWarmRank, hBullet] <;> omega

/-- The D.6 initial W plus the n birth credits and the single
2(n-2) exceptional reserve is at most 6n. -/
theorem grantDrainChargedEntranceInitialSixCap
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (g : Fin n) :
    grantDrainWarmRank ring N g + n + 2 * (n - 2) ≤ 6 * n := by
  have hRaw := grantDrainWarmRankUniformCap ring hn N g
  omega

/-- Therefore the 12n quota envelope also bounds the initial charge. -/
theorem grantDrainChargedEntranceInitialTwelveCap
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (g : Fin n) :
    grantDrainWarmRank ring N g + n + 2 * (n - 2) ≤ 12 * n := by
  have hSix := grantDrainChargedEntranceInitialSixCap
    ring hn N g
  omega

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
The clean-DUMMY geometry, immutable label transport, strict
nearest-clockwise-leader distance charge, per-label outgoing-hit
quota, and collective 4n² retirement cost already exist in
GrantDrainDummy.lean. This section bridges that verified ghost
clock to the literal physical IntermediateZ stopping predicate.
-/

/-- The joint domain of the exact immutable DUMMY carrier.
The last component is BOTH host soundness and reverse coverage. -/
def GrantDrainDummyStageInvariant
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (z : GrantDrainState n Scratch ×
      (Fin n → Option (Fin n))) : Prop :=
  PPlus ring z.1.native ∧
  GrantDrainEntranceNoBadLive ring z.1 ∧
  GrantDrainDummyHostFaithful ring z.1.native z.2

/-- All initially unclean native bullets are covered by their
actual initial identities, not a freshly allocated post-cut host. -/
theorem grantDrainDummyStageInitial
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) :
    GrantDrainDummyStageInvariant ring
      (s, grantDrainDummyInitialUncleanHosts ring s) := by
  exact ⟨hPB, hNoBad,
    grantDrainDummyInitialFaithful ring s hPB hNoBad⟩

/-- Closure of the physical no-BAD cut and the exact DUMMY host
cover on every literal E+FIRE row, with no hypothetical geometry
premise. The difficult native origin fact is the existing
grantDrainDummyEdgeOriginHolds theorem. -/
theorem grantDrainDummyStageNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch ×
      (Fin n → Option (Fin n)))
    (e : Fin n)
    (hInv : GrantDrainDummyStageInvariant ring z) :
    GrantDrainDummyStageInvariant ring
      (grantDrainDummyEdgeWordStep ring fresh update z e) := by
  have hPBNext : PPlus ring
      (grantDrainStep ring fresh update z.1 e).native :=
    grantDrainStep_preserves_PPlus
      (by omega : 3 ≤ n) ring fresh update z.1 e hInv.1
  have hNoBadNext :
      GrantDrainEntranceNoBadLive ring
        (grantDrainStep ring fresh update z.1 e) :=
    grantDrainEntrancePhysicalNoBadNext
      ring hn fresh update z.1 e hInv.1 hInv.2.1
  have hFaithfulNext :=
    grantDrainDummyEdgeFaithfulOfOrigin
      ring hn fresh update z.1 z.2 e
      hInv.1 hInv.2.1 hInv.2.2
      (grantDrainDummyEdgeOriginHolds
        ring hn fresh update z.1 e hInv.1 hInv.2.1)
  exact ⟨hPBNext, hNoBadNext, hFaithfulNext⟩

/-- Every finite scheduler word preserves the genuine carrier
invariant. Its first projection is the canonical physical word. -/
theorem grantDrainDummyStageWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (z : GrantDrainState n Scratch ×
        (Fin n → Option (Fin n))),
      GrantDrainDummyStageInvariant ring z →
      GrantDrainDummyStageInvariant ring
        (word.foldl
          (grantDrainDummyEdgeWordStep ring fresh update) z) := by
  intro word
  induction word with
  | nil =>
      intro z hInv
      exact hInv
  | cons e rest ih =>
      intro z hInv
      change GrantDrainDummyStageInvariant ring
        (rest.foldl
          (grantDrainDummyEdgeWordStep ring fresh update)
          (grantDrainDummyEdgeWordStep ring fresh update z e))
      exact ih (grantDrainDummyEdgeWordStep ring fresh update z e)
        (grantDrainDummyStageNext
          ring hn fresh update z e hInv)

/-- On any faithful protected no-BAD carrier, disappearance of
ALL immutable bad-DUMMY identities forces every physical bullet
to be clean. The exact sector uniqueness and zero-trail clauses
then follow from grantDrainDummyAllCleanImpliesI. -/
theorem grantDrainDummyStageRetiredImpliesIntermediate
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (z : GrantDrainState n Scratch ×
      (Fin n → Option (Fin n)))
    (hInv : GrantDrainDummyStageInvariant ring z)
    (hRetired : GrantDrainDummyUncleanRetired z) :
    GrantDrainEntranceIntermediateZ ring z.1 := by
  have hEvery : ∀ b : Fin n,
      HasBullet z.1.native b →
      GrantDrainEntranceBulletCleanAt ring z.1.native b := by
    intro b hBullet
    by_cases hClean :
        GrantDrainEntranceBulletCleanAt ring z.1.native b
    · exact hClean
    · obtain ⟨id, hHost⟩ := hInv.2.2.2 b hBullet hClean
      have hGone := hRetired id
      rw [hGone] at hHost
      cases hHost
  exact ⟨hInv.2.1,
    grantDrainDummyAllCleanImpliesI ring z.1.native hInv.1 hEvery⟩

/-- Pathwise handoff at the first successful DUMMY retirement cut:
the actual canonical physical word, not a ghost surrogate, is in
NoBadLive ∧ I. -/
theorem grantDrainDummyStageRetiredWordIntermediate
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
    GrantDrainEntranceIntermediateZ ring
      (word.foldl (grantDrainStep ring fresh update) s) := by
  have hAtEnd :=
    grantDrainDummyStageRetiredImpliesIntermediate ring
      (word.foldl (grantDrainDummyEdgeWordStep ring fresh update)
        (s, grantDrainDummyInitialUncleanHosts ring s))
      (grantDrainDummyStageWord ring hn fresh update word
        (s, grantDrainDummyInitialUncleanHosts ring s)
        (grantDrainDummyStageInitial ring s hPB hNoBad))
      hRetired
  have hPhysical :=
    grantDrainDummyEdgeWordPhysical ring fresh update word
      (s, grantDrainDummyInitialUncleanHosts ring s)
  rw [← hPhysical]
  exact hAtEnd

/-- Along the closed faithful carrier domain, the first physical
IntermediateZ visit cannot occur later than retirement of the
last unclean-DUMMY label. This is proved by Bellman induction,
not by assuming pointwise target inclusion for arbitrary forged
ghost states. -/
theorem grantDrainDummyStageIntermediateGhostCostLeRetired
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (T : Nat)
      (z : GrantDrainState n Scratch ×
        (Fin n → Option (Fin n))),
      GrantDrainDummyStageInvariant ring z →
      costNumerator (grantDrainDummyEdgeWordStep ring fresh update)
        (fun w => GrantDrainEntranceIntermediateZ ring w.1) z T ≤
      costNumerator (grantDrainDummyEdgeWordStep ring fresh update)
        GrantDrainDummyUncleanRetired z T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z _
      simp only [costNumerator_zero]
      exact Nat.le_refl _
  | succ T ih =>
      intro z hInv
      by_cases hZ : GrantDrainEntranceIntermediateZ ring z.1
      · have hTarget :
            (fun w : GrantDrainState n Scratch ×
              (Fin n → Option (Fin n)) =>
              GrantDrainEntranceIntermediateZ ring w.1) z := hZ
        rw [costNumerator_terminal
          (grantDrainDummyEdgeWordStep ring fresh update)
          (fun w => GrantDrainEntranceIntermediateZ ring w.1)
          z hTarget (T + 1)]
        exact Nat.zero_le _
      · have hNotRetired : ¬ GrantDrainDummyUncleanRetired z := by
          intro hRet
          exact hZ
            (grantDrainDummyStageRetiredImpliesIntermediate
              ring z hInv hRet)
        have hNotTarget :
            ¬ (fun w : GrantDrainState n Scratch ×
              (Fin n → Option (Fin n)) =>
              GrantDrainEntranceIntermediateZ ring w.1) z := hZ
        rw [costNumerator_succ
            (grantDrainDummyEdgeWordStep ring fresh update)
            (fun w => GrantDrainEntranceIntermediateZ ring w.1)
            z hNotTarget T,
          costNumerator_succ
            (grantDrainDummyEdgeWordStep ring fresh update)
            GrantDrainDummyUncleanRetired z hNotRetired T]
        have hSum :
            (List.ofFn (fun e : Fin n =>
              costNumerator (grantDrainDummyEdgeWordStep ring fresh update)
                (fun w => GrantDrainEntranceIntermediateZ ring w.1)
                (grantDrainDummyEdgeWordStep ring fresh update z e) T)).sum ≤
            (List.ofFn (fun e : Fin n =>
              costNumerator (grantDrainDummyEdgeWordStep ring fresh update)
                GrantDrainDummyUncleanRetired
                (grantDrainDummyEdgeWordStep ring fresh update z e) T)).sum :=
          ofFn_sum_le _ _
            (fun e => ih
              (grantDrainDummyEdgeWordStep ring fresh update z e)
              (grantDrainDummyStageNext ring hn fresh update z e hInv))
        exact Nat.add_le_add_left hSum (n ^ (T + 1))

/-- The missing D.5 second-branch physical cost handoff:
from ANY canonical PPlus/NoBadLive state, the expected clean-I
entrance has a uniform finite-horizon numerator cost ≤ 4n².
No extra prefix, label-survival, or ghost-coverage hypotheses
remain. -/
theorem grantDrainDummyNoBadToIntermediateCost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (T : Nat) :
    costNumerator (grantDrainStep ring fresh update)
      (GrantDrainEntranceIntermediateZ ring) s T ≤
      n ^ T * (4 * n ^ 2) := by
  have hProjection :
      ∀ z : GrantDrainState n Scratch ×
          (Fin n → Option (Fin n)),
        ∀ e : Fin n,
          (grantDrainDummyEdgeWordStep ring fresh update z e).1 =
            grantDrainStep ring fresh update z.1 e := by
    intro z e
    rfl
  have hPhysicalGhostCost :=
    L3.Prob.costNumerator_ghost_eq
      (grantDrainStep ring fresh update)
      (grantDrainDummyEdgeWordStep ring fresh update)
      hProjection (GrantDrainEntranceIntermediateZ ring)
      (s, grantDrainDummyInitialUncleanHosts ring s) T
  have hStageCost :=
    grantDrainDummyStageIntermediateGhostCostLeRetired
      ring hn fresh update T
      (s, grantDrainDummyInitialUncleanHosts ring s)
      (grantDrainDummyStageInitial ring s hPB hNoBad)
  calc
    costNumerator (grantDrainStep ring fresh update)
        (GrantDrainEntranceIntermediateZ ring) s T =
      costNumerator (grantDrainDummyEdgeWordStep ring fresh update)
        (fun w => GrantDrainEntranceIntermediateZ ring w.1)
        (s, grantDrainDummyInitialUncleanHosts ring s) T :=
      hPhysicalGhostCost.symm
    _ ≤ costNumerator
          (grantDrainDummyEdgeWordStep ring fresh update)
          GrantDrainDummyUncleanRetired
          (s, grantDrainDummyInitialUncleanHosts ring s) T :=
      hStageCost
    _ ≤ n ^ T * (4 * n ^ 2) :=
      grantDrainDummyUncleanRetirementCost
        ring hn fresh update s hPB hNoBad T

/-- The actual uniform-scheduler conditional mean of the
NoBadLive-to-I stage is at most 4n² on the canonical machine. -/
theorem grantDrainDummyNoBadToIntermediateExpected
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (grantDrainStep ring fresh update)
      (GrantDrainEntranceIntermediateZ ring)
      s (((4 * n ^ 2 : Nat) : Rat)) := by
  exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (grantDrainStep ring fresh update)
    (GrantDrainEntranceIntermediateZ ring)
    (by omega : 0 < n) s (4 * n ^ 2)).2
    (grantDrainDummyNoBadToIntermediateCost
      ring hn fresh update s hPB hNoBad)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- On a literal warm incoming Y-to-X host transfer the charged D.6
rank drops by one.  No FIRE is possible on a continuing warm move,
so the birth credit stays unchanged; the exceptional credit cannot
be refilled.  The rebase W(new,e)+1 <= W(old,y) is the already proved
physical moving-host theorem, not a new scan hypothesis. -/
theorem grantDrainWarmIncomingMoveChargedStrict
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hOldPhysical :
      grantDrainWarmAt s (ring.rightNeighbor e) = true)
    (hOldWarm : label.warm = true)
    (hOldHost : label.host = some (ring.rightNeighbor e))
    (hOldGrant : s.grant (ring.rightNeighbor e) = true)
    (hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm = true)
    (hNewHost :
      (grantDrainWarmLabelStep ring fresh update s e
        label).host = some e)
    (hNewGrant :
      (grantDrainStep ring fresh update s e).grant e = true) :
    grantDrainChargedWarmRank ring
      (grantDrainStep ring fresh update s e)
      (grantDrainWarmLabelStep ring fresh update s e label) + 1 ≤
    grantDrainChargedWarmRank ring s label := by
  have hNone :=
    grantDrainD6MovingHostNoFire
      ring hn fresh update s e label
      hOldHost hNewHost hNewWarm
  have hRank :=
    grantDrainD6MovingHostRankStrict
      ring hn fresh update s e label
      hC hOldHost hOldPhysical hOldGrant hNewHost hNewWarm
  have hBirth :
      (grantDrainWarmLabelStep ring fresh update s e
        label).birthsLeft = label.birthsLeft := by
    simp [grantDrainWarmLabelStep, hNone]
  have hReserveLe :
      (if (grantDrainWarmLabelStep ring fresh update s e
        label).exceptionalLeft then 2 * (n - 2) else 0) ≤
      (if label.exceptionalLeft then 2 * (n - 2) else 0) := by
    cases hReserve : label.exceptionalLeft with
    | false =>
        have hNew :=
          grantDrainD6MergeReserveNeverRefills
            ring fresh update s e label hReserve
        simp [hReserve, hNew]
    | true =>
        cases hNew :
            (grantDrainWarmLabelStep ring fresh update s e
              label).exceptionalLeft <;>
          simp [hReserve, hNew]
  have hOldCost :
      grantDrainChargedWarmRank ring s label =
        grantDrainWarmRank ring s.native (ring.rightNeighbor e) +
          label.birthsLeft +
          (if label.exceptionalLeft then 2 * (n - 2) else 0) := by
    simp [grantDrainChargedWarmRank,
      hOldWarm, hOldHost, hOldGrant]
  have hNewCost :
      grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label) =
        grantDrainWarmRank ring
          (grantDrainStep ring fresh update s e).native e +
        (grantDrainWarmLabelStep ring fresh update s e
          label).birthsLeft +
        (if (grantDrainWarmLabelStep ring fresh update s e
            label).exceptionalLeft then 2 * (n - 2) else 0) := by
    simp [grantDrainChargedWarmRank,
      hNewWarm, hNewHost, hNewGrant]
  rw [hOldCost, hNewCost, hBirth]
  omega

/-- A selected incoming edge to an OLD unheld warm GRANT:
either this very service ends the tracked warm phase, or the
literal ghost router sends the grant to the source and the
charged rank decreases strictly.  The no-FIRE moving row is
certified by grantDrainD6MovingHostRankStrict. -/
theorem grantDrainWarmNominatedIncomingStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hOldPhysical :
      grantDrainWarmAt s (ring.rightNeighbor e) = true)
    (hOldWarm : label.warm = true)
    (hOldHost : label.host = some (ring.rightNeighbor e))
    (hOldGrant : s.grant (ring.rightNeighbor e) = true) :
    (grantDrainWarmLabelStep ring fresh update s e
      label).warm = false ∨
    ((grantDrainWarmLabelStep ring fresh update s e
        label).host = some e ∧
      grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label) + 1 ≤
      grantDrainChargedWarmRank ring s label) := by
  cases hNewWarm :
      (grantDrainWarmLabelStep ring fresh update s e
        label).warm with
  | false =>
      exact Or.inl rfl
  | true =>
      have hNonempty :
          (grantDrainWarmLabelStep ring fresh update s e
            label).host ≠ none := by
        intro hNone
        have hRead :=
          grantDrainD6LabelWarmHostReadout
            ring fresh update s e label
        rw [hNone] at hRead
        rw [hRead] at hNewWarm
        cases hNewWarm
      have hUnheld :
          s.request (ring.rightNeighbor e) = false := by
        cases hr : s.request (ring.rightNeighbor e) with
        | false => rfl
        | true =>
            simp [grantDrainWarmAt, hr] at hOldPhysical
      have hRoute :=
        grantDrainD6ContactHostAtResponder
          ring hn fresh update s e label hOldHost
      have hHostSource :
          (grantDrainWarmLabelStep ring fresh update s e
            label).host = some e := by
        by_cases hRetire :
            grantDrainSelect ring s e = .rightLocal ∨
            grantDrainSelect ring s e = .cross ∨
            (grantDrainNativeNext ring s e e).l = true ∨
            (grantDrainNativeNext ring s e
              (ring.rightNeighbor e)).l = true
        · have hNone :
              (grantDrainWarmLabelStep ring fresh update s e
                label).host = none := by
            simpa [hRetire, hUnheld] using hRoute
          exact False.elim (hNonempty hNone)
        · by_cases hRow :
            grantDrainD6ContactRowSourceGrant ring fresh s e = true
          · simpa [hRetire, hUnheld, hRow] using hRoute
          · have hNone :
                (grantDrainWarmLabelStep ring fresh update s e
                  label).host = none := by
              simpa [hRetire, hUnheld, hRow] using hRoute
            exact False.elim (hNonempty hNone)
      have hNewCoherent :
          GrantDrainD6HostCoherent
            (grantDrainStep ring fresh update s e)
            (grantDrainWarmLabelStep ring fresh update s e
              label) := by
        have hCoherent :
            GrantDrainD6HostCoherent s label := by
          intro q hWarm hHost
          have hEq : ring.rightNeighbor e = q :=
            Option.some.inj (hOldHost.symm.trans hHost)
          rw [← hEq]
          exact hOldGrant
        exact grantDrainD6HostCoherentStep
          ring hn fresh update s e label hCoherent
      have hNewGrant :
          (grantDrainStep ring fresh update s e).grant e = true :=
        hNewCoherent e hNewWarm hHostSource
      exact Or.inr ⟨hHostSource,
        grantDrainWarmIncomingMoveChargedStrict
          ring hn fresh update s e label
          hC hOldPhysical hOldWarm hOldHost hOldGrant
          hNewWarm hHostSource hNewGrant⟩

/-- The same actual nominated-edge dichotomy, using the OLD
D.6 GRANT-host and physical-warm coherence interfaces rather
than repeating the host/grant facts as independent premises. -/
theorem grantDrainWarmNominatedIncomingCoherent
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n)
    (hC : C_native ring s.native)
    (hCoherent : GrantDrainD6HostCoherent s label)
    (hPhysical : GrantDrainD6PhysicalWarmHost s label)
    (hOldWarm : label.warm = true)
    (hOldHost : label.host = some (ring.rightNeighbor e)) :
    (grantDrainWarmLabelStep ring fresh update s e
      label).warm = false ∨
    ((grantDrainWarmLabelStep ring fresh update s e
        label).host = some e ∧
      grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update s e)
        (grantDrainWarmLabelStep ring fresh update s e label) + 1 ≤
      grantDrainChargedWarmRank ring s label) := by
  exact grantDrainWarmNominatedIncomingStep
    ring hn fresh update s e label hC
    (hPhysical (ring.rightNeighbor e) hOldWarm hOldHost)
    hOldWarm hOldHost
    (hCoherent (ring.rightNeighbor e) hOldWarm hOldHost)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
The charged warm-phase is a literal physical/ghost pair chain.
The certified state carries the five D.6 one-step invariants and the
elementary fact that a true warm bit has a named host.  The latter
is preserved definitionally by grantDrainWarmLabelStep.
No safety condition is assumed of arbitrary raw states.
-/

/-- Closed warm-phase state for the actual physical and ghost pair. -/
structure GrantDrainWarmCertified {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) where
  state : GrantDrainState n Scratch
  label : GrantDrainWarmLabel n
  clean : C_native ring state.native
  merge : GrantDrainWarmMergeSpent ring state label
  budget : GrantDrainD6BirthBudget ring state label
  coherent : GrantDrainD6HostCoherent state label
  physicalWarm : GrantDrainD6PhysicalWarmHost state label
  hosted : label.warm = true →
    ∃ g : Fin n, label.host = some g

/-- The exact physical GrantDrain step and literal label step
lift to the five-invariant closed space. -/
def grantDrainWarmCertifiedNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (e : Fin n) :
    GrantDrainWarmCertified (Scratch := Scratch) ring :=
  { state := grantDrainStep ring fresh update z.state e
    label := grantDrainWarmLabelStep ring fresh update
      z.state e z.label
    clean :=
      grantDrainStepPreservesC_native ring hn
        fresh update z.state e z.clean
    merge :=
      grantDrainD6XOneStep ring hn fresh update
        z.state e z.label z.clean z.merge z.physicalWarm
    budget :=
      grantDrainD6BirthBudgetStepOfCoherent
        ring hn fresh update z.state e z.label z.budget z.coherent
    coherent :=
      grantDrainD6HostCoherentStep
        ring hn fresh update z.state e z.label z.coherent
    physicalWarm :=
      grantDrainD6PhysicalWarmHostStep
        ring fresh update z.state e z.label
    hosted := by
      intro hWarm
      cases hHost :
          (grantDrainWarmLabelStep ring fresh update
            z.state e z.label).host with
      | none =>
          have hRead := grantDrainD6LabelWarmHostReadout
            ring fresh update z.state e z.label
          have hCold :
              (grantDrainWarmLabelStep ring fresh update
                z.state e z.label).warm = false := by
            simpa only [hHost] using hRead
          rw [hCold] at hWarm
          cases hWarm
      | some g =>
          exact ⟨g, rfl⟩ }

/-- The original unrestricted physical and proof-only label pair,
without replacing either step with an artificial transition. -/
def grantDrainWarmRawPairNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch × GrantDrainWarmLabel n)
    (e : Fin n) :
    GrantDrainState n Scratch × GrantDrainWarmLabel n :=
  (grantDrainStep ring fresh update z.1 e,
    grantDrainWarmLabelStep ring fresh update z.1 e z.2)

/-- One extra unit is paid only while warm.
This also charges the *last* nominated edge if it terminates
warmth rather than transporting the grant. -/
def grantDrainWarmCertifiedRank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring) : Nat :=
  if z.label.warm = true then
    grantDrainChargedWarmRank ring z.state z.label + 1
  else 0

/-- The adapted incoming edge at the current named host.  The
hostless alternative is irrelevant to an active certified state. -/
def grantDrainWarmCertifiedChosen
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring) :
    Fin n :=
  match z.label.host with
  | some g => PPL.shiftLeft ring g 1
  | none => z.label.identity

/-- The true clockwise successor of the nominated predecessor
is the current old host, including the modular wrap boundary. -/
private theorem grantDrainWarmChosenIncomingGeometry
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (g : Fin n) :
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
  · have heq : g.val + n - 1 =
        n + (g.val - 1) := by omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : g.val - 1 < n)]
    have hplus : g.val - 1 + 1 = g.val := by omega
    rw [hplus, Nat.mod_eq_of_lt g.isLt]

private theorem grantDrainWarmCertifiedRankWarm
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (hWarm : z.label.warm = true) :
    grantDrainWarmCertifiedRank ring z =
      grantDrainChargedWarmRank ring z.state z.label + 1 := by
  simp [grantDrainWarmCertifiedRank, hWarm]

private theorem grantDrainWarmCertifiedRankNextWarm
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (e : Fin n)
    (hWarm : (grantDrainWarmLabelStep ring fresh update
      z.state e z.label).warm = true) :
    grantDrainWarmCertifiedRank ring
      (grantDrainWarmCertifiedNext ring hn fresh update z e) =
      grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update z.state e)
        (grantDrainWarmLabelStep ring fresh update
          z.state e z.label) + 1 := by
  change (if (grantDrainWarmLabelStep ring fresh update
      z.state e z.label).warm = true then
      grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update z.state e)
        (grantDrainWarmLabelStep ring fresh update
          z.state e z.label) + 1 else 0) = _
  rw [if_pos hWarm]

private theorem grantDrainWarmCertifiedRankNextCold
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (e : Fin n)
    (hCold : (grantDrainWarmLabelStep ring fresh update
      z.state e z.label).warm = false) :
    grantDrainWarmCertifiedRank ring
      (grantDrainWarmCertifiedNext ring hn fresh update z e) =
        0 := by
  have hNot : ¬ (grantDrainWarmLabelStep ring fresh update
      z.state e z.label).warm = true := by
    intro h
    rw [hCold] at h
    cases h
  change (if (grantDrainWarmLabelStep ring fresh update
      z.state e z.label).warm = true then
      grantDrainChargedWarmRank ring
        (grantDrainStep ring fresh update z.state e)
        (grantDrainWarmLabelStep ring fresh update
          z.state e z.label) + 1 else 0) = 0
  rw [if_neg hNot]

/-- hnoninc: the charged rank controls every real edge within
the closed D.6 state space.  A cold successor has rank zero;
a surviving warm successor inherits D.6's monotone charge. -/
theorem grantDrainWarmCertifiedRankNonincrease
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (e : Fin n) :
    grantDrainWarmCertifiedRank ring
      (grantDrainWarmCertifiedNext ring hn fresh update z e) ≤
    grantDrainWarmCertifiedRank ring z := by
  have hCharge :=
    grantDrainD6ChargedWarmRankStep ring hn
      fresh update z.state e z.label
      z.clean z.merge z.budget z.coherent z.physicalWarm
  cases hOldWarm : z.label.warm with
  | false =>
      have hNextCold :=
        grantDrainD6MergeColdLabelRemainsCold
          ring fresh update z.state e z.label hOldWarm
      have hOldZero :
          grantDrainWarmCertifiedRank ring z = 0 := by
        simp [grantDrainWarmCertifiedRank, hOldWarm]
      have hNewZero :=
        grantDrainWarmCertifiedRankNextCold
          ring hn fresh update z e hNextCold
      rw [hOldZero, hNewZero]
      all_goals exact Nat.le_refl _
  | true =>
      have hOld :=
        grantDrainWarmCertifiedRankWarm ring z hOldWarm
      cases hNextWarm :
          (grantDrainWarmLabelStep ring fresh update
            z.state e z.label).warm with
      | false =>
          have hNext :=
            grantDrainWarmCertifiedRankNextCold
              ring hn fresh update z e hNextWarm
          rw [hOld, hNext]
          exact Nat.zero_le _
      | true =>
          have hNext :=
            grantDrainWarmCertifiedRankNextWarm
              ring hn fresh update z e hNextWarm
          rw [hOld, hNext]
          exact Nat.add_le_add_right hCharge 1

/-- hdrop: while warm, the chosen incoming edge either ends the
phase (the one-unit terminal credit drops) or moves Y to X
and uses the strict charged-rank rebase from the lemma. -/
theorem grantDrainWarmCertifiedNominatedDrop
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (hActive : ¬ (z.label.warm = false)) :
    grantDrainWarmCertifiedRank ring
      (grantDrainWarmCertifiedNext ring hn fresh update z
        (grantDrainWarmCertifiedChosen ring z)) + 1 ≤
    grantDrainWarmCertifiedRank ring z := by
  have hWarm : z.label.warm = true := by
    cases h : z.label.warm with
    | true => rfl
    | false => exact False.elim (hActive h)
  obtain ⟨g, hHost⟩ := z.hosted hWarm
  have hChosen :
      grantDrainWarmCertifiedChosen ring z =
        PPL.shiftLeft ring g 1 := by
    simp [grantDrainWarmCertifiedChosen, hHost]
  have hIncoming :
      z.label.host =
        some (ring.rightNeighbor (PPL.shiftLeft ring g 1)) := by
    rw [grantDrainWarmChosenIncomingGeometry ring hn g]
    exact hHost
  have hNominated :=
    grantDrainWarmNominatedIncomingCoherent
      ring hn fresh update z.state
      (PPL.shiftLeft ring g 1) z.label
      z.clean z.coherent z.physicalWarm hWarm hIncoming
  have hOldRank :=
    grantDrainWarmCertifiedRankWarm ring z hWarm
  rw [hChosen]
  rcases hNominated with hEnd | ⟨hMove, hStrict⟩
  · have hNewRank :=
      grantDrainWarmCertifiedRankNextCold
        ring hn fresh update z
        (PPL.shiftLeft ring g 1) hEnd
    rw [hNewRank, hOldRank]
    omega
  · cases hNewWarm :
      (grantDrainWarmLabelStep ring fresh update
        z.state (PPL.shiftLeft ring g 1) z.label).warm with
    | false =>
        have hNewRank :=
          grantDrainWarmCertifiedRankNextCold
            ring hn fresh update z
            (PPL.shiftLeft ring g 1) hNewWarm
        rw [hNewRank, hOldRank]
        omega
    | true =>
        have hNewRank :=
          grantDrainWarmCertifiedRankNextWarm
            ring hn fresh update z
            (PPL.shiftLeft ring g 1) hNewWarm
        rw [hNewRank, hOldRank]
        omega

/-- Bellman/nominated-edge theorem with the two exact hdrop and
hnoninc certificates above.  No optional stopping theorem or
independence assumption is inserted here. -/
theorem grantDrainWarmCertifiedCost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (T : Nat) :
    costNumerator
      (grantDrainWarmCertifiedNext ring hn fresh update)
      (fun x : GrantDrainWarmCertified (Scratch := Scratch) ring =>
        x.label.warm = false) z T ≤
      n ^ T * (n * grantDrainWarmCertifiedRank ring z) := by
  exact Prob.costNumerator_le_of_nominated_edge
    (grantDrainWarmCertifiedNext ring hn fresh update)
    (fun x : GrantDrainWarmCertified (Scratch := Scratch) ring =>
      x.label.warm = false)
    (grantDrainWarmCertifiedRank ring)
    (grantDrainWarmCertifiedChosen ring)
    (fun x hx =>
      grantDrainWarmCertifiedNominatedDrop
        ring hn fresh update x hx)
    (fun x _ e =>
      grantDrainWarmCertifiedRankNonincrease
        ring hn fresh update x e)
    z T

/-- Genuine warm entrance.  There are at most n-1 *other*
physical grants after reserving the tracked GRANT at g.  This
saves the terminal unit in the potential and stays below 6n. -/
def grantDrainWarmCertifiedEntrance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true) :
    GrantDrainWarmCertified (Scratch := Scratch) ring :=
  { state := s
    label := grantDrainD6MergeInitialLabel g true (n - 1)
    clean := hC
    merge := grantDrainD6MergeInitially
      ring s g true (n - 1)
    budget := grantDrainD6BirthBudgetInitialMinusOne
      ring (by omega : 1 ≤ n) s
      (grantDrainD6MergeInitialLabel g true (n - 1)) rfl
    coherent := grantDrainD6HostCoherentInitial
      s g (n - 1) hGrant
    physicalWarm := grantDrainD6PhysicalWarmHostInitial
      s g (n - 1) hWarm
    hosted := by
      intro _
      exact ⟨g, rfl⟩ }

/-- For any native word, the literal D.6 warm rank is at most
three times the ring size. This local proof avoids depending on
an as-yet-unmerged entrance-cap sidecar. -/
theorem grantDrainWarmCertifiedRawRankCap
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (g : Fin n) :
    grantDrainWarmRank ring N g ≤ 3 * n := by
  have hDistance :=
    (grantDrainD6ExceptionalDistanceRange ring hn N g).2
  cases hBullet :
      grantDrainLeftBulletDistance ring N g
        (grantDrainLeftLeaderDistance ring N g) with
  | none =>
      cases hSignal :
          (N (PPL.shiftLeft ring g
            (grantDrainLeftLeaderDistance ring N g))).sg with
      | false =>
          simp [grantDrainWarmRank, hBullet, hSignal] <;> omega
      | true =>
          simp [grantDrainWarmRank, hBullet, hSignal] <;> omega
  | some p =>
      have hBulletWithin :=
        ((grantDrainWarmBulletSomeCharacterization
          ring N g (grantDrainLeftLeaderDistance ring N g)
          p).mp hBullet).2.1
      simp [grantDrainWarmRank, hBullet] <;> omega

/-- The one-time birth and exceptional-reserve charge remains
under 6n, purely from the literal rank scan. -/
theorem grantDrainWarmCertifiedEntranceChargeCap
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (N : Fin n → CertNative) (g : Fin n) :
    grantDrainWarmRank ring N g + n + 2 * (n - 2) ≤
      6 * n := by
  have hRank := grantDrainWarmCertifiedRawRankCap
    ring hn N g
  omega

/-- The plus-one stopped potential has the requested six-n
entrance cap; n-1 birth credits, not an assumed extra budget,
pay for the last nominated service. -/
theorem grantDrainWarmCertifiedEntranceRankCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true) :
    grantDrainWarmCertifiedRank ring
      (grantDrainWarmCertifiedEntrance ring hn
        s g hC hWarm hGrant) ≤ 6 * n := by
  have hExact :
      grantDrainWarmCertifiedRank ring
        (grantDrainWarmCertifiedEntrance ring hn
          s g hC hWarm hGrant) =
      grantDrainWarmRank ring s.native g +
        (n - 1) + 2 * (n - 2) + 1 := by
    simp [grantDrainWarmCertifiedRank,
      grantDrainWarmCertifiedEntrance,
      grantDrainD6MergeInitialLabel,
      grantDrainChargedWarmRank, hGrant]
  have hSix :=
    grantDrainWarmCertifiedEntranceChargeCap
      ring hn s.native g
  rw [hExact]
  omega

/-- The exact finite-horizon D.7 warm-phase charge on the
closed physical/ghost pair chain, with the paper's 6n cap. -/
theorem grantDrainWarmCertifiedEntranceCost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (T : Nat) :
    costNumerator
      (grantDrainWarmCertifiedNext ring hn fresh update)
      (fun x : GrantDrainWarmCertified (Scratch := Scratch) ring =>
        x.label.warm = false)
      (grantDrainWarmCertifiedEntrance ring hn
        s g hC hWarm hGrant) T ≤
      n ^ T * (n * (6 * n)) := by
  have hCost := grantDrainWarmCertifiedCost
    ring hn fresh update
    (grantDrainWarmCertifiedEntrance ring hn
      s g hC hWarm hGrant) T
  have hCap := grantDrainWarmCertifiedEntranceRankCap
    ring hn s g hC hWarm hGrant
  exact Nat.le_trans hCost
    (Nat.mul_le_mul_left (n ^ T)
      (Nat.mul_le_mul_left n hCap))


/-- The certified closed-space chain projects exactly to the
unrestricted physical-state/label pair, even at a terminal cut. -/
theorem grantDrainWarmCertifiedRawCostEq
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (T : Nat) :
    costNumerator
      (grantDrainWarmCertifiedNext ring hn fresh update)
      (fun x : GrantDrainWarmCertified (Scratch := Scratch) ring =>
        x.label.warm = false) z T =
    costNumerator
      (grantDrainWarmRawPairNext ring fresh update)
      (fun x : GrantDrainState n Scratch × GrantDrainWarmLabel n =>
        x.2.warm = false) (z.state,z.label) T := by
  induction T generalizing z with
  | zero =>
      simp only [costNumerator_zero]
  | succ T ih =>
      by_cases hEnd : z.label.warm = false
      · rw [costNumerator_terminal
          (grantDrainWarmCertifiedNext ring hn fresh update)
          (fun x : GrantDrainWarmCertified (Scratch := Scratch) ring =>
            x.label.warm = false) z hEnd (T + 1),
          costNumerator_terminal
          (grantDrainWarmRawPairNext ring fresh update)
          (fun x : GrantDrainState n Scratch × GrantDrainWarmLabel n =>
            x.2.warm = false) (z.state,z.label) hEnd (T + 1)]
      · rw [costNumerator_succ
          (grantDrainWarmCertifiedNext ring hn fresh update)
          (fun x : GrantDrainWarmCertified (Scratch := Scratch) ring =>
            x.label.warm = false) z hEnd T,
          costNumerator_succ
          (grantDrainWarmRawPairNext ring fresh update)
          (fun x : GrantDrainState n Scratch × GrantDrainWarmLabel n =>
            x.2.warm = false) (z.state,z.label) hEnd T]
        have hfun :
            (fun e : Fin n =>
              costNumerator
                (grantDrainWarmCertifiedNext ring hn fresh update)
                (fun x : GrantDrainWarmCertified (Scratch := Scratch) ring =>
                  x.label.warm = false)
                (grantDrainWarmCertifiedNext ring hn fresh update z e) T) =
            (fun e : Fin n =>
              costNumerator
                (grantDrainWarmRawPairNext ring fresh update)
                (fun x : GrantDrainState n Scratch × GrantDrainWarmLabel n =>
                  x.2.warm = false)
                (grantDrainWarmRawPairNext ring fresh update
                  (z.state,z.label) e) T) := by
          funext e
          exact ih (grantDrainWarmCertifiedNext ring hn fresh update z e)
        rw [hfun]

/-- The requested raw physical/ghost pair-chain warm-phase cost. -/
theorem grantDrainWarmRawEntranceCost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (T : Nat) :
    costNumerator
      (grantDrainWarmRawPairNext ring fresh update)
      (fun x : GrantDrainState n Scratch × GrantDrainWarmLabel n =>
        x.2.warm = false)
      (s, grantDrainD6MergeInitialLabel g true (n - 1)) T ≤
      n ^ T * (n * (6 * n)) := by
  have hCost := grantDrainWarmCertifiedEntranceCost
    ring hn fresh update s g hC hWarm hGrant T
  have hEq := grantDrainWarmCertifiedRawCostEq
    ring hn fresh update
    (grantDrainWarmCertifiedEntrance ring hn
      s g hC hWarm hGrant) T
  change costNumerator
      (grantDrainWarmCertifiedNext ring hn fresh update)
      (fun x : GrantDrainWarmCertified (Scratch := Scratch) ring =>
        x.label.warm = false)
      (grantDrainWarmCertifiedEntrance ring hn
        s g hC hWarm hGrant) T =
    costNumerator
      (grantDrainWarmRawPairNext ring fresh update)
      (fun x : GrantDrainState n Scratch × GrantDrainWarmLabel n =>
        x.2.warm = false)
      (s, grantDrainD6MergeInitialLabel g true (n - 1)) T at hEq
  rw [← hEq]
  exact hCost

end L3.GrantDrainEntrance






#print axioms L3.GrantDrainEntrance.grantDrainD6ShieldedFrontOfNearestArc
#print axioms L3.GrantDrainEntrance.grantDrainD6NearestArcAfterBirth
#print axioms L3.GrantDrainEntrance.grantDrainD6OldNearestArcOfScan
#print axioms L3.GrantDrainEntrance.grantDrainD6NearestArcConcat
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalPhysicalNewFrontShield
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalNewFrontShield
#print axioms L3.GrantDrainEntrance.grantDrainD6ExceptionalHOneMergeSpent
#print axioms L3.GrantDrainEntrance.grantDrainD6EmptyFollowerNoFireSpent
#print axioms L3.GrantDrainEntrance.grantDrainD6EmptyFollowerInteriorFireFrontShield
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentInteriorEmptyFollowerContact
#print axioms L3.GrantDrainEntrance.grantDrainD6XOneFailureOnlySpentScanContact
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentOldFrontGeometry
#print axioms L3.GrantDrainEntrance.grantDrainD6WarmFollowerSourceLiteralFixed
#print axioms L3.GrantDrainEntrance.grantDrainD6ResponderFollowerELeaderFrame
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentProtectedFrontSource
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostSourceNoFireAwayScan
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostResponderIncomingBulletNoFire
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostBirthRetires
#print axioms L3.GrantDrainEntrance.grantDrainD6CertFinThreeRoundTrip
#print axioms L3.GrantDrainEntrance.grantDrainD6FollowerPairResponderKeepsBullet
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentInteriorFollowerNoFire
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentInteriorFollowerFire
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentInteriorFollowerContact
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentReadyFrontSource
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentReadyFrontResponderSurvivesNoFire
#print axioms L3.GrantDrainEntrance.grantDrainD6QuietFrontDeathSourceAwayWarm
#print axioms L3.GrantDrainEntrance.grantDrainD6QuietFrontDeathPhysicalNewShield
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentQuietFrontResponderDeath
#print axioms L3.GrantDrainEntrance.grantDrainD6EmptyFollowerNoResponderDeath
#print axioms L3.GrantDrainEntrance.grantDrainD6AnyFrontDeathSourceAwayWarm
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderDummyNativeE
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentReadyFrontResponderNoFire
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostMoveToSource
#print axioms L3.GrantDrainEntrance.grantDrainD6BulletLeaderFollowerNoFire
#print axioms L3.GrantDrainEntrance.grantDrainD6BulletLeaderFollowerPhysicalRow
#print axioms L3.GrantDrainEntrance.grantDrainD6FrontSourceResponderIsFollower
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentFrontSourceBulletAway
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentFrontSourceBulletAtHost
#print axioms L3.GrantDrainEntrance.grantDrainD6ReadyResponderCannotBirthAtResponder
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentReadyFrontResponderAwaySource
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentReadyFrontResponder
#print axioms L3.GrantDrainEntrance.grantDrainD6QuietSurvivorCannotBirthAtResponder
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentQuietFrontResponderSurvivesAwaySource
#print axioms L3.GrantDrainEntrance.grantDrainD6ShieldedQuietResponderSurvivesPair
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentFrontResponderAwaySource
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentFrontResponderAtHostSource
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentFrontResponderContact
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentFrontSourceResidentBulletContact
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostResponderEmptyPairNoFire

#print axioms L3.GrantDrainEntrance.grantDrainD6QuietEmptyLeaderFollowerFields
#print axioms L3.GrantDrainEntrance.grantDrainD6FrontSourceInteriorBulletDistance
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentFrontSourceInteriorBullet
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostResponderFireRetires
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostResponderLeaderEmpty
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostResponderNoFire
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostResponderContact
#print axioms L3.GrantDrainEntrance.grantDrainD6HostSourceResponderOutsideUnlessFront
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostSourceRightLocalOutsideScan
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentHostSourceContact
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentFrontSourceContact
#print axioms L3.GrantDrainEntrance.grantDrainD6SpentScanContactMergeSpent
#print axioms L3.GrantDrainEntrance.grantDrainD6XOneStep
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeSpentGhostWord
#print axioms L3.GrantDrainEntrance.grantDrainD6MergeSpentPrefixes
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedWord
#print axioms L3.GrantDrainEntrance.grantDrainD6ChargedEntrance
#print axioms L3.GrantDrainEntrance.grantDrainBankCanonicalRefinementFromProjection
#print axioms L3.GrantDrainEntrance.grantDrainWarmRankUniformCap
#print axioms L3.GrantDrainEntrance.grantDrainChargedEntranceInitialSixCap
#print axioms L3.GrantDrainEntrance.grantDrainChargedEntranceInitialTwelveCap
#print axioms L3.GrantDrainEntrance.grantDrainDummyStageInitial
#print axioms L3.GrantDrainEntrance.grantDrainDummyStageNext
#print axioms L3.GrantDrainEntrance.grantDrainDummyStageWord
#print axioms L3.GrantDrainEntrance.grantDrainDummyStageRetiredImpliesIntermediate
#print axioms L3.GrantDrainEntrance.grantDrainDummyStageRetiredWordIntermediate
#print axioms L3.GrantDrainEntrance.grantDrainDummyStageIntermediateGhostCostLeRetired
#print axioms L3.GrantDrainEntrance.grantDrainDummyNoBadToIntermediateCost
#print axioms L3.GrantDrainEntrance.grantDrainDummyNoBadToIntermediateExpected
#print axioms L3.GrantDrainEntrance.grantDrainWarmIncomingMoveChargedStrict
#print axioms L3.GrantDrainEntrance.grantDrainWarmNominatedIncomingStep
#print axioms L3.GrantDrainEntrance.grantDrainWarmNominatedIncomingCoherent
#print axioms L3.GrantDrainEntrance.grantDrainWarmCertifiedRankNonincrease
#print axioms L3.GrantDrainEntrance.grantDrainWarmCertifiedNominatedDrop
#print axioms L3.GrantDrainEntrance.grantDrainWarmCertifiedCost
#print axioms L3.GrantDrainEntrance.grantDrainWarmCertifiedRawRankCap
#print axioms L3.GrantDrainEntrance.grantDrainWarmCertifiedEntranceChargeCap
#print axioms L3.GrantDrainEntrance.grantDrainWarmCertifiedEntranceRankCap
#print axioms L3.GrantDrainEntrance.grantDrainWarmCertifiedEntranceCost
#print axioms L3.GrantDrainEntrance.grantDrainWarmCertifiedRawCostEq
#print axioms L3.GrantDrainEntrance.grantDrainWarmRawEntranceCost
