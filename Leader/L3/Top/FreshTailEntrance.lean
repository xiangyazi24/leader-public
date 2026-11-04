import Leader.L3.Top.FreshTailEntranceCarrier
import Leader.L3.Top.FreshTailJointAnchor

/-!
Q7c P.3 J5 entrance: the receipt-selected forward issued-barrier
composition.  Source S (the sample/port historical preimage) is
supplied as explicit hypotheses; this file does not prove S.

The initially selected barrier sample need not be definitionally
equal to the accepted receipt's sample.  Both identify the SAME
full moving root, because S fixes the accepted sample's time to
the source-zero U service, and the established carrier invariant
authenticates the predecessor's sampled terminal D.

No physical or audit changes.
Consumer: TopFreshTailFirstGenuineEntrance in TopClockBundle.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Starting at the actual source-zero U service specified by
the historical receipt preimage, carry the issued barrier along
the intervening OLD scheduler word.  A barrier acceptance inside
this word would be a strict earlier genuine tail, excluded by
TopFreshTailJointPreAnchor.  At the terminal predecessor the
full carrier authenticated by topFreshTailEntranceCarrierReached
equals the moving root; queue.identity forces its position to
the terminal source home.

Consumer: topFreshTailEntranceOfFactorization, then
TopFreshTailFirstGenuineEntrance in TopClockBundle. -/
theorem topFreshTailEntranceBarrierAtPredecessor
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (hpre : TopFreshTailJointPreAnchor ring C s Z)
    (u v : List (Fin n))
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hword :
      Z.2 = ((u ++ [certSite s 0]) ++ v) ++
        [certSite s (topClockSpan n - 1)])
    (hunread :
      ((topFixedTraceRun ring C u).1.1
        (certSite s 0)).qOut = .U)
    (hlane : sigma.id.lane = .comparison)
    (hzeroSite : sigma.id.site = certSite s 0)
    (hstamp :
      sigma.id.time =
        (topFixedTraceRun ring C u).1.2.clock + 1)
    (hterminalData :
      ((topFixedTraceRun ring C
        ((u ++ [certSite s 0]) ++ v)).1.1
        (certSite s (topClockSpan n - 1))).qOut =
          .D sigma.value true)
    (hterminalAtom :
      ((topFixedTraceRun ring C
        ((u ++ [certSite s 0]) ++ v)).1.2.current
        (certSite s (topClockSpan n - 1))).comparison.out.atom =
          some (.sampled sigma.id)) :
    ∃ (k : Fin (topClockSpan n))
      (birthSample : DigitSample
        (compileAdvice (ceilLogTwo n)) n),
      TopFreshTailCohortIssuedBarrier
        ring C s ((u ++ [certSite s 0]) ++ v)
        { origin := .freshBorder
            ((topFixedTraceRun ring C u).1.2.clock + 1),
          born := (topFixedTraceRun ring C u).1.2.clock + 1 }
        k birthSample ∧
      k.val + 1 = topClockSpan n := by
  have hr : 3 ≤ topClockSpan n :=
    cert_rho_ge_three n hn
  have hzeroBound : 0 < topClockSpan n := by omega
  have hlastBound :
      topClockSpan n - 1 < topClockSpan n := by omega
  obtain ⟨birthSample, hbirth⟩ :=
    topFreshTailCohortIssuedBarrierInitial
      ring C s hn hbad u
      (certSite s 0) rfl hunread
  rcases topFreshTailCohortIssuedBarrierRun
      ring C s hn hbad hl v
      (u ++ [certSite s 0])
      { origin := .freshBorder
          ((topFixedTraceRun ring C u).1.2.clock + 1),
        born := (topFixedTraceRun ring C u).1.2.clock + 1 }
      (⟨0, hzeroBound⟩ : Fin (topClockSpan n))
      birthSample hbirth with
    ⟨k, hbarrier, _⟩ |
    ⟨front, suffix, edge, hmid, hearlier, _⟩
  · have hT :=
      topFreshTailEntranceCarrierReached
        ring C s hn hbad hl
        (topFixedTraceRun ring C
          ((u ++ [certSite s 0]) ++ v))
        (topFreshTailAuditRunReached
          ring C ((u ++ [certSite s 0]) ++ v))
    have hsampledSlot :
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C
            ((u ++ [certSite s 0]) ++ v))).slots
          (⟨topClockSpan n - 1, hlastBound⟩ :
            Fin (topClockSpan n)) =
          some
            { origin := .freshBorder sigma.id.time,
              born := sigma.id.time } :=
      (hT
        (⟨topClockSpan n - 1, hlastBound⟩ :
          Fin (topClockSpan n))
        sigma sigma.value true
        hlane hzeroSite
        (by exact hterminalData)
        (by exact hterminalAtom)).1
    have hterminalRoot :
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C
            ((u ++ [certSite s 0]) ++ v))).slots
          (⟨topClockSpan n - 1, hlastBound⟩ :
            Fin (topClockSpan n)) =
          some
            { origin := .freshBorder
                ((topFixedTraceRun ring C u).1.2.clock + 1),
              born := (topFixedTraceRun ring C u).1.2.clock + 1 } := by
      rw [hstamp] at hsampledSlot
      exact hsampledSlot
    have hsamePosition :
        k =
          (⟨topClockSpan n - 1, hlastBound⟩ :
            Fin (topClockSpan n)) :=
      hbarrier.barrier.spatial.queue.identity
        k
        (⟨topClockSpan n - 1, hlastBound⟩ :
          Fin (topClockSpan n))
        { origin := .freshBorder
            ((topFixedTraceRun ring C u).1.2.clock + 1),
          born := (topFixedTraceRun ring C u).1.2.clock + 1 }
        { origin := .freshBorder
            ((topFixedTraceRun ring C u).1.2.clock + 1),
          born := (topFixedTraceRun ring C u).1.2.clock + 1 }
        hbarrier.barrier.spatial.rootSlot
        hterminalRoot rfl rfl
    have hterminal : k.val + 1 = topClockSpan n := by
      have hk := congrArg Fin.val hsamePosition
      change k.val = topClockSpan n - 1 at hk
      omega
    exact ⟨k, birthSample, hbarrier, hterminal⟩
  · have hsplit :
        (((u ++ [certSite s 0]) ++ front) ++ [edge]) ++
          (suffix ++ [certSite s (topClockSpan n - 1)]) =
        Z.2 := by
      rw [hword, hmid]
      simp only [List.append_assoc, List.singleton_append,
        List.cons_append, List.nil_append]
    have hnonempty :
        suffix ++ [certSite s (topClockSpan n - 1)] ≠ [] := by
      intro hempty
      have hlen := congrArg List.length hempty
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hlen
      omega
    have hnoEarlier :=
      hpre.2
        (((u ++ [certSite s 0]) ++ front) ++ [edge])
        (suffix ++ [certSite s (topClockSpan n - 1)])
        hsplit hnonempty
    exact False.elim (hnoEarlier hearlier)

/-- Once S supplies the real selected source-zero U birth, the
last receipt's sampled terminal D, and its OLD responder
acceptance guards, the tracked full root is terminal by
topFreshTailEntranceBarrierAtPredecessor.  The existing
first-anchor all-home historical issue theorem and the
post-anchor cohort-wave base produce the genuine time-now
anchor and the COMPLETE selected first cohort.

Consumer: TopFreshTailFirstGenuineEntrance in TopClockBundle,
once the separate historical-preimage producer S is proved. -/
theorem topFreshTailEntranceOfFactorization
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (hpre : TopFreshTailJointPreAnchor ring C s Z)
    (haccepted : topClockGenuineTailAccepted C s Z)
    (u v : List (Fin n))
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hword :
      Z.2 = ((u ++ [certSite s 0]) ++ v) ++
        [certSite s (topClockSpan n - 1)])
    (hunread :
      ((topFixedTraceRun ring C u).1.1
        (certSite s 0)).qOut = .U)
    (hlane : sigma.id.lane = .comparison)
    (hzeroSite : sigma.id.site = certSite s 0)
    (hstamp :
      sigma.id.time =
        (topFixedTraceRun ring C u).1.2.clock + 1)
    (hterminalData :
      ((topFixedTraceRun ring C
        ((u ++ [certSite s 0]) ++ v)).1.1
        (certSite s (topClockSpan n - 1))).qOut =
          .D sigma.value true)
    (hterminalAtom :
      ((topFixedTraceRun ring C
        ((u ++ [certSite s 0]) ++ v)).1.2.current
        (certSite s (topClockSpan n - 1))).comparison.out.atom =
          some (.sampled sigma.id))
    (hyi :
      ((topFixedTraceRun ring C
        ((u ++ [certSite s 0]) ++ v)).1.1
        (ring.rightNeighbor
          (certSite s (topClockSpan n - 1)))).qIn = .E)
    (hyc :
      ((topFixedTraceRun ring C
        ((u ++ [certSite s 0]) ++ v)).1.1
        (ring.rightNeighbor
          (certSite s (topClockSpan n - 1)))).qCarry = .OFF) :
    ∃ anchor : DigitExport
        (compileAdvice (ceilLogTwo n)) n,
      topClockConcreteTailAnchor s Z anchor ∧
      anchor.time = Z.1.2.clock ∧
      Nonempty (TopFreshTailPostAnchorCohortWave
        ring C s hn Z anchor) := by
  obtain ⟨k, birthSample, hbarrier, hterminal⟩ :=
    topFreshTailEntranceBarrierAtPredecessor
      ring C s hn hbad hl Z hpre u v sigma
      hword hunread hlane hzeroSite hstamp
      hterminalData hterminalAtom
  have hk : k.val = topClockSpan n - 1 := by
    have hklimit := k.isLt
    omega
  have hportSite :
      certSite s (topClockSpan n - 1) = certSite s k.val := by
    rw [hk]
  have hissues :=
    topFreshTailCohortFirstAnchorAllHomeIssuesOfBarrier
      ring C s hn hbad
      ((u ++ [certSite s 0]) ++ v)
      { origin := .freshBorder
          ((topFixedTraceRun ring C u).1.2.clock + 1),
        born := (topFixedTraceRun ring C u).1.2.clock + 1 }
      k birthSample hbarrier hterminal
      (certSite s (topClockSpan n - 1))
      hportSite hyi hyc
  have hbase :=
    topFreshTailPostAnchorCohortWaveBase
      ring C s hn hbad hl
      ((u ++ [certSite s 0]) ++ v)
      { origin := .freshBorder
          ((topFixedTraceRun ring C u).1.2.clock + 1),
        born := (topFixedTraceRun ring C u).1.2.clock + 1 }
      k birthSample hbarrier hterminal
      (certSite s (topClockSpan n - 1))
      hportSite hyi hyc
  have hfinalState :
      Z =
        topFixedTraceRun ring C
          (((u ++ [certSite s 0]) ++ v) ++
            [certSite s (topClockSpan n - 1)]) := by
    have hreach : Z = topFixedTraceRun ring C Z.2 := hpre.1
    rw [hword] at hreach
    exact hreach
  rw [hfinalState]
  exact hbase

end L3

#print axioms L3.topFreshTailEntranceBarrierAtPredecessor
#print axioms L3.topFreshTailEntranceOfFactorization
