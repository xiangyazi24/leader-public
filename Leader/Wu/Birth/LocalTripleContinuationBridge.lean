import Leader.Wu.Birth.LocalTripleOneStep


namespace BirthB1Local3ContinuationBridge


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau
abbrev reentryHorizon := BirthB1ReacquireReentryMass.reentryHorizon
abbrev local3Horizon := BirthB1ReacquireReentryMass.local3Horizon


/-- Prefix-closed B3 success survives every appended scheduler word. -/
theorem stoppedResolves_append
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u v : List (Fin n))
    (h : BirthB1Local3OneStep.StoppedResolves
      hpsi h2 kappa ring anchor C u) :
    BirthB1Local3OneStep.StoppedResolves
      hpsi h2 kappa ring anchor C (u ++ v) := by
  induction v generalizing u with
  | nil => simpa using h
  | cons e v ih =>
      have h1 := BirthB1Local3OneStep.stoppedResolves_one_step
        hpsi h2 kappa ring anchor C u e h
      have hr := ih (u := u ++ [e]) h1
      simpa [List.append_assoc] using hr


/-- The historical cap target also survives every appended scheduler word. -/
theorem target_true_append
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (u v : List (Fin n))
    (h : BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C u = true) :
    BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C (u ++ v) = true := by
  induction v generalizing u with
  | nil => simpa using h
  | cons e v ih =>
      have h1 := BirthB1Local3OneStep.target_true_one_step
        hpsi h2 kappa ring C u e h
      have hr := ih (u := u ++ [e]) h1
      simpa [List.append_assoc] using hr


/-- The still-missing semantic leaf.  A counted Local3 entry-or-cap word must
identify a prefix of that suffix at which B3 `Resolves` already holds relative
to the original Reacquire start.  The arbitrary tail is then harmless. -/
def Local3EventHitResolves
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall pre : List (Fin n), pre.length = reentryHorizon n ->
      BirthShortDoneTerminalPassiveLocal3Rotation.LocalLine3At
          hpsi hn ring anchor
            (BirthB1ReacquireReentryMass.prefixEndpoint
              hpsi h2 ring C pre) ->
      forall post : List (Fin n), post.length = local3Horizon n ->
        BirthShortDoneTerminalPassiveLocal3Rotation.actualEventBitAt
            h2 hn kappa tau ring anchor
              (BirthB1ReacquireReentryMass.prefixEndpoint
                hpsi h2 ring C pre) post = 1 ->
          exists hit tail, post = hit ++ tail /\
            BirthPhaseB3ReacquireEvent.Resolves
              hpsi h2 kappa ring anchor C (pre ++ hit)


/-- Correct stopped replacement for the false endpoint bridge. -/
def Local3SuffixStoppedBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall pre : List (Fin n), pre.length = reentryHorizon n ->
      BirthShortDoneTerminalPassiveLocal3Rotation.LocalLine3At
          hpsi hn ring anchor
            (BirthB1ReacquireReentryMass.prefixEndpoint
              hpsi h2 ring C pre) ->
      forall post : List (Fin n), post.length = local3Horizon n ->
        BirthShortDoneTerminalPassiveLocal3Rotation.actualEventBitAt
            h2 hn kappa tau ring anchor
              (BirthB1ReacquireReentryMass.prefixEndpoint
                hpsi h2 ring C pre) post = 1 ->
          BirthB1Local3OneStep.StoppedResolves
            hpsi h2 kappa ring anchor C (pre ++ post)


theorem local3SuffixStoppedBridge_of_hit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hhit : Local3EventHitResolves
      hpsi h2 hn kappa tau ring anchor) :
    Local3SuffixStoppedBridge
      hpsi h2 hn kappa tau ring anchor := by
  unfold Local3EventHitResolves at hhit
  unfold Local3SuffixStoppedBridge
  intro C hR pre hpre hline post hpost hbit
  rcases hhit C hR pre hpre hline post hpost hbit with
    ⟨hit, tail, hword, hres⟩
  have h0 : BirthB1Local3OneStep.StoppedResolves
      hpsi h2 kappa ring anchor C (pre ++ hit) :=
    ⟨pre ++ hit, [], by simp, hres⟩
  have hs := stoppedResolves_append
    hpsi h2 kappa ring anchor C (pre ++ hit) tail h0
  rw [hword]
  simpa [List.append_assoc] using hs


/-- Literal stopped replacement of `ReacquireSuccess`. -/
def StoppedReacquireSuccess
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  u.length = BirthPhaseWait2BlockProgress.L n /\
    BirthB1Local3OneStep.StoppedResolves
      hpsi h2 kappa ring anchor C u


/-- Smallest adapter needed by the current Reacquire/B4 consumer.  It is
restricted to genuine Reacquire starts and full `L n` words. -/
def ReacquireStoppedEndpointAdapter
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n ->
      BirthB1Local3OneStep.StoppedResolves
          hpsi h2 kappa ring anchor C u ->
        BirthPhaseB3ReacquireEvent.Resolves
          hpsi h2 kappa ring anchor C u


/-- Convert the stopped bridge back to the old endpoint bridge only at
its actual consumer boundary. -/
theorem endpointBridge_of_stopped
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hstop : Local3SuffixStoppedBridge
      hpsi h2 hn kappa tau ring anchor)
    (hadapt : ReacquireStoppedEndpointAdapter
      hpsi h2 hn kappa tau ring anchor) :
    BirthB1ReacquireReentryMass.Local3SuffixResolvesBridge
      hpsi h2 hn kappa tau ring anchor := by
  unfold Local3SuffixStoppedBridge at hstop
  unfold ReacquireStoppedEndpointAdapter at hadapt
  unfold BirthB1ReacquireReentryMass.Local3SuffixResolvesBridge
  intro C hR pre hpre
  dsimp
  intro hline post hpost hbit
  have hs := hstop C hR pre hpre hline post hpost hbit
  apply hadapt C hR (pre ++ post)
  · calc
      (pre ++ post).length =
          reentryHorizon n + local3Horizon n := by
        simp only [List.length_append, hpre, hpost]
      _ = BirthPhaseWait2BlockProgress.L n :=
        (BirthB1ReacquireReentryMass.L_eq_reentry_add_local3 n).symm
  · exact hs


/-- Exact `1/8 * 1/16 = 1/128` finite-word multiplication can be
reused unchanged after the stopped event is adapted at the existing endpoint
consumer. -/
theorem reacquireReentryMass_composes_via_stopped
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hmass : BirthB1ReacquireReentryMass.ReacquireReentryMass
      hpsi h2 hn kappa tau ring anchor)
    (hstop : Local3SuffixStoppedBridge
      hpsi h2 hn kappa tau ring anchor)
    (hadapt : ReacquireStoppedEndpointAdapter
      hpsi h2 hn kappa tau ring anchor) :
    BirthPhaseB3ReacquireEvent.ReacquireSuccessMass
      hpsi h2 hn kappa tau ring anchor := by
  apply BirthB1ReacquireReentryMass.reacquireReentryMass_composes
    hpsi h2 hn kappa tau ring anchor hmass
  exact endpointBridge_of_stopped
    hpsi h2 hn kappa tau ring anchor hstop hadapt


end BirthB1Local3ContinuationBridge


#print axioms BirthB1Local3ContinuationBridge.stoppedResolves_append
#print axioms BirthB1Local3ContinuationBridge.target_true_append
#print axioms BirthB1Local3ContinuationBridge.local3SuffixStoppedBridge_of_hit
#print axioms BirthB1Local3ContinuationBridge.endpointBridge_of_stopped
#print axioms BirthB1Local3ContinuationBridge.reacquireReentryMass_composes_via_stopped
