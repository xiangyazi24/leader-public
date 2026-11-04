import Leader.PPL.Modes.MidEntryResetLineageCount
import Leader.PPL.Modes.SignalLineageLocal


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability
open PPL.Modes.SignalLineage


/-!
# Lemma 5(i): reset-lineage charge truth audit


Verdict: the frozen `Lemma5iResetLineageWordCharge` is FALSE as the
intended fixed-lineage/suffix-only charge.


There are two independent defects.


1. A max-TTL tag need not die by spending its TTL through completed lottery
   rounds.  Suppose the current host `e` owns an old tag `t`, has
   `signalR = kappa`, and is also a leader.  On scheduler letter `e`,
   Algorithm 4 line 35 re-arms `e` with a fresh tag.  The proved
   `RearmTerminatesPreserved` clause of `SignalLineageOwnership` says that
   the old tag has no owner after this literal step.  Relative to the old host,
   this scheduler letter is T, and `lotteryStep psi s false` leaves
   `s.wins` unchanged.  Thus an old max-TTL lineage can disappear with zero
   new lottery wins.  A competing winner can likewise overwrite an old owner;
   `TagTTLNonincreasePreserved` constrains only a tag that survives.


2. The frozen word event says only that `maxResetSignalB` was reached
   somewhere in `lemma5iArmPrefix`.  But its two charge events inspect only
   `suf.take (lemma5PaperSweepHorizon n)`.  Hence a max signal can be
   consumed or overwritten during the remainder of the already-fixed arm
   prefix.  Those interactions are invisible to the suffix lottery and
   encounter streams.


The smallest correction at this boundary is therefore:
* add a prefix event saying that arm success has already been spent before the
  sweep boundary;
* on the complementary branch, where a physical max-TTL signal is still
  present at the sweep boundary, follow a maximal physical carrier chain
  across owner replacement/re-arm rather than stopping at death of one fixed
  tag.


If one insists on following one fixed tag, then tag replacement/re-arm must
instead be a third counted sweep event.
-/


theorem lemma5iResetRightNeighbor_ne_self
    {n : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega


/--
Exact one-interaction counterexample to the claimed implication
"old max-TTL lineage death forces a lottery win".


The row is literal P_PL: a leader that already owns an old max-TTL tag
re-arms on its initiator letter.  The ownership interface itself proves that
the old tag terminates, while the corresponding T parser step adds no win.
-/
theorem lemma5iReset_rearm_kills_old_max_without_win
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (hlineage :
      SignalLineageOwnership
        (psi := psi) (kappa := kappa) ring)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (t : SignalTag n)
    (hwf : LineageWellFormed g)
    (hleader : (g.physical e).leader = true)
    (howner : g.owner e = some t)
    (hmax : (g.physical e).signalR.val = kappa)
    (s : LotteryState) :
    And
      (forall k : Fin n,
        (ghostStep ring g e).owner k ≠ some t)
      (And
        ((g.physical e).signalR.val = kappa)
        ((lotteryStep psi s false).wins = s.wins)) := by
  have hself :
      ring.rightNeighbor e ≠ e :=
    lemma5iResetRightNeighbor_ne_self hn3 ring e
  refine And.intro ?_ (And.intro hmax ?_)
  · exact
      hlineage.2.2.2.2.1
        g e hpsi hself hwf
        hleader t howner
  · simp [lotteryStep]


/--
Prefix-side event missing from the frozen charge.


It records exactly the case in which the arm window did see a max reset
signal, but no max reset signal remains at the arm/sweep boundary.
Any TTL consumption, collision, or re-arm responsible for that loss occurred
inside the fixed prefix and cannot be charged to a suffix-only stopped stream.
-/
def lemma5iResetArmSpentB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n) : Bool :=
  reachesAux ring maxResetSignalB C pre &&
    !(maxResetSignalB (runPPL ring C pre))


/-- The new prefix event is forced whenever a frozen phase-B word has arm
success but no max-TTL signal at the sweep boundary. -/
theorem lemma5iResetArmSpent_of_bad_and_no_end_max
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre suf : DetSchedule n)
    (hpre :
      pre ∈ allSchedules n
        (lemma5ArmHorizon n))
    (hbad :
      lemma5iResetLineageBadB
        ring C (pre ++ suf) = true)
    (hend :
      maxResetSignalB
        (runPPL ring C pre) = false) :
    lemma5iResetArmSpentB
      ring C pre = true := by
  have hlen :
      pre.length = lemma5ArmHorizon n :=
    allSchedules_schedule_length
      n (lemma5ArmHorizon n) pre hpre
  have htake :
      lemma5iArmPrefix (pre ++ suf) = pre := by
    unfold lemma5iArmPrefix
    rw [← hlen]
    simp
  unfold lemma5iResetLineageBadB at hbad
  have hparts :=
    Bool.and_eq_true_iff.mp hbad
  have hreach :
      reachesAux ring maxResetSignalB
        C pre = true := by
    have h := hparts.1
    rw [htake] at h
    exact h
  unfold lemma5iResetArmSpentB
  simp [hreach, hend]


/--
Corrected word-charge surface.


Compared with `Lemma5iResetLineageWordCharge`, the only new Boolean charge
is `lemma5iResetArmSpentB ring C pre`.  On its complement, any phase-B bad
word has an actual max-TTL signal at the start of the sweep, so a proof may
choose `host` to follow the current maximal physical carrier through
winner/re-arm handoffs.  It must not use "death of one ghost tag" as the stop,
because the theorem above shows that such death is uncharged.


The existing suffix-count theorem cannot consume this statement unchanged:
the prefix-only arm-spent branch needs its own count (or must be absorbed into
a revised arm phase).
-/
def Lemma5iResetLineageWordChargeCorrected : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    forall pre : DetSchedule n,
      pre ∈ allSchedules n
        (lemma5ArmHorizon n) ->
      exists
        host : List (Fin n) -> Fin n,
      exists
        stop : List (Fin n) -> Bool,
      exists h : Nat,
        And
          (h <= psi)
          (forall suf : DetSchedule n,
            suf ∈
              allSchedules n
                (lemma5SweepHorizon n) ->
            lemma5iResetLineageBadB
                ring C (pre ++ suf) = true ->
            (lemma5iResetArmSpentB
                ring C pre ||
              lemma5iResetEncounterBadB
                ring host stop
                (suf.take
                  (lemma5PaperSweepHorizon n)) ||
              lemma5iResetLotteryBadB
                psi h ring host stop
                (suf.take
                  (lemma5PaperSweepHorizon n))) =
              true)


end PPL.Modes.Lemma5


#print axioms PPL.Modes.Lemma5.lemma5iReset_rearm_kills_old_max_without_win
#print axioms PPL.Modes.Lemma5.lemma5iResetArmSpent_of_bad_and_no_end_max
