import Leader.PPL.Convergence.BulletLineage

/-!
# Lemma 15 ordered-subsequence bullet-lineage sweep

Truth audit.

Conjunct (2) is TRUE.  The two R6 facts already on the import cone are

  PPL.Safety.PeacefulProps.newFirePeaceful
    PPL.Safety.PeacefulProps.peacefulScanLocality

and

  PPL.Safety.PeacefulProps.peacefulKeepPhysical
    PPL.Safety.PeacefulProps.peacefulScanLocality.

The first excludes a genuinely fresh live post-bullet from being bad.  The
second says that an old peaceful live bullet cannot become bad, either at its
old site or after the line-59 move.  Thus every bad post-bullet has a bad
predecessor.  Residual 1 below packages exactly that physical fact together
with the proof-only owner/no-cloning/serial bookkeeping needed by ghostStep.

For conjunct (1), Advances really does increment swept: its conclusion is
owner = some (advanceOwner o), and advanceOwner writes swept := o.swept + 1.
The source taggedBad_one_step also says that every arbitrary interleaving
letter either retires the lineage, advances it when its current site initiates,
or leaves its owner unchanged.  What is not yet a theorem on main is the
historical full-lap fact needed to keep a still-bad survivor below one complete
sweep.  Residual 2 is a single-interaction version of exactly that fact.

The rest of this file is closed.  In particular the List.Sublist part is not
left in either residual: a small greedy pending-word machine consumes the
literal two-sweep word through arbitrary interleavings, and the induction below
forces matched progress 2*n.  A surviving initial bad lineage would then have
swept >= n, contradicting the one-step bad-survivor cap carried by Residual 2.
-/

namespace PPL.Convergence.BulletLineage

set_option autoImplicit false
set_option Elab.async false

open PPL.Convergence.BulletSweep

/-! ## Ghost soundness used by bad ancestry -/

def BadOwnerCoverage
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa) : Prop :=
  forall i : Fin n,
    BadLive ring g.physical i ->
      exists o : BulletOwner n, g.owner i = some o

def OwnerSerialBound
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) : Prop :=
  forall (i : Fin n) (o : BulletOwner n),
    g.owner i = some o ->
      o.tag.serial < g.nextBirth

def LineageSound
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa) : Prop :=
  And
    (NoCloning g)
    (And
      (OwnerSerialBound g)
      (BadOwnerCoverage ring g))

private theorem initial_owner_serial_bound
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    OwnerSerialBound (initialGhost C) := by
  intro i o howner
  by_cases hlive : (C i).bullet = (2 : Fin 3)
  · let oi : BulletOwner n :=
      { tag := { origin := i, serial := 0 }, swept := 0 }
    have hsome : some oi = some o := by
      simpa [initialGhost, hlive, oi] using howner
    have ho : oi = o := Option.some.inj hsome
    subst o
    simp [initialGhost, oi]
  · simp [initialGhost, hlive] at howner

private theorem initial_bad_owner_coverage
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    BadOwnerCoverage ring (initialGhost C) := by
  intro i hbad
  refine ⟨
    ({ tag := { origin := i, serial := 0 }, swept := 0 } :
      BulletOwner n), ?_⟩
  have hb : (C i).bullet = (2 : Fin 3) := hbad.1
  simp [initialGhost, hb]

private theorem initial_lineage_sound
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    LineageSound ring (initialGhost C) := by
  exact And.intro
    (initialGhost_noCloning C)
    (And.intro
      (initial_owner_serial_bound C)
      (initial_bad_owner_coverage ring C))

/-!
Residual 1: exact no-new-bad one-step law.

The second field is the useful ancestry direction.  A bad final owner comes
from a bad old owner with the same tag.  The first field keeps the proof-only
ghost invariants needed to iterate this statement.

The physical content of the second field is precisely R6 new-fire/peaceful-
keep.  The remaining bookkeeping is only the explicit ghostStep owner cases.
-/
def NoNewBadOneStep : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n),
    LineageSound ring g ->
      let g' := ghostStep hpsi ring g e
      And
        (LineageSound ring g')
        (forall (i : Fin n) (o' : BulletOwner n),
          g'.owner i = some o' ->
          BadLive ring g'.physical i ->
            exists j : Fin n, exists o : BulletOwner n,
              And
                (g.owner j = some o)
                (And
                  (BadLive ring g.physical j)
                  (o'.tag = o.tag)))

/-! ## Greedy ordered-subsequence machine -/

def sweepPendingStep
    {n : Nat}
    (pending : DetSchedule n)
    (e : Fin n) : DetSchedule n :=
  match pending with
  | [] => []
  | requested :: rest =>
      if e = requested then rest else requested :: rest

def sweepPendingRun
    {n : Nat} :
    DetSchedule n -> DetSchedule n -> DetSchedule n
  | pending, [] => pending
  | pending, e :: rest =>
      sweepPendingRun (sweepPendingStep pending e) rest

private theorem sweepPendingRun_nil
    {n : Nat}
    (schedule : DetSchedule n) :
    sweepPendingRun ([] : DetSchedule n) schedule = [] := by
  induction schedule with
  | nil =>
      rfl
  | cons e rest ih =>
      simpa [sweepPendingRun, sweepPendingStep] using ih

/-- Generic greedy matching: every Sublist witness is consumed even with
arbitrary letters inserted between selected letters. -/
private theorem sweepPendingRun_nil_of_sublist
    {n : Nat}
    (pending schedule : DetSchedule n)
    (hsub : pending.Sublist schedule) :
    sweepPendingRun pending schedule = [] := by
  induction schedule generalizing pending with
  | nil =>
      have hlength : pending.length <= 0 := by
        simpa using hsub.length_le
      have hpending : pending = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst pending
      rfl
  | cons fired rest ih =>
      cases pending with
      | nil =>
          exact sweepPendingRun_nil (fired :: rest)
      | cons requested tail =>
          by_cases hfire : fired = requested
          · subst fired
            have htail : tail.Sublist rest := by
              rcases List.sublist_cons_iff.mp hsub with
                hskip | ⟨tail', heq, ht⟩
              · exact
                  (List.sublist_cons_self requested tail).trans hskip
              · cases heq
                exact ht
            simp only [sweepPendingRun]
            rw [show
              sweepPendingStep (requested :: tail) requested = tail by
                simp [sweepPendingStep]]
            exact ih tail htail
          · have htail : (requested :: tail).Sublist rest := by
              rcases List.sublist_cons_iff.mp hsub with
                hskip | ⟨tail', heq, ht⟩
              · exact hskip
              · have hhead : requested = fired :=
                  (List.cons.inj heq).1
                exact False.elim (hfire hhead.symm)
            simp only [sweepPendingRun]
            rw [show
              sweepPendingStep (requested :: tail) fired =
                  requested :: tail by
                simp [sweepPendingStep, hfire]]
            exact ih (requested :: tail) htail

def SweepPendingSuffix
    {n : Nat}
    (ring : DirectedRing n)
    (pending : DetSchedule n) : Prop :=
  exists pre : DetSchedule n,
    PPL.Convergence.BulletSweep.lemma15SweepWord ring =
      pre ++ pending

/-! ## Tracked bad-lineage progress -/

def BadProgressState
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (origin : Fin n)
    (tag : BulletTag n)
    (pending : DetSchedule n)
    (g : GhostConfig n psi kappa) : Prop :=
  And
    (SweepPendingSuffix ring pending)
    (exists i : Fin n, exists o : BulletOwner n,
      And
        (g.owner i = some o)
        (And
          (o.tag = tag)
          (And
            (BadLive ring g.physical i)
            (And
              (i = PPL.shiftRight ring origin o.swept)
              (And
                (o.swept < n)
                ((PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
                    pending.length <=
                  origin.val + o.swept))))))

/-!
Residual 2: one-interaction swept-counter law.

This is the exact local strengthening still absent from BulletLineage.lean.
The pre-state records a still-bad descendant of one initial tag, its physical
site as shiftRight(origin,swept), and the amount of the fixed two-sweep word
already greedily matched.  One literal interaction either retires that tag or
preserves the same state after updating both the ghost owner and the greedy
pending word.

The clause o'.swept < n is the historical full-lap fact: a lineage that has
completed n clockwise line-59 transfers cannot still be bad.  Advances from
taggedBad_one_step supplies the +1 update; ArcUnchanged handles arbitrary gap
letters.  Thus this residual is one interaction, not a Sublist/run theorem.
-/
def BadSweepProgressOneStep : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (origin : Fin n)
    (tag : BulletTag n)
    (pending : DetSchedule n),
    LineageSound ring g ->
    BadProgressState ring origin tag pending g ->
      let g' := ghostStep hpsi ring g e
      let pending' := sweepPendingStep pending e
      Or
        (LineageRetired ring g' tag)
        (BadProgressState ring origin tag pending' g')

/-! ## Iteration of the two one-step laws -/

private theorem lineage_sound_run
    (hnew : NoNewBadOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (hsound : LineageSound ring g) :
    LineageSound ring (ghostRun hpsi ring g schedule) := by
  induction schedule generalizing g with
  | nil =>
      simpa [ghostRun] using hsound
  | cons e rest ih =>
      have hs1 :
          LineageSound ring (ghostStep hpsi ring g e) :=
        (hnew hn3 hpsi ring g e hsound).1
      simpa [ghostRun] using
        (ih (g := ghostStep hpsi ring g e) hs1)

private theorem bad_ancestry_run
    (hnew : NoNewBadOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (hsound : LineageSound ring g)
    (i : Fin n)
    (ofinal : BulletOwner n)
    (howner :
      (ghostRun hpsi ring g schedule).owner i = some ofinal)
    (hbad :
      BadLive ring (ghostRun hpsi ring g schedule).physical i) :
    exists i0 : Fin n, exists o0 : BulletOwner n,
      And
        (g.owner i0 = some o0)
        (And
          (BadLive ring g.physical i0)
          (ofinal.tag = o0.tag)) := by
  induction schedule generalizing g i ofinal with
  | nil =>
      exact ⟨i, ofinal, howner, hbad, rfl⟩
  | cons e rest ih =>
      let g1 := ghostStep hpsi ring g e
      have hstep := hnew hn3 hpsi ring g e hsound
      have hs1 : LineageSound ring g1 := by
        simpa [g1] using hstep.1
      have hownerTail :
          (ghostRun hpsi ring g1 rest).owner i = some ofinal := by
        simpa [ghostRun, g1] using howner
      have hbadTail :
          BadLive ring (ghostRun hpsi ring g1 rest).physical i := by
        simpa [ghostRun, g1] using hbad
      obtain ⟨j, o1, hj, hbadj, htag1⟩ :=
        ih (g := g1) (i := i) (ofinal := ofinal)
          hs1 hownerTail hbadTail
      have hback := hstep.2 j o1
        (by simpa [g1] using hj)
        (by simpa [g1] using hbadj)
      obtain ⟨i0, o0, hi0, hbadi0, htag0⟩ := hback
      exact
        ⟨i0, o0, hi0, hbadi0, htag1.trans htag0⟩

private theorem lineage_retired_run
    (hnew : NoNewBadOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (hsound : LineageSound ring g)
    (tag : BulletTag n)
    (hret : LineageRetired ring g tag) :
    LineageRetired ring (ghostRun hpsi ring g schedule) tag := by
  intro i htagged
  rcases htagged with ⟨ofinal, howner, htag, hbad⟩
  obtain ⟨i0, o0, hi0, hbadi0, hback⟩ :=
    bad_ancestry_run hnew hn3 hpsi ring
      g schedule hsound i ofinal howner hbad
  apply hret i0
  exact
    ⟨o0, hi0, hback.symm.trans htag, hbadi0⟩

private theorem bad_progress_run
    (hnew : NoNewBadOneStep)
    (hprogress : BadSweepProgressOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (origin : Fin n)
    (tag : BulletTag n)
    (pending : DetSchedule n)
    (hsound : LineageSound ring g)
    (hstate : BadProgressState ring origin tag pending g) :
    Or
      (LineageRetired ring
        (ghostRun hpsi ring g schedule) tag)
      (BadProgressState ring origin tag
        (sweepPendingRun pending schedule)
        (ghostRun hpsi ring g schedule)) := by
  induction schedule generalizing g pending with
  | nil =>
      exact Or.inr
        (by simpa [ghostRun, sweepPendingRun] using hstate)
  | cons e rest ih =>
      have hone :=
        hprogress hn3 hpsi ring g e
          origin tag pending hsound hstate
      have hs1 :
          LineageSound ring (ghostStep hpsi ring g e) :=
        (hnew hn3 hpsi ring g e hsound).1
      rcases hone with hret | hnext
      · apply Or.inl
        have htail :=
          lineage_retired_run hnew hn3 hpsi ring
            (ghostStep hpsi ring g e) rest hs1 tag hret
        simpa [ghostRun] using htail
      · have htail :=
          ih
            (g := ghostStep hpsi ring g e)
            (pending := sweepPendingStep pending e)
            hs1 hnext
        simpa [ghostRun, sweepPendingRun] using htail

private theorem shiftRight_zero_lineage
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftRight ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt i.isLt]

private theorem initial_bad_progress_state
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (o : BulletOwner n)
    (howner : (initialGhost C).owner i = some o)
    (hbad : BadLive ring C i) :
    BadProgressState ring i o.tag
      (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
      (initialGhost C) := by
  let oi : BulletOwner n :=
    { tag := { origin := i, serial := 0 }, swept := 0 }
  have hsome : some oi = some o := by
    simpa [initialGhost, hbad.1, oi] using howner
  have ho : oi = o := Option.some.inj hsome
  subst o
  unfold BadProgressState
  refine And.intro ?_ ?_
  · exact ⟨[], by simp⟩
  · refine ⟨i, oi, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [oi] using howner
    · rfl
    · simpa [initialGhost] using hbad
    · simpa [oi] using
        (shiftRight_zero_lineage ring i).symm
    · dsimp [oi]
      omega
    · simp

/-!
Assembly: all List.Sublist/run induction is proved here.  Only the two explicit
one-step residuals above remain.
-/
theorem orderedSubsequenceBulletSweep
    (hnew : NoNewBadOneStep)
    (hprogress : BadSweepProgressOneStep) :
    OrderedSubsequenceBulletSweep := by
  intro n psi kappa hn3 hpsi ring C schedule hsub
  dsimp only
  have hs0 :
      LineageSound ring (initialGhost C) :=
    initial_lineage_sound ring C
  have hsFinal :
      LineageSound ring
        (ghostRun hpsi ring (initialGhost C) schedule) :=
    lineage_sound_run hnew hn3 hpsi ring
      (initialGhost C) schedule hs0
  constructor
  · intro i o howner hbad
    have hstate0 :=
      initial_bad_progress_state
        hn3 ring C i o howner hbad
    have hrun :=
      bad_progress_run hnew hprogress
        hn3 hpsi ring
        (initialGhost C) schedule i o.tag
        (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
        hs0 hstate0
    rcases hrun with hret | hsurvive
    · exact hret
    · have hdone :
          sweepPendingRun
              (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
              schedule = [] :=
        sweepPendingRun_nil_of_sublist
          (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
          schedule hsub
      unfold BadProgressState at hsurvive
      rcases hsurvive with
        ⟨hsuffix, j, o1, hj, htag, hbad1,
          hsite, hswept, hcredit⟩
      rw [hdone] at hcredit
      simp only [List.length_nil, Nat.sub_zero] at hcredit
      rw [PPL.Convergence.BulletSweep.lemma15SweepWord_length ring]
        at hcredit
      have hi := i.isLt
      omega
  · intro i hbad
    obtain ⟨o1, howner1⟩ :=
      hsFinal.2.2 i hbad
    obtain ⟨i0, o0, howner0, hbad0, htag⟩ :=
      bad_ancestry_run hnew hn3 hpsi ring
        (initialGhost C) schedule hs0
        i o1 howner1 hbad
    exact
      ⟨i0, o0, o1, howner0, hbad0, howner1, htag⟩

theorem lemma15SublistSweep_closed
    (hnew : NoNewBadOneStep)
    (hprogress : BadSweepProgressOneStep) :
    PPL.Convergence.BulletSweep.Lemma15SublistSweep :=
  lemma15SublistSweep
    (orderedSubsequenceBulletSweep hnew hprogress)

end PPL.Convergence.BulletLineage

#print axioms PPL.Convergence.BulletLineage.orderedSubsequenceBulletSweep
#print axioms PPL.Convergence.BulletLineage.lemma15SublistSweep_closed

