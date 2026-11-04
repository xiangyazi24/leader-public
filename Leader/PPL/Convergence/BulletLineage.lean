import Leader.PPL.Convergence.BulletSweep

/-!
# Bullet lineage for Lemma 15 ordered-subsequence sweep

This is a proof-only identity/progress refinement of the literal P_PL run.

* Every initially live bullet receives a stable BulletTag.
* When a live source moves into an empty live destination, its owner is
  transferred and its swept counter is incremented.
* When the responder already carries a live bullet, the responder owner wins;
  the incoming source lineage is thereby retired (collision/absorption).
* A live post-bullet with no live pre-bullet predecessor receives a fresh tag.
* The physical component is definitionally the real P_PL step.

For Lemma 15 only nonpeaceful live descendants matter.  A tag is considered
retired once it no longer owns any nonpeaceful live bullet; it may still be
attached to a live bullet that has become peaceful.

The only remaining semantic obligation is the run-level ordered-subsequence
induction, stated once as OrderedSubsequenceBulletSweep below.
-/

namespace PPL.Convergence.BulletLineage

set_option autoImplicit false
set_option Elab.async false

open PPL.Convergence.BulletSweep

abbrev Config (n psi kappa : Nat) :=
  PPL.Convergence.BulletSweep.Config n psi kappa

/-- Stable identity of one proof-only bullet lineage.  Serial 0 is reserved
for initial bullets; later serials come from nextBirth. -/
structure BulletTag (n : Nat) where
  origin : Fin n
  serial : Nat
  deriving DecidableEq, Repr

/-- A live owner additionally remembers how many clockwise line-59 transfers
this lineage has accumulated. -/
structure BulletOwner (n : Nat) where
  tag : BulletTag n
  swept : Nat
  deriving DecidableEq, Repr

structure GhostConfig (n psi kappa : Nat) where
  physical : Config n psi kappa
  owner : Fin n -> Option (BulletOwner n)
  nextBirth : Nat

def erase {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) : Config n psi kappa :=
  g.physical

def advanceOwner {n : Nat} (o : BulletOwner n) : BulletOwner n :=
  { o with swept := o.swept + 1 }

def bumpOwner {n : Nat} :
    Option (BulletOwner n) -> Option (BulletOwner n)
  | none => none
  | some o => some (advanceOwner o)

private def writePair {n : Nat} {α : Type}
    (f : Fin n -> α)
    (i : Fin n) (xi : α)
    (j : Fin n) (xj : α) : Fin n -> α :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

def freshOwner {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) (e : Fin n) : BulletOwner n :=
  {
    tag := { origin := e, serial := g.nextBirth }
    swept := 0
  }

/-- Canonical initial tagging: every initial live bullet receives its site tag. -/
def initialGhost {n psi kappa : Nat}
    (C : Config n psi kappa) : GhostConfig n psi kappa :=
  {
    physical := C
    owner := fun i =>
      if (C i).bullet = (2 : Fin 3) then
        some
          {
            tag := { origin := i, serial := 0 }
            swept := 0
          }
      else
        none
    nextBirth := 1
  }

/-- One proof-only bullet step.

The responder owner rule mirrors the literal row at exactly the level needed
for bad-bullet ancestry:
* old live responder => keep the responder tag (collision absorbs the source);
* otherwise old live source => transfer/increment the source tag;
* otherwise a new live post-bullet is fresh.

Fresh CreateLeader/line-51 bullets are peaceful by the already-proved R6
new-fire facts, so the only load-bearing ancestry case for a surviving bad
bullet is the second branch above. -/
def ghostStep {n psi kappa : Nat}
    (_hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n) : GhostConfig n psi kappa :=
  let j := ring.rightNeighbor e
  let C' := PPL.Convergence.BulletSweep.step ring g.physical e
  let jOwner :=
    if (C' j).bullet = (2 : Fin 3) then
      if (g.physical j).bullet = (2 : Fin 3) then
        g.owner j
      else if (g.physical e).bullet = (2 : Fin 3) then
        bumpOwner (g.owner e)
      else
        some (freshOwner g e)
    else
      none
  {
    physical := C'
    owner := writePair g.owner e none j jOwner
    nextBirth := g.nextBirth + 1
  }

def ghostRun {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) :
    GhostConfig n psi kappa ->
      DetSchedule n ->
      GhostConfig n psi kappa
  | g, [] => g
  | g, e :: rest =>
      ghostRun hpsi ring (ghostStep hpsi ring g e) rest

@[simp] theorem ghostStep_erase
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n) :
    erase (ghostStep hpsi ring g e) =
      PPL.Convergence.BulletSweep.step ring (erase g) e := by
  rfl

/-- Ghost execution projects to the exact physical P_PL run on the same word. -/
theorem ghostRun_projects
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (word : DetSchedule n) :
    erase (ghostRun hpsi ring g word) =
      PPL.Convergence.BulletSweep.run ring (erase g) word := by
  induction word generalizing g with
  | nil =>
      rfl
  | cons e rest ih =>
      change
        erase
            (ghostRun hpsi ring
              (ghostStep hpsi ring g e) rest) =
          PPL.Probability.runPopulationSchedule
            (PPL.protocol psi kappa) ring
            (PopulationProtocol.step
              (PPL.protocol psi kappa) ring (erase g) e)
            rest
      rw [ih (g := ghostStep hpsi ring g e)]
      rfl

private theorem rightNeighbor_ne_self
    {n : Nat} (hn2 : 2 <= n)
    (ring : DirectedRing n) (e : Fin n) :
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
    omega

@[simp] theorem ghostStep_owner_source
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n) :
    (ghostStep hpsi ring g e).owner e = none := by
  simp [ghostStep, writePair]

theorem ghostStep_owner_responder
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (ghostStep hpsi ring g e).owner (ring.rightNeighbor e) =
      (if
          ((ghostStep hpsi ring g e).physical
            (ring.rightNeighbor e)).bullet = (2 : Fin 3)
        then
          if (g.physical (ring.rightNeighbor e)).bullet =
              (2 : Fin 3)
          then
            g.owner (ring.rightNeighbor e)
          else if (g.physical e).bullet = (2 : Fin 3)
          then
            bumpOwner (g.owner e)
          else
            some (freshOwner g e)
        else
          none) := by
  simp [ghostStep, writePair, hne]
  all_goals rfl

theorem ghostStep_owner_other
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e k : Fin n)
    (hke : k ≠ e)
    (hkr : k ≠ ring.rightNeighbor e) :
    (ghostStep hpsi ring g e).owner k = g.owner k := by
  simp [ghostStep, writePair, hke, hkr]

/-- Live tag identities are unique across sites. -/
def NoCloning {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) : Prop :=
  forall (i j : Fin n) (oi oj : BulletOwner n),
    g.owner i = some oi ->
    g.owner j = some oj ->
    oi.tag = oj.tag ->
    i = j

theorem initialGhost_noCloning
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    NoCloning (initialGhost C) := by
  intro i j oi oj hi hj htag
  by_cases hilive : (C i).bullet = (2 : Fin 3)
  · by_cases hjlive : (C j).bullet = (2 : Fin 3)
    · simp [initialGhost, hilive] at hi
      simp [initialGhost, hjlive] at hj
      subst oi
      subst oj
      simpa using congrArg BulletTag.origin htag
    · simp [initialGhost, hjlive] at hj
  · simp [initialGhost, hilive] at hi

def BadLive {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n) : Prop :=
  (C i).bullet = (2 : Fin 3) /\
    ¬ (PPL.Peaceful ring C i)

def TaggedBad {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (tag : BulletTag n)
    (i : Fin n) : Prop :=
  exists o : BulletOwner n,
    g.owner i = some o /\
      o.tag = tag /\
      BadLive ring g.physical i

/-- The lineage no longer owns a bad bullet.  Absorption, collision, and
becoming peaceful all count as retirement for Lemma 15. -/
def LineageRetired {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (tag : BulletTag n) : Prop :=
  forall i : Fin n, ¬ (TaggedBad ring g tag i)

/-- Exact selected-letter progress: the source owner transfers to the
clockwise responder and its swept counter increments once. -/
def Advances {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g g' : GhostConfig n psi kappa)
    (e : Fin n)
    (tag : BulletTag n) : Prop :=
  exists o : BulletOwner n,
    g.owner e = some o /\
      o.tag = tag /\
      g'.owner (ring.rightNeighbor e) =
        some (advanceOwner o)

/-- A gap letter does not change this lineage's stored arc/progress owner. -/
def ArcUnchanged {n psi kappa : Nat}
    (g g' : GhostConfig n psi kappa)
    (i : Fin n)
    (tag : BulletTag n) : Prop :=
  exists o : BulletOwner n,
    g.owner i = some o /\
      o.tag = tag /\
      g'.owner i = some o

/-- One-step bullet-lineage law.

A tagged bad bullet either:
1. retires (is absorbed/collided, or becomes peaceful);
2. if its own outgoing edge is selected, transfers clockwise and increments
   its accumulated sweep arc;
3. for every other scheduler letter, its stored arc/progress is unchanged.

The only identity hypothesis is NoCloning, exactly as in SignalLineage. -/
theorem taggedBad_one_step
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e i : Fin n)
    (tag : BulletTag n)
    (hnc : NoCloning g)
    (htag : TaggedBad ring g tag i) :
    let g' := ghostStep hpsi ring g e
    LineageRetired ring g' tag \/
      (e = i /\ Advances ring g g' e tag) \/
      (e ≠ i /\ ArcUnchanged g g' i tag) := by
  classical
  dsimp only
  let g' := ghostStep hpsi ring g e
  let j := ring.rightNeighbor e
  have hne : j ≠ e := by
    dsimp [j]
    exact rightNeighbor_ne_self (by omega) ring e
  rcases htag with ⟨oi, hoi, hitag, hibad⟩
  by_cases hret : LineageRetired ring g' tag
  · exact Or.inl hret
  · have hsurvive : exists q : Fin n, TaggedBad ring g' tag q := by
      apply Classical.byContradiction
      intro hnone
      apply hret
      intro q hq
      exact hnone ⟨q, hq⟩
    rcases hsurvive with
      ⟨q, oq, hqowner, hqtag, hqbad⟩
    apply Or.inr
    by_cases hei : e = i
    · subst i
      apply Or.inl
      refine ⟨rfl, ?_⟩
      have hqe : q ≠ e := by
        intro h
        subst q
        rw [ghostStep_owner_source] at hqowner
        cases hqowner
      have hqj : q = j := by
        apply Classical.byContradiction
        intro hnot
        have hold : g.owner q = some oq := by
          rw [← ghostStep_owner_other
            hpsi ring g e q hqe (by simpa [j] using hnot)]
          exact hqowner
        have heq :=
          hnc e q oi oq hoi hold
            (hitag.trans hqtag.symm)
        exact hqe heq.symm
      subst q
      by_cases hjlive :
          (g.physical j).bullet = (2 : Fin 3)
      · have holdj : g.owner j = some oq := by
          have hr :=
            ghostStep_owner_responder
              hpsi ring g e (by simpa [j] using hne)
          have hb :
              ((ghostStep hpsi ring g e).physical
                (ring.rightNeighbor e)).bullet = (2 : Fin 3) :=
            hqbad.1
          have hjl :
              (g.physical (ring.rightNeighbor e)).bullet = (2 : Fin 3) :=
            hjlive
          rw [hr, if_pos hb, if_pos hjl] at hqowner
          exact hqowner
        have heq :=
          hnc e j oi oq hoi holdj
            (hitag.trans hqtag.symm)
        exact False.elim (hne heq.symm)
      · refine ⟨oi, hoi, hitag, ?_⟩
        have hr :=
          ghostStep_owner_responder
            hpsi ring g e (by simpa [j] using hne)
        have hb :
            ((ghostStep hpsi ring g e).physical
              (ring.rightNeighbor e)).bullet = (2 : Fin 3) :=
          hqbad.1
        have hjl :
            ¬ (g.physical (ring.rightNeighbor e)).bullet = (2 : Fin 3) :=
          hjlive
        have hel : (g.physical e).bullet = (2 : Fin 3) := hibad.1
        rw [hr, if_pos hb, if_neg hjl, if_pos hel, hoi]
        rfl
    · apply Or.inr
      refine ⟨hei, ?_⟩
      by_cases hij : i = j
      · subst i
        have hqe : q ≠ e := by
          intro h
          subst q
          rw [ghostStep_owner_source] at hqowner
          cases hqowner
        have hqj : q = j := by
          apply Classical.byContradiction
          intro hnot
          have hold : g.owner q = some oq := by
            rw [← ghostStep_owner_other
              hpsi ring g e q hqe (by simpa [j] using hnot)]
            exact hqowner
          have heq :=
            hnc j q oi oq hoi hold
              (hitag.trans hqtag.symm)
          exact hnot heq.symm
        subst q
        refine ⟨oi, hoi, hitag, ?_⟩
        have hr :=
          ghostStep_owner_responder
            hpsi ring g e (by simpa [j] using hne)
        have hb :
            ((ghostStep hpsi ring g e).physical
              (ring.rightNeighbor e)).bullet = (2 : Fin 3) :=
          hqbad.1
        have hjl :
            (g.physical (ring.rightNeighbor e)).bullet = (2 : Fin 3) :=
          hibad.1
        rw [hr, if_pos hb, if_pos hjl]
        exact hoi
      · refine ⟨oi, hoi, hitag, ?_⟩
        have ho :=
          ghostStep_owner_other
            hpsi ring g e i (Ne.symm hei) (by simpa [j] using hij)
        exact ho.trans hoi

/-- The sole remaining ordered-subsequence semantic lemma.

The first conjunct says every initially bad tagged lineage has retired by the
time the two-sweep word has appeared as an ordered subsequence.

The second conjunct is the converse ancestry/coverage statement: every bad
endpoint bullet still carries the tag of some initially bad bullet.  Fresh
fires and descendants of initially peaceful bullets are excluded by the
already-proved R6 new-fire / peaceful-keep laws; proving those facts through
arbitrary interleavings is exactly the run induction still missing here.

The one-step induction is intended to use taggedBad_one_step plus the two
ordered copies of seq_R(0,n). -/
def OrderedSubsequenceBulletSweep : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    (PPL.Convergence.BulletSweep.lemma15SweepWord ring).Sublist schedule ->
      let g0 := initialGhost C
      let g1 := ghostRun hpsi ring g0 schedule
      (forall (i : Fin n) (o : BulletOwner n),
        g0.owner i = some o ->
        BadLive ring C i ->
        LineageRetired ring g1 o.tag) /\
      (forall i : Fin n,
        BadLive ring g1.physical i ->
        exists i0 : Fin n, exists o0 o1 : BulletOwner n,
          g0.owner i0 = some o0 /\
          BadLive ring C i0 /\
          g1.owner i = some o1 /\
          o1.tag = o0.tag)

/-- The original BulletSweep missing Prop follows immediately from the single
ordered-lineage obligation above and the ghost projection theorem. -/
theorem lemma15SublistSweep
    (hordered : OrderedSubsequenceBulletSweep) :
    PPL.Convergence.BulletSweep.Lemma15SublistSweep := by
  intro n psi kappa hn3 hpsi ring C schedule hsub
  let g0 := initialGhost C
  let g1 := ghostRun hpsi ring g0 schedule
  have hline :=
    hordered hn3 hpsi ring C schedule hsub
  have hproj :
      g1.physical =
        PPL.Convergence.BulletSweep.run ring C schedule := by
    have hp :=
      ghostRun_projects hpsi ring (initialGhost C) schedule
    simpa [g0, g1, erase, initialGhost] using hp
  rw [← hproj]
  unfold PPL.Convergence.BulletSweep.AllLivePeaceful
  intro i hlive
  apply Classical.byContradiction
  intro hpeace
  have hbad : BadLive ring g1.physical i :=
    ⟨hlive, hpeace⟩
  obtain ⟨i0, o0, o1, h0, hbad0, h1, htag⟩ :=
    hline.2 i hbad
  have hret :=
    hline.1 i0 o0 h0 hbad0
  exact
    False.elim
      (hret i ⟨o1, h1, htag, hbad⟩)

end PPL.Convergence.BulletLineage

#print axioms PPL.Convergence.BulletLineage.ghostStep_erase
#print axioms PPL.Convergence.BulletLineage.ghostRun_projects
#print axioms PPL.Convergence.BulletLineage.initialGhost_noCloning
#print axioms PPL.Convergence.BulletLineage.taggedBad_one_step
#print axioms PPL.Convergence.BulletLineage.lemma15SublistSweep
